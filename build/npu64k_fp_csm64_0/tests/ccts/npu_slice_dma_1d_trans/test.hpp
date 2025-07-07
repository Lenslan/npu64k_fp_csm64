/*************************************************************************/
/**                                                                     **/
/** Copyright (C) 2021-2022 Synopsys, Inc.                              **/
/** All Rights Reserved.                                                **/
/**                                                                     **/
/** This Synopsys software and all associated documentation are         **/
/** proprietary to Synopsys, Inc. and may only be used pursuant to the  **/
/** terms and conditions of a written license agreement with Synopsys,  **/
/** Inc. All other use, reproduction, modification, or distribution of  **/
/** this Synopsys software or the associated documentation is strictly  **/
/** prohibited.                                                         **/
/**                                                                     **/
/*************************************************************************/

#include <atomic>

// include accelerator interface definition
#include "tensor_dma.hpp"
#include "../../npu_idma/regression/utils/tensor_utils.hpp"

using namespace npu;
using namespace tensor::v200;
using namespace npu_dma;

#include "arcsync_utils.hpp"
#include "utils/cln_map.hpp"
#include "utils/npu_mem_utils.hpp"
#include "utils/npu_mem_map_define.hpp"
#include "test_param.hpp"

#ifdef RTL_ARC
_Uncached volatile unsigned int err_cnt=0;
_Uncached volatile unsigned int chk_cnt=0;
_Uncached volatile unsigned int * err_msg= (unsigned int*)0x1f00_0000;
#else
unsigned int chk_cnt=0;
unsigned int err_cnt=0;
unsigned int * err_msg;
#endif

mem_alloc_t* xmalloc;
mem_alloc_t* vmalloc;
mem_alloc_t* dmalloc;
mem_alloc_t* csmalloc;
mem_alloc_t* dummy_alloc;

// ARC test program
//
class test_program : public arc_program {
public:
  inline test_program() : arc_program() {
    irq_flag = false;
  }
  //
  // virtual functions from base class
  //
  void exec();
  void irq() {
    //fprintf(log, "REPORT: Interrupt found\n");
    irq_flag = true;
  }

  // information from compiler to run-time
  dma_params_impl_main     pr;
  // input and output buffers
  tensor_t<pix_t,4,buffer_t>*       stns_csm;
  tensor_t<pix_t,4,buffer_t>*       dtns_csm;

  shape<4>                 xm_fshp{XM_FUL_SHP};
  shape<4>                 xm_cshp{XM_SUB_SHP};
  shape<4>                 xm_pos{XM_POS};

  shape<4>                 vm_fshp{VM_FUL_SHP};
  shape<4>                 vm_cshp{VM_SUB_SHP};
  shape<4>                 vm_pos{VM_POS};

  void aot_compile() {
    // Allocate a temporary source and destination tensor
    buffer_t<pix_t>                     xmbuf;
    dummy_alloc->alloc(xmbuf, get_shape_size(xm_fshp));
    tensor_t<pix_t,4,buffer_t>          xmftns(xmbuf, xm_fshp);
    tensor_t<pix_t,4,buffer_t>          xmtns(xmftns.slice(xm_pos, xm_cshp));
    
    buffer_t<pix_t>                     vmbuf;
    dummy_alloc->alloc(vmbuf, get_shape_size(vm_fshp));
    tensor_t<pix_t,4>                   vmftns(vmbuf, vm_fshp);
    tensor_t<pix_t,4>                   vmtns(vmftns.slice(vm_pos, vm_cshp));

    // implementation specific data

    //
    // Set up the DMA parameters as the graph compiler would do
    //
    dma_params<buffer_t> pars;
    // set implementation specific parameters
    dma_params_impl_spec ipars;
    ipars = dma_impl_idma;
    pars.set_impl_params(ipars);

    pars.set_src(xmtns);
    pars.set_dst(vmtns);

    // get run-time parameters
    pars.get_rt_params(pr);
  }

  void prep_operands() {
    // set up actual input and output tensors in the memories
    // allocate source tensor in CSM and destination tensor in VM
    buffer_t<pix_t>          xmbuf;
    buffer_t<pix_t>          vmbuf;

    csmalloc->alloc(xmbuf, get_shape_size(xm_fshp));
    tensor_t<pix_t,4,buffer_t>                   xmtns(xmbuf, xm_fshp);
    tensor_t<pix_t,4,buffer_t>                   xmtns_cut(xmtns.slice(xm_pos, xm_cshp));

    vmalloc->alloc(vmbuf, get_shape_size(vm_fshp));
    tensor_t<pix_t,4,buffer_t>                   vmtns(vmbuf, vm_fshp);
    tensor_t<pix_t,4,buffer_t>                   vmtns_cut(vmtns.slice(vm_pos, vm_cshp));

    #ifdef RTL_FAST_SIM
    // initialize the source tensor
    //TODO: next step is CSM memory backdoor initilization 
    //set_mem_backdoor(1,0);
    //tensor_init_from<pix_t,4>(xmImg, xmtns);    
    //set_mem_backdoor(0,0);
  #endif



    // move tensor metadata to CSM
    xmalloc->alloc(stns_csm);
    mem_write(stns_csm, xmtns_cut);
    xmalloc->alloc(dtns_csm);
    mem_write(dtns_csm, vmtns_cut);
  }
  
  
  void run_time() {
    ctrl_dma_regs<dma_hlapi_t>& iregs(*reinterpret_cast<npu::ctrl_dma_regs<npu_dma::dma_hlapi_t>*>(get_mmio_base_idma()));
    ctrl_dma_regs<dma_hlapi_t>& oregs(*reinterpret_cast<npu::ctrl_dma_regs<npu_dma::dma_hlapi_t>*>(get_mmio_base_odma()));
    // create run-time descriptor in DM memory
    dma_rt& rt1(*create(*dmalloc, pr));
    dma_rt& rt2(*create(*dmalloc, pr));

    // set run-time source and destination tensors
    rt1.set_src(*stns_csm);
    rt1.set_dst(*dtns_csm);

    rt2.set_src(*dtns_csm);
    rt2.set_dst(*stns_csm);
    
    // set run-time specific parameters
    dma_rt_impl_spec* rtp1;
    dma_rt_impl_spec* rtp2;
    xmalloc->alloc(rtp1);
    xmalloc->alloc(rtp2);

    // iDMA
    mem_write(&rtp1->mmio.d, &iregs);  // MMIO base address
    mem_write(&rtp1->ctrl, (uint32_t)1);      // raise event at completion
    rt1.set_impl_params(*rtp1);
    
    // enable interrupts and events
    mmio_write(&iregs.int_enable, 0xffffffff);
    run_cycles(1);

    // oDMA
    mem_write(&rtp2->mmio.d, &oregs);  // MMIO base address
    mem_write(&rtp2->ctrl, (uint32_t)1);      // raise event at completion
    rt2.set_impl_params(*rtp2);
    
    // enable interrupts and events
    mmio_write(&oregs.int_enable, 0xffffffff);
    run_cycles(1);

    // prefetch and execute
    rt1.execute();
    rt2.execute();
    run_cycles(1);

    // wait for completion
    event_wait_all(((1LL<<EVT_IDMA_DONE) | (1LL<<EVT_ODMA_DONE)));
    run_cycles(10);
  }

  void report() {
    tensor_iterator_t<pix_t,4> it(*dtns_csm);
    int i=0;
    do {
      pix_t act=it.read();
      pix_t ref=refImg[i++];
      check(ref, act);
    } while (it.next());
  }

private:

  // checker, stop simulation if mismatch
  template<typename T>
  void check(T a, T b) {
    if (a != b) {
      set_sim_finish_flag(++err_cnt);
    }
  }

  std::atomic<bool> irq_flag;
  uint32_t proc_id;
  
};

// Main test program
void test_program::exec() {
    arcsync_id_init();
    proc_id = get_proc_id();
    evt_cfg();

    if(proc_id == 0) { //l2arc
        cfg_system_map();

        uint64_t mask = (1LL << EVT_CHILD0);
        event_send_children((long long)mask);
        event_wait_all ((long long)mask);
    }
    else if(proc_id == 1 | !NPU_HAS_L2ARC){ //l1arc
        // Add extra flags to test event_wait_any
        uint64_t mask = ((1LL << EVT_PARENT) | (1LL<<EVT_STU0_DONE));
        if (NPU_HAS_L2ARC){
            event_wait_any ((long long)mask);
        }
        #ifdef NPU_MEM_ECC
        uint32_t sfty_erp_ctrl_addr;
        sfty_erp_ctrl_addr = LOCAL_PERI_BASE + L1_SFTY_MMIO_OFFSET + 0x0_0000;
        vm_mem_init((uint32_t *)sfty_erp_ctrl_addr);
        #endif
        
        vmalloc = new mem_alloc_t((uint64_t)get_slice_vm_base(), 0x10000);
        dmalloc = new mem_alloc_t((uint64_t)get_fast_dccm_base(), 0x10000);
        xmalloc = new mem_alloc_t((uint64_t)0, 0x80000000);
        dummy_alloc = new mem_alloc_t((uint64_t)0x80000000, 0x10000000);
        csmalloc = new mem_alloc_t((uint64_t)/*LC_CSM_BASE*/xmImg, 0x0010000);

        aot_compile();
        cout << "aot compile done " << endl;
        prep_operands();
        cout << "opreands done " << endl;
        run_time();
        cout << "run time done " << endl;
        report();

        event_send_parent();
    }
    set_sim_finish_flag(err_cnt);

}

  
