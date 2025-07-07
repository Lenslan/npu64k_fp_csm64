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

#include "utils/cln_map.hpp"
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


mem_alloc_t* xmalloc_stu;
mem_alloc_t* csmalloc_stu;
mem_alloc_t* dmalloc_stu;
mem_alloc_t* dummy_alloc_stu;

mem_alloc_t* xmalloc_dma;
mem_alloc_t* vmalloc_dma;
mem_alloc_t* dmalloc_dma;
mem_alloc_t* csmalloc_dma;
mem_alloc_t* dummy_alloc_dma;

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
  tensor_t<pix_t,4,buffer_t>* stns_csm;
  tensor_t<pix_t,4,buffer_t>* dtns_csm;

  shape<4>                 xm_fshp{XM_FUL_SHP};
  shape<4>                 xm_cshp{XM_SUB_SHP};
  shape<4>                 xm_pos{XM_POS};

  shape<4>                 vm_fshp{VM_FUL_SHP};
  shape<4>                 vm_cshp{VM_SUB_SHP};
  shape<4>                 vm_pos{VM_POS};

  
  dma_params_impl_main     pr_stu;
  // input and output buffers
  tensor_t<pix_t,4,buffer_t>* stns_csm_dma;
  tensor_t<pix_t,4,buffer_t>* dtns_csm_dma;

  shape<4>                 xmi_fshp{XMI_FUL_SHP};
  shape<4>                 xmi_cshp{XMI_SUB_SHP};
  shape<4>                 xmi_pos{XMI_POS};

  shape<4>                 xmo_fshp{XMO_FUL_SHP};
  shape<4>                 xmo_cshp{XMO_SUB_SHP};
  shape<4>                 xmo_pos{XMO_POS};

  void aot_compile_stu() {
    // Allocate a temporary source and destination tensor
    buffer_t<pix_t>                     xmibuf;
    dummy_alloc_stu->alloc(xmibuf, get_shape_size(xmi_fshp));
    tensor_t<pix_t,4,buffer_t>          xmiftns(xmibuf, xmi_fshp);
    tensor_t<pix_t,4,buffer_t>          xmitns(xmiftns.slice(xmi_pos, xmi_cshp));
    
    buffer_t<pix_t>                     xmobuf;
    dummy_alloc_stu->alloc(xmobuf, get_shape_size(xmo_fshp));
    tensor_t<pix_t,4,buffer_t>          xmoftns(xmobuf, xmo_fshp);
    tensor_t<pix_t,4,buffer_t>          xmotns(xmoftns.slice(xmo_pos, xmo_cshp));

    // implementation specific data

    //
    // Set up the DMA parameters as the graph compiler would do
    //
    dma_params<buffer_t> pars;
    // set implementation specific parameters
    dma_params_impl_spec ipars;
    ipars = dma_impl_stu;
    pars.set_impl_params(ipars);

    pars.set_src(xmitns);
    pars.set_dst(xmotns);

    // get run-time parameters
    pars.get_rt_params(pr_stu);
    //pr_stu.hlapi.s.i.xmi_seq.compress = 6;
    pr_stu.hlapi.s.i.xmi_seq.offsets[3] = -127;
    pr_stu.hlapi.s.i.xmi_seq.iter[3] = 2048;
    pr_stu.hlapi.s.i.xmo_seq.offsets[3] = -127;
    pr_stu.hlapi.s.i.xmo_seq.iter[3] = 2048;

  }

  void prep_operands_stu() {
    // set up actual input and output tensors in the memories
    // allocate source tensor in CSM and destination tensor in VM
    buffer_t<pix_t>          xmibuf;
    buffer_t<pix_t>          xmobuf;

    xmalloc_stu->alloc(xmibuf, get_shape_size(xmi_fshp));
    tensor_t<pix_t,4>                   xmitns(xmibuf, xmi_fshp);
    tensor_t<pix_t,4>                   xmitns_cut(xmitns.slice(xmi_pos, xmi_cshp));

    csmalloc_stu->alloc(xmobuf, get_shape_size(xmo_fshp));
    tensor_t<pix_t,4>                   xmotns(xmobuf, xmo_fshp);
    tensor_t<pix_t,4>                   xmotns_cut(xmotns.slice(xmo_pos, xmo_cshp));

    // move tensor metadata to CSM
    xmalloc_stu->alloc(stns_csm);
    mem_write(stns_csm, xmitns_cut);
    xmalloc_stu->alloc(dtns_csm);
    mem_write(dtns_csm, xmotns_cut);
  }
  
  
  void run_time_stu() {
    ctrl_dma_regs<stu_hlapi_t>& regs(*reinterpret_cast<npu::ctrl_dma_regs<npu_stu::stu_hlapi_t>*>(get_mmio_base_stu(0)));
    // create run-time descriptor in DM memory
    dma_rt& rt(*create(*dmalloc_stu, pr_stu));

    // set run-time source and destination tensors
    rt.set_src(*stns_csm);
    rt.set_dst(*dtns_csm);
    
    // set run-time specific parameters
    dma_rt_impl_spec* rtp;
    xmalloc_stu->alloc(rtp);
    mem_write(&rtp->mmio.s, &regs);  // MMIO base address
    mem_write(&rtp->ctrl, (uint32_t)1);      // raise event at completion
    rt.set_impl_params(*rtp);
    
    // enable interrupts and events
    mmio_write(&regs.int_enable, 0xffffffff);
    run_cycles(1);

    // prefetch and execute
    rt.prepare();
    run_cycles(1);
    rt.execute();
    run_cycles(1);

    // wait for completion
    event_wait_any(1LL<<EVT_STU0_DONE);
    run_cycles(10);
  }

  void report_stu() {
    tensor_iterator_t<pix_t,4> it(*dtns_csm);
    int i=0;
    do {
      int act=it.read();
      int ref=xmI_stu[i++];
      cout << "ref:" << endl;
      cout << ref << endl;
      cout << "act:" << endl;
      cout << act << endl;

      check(ref, act);
    } while (it.next());
    
    set_sim_finish_flag(err_cnt);
  }

   void aot_compile_dma() {
    // Allocate a temporary source and destination tensor
    buffer_t<pix_t>                     xmbuf;
    dummy_alloc_dma->alloc(xmbuf, get_shape_size(xm_fshp));
    tensor_t<pix_t,4>                   xmftns(xmbuf, xm_fshp);
    tensor_t<pix_t,4>                   xmtns(xmftns.slice(xm_pos, xm_cshp));
    
    buffer_t<pix_t>                     vmbuf;
    dummy_alloc_dma->alloc(vmbuf, get_shape_size(vm_fshp));
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

    pr.hlapi.d.i.xm_seq.compress = 0;
    pr.hlapi.d.i.xm_seq.iter[3] = 2048;
    pr.hlapi.d.i.xm_seq.offsets[3] = -127;
    pr.hlapi.d.i.vm_seq.iter[3] = 2048;
    pr.hlapi.d.i.vm_seq.offsets[3] = -7;

  }

  void prep_operands_dma() {
    // set up actual input and output tensors in the memories
    // allocate source tensor in CSM and destination tensor in VM
    buffer_t<pix_t>          xmbuf;
    buffer_t<pix_t>          vmbuf;

    csmalloc_dma->alloc(xmbuf, get_shape_size(xm_fshp));
    tensor_t<pix_t,4,buffer_t> xmtns(xmbuf, xm_fshp);
    tensor_t<pix_t,4,buffer_t> xmtns_cut(xmtns.slice(xm_pos, xm_cshp));

    vmalloc_dma->alloc(vmbuf, get_shape_size(vm_fshp));
    tensor_t<pix_t,4,buffer_t> vmtns(vmbuf, vm_fshp);
    tensor_t<pix_t,4,buffer_t> vmtns_cut(vmtns.slice(vm_pos, vm_cshp));

    #ifdef RTL_FAST_SIM
    // initialize the source tensor
    //TODO: next step is CSM memory backdoor initilization 
    //set_mem_backdoor(1,0);
    //tensor_init_from<pix_t,4>(xmImg, xmtns);    
    //set_mem_backdoor(0,0);
  #endif



    // move tensor metadata to CSM
    xmalloc_dma->alloc(stns_csm_dma);
    mem_write(stns_csm_dma, xmtns_cut);
    xmalloc_dma->alloc(dtns_csm_dma);
    mem_write(dtns_csm_dma, vmtns_cut);
  }
  
  
  void run_time_dma() {
    ctrl_dma_regs<dma_hlapi_t>& regs(*reinterpret_cast<npu::ctrl_dma_regs<npu_dma::dma_hlapi_t>*>(get_mmio_base_idma()));
    // create run-time descriptor in DM memory
    dma_rt& rt(*create(*dmalloc_dma, pr));

    // set run-time source and destination tensors
    rt.set_src(*stns_csm_dma);
    rt.set_dst(*dtns_csm_dma);
    
    // set run-time specific parameters
    dma_rt_impl_spec* rtp;
    xmalloc_dma->alloc(rtp);
    mem_write(&rtp->mmio.d, &regs);  // MMIO base address
    mem_write(&rtp->ctrl, (uint32_t)1);      // raise event at completion
    rt.set_impl_params(*rtp);
    
    // enable interrupts and events
    mmio_write(&regs.int_enable, 0xffffffff);
    run_cycles(1);

    // prefetch and execute
    rt.prepare();
    run_cycles(1);
    rt.execute();
    run_cycles(1);

    // wait for completion
    event_wait_any(1LL<<EVT_IDMA_DONE);
    run_cycles(10);
  }

  void report_dma() {
    tensor_iterator_t<pix_t,4> it(*dtns_csm_dma);
    int i=0;
    do {
      int act=it.read();
      int ref=refImg_dma[i++];
      cout << "ref:" << endl;
      cout << ref << endl;
      cout << "act:" << endl;
      cout << act << endl;
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
        dmalloc_stu = new mem_alloc_t((uint64_t)get_fast_dccm_base(), 0x10000);
        xmalloc_stu = new mem_alloc_t((uint64_t)xmI_stu, 0x70000000);
        csmalloc_stu = new mem_alloc_t((uint64_t)LC_CSM_BASE, 0x10000);
        dummy_alloc_stu = new mem_alloc_t((uint64_t)0x70000000, 0x10000000);

        cfg_system_map();

        aot_compile_stu();
        prep_operands_stu();
        run_time_stu();
        report_stu();
    }
    else if(proc_id == 1) { //slice 0 


        vmalloc_dma = new mem_alloc_t((uint64_t)get_slice_vm_base(), 0x10000);
        dmalloc_dma = new mem_alloc_t((uint64_t)get_fast_dccm_base(), 0x10000);
        xmalloc_dma = new mem_alloc_t((uint64_t)0, 0x80000000);
        dummy_alloc_dma = new mem_alloc_t((uint64_t)0x80000000, 0x10000000);
        csmalloc_dma = new mem_alloc_t((uint64_t)/*LC_CSM_BASE*/xmI_dma, 0x0010000);
        

        aot_compile_dma();
        cout << "dma aot compile done " << endl;
        prep_operands_dma();
        cout << "dma opreands done " << endl;
        run_time_dma();
        cout << "run time done " << endl;
        report_dma();

    }
    set_sim_finish_flag(err_cnt);

}

  
