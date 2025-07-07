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

#include "test_param.hpp"
#include "utils/cln_map.hpp"

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
mem_alloc_t* csmalloc;
mem_alloc_t* dmalloc;
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
  tensor_t<pix_t,4,buffer_t>* stns_csm;
  tensor_t<pix_t,4,buffer_t>* dtns_csm;

  shape<4>                 xmi_fshp{XMI_FUL_SHP};
  shape<4>                 xmi_cshp{XMI_SUB_SHP};
  shape<4>                 xmi_pos{XMI_POS};

  shape<4>                 xmo_fshp{XMO_FUL_SHP};
  shape<4>                 xmo_cshp{XMO_SUB_SHP};
  shape<4>                 xmo_pos{XMO_POS};

  void aot_compile() {
    // Allocate a temporary source and destination tensor
    buffer_t<pix_t>                     xmibuf;
    dummy_alloc->alloc(xmibuf, get_shape_size(xmi_fshp));
    tensor_t<pix_t,4,buffer_t>          xmiftns(xmibuf, xmi_fshp);
    tensor_t<pix_t,4,buffer_t>          xmitns(xmiftns.slice(xmi_pos, xmi_cshp));
    
    buffer_t<pix_t>                     xmobuf;
    dummy_alloc->alloc(xmobuf, get_shape_size(xmo_fshp));
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
    pars.get_rt_params(pr);
  }

  void prep_operands() {
    // set up actual input and output tensors in the memories
    // allocate source tensor in CSM and destination tensor in VM
    buffer_t<pix_t>          xmibuf;
    buffer_t<pix_t>          xmobuf;

    xmalloc->alloc(xmibuf, get_shape_size(xmi_fshp));
    tensor_t<pix_t,4>                   xmitns(xmibuf, xmi_fshp);
    tensor_t<pix_t,4>                   xmitns_cut(xmitns.slice(xmi_pos, xmi_cshp));

    csmalloc->alloc(xmobuf, get_shape_size(xmo_fshp));
    tensor_t<pix_t,4>                   xmotns(xmobuf, xmo_fshp);
    tensor_t<pix_t,4>                   xmotns_cut(xmotns.slice(xmo_pos, xmo_cshp));

    set_mem_backdoor(1,0);
    //tensor_init_from<pix_t,4>(xmarr, xmitns);    
    set_mem_backdoor(0,0);

    // move tensor metadata to CSM
    xmalloc->alloc(stns_csm);
    mem_write(stns_csm, xmitns_cut);
    xmalloc->alloc(dtns_csm);
    mem_write(dtns_csm, xmotns_cut);
  }
  
  
  void run_time_in() {
    ctrl_dma_regs<stu_hlapi_t>& regs(*reinterpret_cast<npu::ctrl_dma_regs<npu_stu::stu_hlapi_t>*>(get_mmio_base_stu(0)));
    // create run-time descriptor in DM memory
    dma_rt& rt(*create(*dmalloc, pr));

    // set run-time source and destination tensors
    rt.set_src(*stns_csm);
    rt.set_dst(*dtns_csm);
    
    // set run-time specific parameters
    dma_rt_impl_spec* rtp;
    xmalloc->alloc(rtp);
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
    // Add extra flags to test event_wait_any
    event_wait_any((1LL<<EVT_STU0_DONE) | (1LL<<EVT_CONV_DONE));
    run_cycles(10);
  }

  void run_time_out() {
    ctrl_dma_regs<stu_hlapi_t>& regs(*reinterpret_cast<npu::ctrl_dma_regs<npu_stu::stu_hlapi_t>*>(get_mmio_base_stu(0)));
    // create run-time descriptor in DM memory
    dma_rt& rt(*create(*dmalloc, pr));

    // set run-time source and destination tensors
    rt.set_src(*dtns_csm);
    rt.set_dst(*stns_csm);
    
    // set run-time specific parameters
    dma_rt_impl_spec* rtp;
    xmalloc->alloc(rtp);
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
    // Add extra flags to test event_wait_any
    event_wait_any((1LL<<EVT_STU0_DONE) | (1LL<<EVT_CONV_DONE));
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
    
    set_sim_finish_flag(err_cnt);
  }

private:

  // checker, stop simulation if mismatch
  template<typename T> void check(T a, T b) {
    chk_cnt++;
    if (a != b) {
        *err_msg++ = err_cnt++;
        *err_msg++ = (unsigned int)a;
        *err_msg++ = (unsigned int)b;
        set_sim_finish_flag(err_cnt);
    }
  }

  std::atomic<bool> irq_flag;
  
};

// Main test program
void test_program::exec() {
  evt_cfg();
  dmalloc = new mem_alloc_t((uint64_t)get_fast_dccm_base(), 0x10000);
  xmalloc = new mem_alloc_t((uint64_t)xmImg, 0x70000000);
  csmalloc = new mem_alloc_t((uint64_t)LC_CSM_BASE, 0x10000);
  dummy_alloc = new mem_alloc_t((uint64_t)0x70000000, 0x10000000);

  cfg_system_map();

  aot_compile();
//  cout << "aot compile done " << endl;
  prep_operands();
//  cout << "opreands done " << endl;
  run_time_in();
  run_time_out();
//  cout << "run time done " << endl;
  report();

}

  
