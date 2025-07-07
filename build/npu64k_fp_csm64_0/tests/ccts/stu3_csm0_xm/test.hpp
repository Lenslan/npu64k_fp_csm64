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
#include "test_param.hpp"
#include "utils/npu_mem_utils.hpp"
/*
  this test execute test data movement from source memory to destination mem
  It consists of two STU descriptors
      descp0: move full size of iImg from XM(in MSS) to source memory, used to initilizate source memory.
      descp1: move data from source memory to target memory(main test purpose)
*/


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
mem_alloc_t* dmalloc;
mem_alloc_t* dummy_alloc;
mem_alloc_t* x_alloc;
mem_alloc_t* src_alloc;
mem_alloc_t* dst_alloc;

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
  dma_params_impl_main     pr0, pr;
  // input and output buffers
  tensor_t<pix_t,4,buffer_t>*       stns;
  tensor_t<pix_t,4,buffer_t>*       dtns;
  tensor_t<pix_t,4,buffer_t>*       sftns;
  tensor_t<pix_t,4,buffer_t>*       dftns;

  shape<4>                 i_fshp{XMI_FUL_SHP};
  shape<4>                 i_cshp{XMI_SUB_SHP};
  shape<4>                 i_pos{XMI_POS};

  shape<4>                 o_fshp{XMO_FUL_SHP};
  shape<4>                 o_cshp{XMO_SUB_SHP};
  shape<4>                 o_pos{XMO_POS};

  void aot_compile() {
    // Allocate a temporary source and destination tensor
    buffer_t<pix_t>                     ibuf;
    dummy_alloc->alloc(ibuf, get_shape_size(i_fshp));
    tensor_t<pix_t,4,buffer_t>          iftns(ibuf, i_fshp);
    tensor_t<pix_t,4,buffer_t>          itns(iftns.slice(i_pos, i_cshp));
    
    buffer_t<pix_t>                     obuf;
    dummy_alloc->alloc(obuf, get_shape_size(o_fshp));
    tensor_t<pix_t,4,buffer_t>          oftns(obuf, o_fshp);
    tensor_t<pix_t,4,buffer_t>          otns(oftns.slice(o_pos, o_cshp));

    // implementation specific data

    //
    // Set up the DMA parameters as the graph compiler would do
    //
    dma_params<buffer_t> pars0, pars;
    // set implementation specific parameters
    dma_params_impl_spec ipars;
    ipars = dma_impl_stu;
    pars0.set_impl_params(ipars);
    pars.set_impl_params(ipars);

    pars0.set_src(iftns);
    pars0.set_dst(oftns);

    pars.set_src(itns);
    pars.set_dst(otns);

    // get run-time parameters
    pars0.get_rt_params(pr0);
    pars.get_rt_params(pr);
  }

  void prep_operands() {
    // set up actual input and output tensors in the memories
    // allocate source tensor in CSM and destination tensor in VM
    buffer_t<pix_t>          xbuf;
    buffer_t<pix_t>          ibuf;
    buffer_t<pix_t>          obuf;
    
    x_alloc->alloc(xbuf, get_shape_size(i_fshp));
    tensor_t<pix_t,4,buffer_t> xtns(xbuf, i_fshp);

    src_alloc->alloc(ibuf, get_shape_size(i_fshp));
    tensor_t<pix_t,4,buffer_t> itns(ibuf, i_fshp);
    tensor_t<pix_t,4,buffer_t> itns_cut(itns.slice(i_pos, i_cshp));

    dst_alloc->alloc(obuf, get_shape_size(o_fshp));
    tensor_t<pix_t,4,buffer_t> otns(obuf, o_fshp);
    tensor_t<pix_t,4,buffer_t> otns_cut(otns.slice(o_pos, o_cshp));

    set_mem_backdoor(1,0);
    //tensor_init_from<pix_t,4>(xmarr, itns);    
    set_mem_backdoor(0,0);

    // move tensor metadata to xm
    xmalloc->alloc(sftns);
    mem_write(sftns, xtns);
    xmalloc->alloc(dftns);
    mem_write(dftns, itns);

    xmalloc->alloc(stns);
    mem_write(stns, itns_cut);
    xmalloc->alloc(dtns);
    mem_write(dtns, otns_cut);
  }
  
  
  void run_time() {
    ctrl_dma_regs<stu_hlapi_t>& regs(*reinterpret_cast<npu::ctrl_dma_regs<npu_stu::stu_hlapi_t>*>(get_mmio_base_stu(3)));
    // create run-time descriptor in DM memory
    dma_rt& rt0(*create(*dmalloc, pr0));
    dma_rt& rt(*create(*dmalloc, pr));

    // set run-time source and destination tensors
    rt0.set_src(*sftns);
    rt0.set_dst(*dftns);
    rt.set_src(*stns);
    rt.set_dst(*dtns);
    
    // set run-time specific parameters
    dma_rt_impl_spec *rtp0, *rtp;
    
    xmalloc->alloc(rtp0);
    xmalloc->alloc(rtp);

    mem_write(&rtp0->mmio.s, &regs);  // MMIO base address
    mem_write(&rtp0->ctrl, (uint32_t)1);      // raise event at completion
    mem_write(&rtp->mmio.s, &regs);  // MMIO base address
    mem_write(&rtp->ctrl, (uint32_t)1);      // raise event at completion

    rt0.set_impl_params(*rtp0);
    rt.set_impl_params(*rtp);

    // enable interrupts and events
    mmio_write(&regs.int_enable, 0xffffffff);
    run_cycles(1);

    // prefetch and execute
    rt0.prepare();
    mem_write(&rt.pars.hlapi.s.i.common.next, globalptr_t<hlapi_i_t>(nullptr));

    rt0.execute();

    mmio_write(&regs.concat_head, globalptr_t<stu_hlapi_t>(fast2global_dccm(&rt.pars.hlapi.s)));
    mmio_write(&regs.concat_tail, globalptr_t<stu_hlapi_t>(fast2global_dccm(&rt.pars.hlapi.s)));
    
	mmio_write(&regs.issue,0x00000002U);

    // wait for completion
    event_wait_any(1LL<<EVT_STU3_DONE);
    run_cycles(10);
  }

  void report() {
    tensor_iterator_t<pix_t,4> it(*dtns);
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
  dmalloc = new mem_alloc_t((uint64_t)get_fast_dccm_base(), 0x1000);
  xmalloc = new mem_alloc_t((uint64_t)0, 0x10000);
  dummy_alloc = new mem_alloc_t((uint64_t)0x80000000, 0x10000000);
  x_alloc = new mem_alloc_t((uint64_t)iImg, 0x10000);
  src_alloc = new mem_alloc_t((uint64_t)SRC_MEM_ALLOC_BASE, 0x4000);
  dst_alloc = new mem_alloc_t((uint64_t)DST_MEM_ALLOC_BASE, 0x4000);

  for(int grp=0; grp<NPU_NUM_GRP; grp++) {
    cfg_grp_sid_ssid(grp, grp+0xedcba987, 0x12345678);
  }

  aot_compile();
  cout << "aot compile done " << endl;
  prep_operands();
  //init();
  #ifdef NPU_MEM_ECC
  for(int grp=0; grp<NPU_NUM_GRP; grp++) {
    for(int slc=0; slc<NPU_NUM_SLC_PER_GRP; slc++) {
	    vm_am_mem_init((uint32_t *)(LOCAL_CLST0_BASE + grp*0x1000000 + slc * 0x400000 + L1_SFTY_MMIO_OFFSET));   //init both vm and am
    }
  }
  #endif
  cout << "opreands done " << endl;
  run_time();
  cout << "run time done " << endl;
  report();

}

 
