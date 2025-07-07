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

/*
  Generic tensor PReLU activation test
 */

// number of groups
#define GRP     1
// number of output channels
#define NO      5
// output inner loop
#define ONN     1
// output shape
#define OSHP    {3,4,1}
// 48b input
#define IDBL    false
// 16b output
#define ODBL    false
// output stride
#define OSTR {1,1,1}
// saturation option
#define OSAT    true
// unary operation
#define OPI     op_abs

#include "utils/tensor_utils.hpp"
#include "utils/npu_mem_map_define.hpp"
#include "utils/sim_terminate.hpp"
#include "tensor_gtoa_unary.hpp"
using namespace tensor::v200;

#include <fstream>

#ifdef RTL_ARC
_Uncached volatile unsigned int err_cnt=0;
_Uncached volatile unsigned int chk_cnt=0;
_Uncached volatile unsigned int * err_msg= (unsigned int*)0x1f00_0000;
#else
unsigned int chk_cnt=0;
unsigned int err_cnt=0;
unsigned int * err_msg;
#endif

static pix_t fmok[] = {
    #include "ref/fm.ok"
};


mem_alloc_t* xmalloc;
mem_alloc_t* vmalloc;
mem_alloc_t* amalloc;
mem_alloc_t* dmalloc;
mem_alloc_t* pnmalloc;

//
// The test
//

class test_program : public arc_program
{
public:
  inline test_program() : arc_program()
  {
    irqflag = false;
  }
  virtual void irq() {
    irqflag = true;
  }

  // parameters to run-time
  gtoa_params_impl_main       rtpars;     // main parameters
  acc_buf_impl_t<buffer_t>              ain;        // input accumulator in AM
  impl_spec_container_t<buffer_t>       l1buf;      // output feature-map in VM
  acc_buf_impl_t<xbuffer_t>             ain_xb;        // input accumulator in AM
  impl_spec_container_t<xbuffer_t>      l1buf_xb;      // output feature-map in VM
  acc_buf_impl_t<buffer_t>*             ain_xm;
  impl_spec_container_t<buffer_t>*      l1buf_xm;

  void aot_compile() {

    // create a unary parameter object...
    gtoa_unary_params<buffer_t> pars(NO,OSHP,ODBL,OPI,OSAT);
    gtoa_act_params_impl_shapes shps;
    pars.get_shapes(shps);

    ain = acc_buf_impl_t<buffer_t>(*amalloc, shps.ishape);
    l1buf = impl_spec_container_t<buffer_t>(*vmalloc, shps.oshape);
    pars.init_l1_output(l1buf);
    pars.get_rt_params(rtpars);
  }

  void prepare_operands() {
    shape<3> oshp(OSHP);
    buffer_t<acc_t> abuf;
    xmalloc->alloc(abuf, NO*get_shape_size(oshp)*(ODBL?2:1));
    tensor_t<acc_t,5> atns(abuf, {((aoffset_t)(ODBL?2:1)),NO,oshp[0],oshp[1],oshp[2]});
    tensor_init_incr<acc_t,5>((acc_t)-170, atns);
    convertto(ain, atns);

    xmalloc->alloc(ain_xm);
    xmalloc->alloc(l1buf_xm);
    mem_write(ain_xm, ain);
    mem_write(l1buf_xm, l1buf);
  }

  void run_time() {
    // run-time execution
    npu::ctrl_dma_regs<npu_act::act_hlapi_t>&   rgs(*reinterpret_cast<npu::ctrl_dma_regs<npu_act::act_hlapi_t>*>(get_mmio_base_act()));

    // create a run-time object
    gtoa_rt& act_rt(*create(*dmalloc, rtpars));

    // set run-time specific parameters
    gtoa_rt_impl_spec* rtp;
    xmalloc->alloc(rtp);
    mem_write(&rtp->mmio, &rgs);  // MMIO base address
    mem_write(&rtp->ctrl, (uint32_t)1);     // raise event at completion
    mem_write(&rtp->id,  (int32_t)(proc_id + 0x1234)); // trace payload
    act_rt.set_impl_params(*rtp);

    act_rt.set_acc_input0(*ain_xm);
    act_rt.set_output(*l1buf_xm);
    mmio_write(&rgs.int_enable, 0xffffffff);
    act_rt.prepare();
    act_rt.execute();

    // wait for completion
    event_wait_any(1LL<<EVT_ACT_DONE);
  }

  void report() {
    // report the output tensor
    shape<3> oshp(OSHP);

    buffer_t<pix_t>                     dbuf;
    xmalloc->alloc(dbuf, NO*get_shape_size(oshp));
    tensor_t<pix_t,4>                   dtns(dbuf, {NO, oshp[0],oshp[1],oshp[2]});

    bool active;
    const_tensor_iterator_t<ixpix_t,5> bit(l1buf_xm->data);
    tensor_iterator_t<pix_t,4> oit(dtns);
    int j = 0;
    do {
      for (int w = 0; w < l1buf_xm->data.get_dim(2); w++) {
        aoffset_t c = 0;
        for (int n = 0; n < l1buf_xm->data.get_dim(0); n++) {
          ixpix_t v(bit.read());
          bit.next();
          for (int i = 0; i < ISIZE; i++) {
            if (c < dtns.get_dim(0) && w < dtns.get_dim(1)) {
              //oit.write(v[i]);
              if(fmok[j++] != v[i]){
                set_sim_finish_flag(++err_cnt);
              }
              active = oit.next();
              c++;
            }
          }
        }
      }
    } while (active);
  //}
  }

  void exec() {
    arcsync_id_init();
    proc_id = get_proc_id();
    evt_cfg();
    if((proc_id == 0) && (NPU_HAS_L2ARC)) {  // L2 ARC
      uint64_t mask = 0;
      for(int slc=0; slc<NPU_SLICE_NUM; slc++){
          mask = mask | (1 << (EVT_CHILD0+slc));
      }
      event_wait_all ((long long)mask);

      // do anything
      _Uncached volatile int* ptr = (int*)NPU_ARC_DCCM_BASE;
      int data = 0;
      for(int i=0; i<200; i++){
        *ptr++ = data + i;
      }
       _sr(0XABCDE012, 0X387); //SWE 0
       _sr(0x12345678, 0X388);//SWE 1

        //self checking -- comparing the tcodes of generted meassages 
        //tcodes dumped into 0x40 & 0x41 aux regs
    //    uint32_t tcode_data = 0;
    //    while (tcode_data != 0x07_07_07_3d) { // expected tcode -- first cstm and then all swe's 
    //          _sr (0x40,0x380);
    //          _sr (0x0,0x382);
    //    tcode_data = _lr(0x381);
    //    }

    //    uint32_t tcode_data1 = 0;
    //    while ((tcode_data1 != 0x07_07_07_07) && (tcode_data1 != 0x00_07_07_07)) { // expected tcode -- all swe's 
    //          _sr (0x41,0x380);
    //          _sr (0x0,0x382);
    //    tcode_data1 = _lr(0x381);
    //    }      
      
    }
    else { // L1 ARC
      xmalloc  = new mem_alloc_t((uint64_t)0, 0x80000000);
      vmalloc  = new mem_alloc_t((uint64_t)get_slice_vm_base(), 0x10000);
      amalloc  = new mem_alloc_t((uint64_t)get_slice_am_base(), 0x10000);
      dmalloc  = new mem_alloc_t((uint64_t)get_fast_dccm_base(), 0x10000);
      size_t nm_sz = 1*1024*1024;
      uint8_t* pnm = (uint8_t *)malloc(nm_sz);// assert(pnm);
      pnmalloc = new mem_alloc_t(reinterpret_cast<uint64_t>(pnm), nm_sz);
       _sr(0XABCDE012, 0X387); //SWE 0

      aot_compile();
      prepare_operands();
      run_time();
      report();
      event_send_parent();
    }
    set_sim_finish_flag(err_cnt);
  }

private:
  bool irqflag;
  uint32_t proc_id;
};
