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
  Generic tensor API convolution test
 */
// pack-mode
#define PACK_MODE pack_mode_i4_e
// input, output channels per group and number of groups
// output shape 32,3 = 32/4,3
#define OSHP  {8,3,1}
// filter shape 3,3 = rndup(3/4,2),3 = 2,3
#define FSHP  {2,3,1}
#define SSHP  {1,1,1}
#ifdef NOPAD
// no padding
#define PADPOS {0,0,0}
#define PLIM  {0x7fff,0x7fff,0}
#else
// padding of all edges
#define PADPOS {-1,0,0}
#define PLIM  {31,0x7fff,0}
#endif

/*
  PReLU and max-pooling
 */
// output inner loop
#define ONN 1
// output stride
#define OSTR {1,1,1}
// pooling kernel shape
#define KSHP {2,2}
// pooling kernel stride
#define KSTR {1,1}
// pooling output shape pshp[i] = (ishp[i] - kshp[i])/str[i] + 1
#define PSHP {7,2}
// padding limits, assume last 3 columns are padded
#define ACT_PADLIM {19,0x7fff}
// padding position
#define ACT_PADPOS {-1,0}
// double input
#define IDBL false
// double output
#define ODBL false

// fixed parameters
#define GRP   1
#define NI    16
#define NO    16
// use input accumulator, keep output accumulator
#define UA    false
#define KA    true
// feature-map 8b or 16b
#define FMDBL false
// coefficients 8b or 16b with/without output zero-point
#define CFDBL false
#define CFZP  false
// no dilation
#define DSHP  {1,1,1}

#include "utils/tensor_utils.hpp"
#include "utils/sim_terminate.hpp"
#include "tensor_conv.hpp"
#include "tensor_gtoa_prelu.hpp"
#include "tensor_gtoa_pool.hpp"
using namespace tensor::v200;
#include "arcsync_utils.hpp"
#include "utils/cln_map.hpp"
#include "utils/npu_mem_utils.hpp"
#include "utils/npu_mem_map_define.hpp"
// load convolution coefficients from existing hex file
#define LOAD_COEF_HEX true

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

//static ixpix_t conv_coef[] = {
//    #include "ref/conv_cf.mhex"
//}


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
  conv_params_impl_shapes           cshps;          // buffer shapes
  conv_params_impl_main             crtpars;        // main parameters
  conv_params_impl_coef<buffer_t>   impl_cf;        // encoded coefficients modeled memory
  conv_params_impl_pad<buffer_t>    impl_pad;       // encoded padding
  impl_spec_container_t<buffer_t>   l1buf;          // input feature-map in VM
  acc_buf_impl_t<buffer_t>          ab;             // output accumulator in AM

  conv_params_impl_coef<xbuffer_t>  impl_cf_xb;
  conv_params_impl_pad<xbuffer_t>   impl_pad_xb;
  acc_buf_impl_t<xbuffer_t>         ab_xb;
  impl_spec_container_t<xbuffer_t>  l1buf_xb;

  conv_params_impl_coef<buffer_t>*  impl_cf_xm;    // encoded coefficients
  conv_params_impl_pad<buffer_t>*   impl_pad_xm;   // encoded padding
  impl_spec_container_t<buffer_t>*  l1buf_xm;      // input feature-map in VM
  acc_buf_impl_t<buffer_t>*         ab_xm;         // output accumulator in AM

  conv_rt*                          pcv;

  gtoa_act_params_impl_shapes       ashps;
  gtoa_params_impl_main             artpars;       // main parameters
  gtoa_params_impl_pchan<xbuffer_t> pchan_xb;
  impl_spec_container_t<xbuffer_t>  l1buf_i_xb;

  gtoa_params_impl_pchan<buffer_t>  pchan;         // per channel parameters encoded in VM
  impl_spec_container_t<buffer_t>   l1buf_i;       // output feature-map in VM

  gtoa_params_impl_pchan<buffer_t>* pchan_xm;      // per channel parameters encoded in VM
  impl_spec_container_t<buffer_t>*  l1buf_i_xm;    // output feature-map in VM

  gtoa_rt*                          pac;

  gtoa_act_params_impl_shapes       pshps;
  gtoa_params_impl_main             prtpars;       // main parameters
  impl_spec_container_t<xbuffer_t>  l1buf_o_xb;
  impl_spec_container_t<buffer_t>   l1buf_o;       // output feature-map in VM
  impl_spec_container_t<buffer_t>*  l1buf_o_xm;    // output feature-map in VM

  gtoa_rt*                          pmp;

  void aot_compile() {
    // create a convolution parameter object...
    conv_params<xbuffer_t> cpars(GRP,
             NI,
             NO,
             OSHP,
             FSHP,
             SSHP,
             DSHP,
             PLIM,
             UA,
             KA,
             fm_cfg_8b_e,
             cf_cfg_8b_nozp_e,
             PACK_MODE
             );

    conv_params_impl_spec spc;
    cpars.get_impl_params(spc);

    // get the shapes of input/output tensors
    cpars.get_shapes(cshps);

    // allocate and initialize the l1 feature-map buffer
    l1buf_xb = impl_spec_container_t<xbuffer_t>(*pnmalloc, cshps.ishape);
    cpars.init_l1(l1buf_xb);
    //cpars.init_l1(l1buf);

    // create an input coefficient tensor [grp][no][ni][fd][fh][fw][msb/lsb]
    shape<3>           flt(FSHP);
    xbuffer_t<coef_t>   cibuf;
    pnmalloc->alloc(cibuf, (CFDBL?2:1)*NI*flt[SPATIAL_W]*flt[SPATIAL_H]*flt[SPATIAL_D]*NO*GRP);

    // structure for encoded coefficients and zero-points in VM L1
    impl_cf_xb = conv_params_impl_coef<xbuffer_t>(*pnmalloc, cshps);

#ifndef LOAD_COEF_HEX
    tensor_t<coef_t,7,xbuffer_t> citns(cibuf, {CFDBL?2:1, NI, flt[SPATIAL_W], flt[SPATIAL_H], flt[SPATIAL_D], NO, GRP});
    tensor_init_incr<coef_t,7,xbuffer_t>((coef_t)0, citns);
    // encode coefficients
    size_t dummy_cf_sz = 1*256*1024;
    uint8_t *pdummy_cf = (uint8_t *)malloc(dummy_cf_sz);
    assert(pdummy_cf);
    mem_alloc_t dummy_coef_alloc(reinterpret_cast<uint64_t>(pdummy_cf), dummy_cf_sz);
    xbuffer_t<coef_t> czbuf;
    dummy_coef_alloc.alloc(czbuf, dummy_cf_sz);
    if (CFZP) {
      // encode the coefficients with zero-point
      assert(!CFDBL);
      // zero point values
      xbuffer_t<coef_t>   zibuf;
      pnmalloc->alloc(zibuf, NO*GRP);
      tensor_t<coef_t,1,xbuffer_t> zitns(zibuf, {NO*GRP});
      tensor_init_fixed<coef_t,1,xbuffer_t>((coef_t)10, zitns);
      // encode with zero-points
      //cpars.coef_enc(citns.reduce(0), zitns, impl_cf, &dummy_coef_alloc);
      cpars.coef_enc(citns.reduce(0), zitns, impl_cf_xb, czbuf);
      //cpars.coef_enc(citns.reduce(0), zitns, impl_cf_xb, &dummy_coef_alloc); //NOTE: replace the allocator with a scratch buffer
    } else {
      // encode the coefficients without zero-point
      cpars.coef_enc(citns, impl_cf_xb, czbuf);
      //cpars.coef_enc(citns, impl_cf, &dummy_coef_alloc);
    }
#endif
    //copy structure & data from mm to nm
    //impl_cf.cbuf.set_base(impl_cf_xb.cbuf.get_base());
    //impl_cf.cbuf.set_size(impl_cf_xb.cbuf.get_size());
    //mem_write(&impl_cf, impl_cf_xb);
    //copy_buffer(impl_cf.cbuf, impl_cf_xb.cbuf);

    // create an input padding tensor [ni][msb/lsb]
    xbuffer_t<pix_t>   pibuf;
    pnmalloc->alloc(pibuf, (FMDBL?2:1)*NI*GRP);
    tensor_t<pix_t,2,xbuffer_t> pitns(pibuf, {(aoffset_t)(FMDBL?2:1), (aoffset_t)(GRP*NI)});
    tensor_init_fixed<pix_t,2,xbuffer_t>((pix_t)0, pitns);

    // encoded the feature-map zero-point padding information
    impl_pad_xb = conv_params_impl_pad<xbuffer_t>(*pnmalloc, cshps);
    // encode the coefficients without zero-point
    cpars.pad_enc(pitns, impl_pad_xb);
    //cpars.pad_enc(pitns, impl_pad);

    // create an implementation specific output buffer
    ab    = acc_buf_impl_t<buffer_t>(*amalloc, cshps.oshape);
    ab_xb = acc_buf_impl_t<xbuffer_t>(*pnmalloc, cshps.oshape);

    // Get the information for the run-time
    cpars.get_rt_params(crtpars);

    // create a prelu parameter object...
    gtoa_prelu_params<xbuffer_t> apars(NO,
                                       OSHP,
                                       OSTR,
                                       IDBL,
                                       ODBL);

    // set implementation specific parameters
    gtoa_act_params_impl_spec spa;
    spa.onn = ONN; // inner loop of multiple output channel groups
    apars.set_impl_params(spa);

    // get the shapes of input/output tensors
    apars.get_shapes(ashps);

    // allocate and initialize the output l1 buffer
    l1buf_i_xb = impl_spec_container_t<xbuffer_t>(*pnmalloc, ashps.oshape);
    apars.init_l1(l1buf_i_xb);

    //// allocate maxpool stash buffer
    //mpst = gtoa_maxpool_buffer(*vmalloc, ashps);

    // create per channel parameters
    xbuffer_t<prescale_t>              pbuf;        // per channel 2b+6b prescale for scaling down wide accumulators
    xbuffer_t<int32_t>                 bbuf;        // per channel bias [Cout]
    xbuffer_t<int16_t>                 psbuf;       // per channel positive scaling factor [Cout]
    xbuffer_t<int16_t>                 nsbuf;       // per channel negative scaling factor [Cout]
    xbuffer_t<uint8_t>                 phbuf;       // per channel positive shift right amount [Cout]
    xbuffer_t<uint8_t>                 nhbuf;       // per channel negative shift right amount [Cout]
    xbuffer_t<int8_t>                  asbuf;       // per channel output quantization offset [Cout]
    tensor_t<prescale_t,1,xbuffer_t>   prescale;    // per channel 2b+6b prescale for scaling down wide accumulators
    tensor_t<int32_t,1,xbuffer_t>      bias;        // per channel bias [Cout]
    tensor_t<int16_t,1,xbuffer_t>      posscale;    // per channel positive scaling factor [Cout]
    tensor_t<int16_t,1,xbuffer_t>      negscale;    // per channel negative scaling factor [Cout]
    tensor_t<uint8_t,1,xbuffer_t>      posshift;    // per channel positive shift right amount [Cout]
    tensor_t<uint8_t,1,xbuffer_t>      negshift;    // per channel negative shift right amount [Cout]
    tensor_t<int8_t, 1,xbuffer_t>      asymm;       // per channel output quantization offset [Cout]
    pnmalloc->alloc(pbuf, NO);
    pnmalloc->alloc(bbuf, NO);
    pnmalloc->alloc(psbuf, NO);
    pnmalloc->alloc(nsbuf, NO);
    pnmalloc->alloc(phbuf, NO);
    pnmalloc->alloc(nhbuf, NO);
    pnmalloc->alloc(asbuf, NO);
    prescale = tensor_t<prescale_t,1,xbuffer_t>(pbuf, {NO});
    bias     = tensor_t<int32_t,1,xbuffer_t>(bbuf, {NO});
    posscale = tensor_t<int16_t,1,xbuffer_t>(psbuf, {NO});
    negscale = tensor_t<int16_t,1,xbuffer_t>(nsbuf, {NO});
    posshift = tensor_t<uint8_t,1,xbuffer_t>(phbuf, {NO});
    negshift = tensor_t<uint8_t,1,xbuffer_t>(nhbuf, {NO});
    asymm    = tensor_t<int8_t, 1,xbuffer_t>(asbuf, {NO});

    // initialize per channel parameters (scale pos by 1.0, neg by -0.5)
    tensor_init_fixed<prescale_t,1,xbuffer_t>(FP_PRESCALE_ONE, prescale);
    tensor_init_fixed<int32_t,1,xbuffer_t>((int32_t)0, bias);
    tensor_init_fixed<int16_t,1,xbuffer_t>((int16_t)1, posscale);
    tensor_init_fixed<int16_t,1,xbuffer_t>((int16_t)-1, negscale);
    tensor_init_fixed<uint8_t,1,xbuffer_t>((uint8_t)47-10, posshift);
    tensor_init_fixed<uint8_t,1,xbuffer_t>((uint8_t)47-11, negshift);
    tensor_init_fixed<int8_t, 1,xbuffer_t>((int8_t)0, asymm);

    // encode the parameters
    pchan_xb = gtoa_params_impl_pchan<xbuffer_t>(*pnmalloc, ashps);
    // 32b input, 8b output
    apars.param_enc(bias,        // per channel bias [Cout]
                   posscale,    // per channel positive scaling factor [Cout]
                   negscale,    // per channel negative scaling factor [Cout]
                   posshift,    // per channel positive shift right amount [Cout]
                   negshift,    // per channel negative shift right amount [Cout]
                   asymm,       // per channel output quantization offset [Cout]
                   pchan_xb     // output encoded parameters
                   );

    // serialize run-time parameters
    apars.get_rt_params(artpars);

    // create a max-pooling parameter object... 
    gtoa_maxpool_params<xbuffer_t> ppars(NO,
                                        PSHP,
                                        KSHP,
                                        KSTR,
                                        ACT_PADLIM,
                                        ODBL
                                        );

    //set pack mode
    ppars.set_pack_mode(PACK_MODE);

    // get the shapes of input/output tensors
    ppars.get_shapes(pshps);

    // allocated input feature-map array
    ppars.init_l1_input(l1buf_i_xb);
    
    // allocate and initialize the output l1 buffer
    l1buf_o_xb = impl_spec_container_t<xbuffer_t>(*pnmalloc, pshps.oshape);
    ppars.init_l1_output(l1buf_o_xb);
    
    // serialize run-time parameters
    ppars.get_rt_params(prtpars);

  }

  void prepare_operands() {
    // initialize input tensor
    // ixpix_t [D][H][W][Grp][C]
    tensor_vinit_incr<5>(FMDBL?2*GRP*NI:GRP*NI, (pix_t)13, l1buf_xb.data);
    l1buf    = impl_spec_container_t<buffer_t>(*vmalloc, cshps.ishape);
    impl_cf  = conv_params_impl_coef<buffer_t>(*vmalloc, cshps);
    impl_pad = conv_params_impl_pad<buffer_t>(*vmalloc, cshps);
    l1buf_i  = impl_spec_container_t<buffer_t>(*vmalloc, ashps.oshape);
    pchan    = gtoa_params_impl_pchan<buffer_t>(*vmalloc, ashps);
    l1buf_o  = impl_spec_container_t<buffer_t>(*vmalloc, pshps.oshape);
    deep_copy(l1buf, l1buf_xb);
    deep_copy(impl_cf, impl_cf_xb);
    deep_copy(impl_pad, impl_pad_xb);
    deep_copy(l1buf_i, l1buf_i_xb);
    deep_copy(pchan, pchan_xb);
    deep_copy(l1buf_o, l1buf_o_xb);

#ifdef LOAD_COEF_HEX
    tensor_t<ixpix_t,1,buffer_t> cftns(impl_cf.cbuf,{(aoffset_t)impl_cf.cbuf.get_size()});
    tensor_iterator_t<ixpix_t,1,buffer_t> cft(cftns);
    ixpix_t conv_coef[] = {
      #include "ref/conv_cf.mhex"
    };
    int k = 0;
    set_mem_backdoor(1,0);
    do {
       cft.write(conv_coef[k]);
       k++;
    }while(cft.next());
    set_mem_backdoor(0,0);
#endif

    // move data structures to XM
    xmalloc->alloc(impl_cf_xm);    // encoded coefficients
    xmalloc->alloc(impl_pad_xm);   // encoded padding
    xmalloc->alloc(l1buf_xm);      // input feature-map in VM
    xmalloc->alloc(ab_xm);         // output accumulator in AM
    xmalloc->alloc(pchan_xm);
    xmalloc->alloc(l1buf_i_xm);
    xmalloc->alloc(l1buf_o_xm);
    mem_write(impl_cf_xm, impl_cf);
    mem_write(impl_pad_xm, impl_pad);
    mem_write(l1buf_xm, l1buf);
    mem_write(ab_xm, ab);
    mem_write(pchan_xm, pchan);
    mem_write(l1buf_i_xm, l1buf_i);
    mem_write(l1buf_o_xm, l1buf_o);

    pcv = create(*dmalloc, crtpars); //copy crtpars to DM and create a rt oject
    pac = create(*dmalloc, artpars); //copy artpars to DM and create a rt oject
    pmp = create(*dmalloc, prtpars); //copy prtpars to DM and create a rt oject

  }

  void run_time() {
    // run-time execution
    npu::ctrl_dma_regs<npu_conv::conv_hlapi_t>&   crgs(*reinterpret_cast<npu::ctrl_dma_regs<npu_conv::conv_hlapi_t>*>(get_mmio_base_conv()));

    conv_rt& cv(*pcv);

    // set the source input feature-map
    cv.set_input(*l1buf_xm);

    conv_rt_impl_spec* crt;
    xmalloc->alloc(crt);
    mem_write(&crt->mmio, &crgs);  // MMIO base address
    mem_write(&crt->ctrl,  (uint32_t)1);     // raise event at completion
    cv.set_impl_params(*crt);

    // set some tile specific parameters
    shape<3> cpadpos;
    cpadpos = PADPOS;
    shape<3>* cpadpos_xm;
    xmalloc->alloc(cpadpos_xm);
    mem_write(cpadpos_xm, cpadpos);
    cv.init_tile_params(*cpadpos_xm, *impl_cf_xm, *impl_pad_xm);

    // assign an output buffer
    cv.set_output(*ab_xm);

    // enable interrupts and events
    mmio_write(&crgs.int_enable , 0xffffffff);

    // execute
    cv.prepare();
    cv.execute();

    // wait for completion
    event_wait_any(1LL<<EVT_CONV_DONE);

    // PReLU
    npu::ctrl_dma_regs<npu_act::act_hlapi_t>&   args(*reinterpret_cast<npu::ctrl_dma_regs<npu_act::act_hlapi_t>*>(get_mmio_base_act()));

    // create a run-time object
    gtoa_rt& act_rt(*pac);

    // set run-time specific parameters
    gtoa_rt_impl_spec* artp;
    xmalloc->alloc(artp);
    mem_write(&artp->mmio, &args);  // MMIO base address
    mem_write(&artp->ctrl, (uint32_t)1);     // raise event at completion
    act_rt.set_impl_params(*artp);

    // initialize tile parameters
    act_rt.init_tile_params(*pchan_xm);

    // set input accumulator
    act_rt.set_acc_input0(*ab_xm);

    // set output tensor
    act_rt.set_output(*l1buf_i_xm);

    // enable interrupts and events
    mmio_write(&args.int_enable, 0xffffffff);

    // prefetch and execute
    act_rt.prepare();
    act_rt.execute();

    // wait for completion
    event_wait_any(1LL<<EVT_ACT_DONE);

    // maxpool
    npu::ctrl_dma_regs<npu_act::act_hlapi_t>&   prgs(*reinterpret_cast<npu::ctrl_dma_regs<npu_act::act_hlapi_t>*>(get_mmio_base_act()));

    // create a run-time object in DCCM (fast access)
    gtoa_rt& mp_rt(*pmp);

    // set run-time specific parameters
    gtoa_rt_impl_spec* prtp;
    xmalloc->alloc(prtp);
    mem_write(&prtp->mmio, &prgs);            // MMIO base address
    mem_write(&prtp->ctrl, (uint32_t)1);     // raise event at completion
    mp_rt.set_impl_params(*prtp);

    // set input tensor
    mp_rt.set_input0(*l1buf_i_xm);

    // set output tensor
    mp_rt.set_output(*l1buf_o_xm);
    
    // set padding position
    mp_rt.set_padpos(ACT_PADPOS);

    // enable interrupts and events
    mmio_write(&prgs.int_enable, 0xffffffff);

    // prefetch and execute
    mp_rt.prepare();
    mp_rt.execute();

    // wait for completion
    event_wait_any(1LL<<EVT_ACT_DONE);
  }

  void report() {
    // report the output tensor
    shape<2> pshp(PSHP);

    buffer_t<pix_t>                     dbuf;
    xmalloc->alloc(dbuf, NO*get_shape_size(pshp));
    tensor_t<pix_t,4>                   dtns(dbuf, {NO, pshp[0],pshp[1],1});

    //convertfrom(dtns, mem_read(l1buf_xm));
    //tensor::v200::report(rptos, dtns);
    //void convertfrom(tensor_t<pix_t,4>& o, const impl_spec_container_t& b) {
    bool active;
    const_tensor_iterator_t<ixpix_t,5> bit(l1buf_o_xm->data);
    tensor_iterator_t<pix_t,4> oit(dtns);
    int j = 0;
    do {
      for (int w = 0; w < l1buf_o_xm->data.get_dim(2); w++) {
        aoffset_t c = 0;
        for (int n = 0; n < l1buf_o_xm->data.get_dim(0); n++) {
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
    evt_cfg();
    xmalloc  = new mem_alloc_t((uint64_t)0, 0x80000000);
    vmalloc  = new mem_alloc_t((uint64_t)get_slice_vm_base(), 0x200000);
    amalloc  = new mem_alloc_t((uint64_t)get_slice_am_base(), 0x100000);
    dmalloc  = new mem_alloc_t((uint64_t)get_fast_dccm_base(), 0x10000);
    size_t nm_sz = 4*1024*1024;
    uint8_t* pnm = (uint8_t *)malloc(nm_sz);// assert(pnm);
    pnmalloc = new mem_alloc_t(reinterpret_cast<uint64_t>(pnm), nm_sz);

    aot_compile();
    prepare_operands();
    run_time();
    report();
    set_sim_finish_flag(err_cnt);
  }

private:
  bool irqflag;
};
