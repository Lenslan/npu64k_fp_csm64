/*
  Generic tensor API convolution test
 */
#include <fstream>

#include "tensor_utils.hpp"
#include "tensor_conv.hpp"
#ifdef SYSTEMC
#include "npu_conv_hl_top.hpp"
using namespace npu_conv;
#endif

#ifdef SYSTEMC
// SystemC mode
hl_mm csm("tb_mm", 1024*1024);
hl_vm vm("tb_vm");
hl_am am("tb_am");
hl_dm dm("tb_dm");
ctrl_dma_regs<conv_hlapi_t> rgs;
#else
// Native mode
mem_t csm(1024*1024);
mem_t vm(1024*1024);
mem_t am(1024*1024);
mem_t dm(1024*1024);
#endif
mem_alloc_t csmalloc(reinterpret_cast<uint64_t>(NPU_CSM_BASE), csm.size());
mem_alloc_t vmalloc(reinterpret_cast<uint64_t>(NPU_INTRA_SLICE_VM_BASE), vm.size());
mem_alloc_t amalloc(reinterpret_cast<uint64_t>(NPU_INTRA_SLICE_AM_BASE), am.size());
mem_alloc_t dmalloc(reinterpret_cast<uint64_t>(NPU_INTRA_SLICE_DCCM_BASE), dm.size());
mem_alloc_t *dummy_alloc;


//
// The test
//
class testprog : public arc_program
{
public:
  inline testprog(const char* file) : arc_program() {
    irqflag = false;
    rptos.open(file);
  }
  virtual void irq() {
    rptos << "REPORT interrupt" << endl;
    irqflag = true;
  }

  // parameters to run-time
  conv_params_impl_shapes shps;           // buffer shapes
  conv_params_impl_main   rtpars;         // main parameters

  conv_params_impl_coef<xbuffer_t>   impl_cf_xb;
  conv_params_impl_pad<xbuffer_t>    impl_pad_xb;
  impl_spec_container_t<xbuffer_t>   l1buf_xb;
  acc_buf_impl_t<xbuffer_t>          ab_xb;
  conv_params_impl_coef<buffer_t>   impl_cf;        // encoded coefficients
  conv_params_impl_pad<buffer_t>    impl_pad;       // encoded padding
  impl_spec_container_t<buffer_t>   l1buf;          // input feature-map in VM
  acc_buf_impl_t<buffer_t>          ab;             // output accumulator in AM

  conv_params_impl_coef<buffer_t>*  impl_cf_csm;    // encoded coefficients
  conv_params_impl_pad<buffer_t>*   impl_pad_csm;   // encoded padding
  impl_spec_container_t<buffer_t>*  l1buf_csm;      // input feature-map in VM
  acc_buf_impl_t<buffer_t>*         ab_csm;         // output accumulator in AM

  void aot_compile() {
    // compiler function

    // create a convolution parameter object...
    fc_params<xbuffer_t> pars(NI,
                              NO,
                              UA,
                              KA,
                              FMDBL,
                              CFDBL,
                              CFZP);

#ifdef SYSTEMC
    conv_params_impl_spec spc;
    pars.get_impl_params(spc);
    cout << "mode: " << spc.conv_mode << " inn " << spc.inn << " onn " << spc.onn << " cf_mode " << spc.cf_mode << " cf_4b " << spc.cf_4b << endl;
#endif

    // get the shapes of input/output tensors
    pars.get_shapes(shps);

    // allocate and initialize the l1 feature-map buffer
    l1buf_xb = impl_spec_container_t<xbuffer_t>(*dummy_alloc, shps.ishape);
    l1buf    = impl_spec_container_t<buffer_t>(vmalloc, shps.ishape);
    pars.init_l1(l1buf_xb);

    // create an input coefficient tensor [no][ni][msb/lsb]
    xbuffer_t<coef_t>   cibuf;
    dummy_alloc->alloc(cibuf, (CFDBL?2:1)*NI*NO);
    tensor_t<coef_t,3,xbuffer_t> citns(cibuf, {CFDBL?2:1, NI, NO});
    tensor_init_incr<coef_t,3,xbuffer_t>((coef_t)0, citns);

    // structure for encoded coefficients and zero-points in VM L1
    impl_cf_xb = conv_params_impl_coef<xbuffer_t>(*dummy_alloc, shps);
    impl_cf    = conv_params_impl_coef<buffer_t>(vmalloc, shps);

    // encode coefficients
    xbuffer_t<coef_t>  tbuf;
    dummy_alloc->alloc(tbuf, 4*1024*1024);
    if (CFZP) {
      // encode the coefficients with zero-point
      assert(!CFDBL);
      // zero point values
      xbuffer_t<coef_t>   zibuf;
      dummy_alloc->alloc(zibuf, NO);
      tensor_t<coef_t,1,xbuffer_t> zitns(zibuf, {NO});
      tensor_init_fixed<coef_t,1,xbuffer_t>((coef_t)10, zitns);
      // encode with zero-points
      pars.coef_enc(citns.reduce(0), zitns, impl_cf_xb, tbuf);
    } else {
      // encode the coefficients without zero-point
      pars.coef_enc(citns, impl_cf_xb, tbuf);
    }

    // create an input padding tensor [ni][msb/lsb]
    xbuffer_t<pix_t>   pibuf;
    dummy_alloc->alloc(pibuf, (FMDBL?2:1)*NI);
    tensor_t<pix_t,2,xbuffer_t> pitns(pibuf, {(aoffset_t)(FMDBL?2:1), (aoffset_t)(NI)});

    // encoded the feature-map zero-point padding information
    impl_pad_xb = conv_params_impl_pad<xbuffer_t>(*dummy_alloc, shps);
    impl_pad    = conv_params_impl_pad<buffer_t>(vmalloc, shps);

    // encode the coefficients without zero-point

    // create an implementation specific output buffer
    ab_xb = acc_buf_impl_t<xbuffer_t>(*dummy_alloc, shps.oshape);
    ab    = acc_buf_impl_t<buffer_t>(amalloc, shps.oshape);

    // Get the information for the run-time
    pars.get_rt_params(rtpars);
  }

  void prep_operands() {
    // initialize input tensor
#ifdef SYSTEMC
    // in HW the DMA will translate L2/L3 pix_t based memory format to ixpix_t L1 memory format
    // ixpix_t [D][H][W][Grp][C]
    tensor_vinit_incr<5,xbuffer_t>(FMDBL?2*NI:NI, (pix_t)13, l1buf_xb.data);
#else
    tensor_init_incr<pix_t,4,xbuffer_t>((pix_t)13, l1buf_xb.data);
#endif

    // move data structures to CSM
    csmalloc.alloc(impl_cf_csm);    // encoded coefficients
    csmalloc.alloc(impl_pad_csm);   // encoded padding
    csmalloc.alloc(l1buf_csm);      // input feature-map in VM
    csmalloc.alloc(ab_csm);         // output accumulator in AM

    deep_copy(impl_cf, impl_cf_xb);
    deep_copy(impl_pad, impl_pad_xb);
    deep_copy(l1buf, l1buf_xb);
    deep_copy(ab, ab_xb);
    mem_write(impl_cf_csm, impl_cf);
    mem_write(impl_pad_csm, impl_pad);
    mem_write(l1buf_csm, l1buf);
    mem_write(ab_csm, ab);
  }

  void run_time() {
    // run-time execution
    // create a run-time object in DM
    conv_rt& cv(*create(dmalloc, rtpars));

    // set the source input feature-map
    cv.set_input(*l1buf_csm);

    conv_rt_impl_spec* rt;
    csmalloc.alloc(rt);
#ifdef SYSTEMC
    mem_write(&rt->mmio, &rgs);  // MMIO base address
    mem_write(&rt->ctrl,  (uint32_t)1);     // raise event at completion
#else
    // no implementation specific parameters in native mode, synchronous execution
#endif
    cv.set_impl_params(*rt);

    // set some tile specific parameters
    shape<3> padpos;
      // pad also in depth dimension
      padpos = {0,0,0};
    shape<3>* padpos_csm;
    csmalloc.alloc(padpos_csm);
    mem_write(padpos_csm, padpos);
    cv.init_tile_params(*padpos_csm, *impl_cf_csm, *impl_pad_csm);

    // assign an output buffer
    cv.set_output(*ab_csm);

#ifdef SYSTEMC
    // enable interrupts and events
    rgs.int_enable = 0xffffffff;
    run_cycles(1);

    // prefetch and execute
    cv.prepare();
    run_cycles(1);
    cv.execute();
    run_cycles(1);

    // wait for completion
    cout << "wait event" << endl;
    event_wait_any(1LL<<EVT_CONV_DONE);
    rptos << "REPORT event" << endl;
    run_cycles(10);
#else
    // execute synchronously
    cv.execute();
#endif
  }

  void report() {
    // get output
    buffer_t<acc_t> obuf;
    shape<5> os1({CFDBL&&FMDBL?2:1, NO/8, 8, 1, 1});
    csmalloc.alloc(obuf, get_shape_size(os1));
    tensor_t<acc_t,5> otns(obuf, os1); // [D][H][W][C][msb/lsb]
    // convert implementation specific to general
    convertfrom(otns, ab);

    // report the output
    tensor::v200::report(rptos, otns, otns.get_dim(0)*otns.get_dim(1)); 
  }

  // test code
  void exec() {
    size_t dummy_sz = (1+4)*1024*1024;
    uint8_t *pdummy = (uint8_t *)malloc(dummy_sz);
    assert(pdummy);
    dummy_alloc = new mem_alloc_t(reinterpret_cast<uint64_t>(pdummy), dummy_sz);

    aot_compile();
    prep_operands();
    run_time();
    report();
    rptos.close();
    arc_exit();
  }
private:
  bool irqflag;
  std::ofstream rptos;
};


#ifdef SYSTEMC
#include "../common/test_sc.hpp"
#else
//
// main nativeprogram
//
int main(int argc, char** argv) {
 // create testprogram and testbench
  testprog tst;

  tst.main(0, nullptr);

  return 0;
}
#endif
