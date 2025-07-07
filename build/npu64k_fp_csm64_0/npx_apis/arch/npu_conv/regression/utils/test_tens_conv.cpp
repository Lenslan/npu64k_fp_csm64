/*
  Generic tensor API convolution test
 */
#include <fstream>
#include <boost/format.hpp>

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
mem_alloc_t* pnm=NULL;

//#define TEST_DEBUG

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
  conv_params_impl_coef<buffer_t>   impl_cf;        // encoded coefficients modeled memory
  conv_params_impl_pad<buffer_t>    impl_pad;       // encoded padding
  impl_spec_container_t<buffer_t>   l1buf;          // input feature-map in VM
  acc_buf_impl_t<buffer_t>          ab;             // output accumulator in AM

  conv_params_impl_coef<xbuffer_t>  impl_cf_xb;
  conv_params_impl_pad<xbuffer_t>   impl_pad_xb;
  acc_buf_impl_t<xbuffer_t>         ab_xb;
  impl_spec_container_t<xbuffer_t>  l1buf_xb;

  conv_params_impl_coef<buffer_t>*  impl_cf_csm;    // encoded coefficients
  conv_params_impl_pad<buffer_t>*   impl_pad_csm;   // encoded padding
  impl_spec_container_t<buffer_t>*  l1buf_csm;      // input feature-map in VM
  acc_buf_impl_t<buffer_t>*         ab_csm;         // output accumulator in AM

  conv_rt*                          pcv;

  void aot_compile() {
    // compiler function
    //mem_t dummy(1024*1024);
    //mem_alloc_t dummy_alloc(dummy.base_addr, dummy.size);
    size_t dummy_sz = 4*1024*1024;
    uint8_t *pdummy = (uint8_t *)malloc(dummy_sz);
    assert(pdummy);
    mem_alloc_t dummy_alloc(reinterpret_cast<uint64_t>(pdummy), dummy_sz);

    // create a convolution parameter object...
    conv_params<xbuffer_t> pars(GRP,
             NI,
             NO,
             OSHP,
             FSHP,
             SSHP,
             DSHP,
             PLIM,
             UA,
             KA,
             FMDBL,
             CFDBL,
             CFZP);

    conv_params_impl_spec spc;
    pars.get_impl_params(spc);
    cout << "mode: " << spc.conv_mode << " inn " << spc.inn << " onn " << spc.onn << " cf_mode " << spc.cf_mode << " cf_4b " << spc.cf_4b << endl;

    // get the shapes of input/output tensors
    pars.get_shapes(shps);
#ifdef TEST_DEBUG
    cout << "shapes:" << endl << shps.cshape << endl;
    tensor::v200::report(cout, shps.ishape);
    tensor::v200::report(cout, shps.oshape);
    cout << endl;
#endif
    // allocate and initialize the l1 feature-map buffer
    l1buf_xb = impl_spec_container_t<xbuffer_t>(dummy_alloc, shps.ishape);
    pars.init_l1(l1buf_xb);
    tensor_vinit_incr<5>(FMDBL?2*GRP*NI:GRP*NI, (pix_t)13, l1buf_xb.data);
#ifdef TEST_DEBUG
    cout << "Input:" << endl;
    const_tensor_iterator_t<ixpix_t,5,xbuffer_t> in_it(l1buf_xb.data);
    for (int h = 0; h < l1buf_xb.data.get_dim(3); h++) {
      for (int w = 0; w < l1buf_xb.data.get_dim(2); w++) {
        for (int g = 0; g < l1buf_xb.data.get_dim(1); g++) {
          for (int c = 0; c < l1buf_xb.data.get_dim(0); c++) {
            cout << "[h=" << h << "][w=" << w << "][g=" << g << "][c=" << c << "] " << in_it.read() << endl;
            in_it.next();
          }
        }
      }
    }
#endif


    // create an input coefficient tensor [grp][no][fd][fh][fw][ni][msb/lsb]
    shape<3>           flt(FSHP);
    xbuffer_t<coef_t>   cibuf;
    dummy_alloc.alloc(cibuf, (CFDBL?2:1)*NI*flt[SPATIAL_W]*flt[SPATIAL_H]*flt[SPATIAL_D]*NO*GRP);
    tensor_t<coef_t,7,xbuffer_t> citns(cibuf, {CFDBL?2:1, NI, flt[SPATIAL_W], flt[SPATIAL_H], flt[SPATIAL_D], NO, GRP});
    tensor_init_incr<coef_t,7,xbuffer_t>((coef_t)0, citns);
    // zero point values (if needed)
    xbuffer_t<coef_t>   zibuf;
    dummy_alloc.alloc(zibuf, NO*GRP);
    tensor_t<coef_t,1,xbuffer_t> zitns(zibuf, {NO*GRP});
    tensor_init_fixed<coef_t,1,xbuffer_t>((coef_t)10, zitns);
    
    // structure for encoded coefficients and zero-points in VM L1
    impl_cf_xb = conv_params_impl_coef<xbuffer_t>(dummy_alloc, shps);

    // encode coefficients
    size_t dummy_cf_sz = 4*1024*1024;
    uint8_t *pdummy_cf = (uint8_t *)malloc(dummy_cf_sz);
    assert(pdummy_cf);
    mem_alloc_t dummy_coef_alloc(reinterpret_cast<uint64_t>(pdummy_cf), dummy_cf_sz);
    xbuffer_t<coef_t> czbuf;
    dummy_coef_alloc.alloc(czbuf, dummy_cf_sz);
    if (CFZP) {
      // encode the coefficients with zero-point
      assert(!CFDBL);
      // encode with zero-points
      //pars.coef_enc(citns.reduce(0), zitns, impl_cf, &dummy_coef_alloc);
      pars.coef_enc(citns.reduce(0), zitns, impl_cf_xb, czbuf);
      //pars.coef_enc(citns.reduce(0), zitns, impl_cf_xb, &dummy_coef_alloc); //NOTE: replace the allocator with a scratch buffer
    } else {
      // encode the coefficients without zero-point
      pars.coef_enc(citns, impl_cf_xb, czbuf);
      //pars.coef_enc(citns, impl_cf, &dummy_coef_alloc);
    }
    //copy structure & data from mm to nm
    //impl_cf.cbuf.set_base(impl_cf_xb.cbuf.get_base());
    //impl_cf.cbuf.set_size(impl_cf_xb.cbuf.get_size());
    //mem_write(&impl_cf, impl_cf_xb);
    //copy_buffer(impl_cf.cbuf, impl_cf_xb.cbuf);
#ifdef TEST_DEBUG
    cout << "new cshape " << impl_cf_xb.get_size() << endl;
    cout << "Outputs:" << endl;
    shape<3> oshp(OSHP);
    shape<3> fshp(FSHP);
    shape<3> sshp(SSHP);
    shape<3> dshp(DSHP);
    for (int h = 0; h < oshp[1]; h++) {
      for (int w = 0; w < oshp[0]; w++) {
        for (int g = 0; g < GRP; g++) {
          for (int no = 0; no < NO; no++) {
            cout << "[h=" << h << "][w=" << w << "][g=" << g << "][o=" << no << "]= 0";
            coef_t zp;
            if (CFZP) zp = zitns.read({aoffset_t(g*NO+no)});
            else zp = 0;
            acc_t s(0);
            for (int fh = 0; fh < fshp[1]; fh++) {
              for (int fw = 0; fw < fshp[0]; fw++) {
                for (int ni = 0; ni < NI; ni++) {
                  int cfi;
                  if (CFDBL) {
                    coef_t  cf0 = citns.read({0,(aoffset_t)ni,(aoffset_t)fw,(aoffset_t)fh,0,(aoffset_t)no,(aoffset_t)g});
                    coef_t  cf1 = citns.read({1,(aoffset_t)ni,(aoffset_t)fw,(aoffset_t)fh,0,(aoffset_t)no,(aoffset_t)g});
                    cfi = uint32_t(uint8_t(cf0)) + (int32_t(cf1)<<8);
                  } else {
                    coef_t  cf = citns.read({0,(aoffset_t)ni,(aoffset_t)fw,(aoffset_t)fh,0,(aoffset_t)no,(aoffset_t)g});
                    cfi = int32_t(cf)-int32_t(zp);
                  }
                  int     wi = w*sshp[0]+fw*dshp[0];
                  int     hi = h*sshp[1]+fh*dshp[1];
                  if (FMDBL) {
                    int     ci = 2*(g*NI+ni);
                    ixpix_t vp = l1buf_xb.data.read({(aoffset_t)(ci/ISIZE),0,(aoffset_t)wi,(aoffset_t)hi,0});
                    pix_t   p0  = vp[ci%ISIZE];
                    pix_t   p1  = vp[(ci+1)%ISIZE];
                    int     p   = uint8_t(p0) + (int32_t(p1)<<8);
                    cout << "+" << boost::format("0x%08x") % int(p) << "*" << boost::format("0x%08x") % cfi;
                    s += int32_t(p)*cfi;
                  } else {
                    int     ci = g*NI+ni;
                    ixpix_t vp = l1buf_xb.data.read({(aoffset_t)(ci/ISIZE),0,(aoffset_t)wi,(aoffset_t)hi,0});
                    pix_t   p  = vp[ci%ISIZE];
                    cout << "+" << boost::format("0x%08x") % int(p) << "*" << boost::format("0x%08x") % cfi;
                    s += int32_t(p)*cfi;
                  }
                }
              }
            }
            cout << "=" << boost::format("0x%08x") % int(s) << endl;
          }
        }
      }
    }
#endif

    // create an input padding tensor [ni][msb/lsb]
    xbuffer_t<pix_t>   pibuf;
    dummy_alloc.alloc(pibuf, (FMDBL?2:1)*NI*GRP);
    tensor_t<pix_t,2,xbuffer_t> pitns(pibuf, {(aoffset_t)(FMDBL?2:1), (aoffset_t)(GRP*NI)});
    tensor_init_incr<pix_t,2,xbuffer_t>((pix_t)-5, pitns);

    // encoded the feature-map zero-point padding information
    impl_pad_xb = conv_params_impl_pad<xbuffer_t>(dummy_alloc, shps);
    // encode the coefficients without zero-point
    pars.pad_enc(pitns, impl_pad_xb);
    //pars.pad_enc(pitns, impl_pad);

    // create an implementation specific output buffer
    ab    = acc_buf_impl_t<buffer_t>(amalloc, shps.oshape);
    ab_xb = acc_buf_impl_t<xbuffer_t>(dummy_alloc, shps.oshape);

    // Get the information for the run-time
    pars.get_rt_params(rtpars);
  }

  void prep_operands() {
    // initialize input tensor
    // ixpix_t [D][H][W][Grp][C]
    l1buf    = impl_spec_container_t<buffer_t>(vmalloc, shps.ishape);
    impl_cf  = conv_params_impl_coef<buffer_t>(vmalloc, shps);
    impl_pad = conv_params_impl_pad<buffer_t>(vmalloc, shps);
    deep_copy(l1buf, l1buf_xb);
    deep_copy(impl_cf, impl_cf_xb);
    deep_copy(impl_pad, impl_pad_xb);

    // move data structures to CSM
    csmalloc.alloc(impl_cf_csm);    // encoded coefficients
    csmalloc.alloc(impl_pad_csm);   // encoded padding
    csmalloc.alloc(l1buf_csm);      // input feature-map in VM
    csmalloc.alloc(ab_csm);         // output accumulator in AM
    mem_write(impl_cf_csm, impl_cf);
    mem_write(impl_pad_csm, impl_pad);
    mem_write(l1buf_csm, l1buf);
    mem_write(ab_csm, ab);

    pcv = create(dmalloc, rtpars); //copy rtpars to DM and create a rt oject
  }

  void run_time() {
    conv_rt& cv(*pcv);

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
    shape<3> os0(OSHP);
#ifdef PADPOS
    padpos = PADPOS;
#else
    if (os0[2] != 1) {
      // pad also in depth dimension
      padpos = {-1,-1,-1};
    } else {
      // only padding in width&height dimensions
      padpos = {-1,-1,0};
    }
#endif
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
    shape<3> os0(OSHP);
    shape<5> os1({CFDBL&&FMDBL?2:1, GRP*NO, os0[0], os0[1], os0[2]});
    csmalloc.alloc(obuf, get_shape_size(os1));
    tensor_t<acc_t,5> otns(obuf, os1); // [D][H][W][C][msb/lsb]
    // convert implementation specific to general
    convertfrom(otns, ab);

    // report the output
    tensor::v200::report(rptos, otns, otns.get_dim(0)*otns.get_dim(1)); 
  }

  // test code
  void exec() {
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
