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

#ifdef RTL_DPI
mem_alloc_t csmalloc((uint64_t)0, 0x80000000);
mem_alloc_t vmalloc((uint64_t)get_slice_vm_base(), 0x80000);
mem_alloc_t amalloc((uint64_t)get_slice_am_base(), 0x20000);
mem_alloc_t dmalloc((uint64_t)get_fast_dccm_base(), 0x8000);
npu::ctrl_dma_regs<npu_conv::conv_hlapi_t>&   rgs(*reinterpret_cast<npu::ctrl_dma_regs<npu_conv::conv_hlapi_t>*>(get_mmio_base_conv()));
#else
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
#endif
mem_alloc_t* pnm=NULL;
#define FPTYP fp_e8m7_t
#define FMTYP fm_cfg_bf16_e
#define CFTYP cf_cfg_bf16_e

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
  conv_params_impl_shapes           shps;           // buffer shapes
  conv_params_impl_main             rtpars;         // main parameters
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
    shape<3> oshp(OSHP);
    shape<3> fshp(FSHP);
    shape<3> sshp(SSHP);
    shape<3> dshp(DSHP);
    shape<3> plim(PLIM);

    size_t dummy_sz = 4*1024*1024;
    uint8_t *pdummy = (uint8_t *)malloc(dummy_sz);
    assert(pdummy);
    mem_alloc_t dummy_alloc(reinterpret_cast<uint64_t>(pdummy), dummy_sz);

    // create a convolution parameter object...
    conv_params<xbuffer_t> pars(
             GRP,
             NI,
             NO,
             OSHP,
             FSHP,
             SSHP,
             DSHP,
             PLIM,
             UA,
             KA,
             FMTYP,
             CFTYP);

    conv_params_impl_spec spc;
    pars.get_impl_params(spc);
    cout << "mode: " << spc.conv_mode << " inn " << spc.inn << " onn " << spc.onn << " cf_mode " << spc.cf_mode << endl;

    // get the shapes of input/output tensors
    pars.get_shapes(shps);
    cout << " ishape:" << endl; tensor::v200::report(cout, shps.ishape); cout << endl;
    cout << " oshape:" << endl; tensor::v200::report(cout, shps.oshape); cout << endl;
    cout << " cshape:" << shps.cshape << endl;
    cout << " pshape:" << endl; tensor::v200::report(cout, shps.pshape); cout << endl;

    // allocate and initialize the l1 feature-map buffer
    xbuffer_t<FPTYP>   fibuf;
    dummy_alloc.alloc(fibuf,
                      NI*GRP*
                      (1+(oshp[SPATIAL_W]-1)*sshp[SPATIAL_W]+(fshp[SPATIAL_W]-1)*dshp[SPATIAL_W])*
                      (1+(oshp[SPATIAL_H]-1)*sshp[SPATIAL_H]+(fshp[SPATIAL_H]-1)*dshp[SPATIAL_H])*
                      (1+(oshp[SPATIAL_D]-1)*sshp[SPATIAL_D]+(fshp[SPATIAL_D]-1)*dshp[SPATIAL_D])
                      );
    tensor_t<FPTYP,4,xbuffer_t> fitns(fibuf, {(aoffset_t)(NI*GRP), 
                                          (aoffset_t)(1+(oshp[SPATIAL_W]-1)*sshp[SPATIAL_W]+(fshp[SPATIAL_W]-1)*dshp[SPATIAL_W]),
                                          (aoffset_t)(1+(oshp[SPATIAL_H]-1)*sshp[SPATIAL_H]+(fshp[SPATIAL_H]-1)*dshp[SPATIAL_H]),
                                          (aoffset_t)(1+(oshp[SPATIAL_D]-1)*sshp[SPATIAL_D]+(fshp[SPATIAL_D]-1)*dshp[SPATIAL_D])
                                          });
    tensor_init_incr_fp<FPTYP,4,xbuffer_t>((float)-13.0, fitns);
    
    l1buf_xb = impl_spec_container_t<xbuffer_t>(dummy_alloc, shps.ishape);
    pars.init_l1(l1buf_xb);
    convertto(l1buf_xb, fitns);

    // create an input coefficient tensor [grp][no][ni][fd][fh][fw][msb/lsb]
    xbuffer_t<FPTYP>   cibuf;
    dummy_alloc.alloc(cibuf, NI*fshp[SPATIAL_W]*fshp[SPATIAL_H]*fshp[SPATIAL_D]*NO*GRP);
    tensor_t<FPTYP,6,xbuffer_t> citns(cibuf, {NI, fshp[SPATIAL_W], fshp[SPATIAL_H], fshp[SPATIAL_D], NO, GRP});
    tensor_init_incr_fp<FPTYP,6,xbuffer_t>((float)-1.0, citns, 0.5);
    // structure for encoded coefficients and zero-points in VM L1
    impl_cf_xb = conv_params_impl_coef<xbuffer_t>(dummy_alloc, shps);
    // encode coefficients
    size_t dummy_cf_sz = 128*1024;
    xbuffer_t<coef_t> czbuf;
    dummy_alloc.alloc(czbuf, dummy_cf_sz);
    pars.coef_enc(citns, impl_cf_xb, czbuf);

    // create an input padding tensor [ni][msb/lsb], fixed to 0
    xbuffer_t<FPTYP>   pibuf;
    dummy_alloc.alloc(pibuf, NI*GRP);
    tensor_t<FPTYP,1,xbuffer_t> pitns(pibuf, {(aoffset_t)(GRP*NI)});
    tensor_init_fixed_fp<FPTYP,1,xbuffer_t>((float)0.0, pitns);
    // encoded the feature-map zero-point padding information
    impl_pad_xb = conv_params_impl_pad<xbuffer_t>(dummy_alloc, shps);
    // encode the padding
    pars.pad_enc(pitns, impl_pad_xb);

    // create an implementation specific output buffer
    ab    = acc_buf_impl_t<buffer_t>(amalloc, shps.oshape);
    ab_xb = acc_buf_impl_t<xbuffer_t>(dummy_alloc, shps.oshape);

    // Get the information for the run-time
    pars.get_rt_params(rtpars);
    for (int i = 0; i < 8; i++)
      cout << "iter " << i << " " << rtpars.i.iter[i] << endl;

    // reference
    cout << "reference:" << endl;
    shape<3> ppos(PADPOS);
    for (int oh = 0; oh < oshp[1]; oh++) {
      for (int ow = 0; ow < oshp[0]; ow++) {    
        for (int grp = 0; grp < GRP; grp++) {
          for (int no = 0; no < NO; no++) {
            float o = 0;
            cout << "{" << oh << "," << ow << "," << no+grp*NO << "}=0";
            for (int ni = 0; ni < NI; ni++) {
              for (int fh = 0; fh < fshp[1]; fh++) {
                for (int fw = 0; fw < fshp[0]; fw++) {
                  shape<3> qpos;
                  qpos[SPATIAL_W] = ppos[SPATIAL_W] + ow*sshp[SPATIAL_W] + fw*dshp[SPATIAL_W];
                  qpos[SPATIAL_H] = ppos[SPATIAL_H] + oh*sshp[SPATIAL_H] + fh*dshp[SPATIAL_H];
                  if (qpos[SPATIAL_W] >= 0 && qpos[SPATIAL_W] <= plim[SPATIAL_W] && 
                      qpos[SPATIAL_H] >= 0 && qpos[SPATIAL_H] <= plim[SPATIAL_H]) {
                    float fm(fitns.read({(short)(ni+NI*grp),
                                            (short)(ow*sshp[0]+fw*dshp[0]),
                                            (short)(oh*sshp[1]+fh*dshp[1]),
                                            0}));
                    float cf(citns.read({(short)ni,(short)fw,(short)fh,0,(short)no,(short)grp}));
                    cout << "+" << fm << "*" << cf;
                    o += fm*cf;
                  } // else pad 0 i.e. do not add
                }
              }
            }
            cout << "=" << o << endl;
          }
        }
      }
    }
  }

  void prep_operands() {
    // copy tensors to VM
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
    mem_write(&rt->mmio, &rgs);  // MMIO base address
    mem_write(&rt->ctrl,  (uint32_t)1);     // raise event at completion
    cv.set_impl_params(*rt);

    // set some tile specific parameters
    shape<3> padpos;
    shape<3> os0(OSHP);
    padpos = PADPOS;
    shape<3>* padpos_csm;
    csmalloc.alloc(padpos_csm);
    mem_write(padpos_csm, padpos);
    cv.init_tile_params(*padpos_csm, *impl_cf_csm, *impl_pad_csm);

    // assign an output buffer
    cv.set_output(*ab_csm);

    // enable interrupts and events
    mmio_write(&rgs.int_enable , 0xffffffff);
    run_cycles(1);

    cout << "begin execute" << endl;
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
  }

  void report() {
        #ifdef RTL_DPI
        size_t dummy_sz = 1024*1024*32;
    uint8_t *pdummy = (uint8_t *)malloc(dummy_sz);
    //dummy_alloc = new mem_alloc_t(reinterpret_cast<uint64_t>(pdummy), dummy_sz);
        mem_alloc_t dummy_alloc(reinterpret_cast<uint64_t>(pdummy),dummy_sz);
        #else
    #endif
    // get output
    buffer_t<fp_e8m23_t> obuf;
    shape<3> os0(OSHP);
    shape<4> os1({GRP*NO, os0[0], os0[1], os0[2]});
    csmalloc.alloc(obuf, get_shape_size(os1));
    tensor_t<fp_e8m23_t,4> otns(obuf, os1); // [D][H][W][C][msb/lsb]

    // convert implementation specific to general
    convertfrom(otns, ab);

    // report the output
    tensor::v200::report(rptos, otns, otns.get_dim(0)); 
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

#ifdef RTL_DPI
void arc_exec() {
  // load and execute a test program
  testprog* prg = new testprog("test.rtlrun.rpt");
  // execute the test program
  prg->exec();
  // stop the simulator
  arc_exit();
}
#else
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

#endif
