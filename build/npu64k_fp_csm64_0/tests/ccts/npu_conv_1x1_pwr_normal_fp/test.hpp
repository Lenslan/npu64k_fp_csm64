//===================================================
// NOTE: This file is automatically generated.
//===================================================
#include "tensor_dma.hpp"
#include "tensor_conv.hpp"
#include "npu_conv_hlapi.hpp"
#ifdef SYSTEMC
#include "../../../shared/hlmodel/npu_shared_hl_mem.hpp"
#endif
using namespace tensor::v200;
using namespace npu;
#include "arcsync_utils.hpp"
#include "utils/cln_map.hpp"
#include "utils/npu_mem_utils.hpp"
#include "utils/npu_mem_map_define.hpp"
//#ifdef RTL_DPI
#include <fstream>
//#endif
#include "utils/sim_terminate.hpp"
#include "utils/arc_utils.h"

mem_alloc_t* xmalloc;
mem_alloc_t* vmalloc;
mem_alloc_t* amalloc;
mem_alloc_t* dmalloc;
mem_alloc_t* dummy_alloc;

static ixpix_t viImg[] = {
    #include "ref/viImg.mhex"
};

static vyixacc_t cAcc[] = {
  #include "ref/cAcc.mhex"
};

static coef_t vCBA[] = {
  #include "ref/vCBA.mhex"
};

#ifdef RTL_ARC
static ixpix_t coef_tran[] = {
   #include "rtl/vCBA.mhex"
};
static vyixacc_t acc[] = { 
    #include "ref/cAcc.ok1" 
};
#endif

#ifdef RTL_ARC
_Uncached volatile unsigned int err_cnt=0;
_Uncached volatile unsigned int chk_cnt=0;
_Uncached volatile unsigned int * err_msg= (unsigned int*)0x1f00_0000;
#else
unsigned int chk_cnt=0;
unsigned int err_cnt=0;
unsigned int * err_msg;
#endif

class test_program : public arc_program {
public:
  inline test_program() : arc_program() {
    irqflag = false;
  }
  virtual void irq() {
    irqflag = true;
  }
  // parameters to run-time
  conv_params_impl_shapes shps;           // buffer shapes
  conv_params_impl_main   rtpars;         // main parameters
  conv_params_impl_coef<buffer_t>   impl_cf;        // encoded coefficients
  conv_params_impl_pad<buffer_t>    impl_pad;       // encoded padding
  impl_spec_container_t<buffer_t>   l1buf;          // input feature-map in VM
  conv_params_impl_coef<xbuffer_t>  impl_cf_xb;    // encoded coefficients
  conv_params_impl_pad<xbuffer_t>   impl_pad_xb;   // encoded padding
  impl_spec_container_t<xbuffer_t>  l1buf_xb;      // input feature-map in VM
  conv_params_impl_coef<buffer_t>*  impl_cf_csm;    // encoded coefficients
  conv_params_impl_pad<buffer_t>*   impl_pad_csm;   // encoded padding
  impl_spec_container_t<buffer_t>*  l1buf_csm;      // input feature-map in VM
  acc_buf_impl_t<buffer_t>          ab;             // output accumulator in AM
  acc_buf_impl_t<xbuffer_t>         ab_xb;         // output accumulator
  acc_buf_impl_t<buffer_t>*         ab_csm;         // output accumulator
  #ifdef SYSTEMC
  hl_xm*                  pxm;            // pointer to xm
  hl_vm*                  pvm;            // pointer to vm
  hl_am*                  pam;            // pointer to am
  hl_dm*                  pdm;            // pointer to dm
  #endif
  
  void aot_compile() {
    conv_params<xbuffer_t> pars( 1/*GRP*/,
                      192/*NI*/,
                      64/*NO*/,
                      {8,60,1}/*OSHP*/,
                      {1,1,1}/*FSHP*/,
                      {1,1,1}/*SSHP*/,
                      {1,1,1}/*DSHP*/,
                      {7,59,191}/*PLIM*/,
                      false/*UA*/,
                      true/*KA*/,
					  fm_cfg_fp16_e/*FMTYP*/,
                      cf_cfg_fp16_e/*CFTYP*/);
    conv_params_impl_spec spc;
    pars.get_impl_params(spc);
    spc = { conv_mode_1x1i32o16,
            1,/*inn*/
            1,/*onn*/
            coef_mode_uncompressed,/*cf_mode*/
            false/*cf_4b*/};
    pars.set_impl_params(spc);
    // get the shapes of input/output tensors
    pars.get_shapes(shps);
    
    impl_cf_xb = conv_params_impl_coef<xbuffer_t>(*dummy_alloc, shps);
  #ifndef RTL_FAST_SIM
    xbuffer_t<fp_e5m10_t>   cibuf;
    dummy_alloc->alloc(cibuf, 1*192*1*1*1*64*1);
    tensor_t<fp_e5m10_t,6,xbuffer_t> citns(cibuf, {192,1,1,1,64,1});
    tensor_iterator_t<fp_e5m10_t,6,xbuffer_t> cit(citns);
    int k = 0;
    do {
      cit.write(fp_e5m10_t((uint8_t)vCBA[2*k+1],(uint8_t)vCBA[2*k]));
      k++;
    } while(cit.next());
    xbuffer_t<coef_t> czbuf;
    dummy_alloc->alloc(czbuf,196608);
    pars.coef_enc(citns, impl_cf_xb, czbuf);
  #endif


    impl_cf  = conv_params_impl_coef<buffer_t>(*vmalloc, impl_cf_xb.get_size());
    deep_copy(impl_cf, impl_cf_xb);
    tensor_t<ixpix_t,1,buffer_t> cftns(impl_cf.cbuf,{(aoffset_t)impl_cf.cbuf.get_size()});
    tensor_iterator_t<ixpix_t,1,buffer_t> cft(cftns);

  #ifdef SYSTEMC
    //dump coef as the input initlization file for RTL simulation
    FILE *outf = NULL;
    outf= fopen("rtl/vCBA.mhex", "w");
    ixpix_t coef_tran;
    do {
        coef_tran = cft.read();
        fprintf(outf,"(ixpix_t){(pix_t)0x%02x,(pix_t)0x%02x,(pix_t)0x%02x,(pix_t)0x%02x,(pix_t)0x%02x,(pix_t)0x%02x,(pix_t)0x%02x,(pix_t)0x%02x,(pix_t)0x%02x,(pix_t)0x%02x,(pix_t)0x%02x,(pix_t)0x%02x,(pix_t)0x%02x,(pix_t)0x%02x,(pix_t)0x%02x,(pix_t)0x%02x},",coef_tran[0]&0xff,coef_tran[1]&0xff,coef_tran[2]&0xff,coef_tran[3]&0xff,coef_tran[4]&0xff,coef_tran[5]&0xff,coef_tran[6]&0xff,coef_tran[7]&0xff,coef_tran[8]&0xff,coef_tran[9]&0xff,coef_tran[10]&0xff,coef_tran[11]&0xff,coef_tran[12]&0xff,coef_tran[13]&0xff,coef_tran[14]&0xff,coef_tran[15]&0xff);
    }while(cft.next());
    fclose(outf);
  #endif




  #ifdef RTL_FAST_SIM
    //Fast initilization with the same coefficients(generared by SC) for RTL simulation
    int k = 0;
    set_mem_backdoor(1,0);
    do {
       cft.write(coef_tran[k]);
       k++;
    }while(cft.next());
    set_mem_backdoor(0,0);
  #endif


    l1buf_xb = impl_spec_container_t<xbuffer_t>(*dummy_alloc,shps.ishape);
    pars.init_l1(l1buf_xb);
    tensor_iterator_t<ixpix_t,5,xbuffer_t> iti(l1buf_xb.data);
    int i = 0;
    set_mem_backdoor(1,0);
    do {
        iti.write(viImg[i]);
        i++;
    } while(iti.next());
    set_mem_backdoor(0,0);


    xbuffer_t<fp_e5m10_t> pibuf;
    dummy_alloc->alloc(pibuf,192*1);
    tensor_t<fp_e5m10_t,1,xbuffer_t> pitns(pibuf,{(aoffset_t)192});
    tensor_iterator_t<fp_e5m10_t,1,xbuffer_t> pti(pitns);


    impl_pad_xb = conv_params_impl_pad<xbuffer_t>(*dummy_alloc, shps);
    pars.pad_enc(pitns, impl_pad_xb);
    ab_xb = acc_buf_impl_t<xbuffer_t>(*dummy_alloc, shps.oshape);
    tensor_t<vyixacc_t,5,xbuffer_t> ab_xb_data(ab_xb.data);
    tensor_iterator_t<vyixacc_t,5,xbuffer_t> otn(ab_xb_data);
    do {
        otn.write(cAcc[(otn.get_index(0)+1*1*otn.get_index(2)+1*1*otn.get_index(1)+1*1*60*otn.get_index(4))]);
    } while(otn.next());
    // serialize run-time parameters
    pars.get_rt_params(rtpars);
  }
    
    void prepare_operands() {
    l1buf    = impl_spec_container_t<buffer_t>(*vmalloc,shps.ishape);
    impl_pad = conv_params_impl_pad<buffer_t>(*vmalloc, shps);
    deep_copy(l1buf, l1buf_xb);
    deep_copy(impl_pad, impl_pad_xb);
    xmalloc->alloc(impl_cf_csm);
    xmalloc->alloc(impl_pad_csm);
    xmalloc->alloc(l1buf_csm);
    mem_write(impl_cf_csm, impl_cf);
    mem_write(impl_pad_csm, impl_pad);
    mem_write(l1buf_csm, l1buf);
    ab = acc_buf_impl_t(*amalloc, shps.oshape);
    deep_copy(ab, ab_xb);
    xmalloc->alloc(ab_csm);
    mem_write(ab_csm, ab);
    }
    
    void run_time() {
    // run-time execution
    npu::ctrl_dma_regs<npu_conv::conv_hlapi_t>&   rgs(*reinterpret_cast<npu::ctrl_dma_regs<npu_conv::conv_hlapi_t>*>(get_mmio_base_conv()));
    conv_rt& cv(*create(*dmalloc,rtpars));
    conv_rt_impl_spec* rt;
    xmalloc->alloc(rt);
    mem_write(&rt->mmio, &rgs);// MMIO base address
    mem_write(&rt->ctrl,  (uint32_t)0xffffff);// raise event at completion
    cv.set_impl_params(*rt);
    shape<3> padpos = {0,0,0};
    shape<3>* padpos_csm;
    xmalloc->alloc(padpos_csm);
    mem_write(padpos_csm, padpos);
    // initialize tile parameters
    cv.init_tile_params(*padpos_csm, *impl_cf_csm, *impl_pad_csm);
    cv.set_input(*l1buf_csm);
    cv.set_output(*ab_csm);
    mmio_write(&rgs.int_enable, 0xffffffff);
    cv.prepare();
    start_power();
    cv.execute();
    event_wait_any(1LL<<EVT_CONV_DONE);
    stop_power();
    run_cycles(10);

    tensor_t<vyixacc_t,5> ab_data(ab.data);
    tensor_iterator_t<vyixacc_t,5> otn(ab_data);
    set_mem_backdoor(1,0);


  #ifndef RTL_ARC
    do{
        //cout << "REPORT: " <<otn.read() <<endl;
        cAcc[(otn.get_index(0)+1*1*otn.get_index(2)+1*1*otn.get_index(1)+1*1*60*otn.get_index(4))] = otn.read();
    } while(otn.next());

    ofstream rptos;
    rptos.open("ref/cAcc.ok1");
    do{
        rptos << otn.read() << "," << endl;
    } while(otn.next());
    rptos.close();
   #endif

    set_mem_backdoor(0,0);
    run_cycles(10);
  }
  

  template<typename T> void check(T a, T b) {
    chk_cnt++;
    if (a != b) {
        *err_msg++ = err_cnt++;
        *err_msg++ = a;
        *err_msg++ = b;
        set_sim_finish_flag(err_cnt);
    }
  }



  void report() {
#ifdef RTL_ARC
    tensor_t<vyixacc_t,5> ab_data(ab.data);
    tensor_iterator_t<vyixacc_t,5> otn(ab_data);
    int k=0;
    do{
        vyixacc_t real = otn.read();
        vyixacc_t ref  = acc[k++];

        for(int y=0;y < VSIZE;y++){
            for(int x=0;x < ISIZE;x++){
				if(k==10){
               check(ref[y][x], real[y][x]);
				}
            }
        }
	if(k==10)
		break;
    set_sim_finish_flag(err_cnt);
    } while(otn.next());
    
#endif

  }

  void exec() {
     evt_cfg();
#ifdef NPU_MEM_ECC
     uint32_t sfty_erp_ctrl_addr;
     sfty_erp_ctrl_addr = LOCAL_PERI_BASE + L1_SFTY_MMIO_OFFSET + 0x0_0000;
     vm_am_mem_init((uint32_t *)sfty_erp_ctrl_addr);
#endif
#ifdef SYSTEMC
    xmalloc = new mem_alloc_t(pxm->base_addr, pxm->size);
    vmalloc = new mem_alloc_t(pvm->base_addr, pvm->size);
    amalloc = new mem_alloc_t(pam->base_addr, pam->size);
    dmalloc = new mem_alloc_t(pdm->base_addr, pdm->size);
    size_t dummy_sz = 1024*1024*4;
    uint8_t *pdummy = (uint8_t *)malloc(dummy_sz);
    dummy_alloc = new mem_alloc_t(reinterpret_cast<uint64_t>(pdummy), dummy_sz);
#else
    vmalloc = new mem_alloc_t((uint64_t)get_slice_vm_base(), 0x100000);
    amalloc = new mem_alloc_t((uint64_t)get_slice_am_base(), 0x200000);
    dmalloc = new mem_alloc_t((uint64_t)get_fast_dccm_base(), 0x80000);
	xmalloc = new mem_alloc_t((uint64_t)0x17000000, 0x3000000);
	dummy_alloc = new mem_alloc_t((uint64_t)0x1a000000, 0x3000000);
#endif


    aot_compile();
    prepare_operands();
    run_time();
    report();
    arc_exit();
  }

private:
  bool irqflag;
};



