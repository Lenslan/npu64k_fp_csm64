#include <fstream>
#include <iomanip>

#include "npu_conv_hlapi.hpp"
#include "npu_conv_hl_coef.hpp"

using namespace npu_conv;

hl_vm        vm("tb_vm");
hl_dm        dm("tb_dm");
hl_am        am("tb_am");
hl_mm        csm("tb_csm");
ctrl_dma_regs<conv_hlapi_t> rgs;
size_t nm_sz = 4*1024*1024;
mem_alloc_t  *pnmalloc; //native memory allocator

conv_hlapi_t hlapi;
coef_data_t  so;
bool zp;

class testprog : public arc_program {
  // allocate compressed coefficient buffer
  xbuffer_t<ixpix_t> cf_buf_xb;
  buffer_t<ixpix_t>  cf_buf;
  size_t             cf_len;

 public:
  inline testprog(const char* file)
  : arc_program()
  , coef("coef", hlapi, vm, zp, so) {
    rptos.open(file);
  }

  //
  // Initialize input memories
  //
  void mem_init() {
    // generate a set of coefficients and zero-points
    //mem_t m(64*1024);
    //mem_alloc_t malloc(m.base_addr, m.size);
    //buffer_t<coef_t> cbuf;
    //buffer_t<coef_t> zbuf;
    //malloc.alloc(cbuf, NI*FW*FH*FD*NO*GRP);
    //malloc.alloc(zbuf, NO*GRP);
    mem_alloc_t  vmalloc(reinterpret_cast<uint64_t>(get_slice_vm_base()), vm.size());

    xbuffer_t<coef_t> cbuf;
    xbuffer_t<coef_t> zbuf;
    pnmalloc->alloc(cbuf, NI*FW*FH*FD*NO*GRP);
    pnmalloc->alloc(zbuf, NO*GRP);

    tensor_t<coef_t,6,xbuffer_t> ctns(cbuf, {NI,FW,FH,FD,NO,GRP});
    tensor_t<coef_t,1,xbuffer_t> ztns(cbuf, {NO*GRP});

    // fill coefficients
    tensor_iterator_t<coef_t,6,xbuffer_t> cit(ctns);
    coef_t c = (coef_t)0;
    do {
      cit.write(c);
      c++;
    } while (cit.next());

    // fill zero points
    tensor_iterator_t<coef_t,1,xbuffer_t> zit(ztns);
    coef_t z = (coef_t)0;
    do {
      zit.write(z);
      z++;
    } while (zit.next());

    // allocate buffer for encoded coeffcients
    vmalloc.alloc(cf_buf, NI*FW*FH*FD*NO*GRP*10/8);
    pnmalloc->alloc(cf_buf_xb, NI*FW*FH*FD*NO*GRP*10/8);

    xbuffer_t<coef_t> tbuf_xb;
    pnmalloc->alloc(tbuf_xb, nm_sz/2);

    // encode coefficients
    if (CF_ZP) {
      coef_enc(ctns, ztns, tbuf_xb, CONV_MODE, COEF_MODE, FM_DBL, CF_4B, INN, ONN, cf_buf_xb, cf_len);
    } else {
      coef_enc(ctns, tbuf_xb, CONV_MODE, COEF_MODE, FM_DBL, CF_4B, INN, ONN, cf_buf_xb, cf_len);
    }

    // dump memory
    cout << "mem" << endl;
    cf_buf_xb.deep_copy(cf_buf);
    ixpix_t* _p = cf_buf.get_base();
    for (int i = 0; i < (int)cf_len; i++) {
      cout << mem_read(_p++) << endl;
    }
  }

  void exec() override {
    hl_hlapi_iterator<CONV_HLAPI_LOOPS> iter(hlapi.i.iter);

    //
    // initialize input arrays
    //
    uint8_t *pnm = (uint8_t *)malloc(nm_sz); assert(pnm);
    pnmalloc = new mem_alloc_t(reinterpret_cast<uint64_t>(pnm), nm_sz);
    mem_init();

    //
    // Program
    //
    // set up HLAPI parameters
    fm_cfg_t fm_cfg = FM_DBL ? fm_cfg_16b_e : fm_cfg_8b_e;
    cf_cfg_t cf_cfg;

    if (CF_DBL) {
      cf_cfg = cf_cfg_16b_e;
    } else if (CF_4B) {
      if (CF_ZP) {
        cf_cfg = cf_cfg_4b_zp_e;
      } else {
        cf_cfg = cf_cfg_4b_nozp_e;
      }
    } else {
      if (CF_ZP) {
        cf_cfg = cf_cfg_8b_zp_e;
      } else {
        cf_cfg = cf_cfg_8b_nozp_e;
      }
    }

    hlapi.i.bf = (((uint32_t)CONV_MODE) << CONV_BF_CONV_MODE_START) |
                (((uint32_t)COEF_MODE) << CONV_BF_CF_MODE_START)   |
                (((uint32_t)fm_cfg)    << CONV_BF_FM_CFG_START)    |
                (((uint32_t)cf_cfg)    << CONV_BF_CF_CFG_START);

    switch (CONV_MODE) {
    case DINO(conv_mode_1x1):
      hlapi.i.iter[CONV_ITER_GRP] = GRP;
      hlapi.i.iter[CONV_ITER_QD]  = FW*FH*FD;
      hlapi.i.iter[CONV_ITER_NO]  = (NO+ONN*ISIZE-1)/(ONN*ISIZE);
      hlapi.i.iter[CONV_ITER_NI]  = (NI+2*ISIZE*INN-1)/(2*ISIZE*INN);
      break;
    case NINO(conv_mode_3x3dws1):
      hlapi.i.iter[CONV_ITER_GRP] = (GRP+ISIZE-1)/ISIZE;
      hlapi.i.iter[CONV_ITER_QD]  = ((FW+2)/3)*((FH+2)/3)*FD;
      hlapi.i.iter[CONV_ITER_NO]  = 1;
      hlapi.i.iter[CONV_ITER_NI]  = 1;
      break;
    default: assert(0);
    }
    hlapi.i.iter[CONV_ITER_COL] = 3;
    hlapi.i.iter[CONV_ITER_ROW] = 2;
    hlapi.i.iter[CONV_ITER_INN] = INN;
    hlapi.i.iter[CONV_ITER_ONN] = ONN;
    hlapi.i.cf_ptr              = cf_buf.get_base();

    // initialize all blocks
    iter.init();
    coef.init();
    int cyc = 0;
    do {
      if ((iter.first() & 0xf0) == 0xf0) {
        cout << "CYCLE: " << cyc << endl;
        // new coefficients required
        if ((iter.first() & 0xfc) == 0xfc) {
          rptos << "REPORT new zero-points" << endl;
          zp = true;
        } else {
          zp = false;
        }
        coef.update();
        for (int io = 0; io < INN*ONN; io++) {
          for (int o = 0; o < ISIZE; o++) {
            std::ios state0(nullptr);
            state0.copyfmt(rptos);
            rptos << std::noshowbase << std::internal << std::hex << std::setfill('0') << "REPORT (" << std::setw(2) << o << "):";
            rptos.copyfmt(state0);
            for (int i = 0; i < 2*ISIZE; i++) {
              rptos << " " << so[io][o].ctrl[i];
            }
            for (int i = 0; i < 2*ISIZE; i++) {
              if (so[io][o].ctrl[i] == selfix0) {
                rptos << " " << "000";
              } else {
                rptos << " " << std::noshowbase << std::internal << std::hex << std::setfill('0') << std::setw(3) << ((int)(so[io][o].coef[i] & 0x0fff));
                rptos.copyfmt(state0);
              }
            }
            rptos << endl;
            rptos.copyfmt(state0);
          }
        }
      }
      cyc++;
    } while (iter.next());
    cout << "done " << cyc << endl;

    rptos.close();

    npu_module_if::report_all(cout);
    arc_exit();
  }

  void irq() override {}

  hl_coef coef;
  std::ofstream rptos;
};

#include "../common/test_sc.hpp"
