#include <fstream>

#include "npu_ctrl_hl.hpp"
#include "arc_program.hpp"
#include "npu_conv_hl_stash.hpp"

using namespace npu_conv;


hl_vm vm("vm");
hl_dm dm("dm");
hl_am am("am");
hl_mm csm("csm");
ctrl_dma_regs<conv_hlapi_t> rgs;
mem_alloc_t vmalloc(reinterpret_cast<uint64_t>(NPU_INTRA_SLICE_VM_BASE), vm.size());
mem_alloc_t dmalloc(reinterpret_cast<uint64_t>(NPU_INTRA_SLICE_DCCM_BASE), dm.size());

class testprog : public arc_program {
  //
  // Shapes
  //
  shape<4> ifs; // input feature-map shape
  int      nn;  // input channel multiplier for i32
  int      ni;  // actual number of input channels
  int      no;  // actual number of output channels
  int      qd;  // actual number of quadrants

  // inputs and outputs
  conv_hlapi_t hlapi;
  stash_out_t  so;

  hl_stash stash;
  std::ofstream rptos;

  //
  // Buffers
  //
  buffer_t<ixpix_t>       fmbuf;
  buffer_t<ixpix_t>       padbuf;
  tensor_t<ixpix_t,4>     fmtns;
  tensor_t<ixpix_t,1>     padtns;

 public:
  inline testprog(const char* file)
  : arc_program()
  , stash("stash", hlapi, dm, vm, so) {
    rptos.open(file);
  }

  //
  // Initialize input memories
  //
  void mem_init() {
    //
    // round feature-map dimensions
    //
    if (CONV_MODE == DINO(conv_mode_1x1)) {
      nn = 2; // input channel mode multiplier
    } else {
      nn = 1;
    }
    ni   = ((GRP*NI+ISIZE-1)/ISIZE)*ISIZE;
    no   = ((GRP*NO+ISIZE-1)/ISIZE)*ISIZE;
    // input shape
    ifs[0] = 1+(FW-1)*DILW+(COLS-1)*STRW;
    ifs[1] = 1+(FH-1)*DILH+(ROWS-1)*STRH;
    ifs[2] = 1+(FD-1)*DILD+(DPTH-1)*STRD;
    ifs[3] = (GRP*NI+ISIZE-1)/ISIZE;
    // allocate buffer and create tensors
    vmalloc.alloc(fmbuf, tensor::v200::get_shape_size(ifs));
    fmtns = tensor_t<ixpix_t,4>(fmbuf, ifs);
    vmalloc.alloc(padbuf, ni/ISIZE);
    padtns = tensor_t<ixpix_t,1>(padbuf, {(aoffset_t)(ni/ISIZE)});
    //
    // fill feature-map and padding
    //
    tensor_iterator_t<ixpix_t,4> fit(fmtns);
    int f = 0;
    do {
      ixpix_t v;
      for (int i = 0; i < ISIZE; i++) {
        v[i] = (pix_t)f++;
      }
      fit.write(v);
    } while (fit.next());
    tensor_iterator_t<ixpix_t,1> pit(padtns);
    int p = -10;
    do {
      ixpix_t v;
      for (int i = 0; i < ISIZE; i++) {
        v[i] = (pix_t)p++;
      }
      pit.write(v);
    } while (pit.next());
  }

  void quad_enc() {
    //
    // determine quadrants and fill info
    //
    switch (CONV_MODE) {
    case DINO(conv_mode_1x1):
    case NINO(conv_mode_1x1):
      {
        qd    = FW*FH*FD;
        hlapi.i.iter[CONV_ITER_QD]   = qd;
        quadrant_t q;
        hlapi.i.quad_iter[0] = FW;
        hlapi.i.quad_iter[1] = FH;
        hlapi.i.quad_iter[2] = FD;
        // next filter column
        q.pdoffs[CONV_PAD_COL] = DILW-(((COLS+VSIZE-1)/VSIZE)-1)*VSIZE*STRW;
        q.pdoffs[CONV_PAD_ROW] = 0;
        q.pdoffs[CONV_PAD_DEP] = 0;
        q.doffs                = q.pdoffs[CONV_PAD_COL]*fmtns.get_offset(0);
        hlapi.i.quad_data[0]   = q;
        // next filter row
        q.pdoffs[CONV_PAD_COL] = (1-FW)*DILW-(((COLS+VSIZE-1)/VSIZE)-1)*VSIZE*STRW;
        q.pdoffs[CONV_PAD_ROW] = DILH;
        q.pdoffs[CONV_PAD_DEP] = 0;
        q.doffs                = q.pdoffs[CONV_PAD_COL]*fmtns.get_offset(0) + DILH*fmtns.get_offset(1);
        hlapi.i.quad_data[1]   = q;
        // next depth
        q.pdoffs[CONV_PAD_COL] = (1-FW)*DILW-(((COLS+VSIZE-1)/VSIZE)-1)*VSIZE*STRW;
        q.pdoffs[CONV_PAD_ROW] = (1-FH)*DILH;
        q.pdoffs[CONV_PAD_DEP] = DILD;
        q.doffs                = q.pdoffs[CONV_PAD_COL]*fmtns.get_offset(0) + (1-FH)*DILH*fmtns.get_offset(1) + DILD*fmtns.get_offset(2);
        hlapi.i.quad_data[2]   = q;
        // last quadrant move to next set of input channels
        q.pdoffs[CONV_PAD_COL] = (1-FW)*DILW-(((COLS+VSIZE-1)/VSIZE)-1)*VSIZE*STRW;
        q.pdoffs[CONV_PAD_ROW] = (1-FH)*DILH;
        q.pdoffs[CONV_PAD_DEP] = (1-FD)*DILD;
        q.doffs                = q.pdoffs[CONV_PAD_COL]*fmtns.get_offset(0) + (1-FH)*DILH*fmtns.get_offset(1) + (1-FD)*DILD*fmtns.get_offset(2) + nn*INN*fmtns.get_offset(3);
        hlapi.i.quad_data[3]   = q;
      }
      break;
    case NINO(conv_mode_3x3dws1):
      {
        assert (NI == 1 && NO == 1 && INN == 1 && ONN == 1);
        assert (STRW == 1 && STRH == 1 && STRD == 1); // else not implemented yet (do strided output)
        aoffset_t fw = (DILW*(FW-1)+3)/3;
        aoffset_t fh = (DILH*(FH-1)+3)/3;
        qd    = fw*fh*FD;
        hlapi.i.iter[CONV_ITER_QD]   = qd;
        quadrant_t q;
        hlapi.i.quad_iter[0] = fw;
        hlapi.i.quad_iter[1] = fh;
        hlapi.i.quad_iter[2] = FD;
        // next filter column
        q.pdoffs[CONV_PAD_COL] = 3-(((COLS+VSIZE-1)/VSIZE)-1)*VSIZE;
        q.pdoffs[CONV_PAD_ROW] = 0;
        q.pdoffs[CONV_PAD_DEP] = 0;
        q.doffs                = q.pdoffs[CONV_PAD_COL]*fmtns.get_offset(0);
        hlapi.i.quad_data[0]   = q;
        // next filter row
        q.pdoffs[CONV_PAD_COL] = (1-fw)*3-(((COLS+VSIZE-1)/VSIZE)-1)*VSIZE;
        q.pdoffs[CONV_PAD_ROW] = 3;
        q.pdoffs[CONV_PAD_DEP] = 0;
        q.doffs                = q.pdoffs[CONV_PAD_COL]*fmtns.get_offset(0) + q.pdoffs[CONV_PAD_ROW]*fmtns.get_offset(1);
        hlapi.i.quad_data[1]   = q;
        // next depth
        q.pdoffs[CONV_PAD_COL] = (1-fw)*3-(((COLS+VSIZE-1)/VSIZE)-1)*VSIZE;
        q.pdoffs[CONV_PAD_ROW] = (1-fh)*3;
        q.pdoffs[CONV_PAD_DEP] = DILD;
        q.doffs                = q.pdoffs[CONV_PAD_COL]*fmtns.get_offset(0) + q.pdoffs[CONV_PAD_ROW]*fmtns.get_offset(1) + q.pdoffs[CONV_PAD_DEP]*fmtns.get_offset(2);
        hlapi.i.quad_data[2]   = q;
        // last quadrant move to next set of input channels
        q.pdoffs[CONV_PAD_COL] = (1-fw)*3-(((COLS+VSIZE-1)/VSIZE)-1)*VSIZE;
        q.pdoffs[CONV_PAD_ROW] = (1-fh)*3;
        q.pdoffs[CONV_PAD_DEP] = (1-FD)*DILD;
        q.doffs                = q.pdoffs[CONV_PAD_COL]*fmtns.get_offset(0) + q.pdoffs[CONV_PAD_ROW]*fmtns.get_offset(1) + q.pdoffs[CONV_PAD_DEP]*fmtns.get_offset(2) + fmtns.get_offset(3);
        hlapi.i.quad_data[3]   = q;
      }
      break;
    default:
      // not implemented yet
      assert(0);
      break;
    }
  }

  inline void report(ostream& os, const stash_out_t& so) {
    cout << "start:" << endl;
    for (int i = 0; i < 16; i++) {
      os << "REPORT: " << so[i] << endl;
    }
  }

  void exec() override {
    // initialize input arrays
    //
    mem_init();

    //
    // Program
    //

    // initialize HLAPI struct
    hlapi.i.common.ctrl          = 0;
    hlapi.o.status               = 0;
    hlapi.io.cycles              = 0;
    hlapi.i.common.next          = nullptr;
    hlapi.i.iter[CONV_ITER_ONN]  = ONN;
    hlapi.i.iter[CONV_ITER_INN]  = INN; 
    hlapi.i.iter[CONV_ITER_ROW]  = ROWS;
    hlapi.i.iter[CONV_ITER_COL]  = (COLS+VSIZE-1)/VSIZE; 
    hlapi.i.iter[CONV_ITER_NI]   = (NI+nn*INN*ISIZE-1)/(nn*INN*ISIZE);
    hlapi.i.iter[CONV_ITER_NO]   = (NO+ISIZE-1)/ISIZE;  
    hlapi.i.iter[CONV_ITER_GRP]  = (GRP+ISIZE-1)/ISIZE; 
    hlapi.i.fm_ptr               = fmtns.get_base();
    hlapi.i.fm_buf.base          = fmtns.get_base();
    hlapi.i.fm_buf.len           = fmtns.get_size();
    // pad left, right, top, bottom edge
    hlapi.i.fm_padlim[CONV_PAD_COL] = ifs[0]-3;
    hlapi.i.fm_padlim[CONV_PAD_ROW] = ifs[1]-3;
    hlapi.i.fm_padlim[CONV_PAD_DEP] = 0;
    hlapi.i.fm_padpos[CONV_PAD_COL] = -1;
    hlapi.i.fm_padpos[CONV_PAD_ROW] = -1;
    hlapi.i.fm_padpos[CONV_PAD_DEP] = 0;
    hlapi.i.fm_pdoffsets[CONV_FM_PDOFF_COL] = STRW;
    hlapi.i.fm_pdoffsets[CONV_FM_PDOFF_ROW] = STRH;
    hlapi.i.fm_doffsets[CONV_FM_DOFF_CHAN]  = fmtns.get_offset(3);
    hlapi.i.fm_doffsets[CONV_FM_DOFF_COL]   = fmtns.get_offset(0)*STRW;
    hlapi.i.fm_doffsets[CONV_FM_DOFF_ROW]   = fmtns.get_offset(1)*STRH;
    hlapi.i.pad_ptr                         = padtns.get_base();
    quad_enc();
    hlapi.i.cf_ptr                          = nullptr;
    hlapi.i.acc_ptr                         = 0;
    hlapi.i.bf = ((uint32_t)CONV_MODE) << CONV_BF_CONV_MODE_START;
    
  #ifdef DBGTEST
    cout << "fmtns" << endl;
    report(cout, fmtns);

    cout << "padtns" << endl;
    report(cout, padtns);
  #endif

    // initialize all blocks
    stash.init();
    int  cyc = 0;
    bool active;
    do {
      cout << "CYCLE: " << cyc << endl;
      active = stash.update();
      report(rptos, so);
      cyc++;
    } while(active);
    cout << "done" << endl;
    
    rptos.close();

    npu_module_if::report_all(cout);
    arc_exit();
  }

  void irq() override {}
};

#include "../common/test_sc.hpp"
