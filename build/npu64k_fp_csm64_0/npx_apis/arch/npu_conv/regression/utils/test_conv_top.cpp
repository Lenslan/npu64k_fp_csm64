#include "npu_conv_hl_top.hpp"
using namespace npu;
using namespace npu_conv;

#include <mutex>
#include <condition_variable>

// MMIO registers
ctrl_dma_regs<conv_hlapi_t> rgs;

// instantiate memories
hl_dm dm("tb.dm");
hl_xm xm("tb.xm");
hl_vm vm("tb.vm");
hl_am am("tb.am");


//
// Derived parameters
//
// macro to divide by 8 and round up
#define DIVRND_UP8(x) ((x+7)/8)
// macro to round up to multiples of 8
#define RND_UP8(x) (8*DIVRND_UP8(x))

// not debug if not defined
#ifndef DBGLVL
#endif

// number of coefficients
#define CFNUM    (DW ? (NI*QD) : (NI*QD*NO))
#define NUMCOEFS (DW ? (NI*QD*IC*FS*INN*ONN) : HALF ? (NI*QD*IC*FS*NO*OC*INN*ONN/2) : (NI*QD*IC*FS*NO*OC*INN*ONN))
// depthwise mode has NO=NI
#define NOI   (DW?1:NO)
#define NOO   (DW?NI:NO)
// row size
#define RSZ   (COLSTR*COLS+OLAP)
// input channel size
#define ICSZ  (RSZ*IROWS)
// total input size
#define ISZ   (ICSZ*INN*NI*CIN)
// accumulator size
#define ACSZ  (HALF?ROWS*COLS*NOO*ONN/2:ROWS*COLS*NOO*ONN)
// padding array size
#define PSZ   DIVRND_UP8(NI*IC*INN)
// offset 1x1i32o8 from end of inner to next row
#define ROFFS ((1-INN)*2*ICSZ+RSZ)
// coefficient layouts, number of nibble per group of 8 coefficients and compression mode
#if   (COEFSEL == COEFSELSPARSE)
#define NIBBLE_PC8 (3+3*8)
#define COEF_MODE  coef_mode_sparse
#elif (COEFSEL == COEFSELCOMPRESSED)
#define NIBBLE_PC8 (2+3*8)
#define COEF_MODE  coef_mode_compressed
#elif (COEFSEL == COEFSELNORMAL)
#define NIBBLE_PC8 (3*8)
#define COEF_MODE  coef_mode_uncompressed
#else
#error
#endif
// round up coefblock to multiples of 8*NUM_COEF_QUEUE
#define NUMCOEFSRND (8*NUM_COEF_QUEUE*((NUMCOEFS+8*NUM_COEF_QUEUE-1)/(8*NUM_COEF_QUEUE)))
// convert number of coefficient nibbles to ixpix_t
#define NUMNIBBLE (NUMCOEFSRND*NIBBLE_PC8)
#ifdef CFG_12B
#define NUMIXPIX  (NUMNIBBLE/(ISIZE*3))
#else
#define NUMIXPIX  (NUMNIBBLE/(ISIZE*2))
#endif


#if (SPARSE == 1)
// double outputs
#define ACSZ1     (ACSZ*2)
#else
// single outputs
#define ACSZ1     ACSZ
#endif

#if (MD8B == true)
#define FMMASK 0x00ff
#else
#define FMMASK 0x0fff
#endif

//
// Input data
//
ixpix_t    pixarr[ISZ];
ixpix_t    padarr[PSZ];
quadrant_t qdarr[QD];

//
// Input/output accumulators
//
vyixacc_t  accin[ACSZ1];

//
// allocate compressed coefficient buffer, 4*8 extra to avoid segmentation fault on prefetching
//
ixpix_t coefs[NUMIXPIX+3*NUM_COEF_QUEUE];

void coef_mem_init() {
  array<list<short>, NUM_COEF_QUEUE> queues;
  int cb = NUMCOEFSRND;
  int q = 0;
  int c = 0;
#ifdef CFG_12B
  int npc = MD8B ? 2 : 3;
#else
  int npc = 2;
#endif
  int m   = 0x0f; // 4 avail bit mask
  int msk[6] = {2,3,4,5,6,7}; // sparse encodings
  int midx[4] = {0,1,3,5};    // sparse encoding indexes
  int sprs;
  bool m9 = false
          #if ISIZE==8
            || (MODE == conv_mode_3x3s1dwi8o8) || (MODE == conv_mode_3x3s2dwi8o8) || (MODE == conv_mode_3x3s1dwdl2i8o8);
          #endif
            ;
  while (cb > 0) {
    // add 8 coefficients into q
    switch (COEF_MODE) {
    case coef_mode_sparse:
      // 12 bits encoding sparsity
      sprs = 0;
      for (int i = 0; i < 4; i++) {
        sprs |= msk[midx[i]] << (i*3);
        midx[i] = midx[i] == 5 ? 0 : midx[i]+1;
      }
      for (int i = 0; i < 3; i++) {
        queues[q].push_back((sprs>>(i*4))&0xf);
      }
      // 8 coefficients
      for (int i = 0; i < 8; i++) {
        for (int j = 0; j < npc; j++) {
          queues[q].push_back((c>>(4*j))&0xf);
        }
        c++;
      }
      break;
    case coef_mode_compressed:
      // avail bits
      queues[q].push_back(m&0xf);
      queues[q].push_back((m>>4)&0xf);
      // rotate mask by 1
      m = m << 1;
      m = (m | (m>>8)) & 0x00ff;
      for (int i = 0; i < 4; i++) {
        for (int j = 0; j < npc; j++) {
          queues[q].push_back((c>>(4*j))&0xf);
        }
        c++;
      }
      if (m9) {
        // push one extra for 3x3dw
        for (int j = 0; j < npc; j++) {
          queues[q].push_back((c>>(4*j))&0xf);
        }
        c++;
      }
      break;
    default:
      for (int i = 0; i < 8; i++) {
        for (int j = 0; j < npc; j++) {
          queues[q].push_back((c>>(4*j))&0xf);
        }
        c++;
      }
      if (m9) {
        // push one extra for 3x3dw
        for (int j = 0; j < npc; j++) {
          queues[q].push_back((c>>(4*j))&0xf);
        }
        c++;
      }
      break;
    }
    // push
    cb -= m9 ? 9 : 8;
    // update q
    q = q == (NUM_COEF_QUEUE-1) ? 0 : q+1;
  }
  // encode the queues
  ixpix_t px;
  for (int q = 0; q < NUM_COEF_QUEUE; q++) {
    ixpix_t* ptr = &coefs[q];
    int el = 0;
    while (queues[q].size() > 0) {
      for (int i = 0; i < ISIZE; i++) {
        px[i] = (pix_t)0;
        for (int j = 0; j < NIBBLE_PPIX; j++) {
          if (queues[q].size() > 0) {
            px[i] = px[i] | (queues[q].front()<<(j*4));
            queues[q].pop_front();
          }
        }
      }
      *ptr = px;
      ptr += NUM_COEF_QUEUE;
      el++;
      assert(el <= (NUMIXPIX/NUM_COEF_QUEUE));
    }
  }
}

void mem_init() {
  int cnt;
  // fill input pixel array
  assert (ISZ <= 0x0000ffff); // max buffer size is (64K-1)*ixpix_t
  assert ((NI == NO) || !DW);
  cnt = 0;
  for (int e = 0; e < ISZ; e++) {
    for (int i = 0; i < ISIZE; i++) {
      pixarr[e][i] = cnt++;
    }
  }
  // fill quadrant array
  qdarr[QD-1].poffs = (1-COLS)*COLSTR;
  qdarr[QD-1].roffs = 0;
  qdarr[QD-1].coffs = (1-COLS)*COLSTR;
  qdarr[QD-1].doffs = 0;
  for (int e = 0; e < QD-1; e++) {
    qdarr[e].poffs = 1 + (1-COLS)*COLSTR;     // subtract column add 1
    qdarr[e].roffs = 0;                       // no row update
    qdarr[e].coffs = 1 + (1-COLS)*COLSTR;     // subtract column
    qdarr[e].doffs = 0;
    qdarr[QD-1].poffs -= 1;
    qdarr[QD-1].roffs -= 0;
    qdarr[QD-1].coffs -= 1;
    qdarr[QD-1].doffs -= 0;
  }
  // fill input padding array
  cnt = 0;
  for (int e = 0; e < PSZ; e++) {
    for (int i = 0; i < ISIZE; i++) {
      padarr[e][i] = 0xfff - (cnt++);
    }
  }
  // initialize input accumulators
  cnt = 0;
  for (int o = 0; o < ACSZ1; o++) {
    for (int v = 0; v < VSIZE; v++) {
      for (int i = 0; i < ISIZE; i++) {
        accin[o][v][i] = cnt++;
      }
    }
  }
}

void hlapi_init(conv_hlapi_t& hlapi) {
  // set up HLAPI parameters
  hlapi.event          = EVENT;
  hlapi.interrupt      = INTERR;
  hlapi.conv_mode      = MODE;
  hlapi.fm_dbl         = FMDBL;
  hlapi.quad_ptr       = &qdarr[0];
  hlapi.fm_ptr         = &pixarr[0];
  hlapi.fm_buf         = {&pixarr[0], (offset_t)ISZ};
  if (PADEN) {
    hlapi.fm_row         = -1;
    hlapi.fm_col         = -1;
  } else {
    hlapi.fm_row         = 0;
    hlapi.fm_col         = 0;
  }
  hlapi.fm_dep         = 0;
  hlapi.fm_istride     = ISTRIDE;
  hlapi.fm_offsets[0]  = ICSZ;
  hlapi.fm_offsets[1]  = ROFFS;
  hlapi.fm_offsets[2]  = COLSTR;
  hlapi.pad_ptr        = &padarr[0];
  hlapi.pad_mul        = INN == 1 ? conv_mul1 : INN == 2 ? conv_mul2 : conv_mul4;
  if (PADEN) {
    // pad one column left and right, one row top and bottom
    hlapi.pad_window.right  = COLSTR*COLS*RPM+OLAP-1-ISTRIDE-1;
    hlapi.pad_window.bottom = IROWS-2-1;
    hlapi.pad_window.back   = 0;
  } else {
    // no padding
    hlapi.pad_window.right  = 0x0fff;
    hlapi.pad_window.bottom = 0x0fff;
    hlapi.pad_window.back   = 0x0fff;
  }
  hlapi.cf_num            = CFNUM;
  hlapi.cf_mul            = INN*ONN == 1 ? conv_mul1 : INN*ONN == 2 ? conv_mul2 : conv_mul4;
  hlapi.cf_4b             = false;
  hlapi.cf_dbl            = false;
  hlapi.cf_mode           = COEF_MODE;
  hlapi.cf_ptr            = &coefs[0];
  hlapi.use_acc           = USE_ACC;
  hlapi.keep_acc          = true;
  hlapi.acci_ptr          = &accin[0];
  hlapi.acco_ptr          = &accin[0];
  // loop iterations, outer to inner
  hlapi.iter[0] = NOI;     // output channel loop
  hlapi.iter[1] = NI;      // input channel loop
  hlapi.iter[2] = QD;      // quadrant loop
  hlapi.iter[3] = COLS;    // column loop
  hlapi.iter[4] = ROWS;    // row loop
  hlapi.iter[5] = ONN > 1 ? ONN :  INN; // multiple outputs or multiple inputs
  hlapi.iter[6] = 1;       // not used
  hlapi.iter[7] = 1;       // not used
  hlapi.fm_iter[0] = NOI;     // output channel loop
  hlapi.fm_iter[1] = NI;      // input channel loop
  hlapi.fm_iter[2] = QD;      // quadrant loop
  hlapi.fm_iter[3] = COLS;    // column loop
  hlapi.fm_iter[4] = ROWS;    // row loop
  hlapi.fm_iter[5] = INN;     // inner feature-map iterator
  hlapi.acc_iter[0] = DW ? NI : NO;     // output channel loop
  hlapi.acc_iter[1] = DW ? QD : QD*NI;  // input/quadrant channel loop
  hlapi.acc_iter[2] = HALF ? ONN*ROWS*COLS/2 : ONN*ROWS*COLS;    // inner/row/col loop
  // tasks
  if (HALF) {
    // two cycles per output
    hlapi.task.pop_acc.sel_mask      = 0x00; // load acc if firstonn
    hlapi.task.pop_acc.set_mask      = 0x20;
    hlapi.task.pop_acc.clr_mask      = 0x00;
    hlapi.task.pop_coef.sel_mask     = 0x00; // load coefficients if firstonn&firstrow&firstcol
    hlapi.task.pop_coef.set_mask     = 0x38;
    hlapi.task.pop_coef.clr_mask     = 0x00;
    hlapi.task.first_d.sel_mask      = 0x00; // start column firstonn & firstrow
    hlapi.task.first_d.set_mask      = 0x30;
    hlapi.task.first_d.clr_mask      = 0x00;
    hlapi.task.next_d.sel_mask       = 0x00; // start column firstonn & ~firstrow
    hlapi.task.next_d.set_mask       = 0x20;
    hlapi.task.next_d.clr_mask       = 0x10;
    hlapi.task.push_acc.sel_mask     = 0xff; // store acc lastonn
    hlapi.task.push_acc.set_mask     = 0x20;
    hlapi.task.push_acc.clr_mask     = 0x00;
  } else if (ONN > 1) {
    // multiple outputs for one input
    hlapi.task.pop_acc.sel_mask      = 0x00; // load acc always
    hlapi.task.pop_acc.set_mask      = 0x00;
    hlapi.task.pop_acc.clr_mask      = 0x00;
    hlapi.task.pop_coef.sel_mask     = 0x00; // load coefficients if firstonn&firstrow&firstcol
    hlapi.task.pop_coef.set_mask     = 0x38;
    hlapi.task.pop_coef.clr_mask     = 0x00;
    hlapi.task.first_d.sel_mask      = 0x00; // start column firstonn & firstrow
    hlapi.task.first_d.set_mask      = 0x30;
    hlapi.task.first_d.clr_mask      = 0x00;
    hlapi.task.next_d.sel_mask       = 0x00; // start column firstonn & ~firstrow
    hlapi.task.next_d.set_mask       = 0x20;
    hlapi.task.next_d.clr_mask       = 0x10;
    hlapi.task.push_acc.sel_mask     = 0xff; // store acc always
    hlapi.task.push_acc.set_mask     = 0x00;
    hlapi.task.push_acc.clr_mask     = 0x00;
  } else {
    // one or multiple inputs for one output
    hlapi.task.pop_acc.sel_mask      = 0x00; // load acc firstinn
    hlapi.task.pop_acc.set_mask      = 0x20;
    hlapi.task.pop_acc.clr_mask      = 0x00;
    hlapi.task.pop_coef.sel_mask     = 0x00; // load coefficients if firstinn&firstrow&firstcol
    hlapi.task.pop_coef.set_mask     = 0x38;
    hlapi.task.pop_coef.clr_mask     = 0x00;
    hlapi.task.first_d.sel_mask      = 0x00; // start column firstinn & firstrow
    hlapi.task.first_d.set_mask      = 0x30;
    hlapi.task.first_d.clr_mask      = 0x00;
    hlapi.task.next_d.sel_mask       = 0x00; // start column ~(firstinn & firstrow)
    hlapi.task.next_d.set_mask       = 0x00;
    hlapi.task.next_d.clr_mask       = 0x30;
    hlapi.task.push_acc.sel_mask     = 0xff; // store acc lastinn
    hlapi.task.push_acc.set_mask     = 0x20;
    hlapi.task.push_acc.clr_mask     = 0x00;
  }
}

bool evt = false;
bool irq = false;
mutex emtx;
condition_variable cv;

//
// The test
//

class testprog : public arc_program {
public:
  inline testprog() : arc_program(0, NULL) {
    irqflag = false;
  }
  virtual void irq() {
    cout << "REPORT interrupt" << endl;
    irqflag = true;
  }
  inline int main(int, char**) {
    cout << "pixarr[" << ISZ << "], padarr[" << PSZ << "], qdarr[" << QD << "], accin[" << ACSZ1 << "], coefs[" << NUMIXPIX << "]" << ", NUMCOEFS: " << NUMCOEFS << ", NUMCOEFSRND: " << NUMCOEFSRND << endl;
    cout << "RSZ=" << RSZ << ", ICSZ=" << ICSZ << ", ISZ=" << ISZ << endl;

    // initialize memory
    mem_init();
    coef_mem_init();

    // read ID register
    cout << "ID " << rgs.id.tp << ":" << rgs.id.maj << ":" << rgs.id.min << endl;
    run_cycles(1);

    // enable interrupts and events
    rgs.int_enable = 0xffffffff;
    run_cycles(1);

    // set up a new hlapi descriptor
    conv_hlapi_t descr;
    hlapi_init(descr);
    run_cycles(50);

    // copy descriptor into HLAPI registers
    rgs.hlapi = descr;
    run_cycles(1);

    // issue HLAPI
    rgs.issue = 1;
    run_cycles(1);

    // wait until idle
    if (EVENT) {
      cout << "wait event" << endl;
      wait_event_any(1<<EVT_CONV_DONE);
      cout << "REPORT event" << endl;
    } else {
      cout << "wait done" << endl;
      while (rgs.status != 0) {
        run_cycles(10);
      }
      cout << "done" << endl;
    }
    run_cycles(10);

    // Dump result accumulators
    for (int i = 0; i < ACSZ1; i++) {
      cout << "REPORT: " << accin[i] << endl;
    }

    // Dump cycle count
    cout << "STAT CYCLECNT HLAPI " << rgs.hlapi.cycles << endl;
    return 0;
  }
private:
  bool irqflag;
};


//
// The testbench
//
class tb : public hl_npu_ctrl {
public:
  inline tb(testprog* prg) : hl_npu_ctrl("tb", 0, 0, prg), astr(), conv("tb.conv", rgs, dm, vm, am, this, astr) {
  }
  virtual void update(int ev) {
    conv.update(ev);
  }
  // instantiate the activation unit
  Queue<vyixacc_t>   astr;
  hl_npu_conv        conv;
};


//
// Run simulation
//
int sc_main(int argc, char * argv[]) {
  // create testprogram and testbench
  testprog tst;
  tb tbi(&tst);

  // run simulation
  npu_timed_module::sim();

  npu_module_if::report_all(cout);
  return 0;
}
