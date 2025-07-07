#include "npu_conv_ca_objects.hpp"
using namespace npu_conv;

// derived parameters
#if (MODESEL == MODESEL1X1I32O8)
#define MODE    conv_mode_1x1i32o8
#define ISTRIDE ISTRIDE1x1
#define INN     2
#define IROWS   ROWS
#define OLAP    0
#define COLSTR  (8*ISTRIDE)
#define IX      32
#define CC      1
#define DW      false
#define CHK     16
#elif (MODESEL == MODESEL3X1S1I4PO8)
#define MODE    conv_mode_3x1s1i4po8
#define ISTRIDE 1
#define INN     1
#define IROWS   ROWS
#define OLAP    2
#define COLSTR  4
#define IX      4
#define CC      1
#define DW      false
#define CHK     10
#elif (MODESEL == MODESEL3X1S2I8O8)
#define MODE    conv_mode_3x1s2i8o8
#define ISTRIDE 1
#define INN     1
#define IROWS   ROWS
#define OLAP    1
#define COLSTR  16
#define IX      8
#define CC      2
#define DW      false
#define CHK     17
#elif (MODESEL == MODESEL3X3S1DWI8O8)
#define MODE    conv_mode_3x3s1dwi8o8
#define ISTRIDE 1
#define INN     1
#define IROWS   (2+ROWS)
#define OLAP    2
#define COLSTR  8
#define IX      8
#define CC      1
#define DW      true
#define CHK     20
#else
#error
#endif

#define NOI   (DW?1:NI)
#define NOO   (DW?NI:NO)
// buffer size and offsets
#define DIVRND_UP8(x) ((x+7)/8)
#define RSZ   (COLSTR*COLS+OLAP)
#define ICSZ  (RSZ*IROWS)
#define OCSZ  (8*ROWS*COLS)
#define ISZ   (ICSZ*INN*NI)
#define OSZ   (NOO*OCSZ)
#define PSZ   DIVRND_UP8(NI*IX)
#define ROFFS ((1-INN)*2*ICSZ+RSZ)

// simulation cycles
#define CYC   (CC*INN*IROWS*COLS*QD*NI*NOI+10)

//
// pretty print only element 0 and 4 of each ixpix_t in the vector
//
void pprint(ostream& os, const vyixpix_t& d) {
  os << "ppvyixpix_t: {";
  for (int v = 0; v < VSIZE; v++) {
    if (v != 0) os << ",";
    os << "{"; pix_stream(os, d[v][0]); os << ","; pix_stream(os, d[v][ISIZE/2]); os << "}";
  }
}

void pprint(ostream& os, const vyixacc_t& d) {
  os << "ppvyixacc_t: {";
  for (int v = 0; v < VSIZE; v++) {
    if (v != 0) os << ",";
    os << "{"; acc_stream(os, d[v][0]); os << ","; acc_stream(os, d[v][ISIZE/2]); os << "}";
  }
}

//
// Input data
//
ixpix_t    pixarr[ISZ];
ixpix_t    padarr[PSZ];
quadrant_t qdarr[QD];

//
// Initialize input memories
//
void init() {
  // fill input pixel array
  for (int e = 0; e < ISZ; e++) {
    for (int i = 0; i < ISIZE; i++) {
      pixarr[e][i] = i+ISIZE*e;
    }
  }
  // fill quadrant array
  qdarr[QD-1].poffs = 0;
  qdarr[QD-1].roffs = 0;
  qdarr[QD-1].coffs = (1-COLS)*COLSTR;
  for (int e = 0; e < QD-1; e++) {
    qdarr[e].poffs = e * (e & 1 ? 1 : -1);
    qdarr[e].roffs = 2*e+1;
    qdarr[e].coffs = 3*e+1 + (1-COLS)*COLSTR; // subtract column
    qdarr[QD-1].poffs -= qdarr[e].poffs;
    qdarr[QD-1].roffs -= qdarr[e].roffs;
    qdarr[QD-1].coffs -= 3*e+1;
  }
  // fill input padding array
  for (int e = 0; e < PSZ; e++) {
    for (int i = 0; i < ISIZE; i++) {
      padarr[e][i] = 0xfff - (i+ISIZE*e);
    }
  }
}

int sc_main(int argc, char * argv[]) {
  //
  // initialize input arrays
  //
  init();

  //
  // Instantiate hardware
  //
  // HLAPI parameter registers
  conv_hlapi hlapi;
  // channels
  fifo<stash::stash_cmd_t> cmd_q(1000);
  fifo<stash_out_t>        out_q(1);
  // instances
  stash stash("tb", hlapi, cmd_q, out_q);
  
  //
  // Program
  //
  // set up HLAPI parameters
  hlapi.conv_mode                = MODE;
  hlapi.stash.quad_load.ptr      = &qdarr[0];
  hlapi.scalar_ptr         = &pixarr[1];
  hlapi.scalar_buf         = {&pixarr[0], (offset_t)ISZ};
  hlapi.scalar_row         = 0;
  hlapi.scalar_col         = 0;
  hlapi.scalar_istride     = ISTRIDE;
  hlapi.scalar_coloffset   = COLSTR;
  hlapi.load_istride       = ISTRIDE;
  hlapi.load_offsets[0]    = 2*ICSZ;
  hlapi.load_offsets[1]    = ROFFS;
  hlapi.load_enable.left   = true;
  hlapi.load_enable.top    = true;
  hlapi.load_enable.right  = true;
  hlapi.load_enable.bottom = true;
  // pad one column left and right, one row top and bottom
  hlapi.load_window.left   = 1;
  hlapi.load_window.top    = 1;
  hlapi.load_window.right  = RSZ-2;
  hlapi.load_window.bottom = IROWS-2;
  hlapi.pad_ptr       = &padarr[0];
  
  // first command
  cmd_q.push_back(stash::stash_init);
  for (int no = 0; no < NOI; no++) {
    bool lastno = no == NOI-1;
    for (int ni = 0; ni < NI; ni++) {
      bool lastni = ni == NI-1;
      for (int qd = 0; qd < QD; qd++) {
        bool lastqd = qd == QD-1;
        for (int col = 0; col < COLS; col++) {
          bool lastcol = col == COLS-1;
          for (int row = 0; row < ROWS; row++) {
            bool lastrow = row == ROWS-1;
            for (int inn = 0; inn < INN; inn++) {
              bool lastinn = inn == INN-1;
              if (lastinn) {
                if (lastrow) {
                  if (lastcol) {
                    if (lastqd) {
                      if (lastni) {
                        if (lastno) {
                          // done
                        } else{
                          cmd_q.push_back(DW ? stash::stash_next_ni : stash::stash_next_no);
                        }
                      } else {
                        cmd_q.push_back(stash::stash_next_ni);
                      }
                    } else {
                      cmd_q.push_back(stash::stash_next_qd);
                    }
                  } else {
                    cmd_q.push_back(stash::stash_next_col);
                  }
                } else {
                  cmd_q.push_back(stash::stash_next_row);
                }
              } else {
                cmd_q.push_back(stash::stash_next_inn);
              }
            }
          }
        }
      }
    }
  }
  
  //
  // Simulation
  //
  cout << "mode: " << MODE << endl;
  for (int i = 0; i < CYC; i++) {
    // down-stream to upstream ordering to avoid races
    cout << "CYCLE: " << i << endl;
    if (!out_q.empty()) {
      stash_out_t d = out_q.pop_front();
#ifdef FULLRES
      cout << "REPORT shft2: " << d.shft2 << ", hold:" << d.hold << ", data:";
      for (int v = 0; v < CHK; v++) {
        cout << d.data[v];
      }
      cout << endl;
#else
      cout << "REPORT shft2: " << d.shft2 << ", hold:" << d.hold;
      cout << ", data:"; pprint(cout, d.data); cout << endl;
#endif
    }
    stash.process();
  }
  
  //
  // Ensure all queues are empty
  //
  stash.pprint();
  cout << CYC << " " << cmd_q.size() <<" " << out_q.size() << endl;
  cout << flush;
  assert(cmd_q.empty());
  assert(out_q.empty());

  npu_module_if::report_all(cout);

  return 0;
}
