#include "npu_conv_ca_objects.hpp"
using namespace npu_conv;

#define COLS    4
#define ROWS    5
#define COFFS   179
#ifdef MODESEL1
#define MODE    conv_mode_1x1i32o8
#define INN     2
#define ISTRIDE 2
#define ROFFS   (8*COLS*ISTRIDE-2*COFFS+1)
#define CYC     (COLS*ROWS*INN+5)
#define PRNT    16
#endif
#ifdef MODESEL2
#define MODE     conv_mode_3x1s1i4po8
#define INN     1
#define ISTRIDE 1
#define ROFFS   (COLS*4+1)
#define CYC     (COLS*ROWS*INN+5)
#define PRNT    10
#endif
#ifdef MODESEL3
#define MODE    conv_mode_3x1s2i8o8
#define INN     1
#define ISTRIDE 1
#define ROFFS   (COLS*16+1)
#define CYC     (2*COLS*ROWS*INN+5)
#define PRNT    16
#endif
#ifdef MODESEL4
#define MODE    conv_mode_3x3s1dwi8o8
#define INN     1
#define ISTRIDE 1
#define ROFFS   (COLS*8+1)
#define CYC     (COLS*(1+ROWS)*INN+5)
#define PRNT    20
#endif

#define DIM 571
ixpix_t pixarr[DIM];

void init() {
  // fill pixel array
  for (int e = 0; e < DIM; e++) {
    for (int i = 0; i < ISIZE; i++) {
      pixarr[e][i] = i+ISIZE*e;
    }
  }
}

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

int main() {
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
  fifo<stash_load::stash_load_cmd_t> cmd_q(1000);
  fifo<stash_scalar_t>               scl_q(1000);
  fifo<stash_load_t>                 out_q(1);
  fifo<stash_data_t>                 data_q(1);
  // instances
  stash_load stash_load("tb", hlapi, cmd_q, scl_q, out_q, data_q);
  
  //
  // Program
  //
  // set up HLAPI parameters
  hlapi.conv_mode                = MODE;
  hlapi.load_istride       = ISTRIDE;
  hlapi.load_offsets[0]    = COFFS;
  hlapi.load_offsets[1]    = ROFFS;
  hlapi.load_enable.left   = true;
  hlapi.load_enable.top    = true;
  hlapi.load_enable.right  = true;
  hlapi.load_enable.bottom = true;
  hlapi.load_window.left   = 1;
  hlapi.load_window.top    = 1;
  hlapi.load_window.right  = 8;
  hlapi.load_window.bottom = 8;
  
  // first command
  stash_scalar_t s;
  s.ptr = &pixarr[0];
  s.row = 0;
  s.col = 0;
  s.buf = buf_t<ixpix_t>(s.ptr, (offset_t)DIM);
  scl_q.push_back(s);
  cmd_q.push_back(stash_load::stash_load_init);
  for (int col = 0; col < COLS; col++) {
    bool lastcol = col == COLS-1;
    for (int row = 0; row < ROWS; row++) {
      bool lastrow = row == ROWS-1;
      for (int inn = 0; inn < INN; inn++) {
        bool lastinn = inn == INN-1;
        if (lastrow && lastinn && !lastcol) {
          s.ptr += 33;
          s.row++;
          s.col++;
          scl_q.push_back(s);
          cmd_q.push_back(stash_load::stash_load_start_col);
        } else if (lastinn) {
          cmd_q.push_back(stash_load::stash_load_next_row);
        } else {
          cmd_q.push_back(stash_load::stash_load_next_inn);
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
    if ((!out_q.empty()) && (!data_q.empty())) {
      stash_load_t l = out_q.pop_front();
      stash_data_t d = data_q.pop_front();
      cout << "REPORT hold:" << l.hold << ", rdup:" << l.rdup << ", paden:";
      int k = 0;
      for (int j = 0; j < 5; j++) {
        for (int i = 0; i < 8; i++) {
          if (k < 2*PRNT) {
            cout << (l.paden[i+j*8] ? "1" : "0");
          }
          k++;
        }
        if (k < 2*PRNT) cout << "_";
      }
      cout << ", data:"; pprint(cout, d[0]); cout << " "; pprint(cout, d[1]); cout << endl;
    }
    stash_load.process();
  }

  //
  // Ensure all queues are empty
  //
  assert(cmd_q.empty());
  assert(scl_q.empty());
  assert(out_q.empty());
  assert(data_q.empty());

  npu_module_if::report_all(cout);

  return 0;
}
