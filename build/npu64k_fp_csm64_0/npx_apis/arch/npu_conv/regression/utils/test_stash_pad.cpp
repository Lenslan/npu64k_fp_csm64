#include "npu_conv_ca_objects.hpp"
using namespace npu_conv;

#define DIM 571
ixpix_t pixarr[DIM];

#if (MODE == 0)
// i32o8
#define CHK 16
#elif (MODE == 1) 
// 3x3s1dw
#define CHK 20
#else
// 3x1s2
#define CHK 17
#endif 

void init() {
  // fill pixel array
  for (int e = 0; e < DIM; e++) {
    for (int i = 0; i < ISIZE; i++) {
      pixarr[e][i] = i+ISIZE*e;
    }
  }
}

void update(stash_load_t& l, bool c) {
  switch (l.rdup) {
  case up_simple:
    if (c) l.rdup = up_s1a;
    break;
  case up_s1a:
    l.rdup = up_s1b;
    break;
  case up_s1b:
    l.rdup = c ? up_s1a : up_simple;
    break;
  case up_s2a:
    l.rdup = up_s2b;
    break;
  case up_s2b:
    l.rdup = up_s2a;
    break;
  }
  // rotate pad enable
  bool p = l.paden[39];
  for (int i = 39; i > 0; i--) {
    l.paden[i] = l.paden[i-1];
  }
  l.paden[0] = p;
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
  fifo<stash_pad::stash_pad_cmd_t> cmd_q(1000);
  fifo<stash_load_t>               load_q(1000);
  fifo<stash_data_t>               data_q(1000);
  fifo<v4ixpix_t>                  pad_q(1000);
  fifo<stash_out_t>                out_q(1);
  // instances
  stash_pad stash_pad("tb", hlapi, cmd_q, load_q, data_q, pad_q, out_q);
  
  //
  // Program
  //
  // set up HLAPI parameters
#if (MODE == 0)
  hlapi.conv_mode        = conv_mode_1x1i32o8;
#elif (MODE == 1) 
  hlapi.conv_mode        = conv_mode_3x3s1dwi8o8;
#else
  hlapi.conv_mode        = conv_mode_3x1s2i8o8;
#endif 
  // first command
  stash_data_t d;
  stash_load_t l;
  v4ixpix_t    p;
  bool         c3s1;
  pv_t vptr;
  vptr.p2pv(&pixarr[0], (offset_t)1);
  cmd_q.push_back(stash_pad::stash_pad_init);
  d[0] = *vptr; vptr += (offset_t)1;
  d[1] = *vptr; vptr += (offset_t)1;
  data_q.push_back(d);
  switch (MODE) {
  case 0:
    l.rdup  = up_simple;
    l.hold  = false;
    c3s1    = false;
    cout << "simple" << endl;
    break;
  case 1:
    l.rdup  = up_s1a;
    l.hold  = false;
    c3s1    = true;
    cout << "c3s1" << endl;
    break;
  case 2:
    l.rdup  = up_s2a;
    l.hold  = false;
    c3s1    = false;
    cout << "c3s2" << endl;
    break;
  }
  l.paden[0] = true;
  for (int i = 1; i < 40; i++) {
    l.paden[i] = false;
  }
  load_q.push_back(l);
  for (int v = 0; v < 4; v++) {
    for (int i = 0; i < ISIZE; i++) {
      p[v][i] = v*ISIZE+i;
    }
  }
  pad_q.push_back(p);
  if (MODE == 2) {
    d[0] = *vptr; vptr += (offset_t)1;
    d[1] = *vptr; vptr += (offset_t)1;
    data_q.push_back(d);
    update(l, false);
    load_q.push_back(l);
  }
  for (int i = 0; i < 5; i++) {
    for (int j = 0; j < 5; j++) {
      // continue
      cmd_q.push_back(stash_pad::stash_pad_next);
      if (MODE == 2) {
        d[0] = *vptr; vptr += (offset_t)1;
        d[1] = *vptr; vptr += (offset_t)1;
        data_q.push_back(d);
        update(l, false);
        load_q.push_back(l);
      }
      d[0] = *vptr; vptr += (offset_t)1;
      d[1] = *vptr; vptr += (offset_t)1;
      data_q.push_back(d);
      update(l, false);
      load_q.push_back(l);
    }
    // next pad
    cmd_q.push_back(stash_pad::stash_pad_next_ni);
    if (MODE == 2) {
      d[0] = *vptr; vptr += (offset_t)1;
      d[1] = *vptr; vptr += (offset_t)1;
      data_q.push_back(d);
      update(l, false);
      load_q.push_back(l);
    }
    d[0] = *vptr; vptr += (offset_t)1;
    d[1] = *vptr; vptr += (offset_t)1;
    data_q.push_back(d);
    update(l, c3s1);
    load_q.push_back(l);
    pad_q.push_back(p);
  }

  //
  // Simulation
  //
  for (int i = 0; i < 100; i++) {
    // down-stream to upstream ordering to avoid races
    cout << "CYCLE: " << i << endl;
    if ((!out_q.empty())) {
      stash_out_t d = out_q.pop_front();
      cout << "REPORT shift2:" << d.shft2 << ", hold:" << d.hold << " data: "; 
      for (int v = 0; v < CHK; v++) {
        cout << d.data[v];
      }
      cout << endl;
    }
    stash_pad.process();
  }

  //
  // Ensure all queues are empty
  //
  assert(cmd_q.empty());
  assert(load_q.empty());
  assert(data_q.empty());
  assert(pad_q.empty());
  assert(out_q.empty());

  npu_module_if::report_all(cout);

  return 0;
}
