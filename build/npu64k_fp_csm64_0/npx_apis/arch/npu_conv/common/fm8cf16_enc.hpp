/*************************************************************************/
/**                                                                     **/
/** Copyright (C) 2021-2023 Synopsys, Inc.                              **/
/** All Rights Reserved.                                                **/
/**                                                                     **/
/** This Synopsys software and all associated documentation are         **/
/** proprietary to Synopsys, Inc. and may only be used pursuant to the  **/
/** terms and conditions of a written license agreement with Synopsys,  **/
/** Inc. All other use, reproduction, modification, or distribution of  **/
/** this Synopsys software or the associated documentation is strictly  **/
/** prohibited.                                                         **/
/**                                                                     **/
/*************************************************************************/

//
// File defining coefficient encoding functions for 16b coefficients and 8b feature-maps
// fm8cf16 does not support:
// - compression
// - 4b
// - sparse
// - coefficient zero-points
// - inn&onn
//


// NINO(3x3dws1), 8b feature-map, 16b coefficient, non-sparse
static void NINO(fm8cf16_3x3dws1)(const tensor_t<coef_t,7,xbuffer_t>&     icf,       // input coefficients [Grp][1][Fd][Fh][Fw][1][Coef h/l]
                                  xbuffer_t<coef_t>&                      tbuf,      // temporary xbuf
                                  // outputs, buffers preallocated by caller
                                  xbuffer_t<ixpix_t>&                     obuf,      // output encoded coefficient tensor
                                  size_t&                                 olen       // size of used coefficient buffer in ixpix_t
                                  ) {
  // std::cout<<__FILE__<<" "<<__LINE__<<std::endl;
  assert(icf.get_dim(1) == 1 && icf.get_dim(5) == 1 && icf.get_dim(0) == 2);
  // get shape size
  shape<5> shp0;
  shp0[0] = icf.get_dim(0);                                   // [lsb/msb]
  shp0[1] = ROUND_UP(icf.get_dim(2), 3);                      // round to filter size w3
  shp0[2] = ROUND_UP(icf.get_dim(3), 3);                      // round to filter size h3
  shp0[3] = icf.get_dim(4);
  shp0[4] = ROUND_UP(icf.get_dim(6), ISIZE);                  // round up to ISIZE
  xbuffer_t<coef_t> cbuf = tbuf.split((size_t)get_shape_size(shp0));
  tensor_t<coef_t,5,xbuffer_t> tns0(cbuf, shp0);
  // initialize to 0
  const_tensor_iterator_t<coef_t,7,xbuffer_t> iit(icf);
  tensor_iterator_t<coef_t,5,xbuffer_t>       cit0(tns0);
  for (int g = 0; g < shp0[4]; g++) {
    for (int fd = 0; fd < shp0[3]; fd++) {
      for (int fh = 0; fh < shp0[2]; fh++) {
        for (int fw = 0; fw < shp0[1]; fw++) {
          if (fw >= icf.get_dim(2) || fh >= icf.get_dim(3) || g >= icf.get_dim(6)) {
            // pad with 0 coefficients
            cit0.write((coef_t)0);
            cit0.next();
            cit0.write((coef_t)0);
            cit0.next();
          } else {
            cit0.write(iit.read());
            iit.next();
            cit0.next();
            cit0.write(iit.read());
            iit.next();
            cit0.next();
          }
        }
      }
    }
  }
  //
  // target shape is [grp/16][fd][fh/3][fw/3][mlsb][g16][fw3][fh3]
  //
  // [grp][fd][fh][fw][coef h/l] --> [grp/16][g16][fd][fh/3][fh3][fw/3][fw3][lmsb]
  tensor_t<coef_t,6,xbuffer_t>  tns1(tns0.split(1, shp0[1]/3));
  tensor_t<coef_t,7,xbuffer_t>  tns2(tns1.split(3, shp0[2]/3));
  tensor_t<coef_t,8,xbuffer_t>  tns3(tns2.split(6, shp0[4]/16));
  // transpose [grp/16][g16][fd][fh/3][fh3][fw/3][fw3][mlsb] -> [grp/16][fd][fh/3][fw/3][mlsb][g16][fw3][fh3]
  tensor_t<coef_t,8,xbuffer_t>  tns4(tns3.transpose({3,1,6,0,2,4,5,7}));
  // reverse order of fh3
  tensor_t<coef_t,8,xbuffer_t>  tnsr(tns4.reverse(0));

  //
  // encode
  //
  array<list<coef_t>,NUM_COEF_QUEUE> vlist;
  int state = 0;
  const_tensor_iterator_t<coef_t,8,xbuffer_t>   coit(tnsr);
  // coefficients
  for (int i = 0; i < (int)tnsr.get_tens_size()/18; i++) {
    // read 18 coefficients and avail bits o2*f3xf3
    array<coef_t,18>  c_temp;
    array<coef_t,18>  c;
    for (int j = 0; j < 18; j++) {
      c_temp[j] = coit.read();
      coit.next();
    }
    // shuffle coefficients, moving spare to back
    c[0]  = c_temp[0 ];
    c[1]  = c_temp[1 ];
    c[2]  = c_temp[2 ];
    c[3]  = c_temp[6 ];
    c[4]  = c_temp[7 ];
    c[5]  = c_temp[3 ];
    c[6]  = c_temp[4 ];
    c[7]  = c_temp[5 ];
    c[8]  = c_temp[9 ];
    c[9]  = c_temp[10];
    c[10] = c_temp[11];
    c[11] = c_temp[15];
    c[12] = c_temp[16];
    c[13] = c_temp[12];
    c[14] = c_temp[13];
    c[15] = c_temp[14];
    c[16] = c_temp[8 ];
    c[17] = c_temp[17];
    for (int k = 0; k < 18; k++) {
      vlist[state].push_back(c[k]);
    }
    state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
  }
  queue_encode(vlist, obuf, olen, coef_mode_uncompressed);
}

// NINO(3x3dws1dl2), 8b feature-map, 16b coefficient, non-sparse
static void NINO(fm8cf16_3x3dws1dl2)(const tensor_t<coef_t,7,xbuffer_t>&    icf,       // input coefficients [Grp][1][Fd][Fh][Fw][1][Coef h/l], 16b only
                                     xbuffer_t<coef_t>&                     tbuf,      // temporary xbuf
                                     // outputs, buffers preallocated by caller
                                     xbuffer_t<ixpix_t>&                    obuf,      // output encoded coefficient tensor
                                     size_t&                                olen       // size of used coefficient buffer in ixpix_t
                                     ) {
  // std::cout<<__FILE__<<" "<<__LINE__<<std::endl;
  assert(icf.get_dim(0) == 2 && icf.get_dim(1) == 1 && icf.get_dim(5) == 1);
  // get shape size
  shape<5> shp0;
  shp0[0] = icf.get_dim(0);
  shp0[1] = ROUND_UP(icf.get_dim(2), 3);                       // round to filter size w3
  shp0[2] = ROUND_UP(icf.get_dim(3), 3);                       // round to filter size h3
  shp0[3] = icf.get_dim(4);
  shp0[4] = ROUND_UP(icf.get_dim(6), ISIZE);                   // round up to ISIZE
  // increase size of tensor
  xbuffer_t<coef_t> cbuf = tbuf.split((size_t)get_shape_size(shp0));
  tensor_t<coef_t,5,xbuffer_t> tns0(cbuf, shp0);
  // initialize to 0
  const_tensor_iterator_t<coef_t,7,xbuffer_t> iit(icf);
  tensor_iterator_t<coef_t,5,xbuffer_t>       cit0(tns0);
  for (int g = 0; g < tns0.get_dim(4); g++) {
    for (int fd = 0; fd < tns0.get_dim(3); fd++) {
      for (int fh = 0; fh < tns0.get_dim(2); fh++) {
        for (int fw = 0; fw < tns0.get_dim(1); fw++) {
          if (fw >= icf.get_dim(2) || fh >= icf.get_dim(3) || g >= icf.get_dim(6)) {
            // pad with 0 coefficients
            cit0.write((coef_t)0);
            cit0.next();
            cit0.write((coef_t)0);
            cit0.next();
          } else {
            cit0.write(iit.read());
            iit.next();
            cit0.next();
            cit0.write(iit.read());
            iit.next();
            cit0.next();
          }
        }
      }
    }
  }
  //
  // target shape is [grp/16][fd][fh/3][fw/3][mlsb][g16][fw3][fh3]
  //
  // [grp][fd][fh][fw][coef h/l] --> [grp/16][g16][fd][fh/3][fh3][fw/3][fw3][mlsb]
  tensor_t<coef_t,6,xbuffer_t>  tns1(tns0.split(1, shp0[1]/3));
  tensor_t<coef_t,7,xbuffer_t>  tns2(tns1.split(3, shp0[2]/3));
  tensor_t<coef_t,8,xbuffer_t>  tns3(tns2.split(6, shp0[4]/16));
  // transpose [grp/16][g16][fd][fh/3][fh3][fw/3][fw3][mlsb] --> [grp/16][fd][fh/3][fw/3][mlsb][g16][fw3][fh3]
  tensor_t<coef_t,8,xbuffer_t>  tns4(tns3.transpose({3,1,6,0,2,4,5,7}));
  // reverse order of fh3
  tensor_t<coef_t,8,xbuffer_t>  tnsr(tns4.reverse(0));

  //
  // encode
  //
  array<list<coef_t>,NUM_COEF_QUEUE> vlist;
  int state = 0;
  const_tensor_iterator_t<coef_t,8,xbuffer_t>   coit(tnsr);
  // coefficients
  for (int i = 0; i < (int)tnsr.get_tens_size()/18; i++) {
    // read 18 coefficients and avail bits o2*f3xf3
    array<coef_t,18>  c_temp;
    array<coef_t,18>  c;
    for (int j = 0; j < 18; j++) {
      c_temp[j] = coit.read();
      coit.next();
    }

    // reorg coefs order
    c[0]  = c_temp[0 ];
    c[1]  = c_temp[8 ];
    c[2]  = c_temp[1 ];
    c[3]  = c_temp[6 ];
    c[4]  = c_temp[2 ];
    c[5]  = c_temp[3 ];
    c[6]  = c_temp[5 ];
    c[7]  = c_temp[4 ];
    c[8]  = c_temp[9 ];
    c[9]  = c_temp[17];
    c[10] = c_temp[10];
    c[11] = c_temp[15];
    c[12] = c_temp[11];
    c[13] = c_temp[12];
    c[14] = c_temp[14];
    c[15] = c_temp[13];
    c[16] = c_temp[7 ];
    c[17] = c_temp[16];
    for (int k = 0; k < 18; k++) {
      vlist[state].push_back(c[k]);
    }
    state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
  }
  queue_encode(vlist, obuf, olen, coef_mode_uncompressed);
}

// NINO(2x3dws2), 8b feature-map, 16b coefficient, non-sparse
static void NINO(fm8cf16_2x3dws2)(const tensor_t<coef_t,7,xbuffer_t>&    icf,       // input coefficients [Grp][1][Fd][Fh][Fw][1][Coef h/l], 16b only
                                  xbuffer_t<coef_t>&                     tbuf,      // temporary xbuf
                                  // attributes
                                  // outputs, buffers preallocated by caller
                                  xbuffer_t<ixpix_t>&                    obuf,      // output encoded coefficient tensor
                                  size_t&                                olen       // size of used coefficient buffer in ixpix_t
                                  ) {
  // std::cout<<__FILE__<<" "<<__LINE__<<std::endl;
  assert(icf.get_dim(0) == 2 && icf.get_dim(1) == 1 && icf.get_dim(5) == 1);
  // get shape size
  shape<5> shp0;
  shp0[0] = icf.get_dim(0);
  shp0[1] = ROUND_UP(icf.get_dim(2), 2);               // round to filter size w2
  shp0[2] = ROUND_UP(icf.get_dim(3), 3);               // round to filter size h3
  shp0[3] = icf.get_dim(4);
  shp0[4] = ROUND_UP(icf.get_dim(6), ISIZE);           // round up to ISIZE
  // increase size of tensor
  xbuffer_t<coef_t> cbuf = tbuf.split((size_t)get_shape_size(shp0));
  tensor_t<coef_t,5,xbuffer_t> tns0(cbuf, shp0);
  // initialize to 0
  const_tensor_iterator_t<coef_t,7,xbuffer_t> iit(icf);
  tensor_iterator_t<coef_t,5,xbuffer_t>       cit0(tns0);
  for (int g = 0; g < tns0.get_dim(4); g++) {
    for (int fd = 0; fd < tns0.get_dim(3); fd++) {
      for (int fh = 0; fh < tns0.get_dim(2); fh++) {
        for (int fw = 0; fw < tns0.get_dim(1); fw++) {
          if (fw >= icf.get_dim(2) || fh >= icf.get_dim(3) || g >= icf.get_dim(6)) {
            // pad with 0 coefficients
            cit0.write((coef_t)0);
            cit0.next();
            cit0.write((coef_t)0);
            cit0.next();
          } else {
            cit0.write(iit.read());
            iit.next();
            cit0.next();
            cit0.write(iit.read());
            iit.next();
            cit0.next();
          }
        }
      }
    }
  }
  //
  // target shape is [grp/16][fd][fh/3][fw/2][lmsb][g16][fw3][fh3]
  //
  // [grp][fd][fh][fw][coef h/l] --> [grp/16][g16][fd][fh/3][fh3][fw/2][fw2][mlsb]
  tensor_t<coef_t,6,xbuffer_t>  tns1(tns0.split(1, shp0[1]/2));
  tensor_t<coef_t,7,xbuffer_t>  tns2(tns1.split(3, shp0[2]/3));
  tensor_t<coef_t,8,xbuffer_t>  tns3(tns2.split(6, shp0[4]/16));
  // transpose [grp/16][g16][fd][fh/3][fh3][fw/2][fw2][mlsb] --> [grp/16][fd][fh/3][fw/2][lmsb][g16][fw3][fh3]
  tensor_t<coef_t,8,xbuffer_t>  tns4(tns3.transpose({3,1,6,0,2,4,5,7}));
  // reverse order of fh3
  tensor_t<coef_t,8,xbuffer_t>  tnsr(tns4.reverse(0));

  //
  // encode
  //
  array<list<coef_t>,NUM_COEF_QUEUE> vlist;
  int state = 0;
  const_tensor_iterator_t<coef_t,8,xbuffer_t>   coit(tnsr);
  // coefficients
  for (int i = 0; i < (int)tnsr.get_tens_size()/12; i++) {
    // due to coefs only has 6 each set, padding zeros each group to meet the requirements
    array<coef_t,12>  c_temp;
    array<coef_t,16>  c;
    for (int j = 0; j < 12; j++) {
      c_temp[j] = coit.read();
      coit.next();
    }

    // reorg coefs order
    c[0]  = c_temp[0 ];
    c[1]  = c_temp[1 ];
    c[2]  = c_temp[2 ];
    c[3]  = 0;
    c[4]  = 0;
    c[5]  = c_temp[3 ];
    c[6]  = c_temp[4 ];
    c[7]  = c_temp[5 ];
    c[8]  = c_temp[6 ];
    c[9]  = c_temp[7 ];
    c[10] = c_temp[8 ];
    c[11] = 0;
    c[12] = 0;
    c[13] = c_temp[9];
    c[14] = c_temp[10];
    c[15] = c_temp[11];
    for (int k = 0; k < 16; k++) {
      vlist[state].push_back(c[k]);
    }
    state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
  }
  queue_encode(vlist, obuf, olen, coef_mode_uncompressed);
}


// NINO(8x1dws1), 8b feature-map, 16b coefficient, non-sparse
static void NINO(fm8cf16_8x1dws1)(const tensor_t<coef_t,7,xbuffer_t>&    icf,       // input coefficients [Grp][1][Fd][Fh][Fw][1][Coef h/l], 16b only
                                  xbuffer_t<coef_t>&                     tbuf,      // temporary xbuf
                                  // outputs, buffers preallocated by caller
                                  xbuffer_t<ixpix_t>&                    obuf,      // output encoded coefficient tensor
                                  size_t&                                olen       // size of used coefficient buffer in ixpix_t
                                  ) {
  // std::cout<<__FILE__<<" "<<__LINE__<<std::endl;
  assert(icf.get_dim(0) == 2 && icf.get_dim(1) == 1 && icf.get_dim(5) == 1);
  // get shape size
  shape<5> shp0;
  shp0[0] = icf.get_dim(0);
  shp0[1] = ROUND_UP(icf.get_dim(2), 8);               // round to filter size w8
  shp0[2] = icf.get_dim(3);
  shp0[3] = icf.get_dim(4);
  shp0[4] = ROUND_UP(icf.get_dim(6), ISIZE);           // round up to ISIZE
  // increase size of tensor
  xbuffer_t<coef_t> cbuf = tbuf.split((size_t)get_shape_size(shp0));
  tensor_t<coef_t,5,xbuffer_t> tns0(cbuf, shp0);
  // initialize to 0
  const_tensor_iterator_t<coef_t,7,xbuffer_t> iit(icf);
  tensor_iterator_t<coef_t,5,xbuffer_t>       cit0(tns0);
  for (int g = 0; g < tns0.get_dim(4); g++) {
    for (int fd = 0; fd < tns0.get_dim(3); fd++) {
      for (int fh = 0; fh < tns0.get_dim(2); fh++) {
        for (int fw = 0; fw < tns0.get_dim(1); fw++) {
          if (fw >= icf.get_dim(2) || g >= icf.get_dim(6)) {
            // pad with 0 coefficients
            cit0.write((coef_t)0);
            cit0.next();
            cit0.write((coef_t)0);
            cit0.next();
          } else {
            cit0.write(iit.read());
            iit.next();
            cit0.next();
            cit0.write(iit.read());
            iit.next();
            cit0.next();
          }
        }
      }
    }
  }
  //
  // target shape is [grp/16][fd][fh][fw/8][mlsb][g16][fw8]
  //
  // [grp][fd][fh][fw][coef h/l] --> [grp/16][g16][fd][fh][fw/8][fw8][mlsb]
  tensor_t<coef_t,6,xbuffer_t>  tns1(tns0.split(1, shp0[1]/8));
  tensor_t<coef_t,7,xbuffer_t>  tns2(tns1.split(5, shp0[4]/16));
  // [grp][g16][fd][fh][fw/8][fw8][mlsb] --> [grp/16][fd][fh][fw/8][mlsb][g16][fw8]
  tensor_t<coef_t,7,xbuffer_t>  tnsr(tns2.transpose({1,5,0,2,3,4,6}));

  //
  // encode
  //
  array<list<coef_t>,NUM_COEF_QUEUE> vlist;
  int state = 0;
  const_tensor_iterator_t<coef_t,7,xbuffer_t>   coit(tnsr);
  for (int i = 0; i < (int)tnsr.get_tens_size()/16; i++) {
    for (int k = 0; k < ISIZE; k++) {
      vlist[state].push_back(coit.read());
      coit.next();
    }
    state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
  }
  queue_encode(vlist, obuf, olen, coef_mode_uncompressed);
}

// DINO(1x1ns), 8b feature-map, 16b coefficient, non-sparse
static void DINO(fm8cf16ns_1x1)(const tensor_t<coef_t,7,xbuffer_t>&     icf,       // input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp][Coef h/l], 16b only
                                xbuffer_t<coef_t>&                     tbuf,      // temporary xbuf
                                // outputs, buffers preallocated by caller
                                xbuffer_t<ixpix_t>&                    obuf,      // output encoded coefficient tensor
                                size_t&                                olen       // size of used coefficient buffer in ixpix_t
                                ) {
  // std::cout<<__FILE__<<" "<<__LINE__<<std::endl;
  assert(icf.get_dim(0) == 2);
  // get shape size
  shape<7> shp0;
  shp0[0] = icf.get_dim(0);
  shp0[1] = ROUND_UP(icf.get_dim(1), 2*ISIZE);   // round up to multiple of ISIZE
  shp0[2] = icf.get_dim(2);
  shp0[3] = icf.get_dim(3);
  shp0[4] = icf.get_dim(4);
  shp0[5] = ROUND_UP(icf.get_dim(5), ISIZE);     // round up to multiple of ISIZE
  shp0[6] = icf.get_dim(6);
  // increase size of tensor
  xbuffer_t<coef_t> cbuf = tbuf.split((size_t)get_shape_size(shp0));
  tensor_t<coef_t,7,xbuffer_t> tns0(cbuf, shp0);
  // initialize to 0
  const_tensor_iterator_t<coef_t,7,xbuffer_t> iit(icf);
  tensor_iterator_t<coef_t,7,xbuffer_t>       cit0(tns0);
  for (int g = 0; g < tns0.get_dim(6); g++) {
    for (int no = 0; no < tns0.get_dim(5); no++) {
      for (int qd = 0; qd < tns0.get_dim(2)*tns0.get_dim(3)*tns0.get_dim(4); qd++) {
        for (int ni = 0; ni < tns0.get_dim(1); ni++) {
          if (ni >= icf.get_dim(1) || no >= icf.get_dim(5)) {
            // pad with 0 coefficient
            cit0.write((coef_t)0);
            cit0.next();
            cit0.write((coef_t)0);
            cit0.next();
          } else {
            cit0.write(iit.read());
            iit.next();
            cit0.next();
            cit0.write(iit.read());
            iit.next();
            cit0.next();
          }
        }
      }
    }
  }
  //
  // target shape is [grp][no/16][ni/16][fd][fh][fw][mlsb][iodd][i2][o16][i8]
  //
  // [grp][no][fd][fh][fw][ni][mlsb] --> [grp][no/16][o16][fd][fh][fw][ni/32][i2][i8][iodd][mlsb]
  tensor_t<coef_t,8,xbuffer_t>  tns1(tns0.split(1, shp0[1]/32));
  tensor_t<coef_t,9,xbuffer_t>  tns2(tns1.split(1, 2));
  tensor_t<coef_t,10,xbuffer_t> tns3(tns2.split(1, 8));
  tensor_t<coef_t,11,xbuffer_t> tns4(tns3.split(8, shp0[5]/16));
  // transpose [grp][no/16][o16][fd][fh][fw][ni/16][i2][i8][iodd][mlsb] --> [grp][no/16][ni/16][fd][fh][fw][mlsb][iodd][i2][o16][i8]
  tensor_t<coef_t,11,xbuffer_t> tnsr(tns4.transpose({2,8,3,1,0,5,6,7,4,9,10}));
  //
  //
  // encode
  //
  array<list<coef_t>,NUM_COEF_QUEUE> vlist;
  int state = 0;
  const_tensor_iterator_t<coef_t,11,xbuffer_t>  coit(tnsr);
  // coefficients
  for (int i = 0; i < (int)tnsr.get_tens_size()/16; i++) {
    for (int k = 0; k < ISIZE; k++) {
      vlist[state].push_back(coit.read());
      coit.next();
    }
    state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
  }
  queue_encode(vlist, obuf, olen, coef_mode_uncompressed);
}


// DINO(1x1ns), 8b feature-map, 16b coefficient, non-sparse, grouped
static void DINO(gfm8cf16ns_1x1)(const tensor_t<coef_t,7,xbuffer_t>&    icf,       // input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp][Coef h/l], 16b only
                                 xbuffer_t<coef_t>&                     tbuf,      // temporary xbuf
                                 // outputs, buffers preallocated by caller
                                 xbuffer_t<ixpix_t>&                    obuf,      // output encoded coefficient tensor
                                 size_t&                                olen       // size of used coefficient buffer in ixpix_t
                                 ) {
  // std::cout<<__FILE__<<" "<<__LINE__<<std::endl;
  // transcode coefficients to [1][Cout*Grp][Fd][Fh][Fw][Cin*Grp][mlsb]
  int grp = icf.get_dim(6);
  shape<7> shp0;
  shp0[0] = 2;
  shp0[1] = icf.get_dim(1)*grp;  // input channels
  shp0[2] = icf.get_dim(2);
  shp0[3] = icf.get_dim(3);
  shp0[4] = icf.get_dim(4);
  shp0[5] = icf.get_dim(5)*grp;  // output channels
  shp0[6] = 1;
  xbuffer_t<coef_t> cbuf = tbuf.split((size_t)get_shape_size(shp0));
  tensor_t<coef_t,7,xbuffer_t> otns(cbuf, shp0);
  const_tensor_iterator_t<coef_t,7,xbuffer_t>  iit(icf);
  tensor_iterator_t<coef_t,7,xbuffer_t>        oit(otns);
  // copy tensor
  coef_t z(0);
  for (int og = 0; og < grp; og++) {
    for (int oc = 0; oc < icf.get_dim(5); oc++) {
      for (int fd = 0; fd < icf.get_dim(4); fd++) {
        for (int fh = 0; fh < icf.get_dim(3); fh++) {
          for (int fw = 0; fw < icf.get_dim(2); fw++) {
            for (int ig = 0; ig < grp; ig++) {
              for (int ic = 0; ic < icf.get_dim(1); ic++) {
                if (ig == og) {
                  oit.write(iit.read());
                  iit.next(); oit.next();
                  oit.write(iit.read());
                  iit.next(); oit.next();
                } else {
                  oit.write(z);
                  oit.next();
                  oit.write(z);
                  oit.next();
                }
              }
            }
          }
        }
      }
    }
  }
  // encode as 1x1
  DINO(fm8cf16ns_1x1)(otns, tbuf, obuf, olen);
}


// NINO(2x1ns), 8b feature-map, 16b coefficient, non-sparse
static void NINO(fm8cf16ns_2x1)(const tensor_t<coef_t,7,xbuffer_t>&     icf,       // input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp][Coef h/l], 16b only
                                xbuffer_t<coef_t>&                      tbuf,      // temporary xbuf
                                // outputs, buffers preallocated by caller
                                xbuffer_t<ixpix_t>&                     obuf,      // output encoded coefficient tensor
                                size_t&                                 olen       // size of used coefficient buffer in ixpix_t
                                ) {
  // std::cout<<__FILE__<<" "<<__LINE__<<std::endl;
  assert(icf.get_dim(0) == 2);
  // get shape size
  shape<7> shp0;
  shp0[0]  = icf.get_dim(0);
  shp0[1]  = ROUND_UP(icf.get_dim(1), ISIZE);     // round up to multiple of ISIZE
  shp0[2]  = ROUND_UP(icf.get_dim(2), 2);         // round width to multiple of 2
  shp0[3]  = icf.get_dim(3);
  shp0[4]  = icf.get_dim(4);
  shp0[5]  = ROUND_UP(icf.get_dim(5), ISIZE);     // round up to multiple of ISIZE
  shp0[6]  = icf.get_dim(6);
  xbuffer_t<coef_t> cbuf = tbuf.split((size_t)get_shape_size(shp0));
  tensor_t<coef_t,7,xbuffer_t> tns0(cbuf, shp0);
  // initialize to 0
  const_tensor_iterator_t<coef_t,7,xbuffer_t> iit(icf);
  tensor_iterator_t<coef_t,7,xbuffer_t>       cit0(tns0);
  for (int g = 0; g < tns0.get_dim(6); g++) {
    for (int no = 0; no < tns0.get_dim(5); no++) {
      for (int qd = 0; qd < tns0.get_dim(4)*tns0.get_dim(3); qd++) {
        for (int fw = 0; fw < tns0.get_dim(2); fw++) {
          for (int ni = 0; ni < tns0.get_dim(1); ni++) {
            if (ni >= icf.get_dim(1) || fw >= icf.get_dim(2) || no >= icf.get_dim(5)) {
              // pad with 0 coefficient
              cit0.write((coef_t)0);
              cit0.next();
              cit0.write((coef_t)0);
              cit0.next();
            } else {
              cit0.write(iit.read());
              iit.next();
              cit0.next();
              cit0.write(iit.read());
              iit.next();
              cit0.next();
            }
          }
        }
      }
    }
  }
  //
  // target shape is [grp][no/16][ni/16][fd][fh][fw/2][mlsb][iodd][fw2][o16][i8]
  //
  // [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp][Coef h/l] --> [Grp][Cout/16][o16][Fd][Fh][Fw/2][fw2][ci/16][i8][iodd][mlsb]
  tensor_t<coef_t, 8,xbuffer_t>   tns1(tns0.split(1, shp0[1]/16));
  tensor_t<coef_t, 9,xbuffer_t>   tns2(tns1.split(1, 8));
  tensor_t<coef_t, 10,xbuffer_t>  tns3(tns2.split(4, shp0[2]/2));
  tensor_t<coef_t, 11,xbuffer_t>  tns4(tns3.split(8, shp0[5]/16));
  // transpose [Grp][no/16][o16][Fd][Fh][Fw/2][fw2][ni/16][i8][iodd][mlsb] --> [grp][no/16][ni/16][fd][fh][fw/2][mlsb][iodd][fw2][o16][i8]
  tensor_t<coef_t,11,xbuffer_t>   tnsr(tns4.transpose({2,8,4,1,0,5,6,7,3,9,10}));

  //
  // encode
  //
  array<list<coef_t>,NUM_COEF_QUEUE> vlist;
  int state = 0;
  const_tensor_iterator_t<coef_t,11,xbuffer_t>  coit(tnsr);
  for (int i = 0; i < (int)tnsr.get_tens_size()/16; i++) {
    for (int k = 0; k < ISIZE; k++) {
      vlist[state].push_back(coit.read());
      coit.next();
    }
    state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
  }
  queue_encode(vlist, obuf, olen, coef_mode_uncompressed);
}

static void FC(fm8cf16ns)(const tensor_t<coef_t,4,xbuffer_t>&     icf,       // input coefficients [grp][Cout][Cin][mlsb], 16b only
                          xbuffer_t<coef_t>&                      tbuf,      // temporary xbuf
                          int                                     vs,        // VSIZE
                          // outputs, buffers preallocated by caller
                          xbuffer_t<ixpix_t>&                     obuf,      // output encoded coefficient tensor
                          size_t&                                 olen       // size of used coefficient buffer in ixpix_t
                          ) {
  assert (icf.get_dim(0) == 2 && "expect 16b coefficients");
  // get shape size
  shape<4> shp0;
  shp0[0] = 2;
  shp0[1] = ROUND_UP(icf.get_dim(1), ISIZE);       // round up to multiple of ISIZE
  shp0[2] = ROUND_UP(icf.get_dim(2), vs*ISIZE);    // round up to multiple of VSIZE*ISIZE
  shp0[3] = icf.get_dim(3);
  // increase size of tensor
  xbuffer_t<coef_t> cbuf = tbuf.split((size_t)get_shape_size(shp0));
  tensor_t<coef_t,4,xbuffer_t> tns0(cbuf, shp0);
  // initialize to 0
  const_tensor_iterator_t<coef_t,4,xbuffer_t> iit(icf);
  tensor_iterator_t<coef_t,4,xbuffer_t> cit0(tns0);
  for (int g = 0; g < tns0.get_dim(3); g++) {
    for (int no = 0; no < tns0.get_dim(2); no++) {
      for (int ni = 0; ni < tns0.get_dim(1); ni++) {
        if (ni >= icf.get_dim(1) || no >= icf.get_dim(2)) {
          // pad with 0 coefficient
          cit0.write((coef_t)0);
          cit0.next();
          cit0.write((coef_t)0);
          cit0.next();
        } else {
          cit0.write(iit.read());
          iit.next();
          cit0.next();
          cit0.write(iit.read());
          iit.next();
          cit0.next();
        }
      }
    }
  }

  //
  // target shape is [grp][no/(VSIZE*ISIZE)][ni/16][o8][mlsb][iodd][o16][i8]
  // shp0[0] = 2, shp0[1] = 16, shp0[2] = 32, shp0[3] = 1
  // [grp][no][ni][mlsb] --> [grp][no/(VSIZE*ISIZE)][o8][o16][ni/16][i8][iodd][mlsb]
  tensor_t<coef_t,5,xbuffer_t>  tns1(tns0.split(1, shp0[1]/16)); // [grp][no][ni][mlsb] --> [grp][no][ni/16][i16][mlsb]
  tensor_t<coef_t,6,xbuffer_t>  tns2(tns1.split(1, 8)); // [grp][no][ni/16][i16][mlsb] --> [grp][no][ni/16][i8][iodd][mlsb]
  tensor_t<coef_t,7,xbuffer_t>  tns3(tns2.split(4, shp0[2]/(vs*ISIZE))); // [grp][no][ni/16][i8][iodd][mlsb] --> [grp][no/(VSIZE*ISIZE)][o32][ni/16][i8][iodd][mlsb]
  tensor_t<coef_t,8,xbuffer_t>  tns4(tns3.split(4, vs)); // [grp][no/(VSIZE*ISIZE)][o32][ni/16][i8][iodd][mlsb] --> [grp][no/(VSIZE*ISIZE)][o2][o16][ni/16][i8][iodd][mlsb]
  // transpose [grp][no/(VSIZE*ISIZE)][o2][o16][ni/16][i8][iodd][mlsb] --> [grp][no/(VSIZE*ISIZE)][ni/16][o2][mlsb][iodd][o16][i8]
  tensor_t<coef_t,8,xbuffer_t>  tnsr(tns4.transpose({2,4,1,0,5,3,6,7}));
  //
  // encode
  //
  array<list<coef_t>,NUM_COEF_QUEUE> vlist;
  int state = 0;
  const_tensor_iterator_t<coef_t,8,xbuffer_t>  coit(tnsr);
  // coefficients
  for (int i = 0; i < (int)tnsr.get_tens_size()/16; i++) {
    for (int k = 0; k < 16; k++) {
      vlist[state].push_back(coit.read());
      coit.next();
    }
    state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
  }
  queue_encode(vlist, obuf, olen, coef_mode_uncompressed);
}

// NINO(4x1dws1), 8b feature-map, 16b coefficient, non-sparse
static void NINO(fm8cf16_4x1dws1)(const tensor_t<coef_t,7,xbuffer_t>&    icf,       // input coefficients [Grp][1][Fd][Fh][Fw][1][Coef h/l], 16b only
                                  xbuffer_t<coef_t>&                     tbuf,      // temporary xbuf
                                  // outputs, buffers preallocated by caller
                                  xbuffer_t<ixpix_t>&                    obuf,      // output encoded coefficient tensor
                                  size_t&                                olen       // size of used coefficient buffer in ixpix_t
                                  ) {
  // std::cout<<__FILE__<<" "<<__LINE__<<std::endl;
  assert(icf.get_dim(0) == 2 && icf.get_dim(1) == 1 && icf.get_dim(5) == 1);
  // get shape size
  shape<5> shp0;
  shp0[0] = icf.get_dim(0);
  shp0[1] = ROUND_UP(icf.get_dim(2), 4);               // round to filter size w4
  shp0[2] = icf.get_dim(3);
  shp0[3] = icf.get_dim(4);
  shp0[4] = ROUND_UP(icf.get_dim(6), ISIZE);           // round up to ISIZE
  // increase size of tensor
  xbuffer_t<coef_t> cbuf = tbuf.split((size_t)get_shape_size(shp0));
  tensor_t<coef_t,5,xbuffer_t> tns0(cbuf, shp0);
  // initialize to 0
  const_tensor_iterator_t<coef_t,7,xbuffer_t> iit(icf);
  tensor_iterator_t<coef_t,5,xbuffer_t>       cit0(tns0);
  for (int g = 0; g < tns0.get_dim(4); g++) {
    for (int fd = 0; fd < tns0.get_dim(3); fd++) {
      for (int fh = 0; fh < tns0.get_dim(2); fh++) {
        for (int fw = 0; fw < tns0.get_dim(1); fw++) {
          if (fw >= icf.get_dim(2) || g >= icf.get_dim(6)) {
            // pad with 0 coefficients
            cit0.write((coef_t)0);
            cit0.next();
            cit0.write((coef_t)0);
            cit0.next();
          } else {
            cit0.write(iit.read());
            iit.next();
            cit0.next();
            cit0.write(iit.read());
            iit.next();
            cit0.next();
          }
        }
      }
    }
  }
  //
  // target shape is [grp/16][fd][fh][fw/4][mlsb][g16][fw4]
  //
  // [grp][fd][fh][fw][coef h/l] --> [grp/16][g16][fd][fh][fw/4][fw4][mlsb]
  tensor_t<coef_t,6,xbuffer_t>  tns1(tns0.split(1, shp0[1]/4));
  tensor_t<coef_t,7,xbuffer_t>  tns2(tns1.split(5, shp0[4]/16));
  // [grp][g16][fd][fh][fw/8][fw8][mlsb] --> [grp/16][fd][fh][fw/4][mlsb][g16][fw4]
  tensor_t<coef_t,7,xbuffer_t>  tnsr(tns2.transpose({1,5,0,2,3,4,6}));

  //
  // encode
  //
  array<list<coef_t>,NUM_COEF_QUEUE> vlist;
  int state = 0;
  const_tensor_iterator_t<coef_t,7,xbuffer_t>   coit(tnsr);
  // coefficients
  for (int i = 0; i < (int)tnsr.get_tens_size()/(ISIZE/2); i++) {
      array<coef_t,8>  c_temp;
      array<coef_t,16>  c;
      for (int k = 0; k < ISIZE/2; k++) {
        c_temp[k] = coit.read();
        coit.next();
      }
      c[0]  = c_temp[0 ];
      c[1]  = c_temp[1 ];
      c[2]  = c_temp[2 ];
      c[3]  = c_temp[3 ];
      c[4]  = 0;
      c[5]  = 0;
      c[6]  = 0;
      c[7]  = 0;

      c[8]  = c_temp[4 ];
      c[9]  = c_temp[5 ];
      c[10] = c_temp[6];
      c[11] = c_temp[7];
      c[12] = 0;
      c[13] = 0;
      c[14] = 0;
      c[15] = 0;
      for (int k = 0; k < ISIZE; k++) {
        vlist[state].push_back(c[k]);
      }

    state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
  }
  queue_encode(vlist, obuf, olen, coef_mode_uncompressed);
}

