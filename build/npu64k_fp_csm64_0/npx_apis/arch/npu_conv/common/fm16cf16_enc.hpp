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
// File defining coefficient encoding functions for 16b coefficients and 16b feature-maps
// fm16cf16 does not support:
// - compression
// - 4b
// - sparse
// - coefficient zero-points
// - inn&onn
// Depthwise functions same as NINO(fm8cf16...)
//

// DINO(1x1ns), 16b feature-map, 16b coefficient
static void DINO(fm16cf16ns_1x1)(const tensor_t<coef_t,7,xbuffer_t>&     icf,       // input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp][Coef h/l], 16b only
                                 xbuffer_t<coef_t>&                      tbuf,      // temporary xbuf
                                 // outputs, buffers preallocated by caller
                                 xbuffer_t<ixpix_t>&                     obuf,      // output encoded coefficient tensor
                                 size_t&                                 olen       // size of used coefficient buffer in ixpix_t
                                 ) {
  // std::cout<<__FILE__<<" "<<__LINE__<<std::endl;
  assert (icf.get_dim(0) == 2);
  // get shape size
  shape<7> shp0;
  shp0[0] = icf.get_dim(0);
  shp0[1] = ROUND_UP(icf.get_dim(1), ISIZE);         // round up to multiple of ISIZE
  shp0[2] = icf.get_dim(2);
  shp0[3] = icf.get_dim(3);
  shp0[4] = icf.get_dim(4);
  shp0[5] = ROUND_UP(icf.get_dim(5), ISIZE);         // round up to multiple of ISIZE
  shp0[6] = icf.get_dim(6);
  // increase size of tensor
  xbuffer_t<coef_t> cbuf = tbuf.split((size_t)get_shape_size(shp0));
  xbuffer_t<coef_t> zbuf;
  tensor_t<coef_t,7,xbuffer_t> tns0(cbuf, shp0);
  // initialize to 0
  const_tensor_iterator_t<coef_t,7,xbuffer_t> iit(icf);
  tensor_iterator_t<coef_t,7,xbuffer_t>       cit0(tns0);
  for (int g = 0; g < shp0[6]; g++) {
    for (int no = 0; no < shp0[5]; no++) {
      for (int qd = 0; qd < shp0[2]*shp0[3]*shp0[4]; qd++) {
        for (int ni = 0; ni < shp0[1]; ni++) {
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
  // target shape is [grp][no/16][ni/16][fd][fh][fw][mlsb][i2][o16][i8]
  //
  // [grp][no][fd][fh][fw][ni][mlsb] --> [grp][no/16][o16][fd][fh][fw][ni/16][i2][i8][mlsb]
  tensor_t<coef_t,8,xbuffer_t>  tns1(tns0.split(1, shp0[1]/16));
  tensor_t<coef_t,9,xbuffer_t>  tns2(tns1.split(1, 2));
  tensor_t<coef_t,10,xbuffer_t> tns3(tns2.split(7, shp0[5]/16));
  // transpose [grp][no/16][o16][fd][fh][fw][ni/16][i2][i8][mlsb] --> [grp][no/16][ni/16][fd][fh][fw][mlsb][i2][o16][i8]
  tensor_t<coef_t,10,xbuffer_t> tnsr(tns3.transpose({1,7,2,0,4,5,6,3,8,9}));
  //
  //
  // encode
  //
  array<list<coef_t>,NUM_COEF_QUEUE> vlist;
  int state = 0;
  const_tensor_iterator_t<coef_t,10,xbuffer_t>  coit(tnsr);
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

// DINO(1x1ns), 16b feature-map, 16b coefficient, grouped
static void DINO(gfm16cf16ns_1x1)(const tensor_t<coef_t,7,xbuffer_t>&     icf,       // input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp][Coef h/l], 16b only
                                  xbuffer_t<coef_t>&                      tbuf,      // temporary xbuf
                                  // outputs, buffers preallocated by caller
                                  xbuffer_t<ixpix_t>&                     obuf,      // output encoded coefficient tensor
                                  size_t&                                 olen       // size of used coefficient buffer in ixpix_t
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
  DINO(fm16cf16ns_1x1)(otns, tbuf, obuf, olen);  
}

// NINO(2x1ns), 8b feature-map, 16b coefficient
static void NINO(fm16cf16ns_2x1)(const tensor_t<coef_t,7,xbuffer_t>&     icf,       // input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp][Coef h/l], 16b only
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
  shp0[1]  = ROUND_UP(icf.get_dim(1), ISIZE/2);     // round up to multiple of ISIZE/2
  shp0[2]  = ROUND_UP(icf.get_dim(2), 2);           // round up to filter width 2
  shp0[3]  = icf.get_dim(3);
  shp0[4]  = icf.get_dim(4);
  shp0[5]  = ROUND_UP(icf.get_dim(5), ISIZE);       // round up to multiple of ISIZE
  shp0[6]  = icf.get_dim(6);
  // increase size of tensor
  xbuffer_t<coef_t> cbuf = tbuf.split((size_t)get_shape_size(shp0));
  tensor_t<coef_t,7,xbuffer_t> tns0(cbuf, shp0);
  // initialize to 0
  const_tensor_iterator_t<coef_t,7,xbuffer_t> iit(icf);
  tensor_iterator_t<coef_t,7,xbuffer_t>       cit0(tns0);
  for (int g = 0; g < shp0[6]; g++) {
    for (int no = 0; no < shp0[5]; no++) {
      for (int qd = 0; qd < shp0[3]*shp0[4]; qd++) {
        for (int w = 0; w < shp0[2]; w++) {
          for (int ni = 0; ni < shp0[1]; ni++) {
            if (ni >= icf.get_dim(1) || w >= icf.get_dim(2) || no >= icf.get_dim(5)) {
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
  // target shape is [grp][no/16][ni/8][fd][fh][fw/2][mlsb][w2][o16][i8]
  //
  // [grp][no][fd][fh][fw][ni][mlsb] --> [grp][no/16][o16][fd][fh][fw/2][w2][ni/8][i8][mlsb]
  tensor_t<coef_t,8,xbuffer_t>   tns1(tns0.split(1, shp0[1]/8));
  tensor_t<coef_t,9,xbuffer_t>   tns2(tns1.split(3, shp0[2]/2));
  tensor_t<coef_t,10,xbuffer_t>  tns3(tns2.split(7, shp0[5]/16));
  // transpose [grp][no/16][o16][fd][fh][fw/2][w2][ni/8][i8][mlsb] --> [grp][no/16][ni/8][fd][fh][fw/2][mlsb][w2][o16][i8]
  tensor_t<coef_t,10,xbuffer_t>  tnsr(tns3.transpose({1,7,3,0,4,5,6,2,8,9}));

  //
  // encode
  //
  array<list<coef_t>,NUM_COEF_QUEUE> vlist;
  int state = 0;
  const_tensor_iterator_t<coef_t,10,xbuffer_t>  coit(tnsr);
  // coefficients
  for (int i = 0; i < (int)tnsr.get_tens_size()/16; i++) {
    for (int k = 0; k < ISIZE; k++) {
      coef_t v = coit.read();
      vlist[state].push_back(v);
      coit.next();
    }
    state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
  }
  queue_encode(vlist, obuf, olen, coef_mode_uncompressed);

}

// NINO(2x1ns), 8b feature-map, 16b coefficient, non-sparse
static void FC(fm16cf16ns)(const tensor_t<coef_t,4,xbuffer_t>&     icf,       // input coefficients [Grp][Cout/Grp][Cin/Grp][Coef h/l], 16b only
                           xbuffer_t<coef_t>&                      tbuf,      // temporary xbuf
                           int                                     vs,        // VSIZE
                           // outputs, buffers preallocated by caller
                           xbuffer_t<ixpix_t>&                     obuf,      // output encoded coefficient tensor
                           size_t&                                 olen       // size of used coefficient buffer in ixpix_t
                           ) {
  
  // get shape size
  assert (icf.get_dim(0) == 2);
  shape<4> shp0;
  shp0[0]  = icf.get_dim(0);
  shp0[1]  = ROUND_UP(icf.get_dim(1), (ISIZE/2)); // round up to multiple of ISIZE
  shp0[2]  = ROUND_UP(icf.get_dim(2), vs*ISIZE);  // round up to multiple of VSIZE*ISIZE
  shp0[3]  = icf.get_dim(3);
  xbuffer_t<coef_t> cbuf = tbuf.split((size_t)get_shape_size(shp0));
  tensor_t<coef_t,4,xbuffer_t> tns0(cbuf, shp0);
  // initialize to 0
  const_tensor_iterator_t<coef_t,4,xbuffer_t> iit(icf);
  tensor_iterator_t<coef_t,4,xbuffer_t>       cit0(tns0);
  for (int g = 0; g < shp0[3]; g++) {
    for (int no = 0; no < shp0[2]; no++) {
      for (int ni = 0; ni < shp0[1]; ni++) {
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
  // target shape is [grp][no/(VSIZE*ISIZE)][ni/8][mlsb][o16][i8]
  //
  // [grp][no][ni][mlsb] --> [grp][no/(VSIZE*ISIZE)][o8][o16][ni/8][i8][mlsb]
  tensor_t<coef_t,5,xbuffer_t>   tns1(tns0.split(1, shp0[1]/8)); //[grp][no][ni/8][i8][mlsb]
  tensor_t<coef_t,6,xbuffer_t>   tns2(tns1.split(3, shp0[2]/(vs*ISIZE))); //[grp][no/(VSIZE*ISIZE)][o8][ni/8][i8][mlsb]
  tensor_t<coef_t,7,xbuffer_t>   tns3(tns2.split(3, vs));
  // transpose [grp][no/(VSIZE*ISIZE)][o8][o16][ni/8][i8][mlsb] --> [grp][no/(VSIZE*ISIZE)][ni/8][o8][mlsb][o16][i8]
  tensor_t<coef_t,7,xbuffer_t>   tnsr(tns3.transpose({1,3,0,4,2,5,6}));

  //
  // encode
  //
  array<list<coef_t>,NUM_COEF_QUEUE> vlist;
  int state = 0;
  const_tensor_iterator_t<coef_t,7,xbuffer_t>  coit(tnsr);
  // coefficients
  for (int i = 0; i < (int)tnsr.get_tens_size()/16; i++) {
    for (int k = 0; k < ISIZE; k++) {
      coef_t v = coit.read();
      vlist[state].push_back(v);
      coit.next();
    }
    state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
  }

  queue_encode(vlist, obuf, olen, coef_mode_uncompressed);
}

