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
// File defining coefficient encoding functions for 8b coefficients and 8b feature-maps
// fm16cf16 supports:
// - compression
// - 4b
// - sparse, for DINO(1x1) only
// - coefficient zero-points
// - inn&onn, for DINO(1x1) only
//

// Newly add 4x1dws1
static void NINO(fm8cf8_4x1dws1)(const tensor_t<coef_t,6,xbuffer_t>&     icf,       // input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp], 8b only
                                 const tensor_t<coef_t,1,xbuffer_t>&     izp,       // input zero-points [Cout]
                                 xbuffer_t<coef_t>&                      tbuf,      // temporary xbuf
                                 // attributes
                                 coef_mode_t                             coef_mode, // coefficient compression mode uncompressed or compressed or sparse
                                 bool                                    cf_4b,     // 4b coefficient encoding
                                 bool                                    cf_zp,     // zero-point enable
                                 // outputs, buffers preallocated by caller
                                 xbuffer_t<ixpix_t>&                     obuf,      // output encoded coefficient tensor
                                 size_t&                                 olen       // size of used coefficient buffer in ixpix_t
                                 ) {
  // std::cout<<__FILE__<<" "<<__LINE__<<std::endl;
  assert(icf.get_dim(0) == 1 && icf.get_dim(4) == 1);
  // get shape size
  shape<4> shp0;
  shp0[0] = ((icf.get_dim(1)+3)/4)*4;                         // round to filter size w4
  shp0[1] = ((icf.get_dim(2)+0)/1)*1;                         // round to filter size h1
  shp0[2] = icf.get_dim(3);
  shp0[3] = ((icf.get_dim(5)+ISIZE-1)/ISIZE)*ISIZE;           // round up to ISIZE
  xbuffer_t<coef_t> cbuf = tbuf.split((size_t)get_shape_size(shp0));
  xbuffer_t<coef_t> zbuf = tbuf.split((size_t)shp0[3]             );
  tensor_t<coef_t,4,xbuffer_t> tns0(cbuf, shp0);
  tensor_t<coef_t,1,xbuffer_t> zp0(zbuf, {shp0[3]});
  // initialize to 0
  const_tensor_iterator_t<coef_t,6,xbuffer_t> iit(icf);
  tensor_iterator_t<coef_t,4,xbuffer_t>       cit0(tns0);
  const_tensor_iterator_t<coef_t,1,xbuffer_t> izit(izp);
  tensor_iterator_t<coef_t,1,xbuffer_t>       zit0(zp0);
  for (int g = 0; g < shp0[3]; g++) {
    coef_t zp;
    if (g >= icf.get_dim(5) || (!cf_zp)) {
      zp = (coef_t)0;
    } else {
      zp = izit.read();
      izit.next();
    }
    zit0.write(zp);
    zit0.next();
    for (int fd = 0; fd < shp0[2]; fd++) {
      for (int fh = 0; fh < shp0[1]; fh++) {
        for (int fw = 0; fw < shp0[0]; fw++) {
          if (fw >= icf.get_dim(1) || fh >= icf.get_dim(2) || g >= icf.get_dim(5)) {
            // pad with 0 coefficients
            cit0.write(zp);
          } else {
            cit0.write(iit.read());
            iit.next();
          }
          cit0.next();
        }
      }
    }
  }
  //
  // target shape is [grp/16][fd][fh][fw/4][g16][fw4]
  //
  // [grp][fd][fh][fw] --> [grp/16][g16][fd][fh][fw/4][fw4]
  tensor_t<coef_t,5,xbuffer_t>  tns1(tns0.split(0, shp0[0]/4));
  tensor_t<coef_t,6,xbuffer_t>  tns2(tns1.split(4, shp0[3]/16));
  // transpose [grp/16][g16][fd][fh][fw/4][fw4] --> [grp/16][fd][fh][fw/4][g16][fw4]
  tensor_t<coef_t,6,xbuffer_t>  tnsr(tns2.transpose({0,4,1,2,3,5}));
  // zero-point reorder [grp] --> [grp/16][g16]
  tensor_t<coef_t,2,xbuffer_t>  zpr(zp0.split(0, shp0[3]/16));

  //
  // Get the avail bits identifying which coefficients are equal to the zero-point
  //
  std::cout<<"tnsr.get_tens_size()="<<tnsr.get_tens_size()<<std::endl;

  xbuffer_t<uint8_t> availbuf = tbuf.split<uint8_t>((size_t)tnsr.get_tens_size());
  tensor_t<uint8_t,6,xbuffer_t>                availtns(availbuf, tnsr.get_shape());
  tensor_iterator_t<uint8_t,6,xbuffer_t>       availit(availtns);
  const_tensor_iterator_t<coef_t,6,xbuffer_t>  eit(tnsr);
  for (int grp = 0; grp < tnsr.get_dim(5); grp++) {
    for (int f = 0; f < tnsr.get_dim(2)*tnsr.get_dim(3)*tnsr.get_dim(4); f++) {
      for (int o16 = 0; o16 < 16; o16++) {
        coef_t zp = cf_zp ? zpr.read({(int16_t)o16,(int16_t)grp}) : (coef_t)0;
        for (int ii = 0; ii < 4; ii++) {
          availit.write(eit.read() != zp);
          availit.next();
          eit.next();
        }
      }
    }
  }

  //
  // encode
  //
  array<list<coef_t>,NUM_COEF_QUEUE> vlist;
  int state = 0;
  const_tensor_iterator_t<coef_t,6,xbuffer_t>   coit(tnsr);
  const_tensor_iterator_t<coef_t,2,xbuffer_t>   zoit(zpr);
  const_tensor_iterator_t<uint8_t,6,xbuffer_t>  ait(availtns);
  std::cout<<"o loop="<<tnsr.get_dim(5)<<std::endl;
  std::cout<<"i loop="<<(int)tnsr.get_tens_size()/tnsr.get_dim(5)/ISIZE<<std::endl;
  for (int o = 0; o < tnsr.get_dim(5); o++) {
    // new zero-point
    if (cf_zp) {
      for (int k = 0; k < ISIZE; k++) {
        vlist[state].push_back(zoit.read());
        zoit.next();
      }
      state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
    }
    // coefficients
    for (int i = 0; i < (int)tnsr.get_tens_size()/tnsr.get_dim(5)/(ISIZE/2); i++) {
      array<coef_t,8>  c_temp;
      array<uint8_t,8> a_temp;
      array<coef_t,16>  c;
      array<uint8_t,16> a;

      for (int k = 0; k < ISIZE/2; k++) {
        if (coef_mode == coef_mode_compressed) {
          a_temp[k] = ait.read();
          ait.next();
        }
        c_temp[k] = coit.read();
        coit.next();
      }
      //FIXME: How many 4x1?
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

      a[0]  = a_temp[0 ];
      a[1]  = a_temp[1 ];
      a[2]  = a_temp[2 ];
      a[3]  = a_temp[3 ];
      a[4]  = 0;
      a[5]  = 0;
      a[6]  = 0;
      a[7]  = 0;
      a[8]  = a_temp[4 ];
      a[9]  = a_temp[5 ];
      a[10] = a_temp[6 ];
      a[11] = a_temp[7 ];
      a[12] = 0;
      a[13] = 0;
      a[14] = 0;
      a[15] = 0;

      if (coef_mode == coef_mode_compressed) {
        uint16_t m = 0;
        for (int k = 0; k < ISIZE; k++) {
          m |= a[k] != 0 ? 1<<k : 0;
        }
        // write avail bits
        vlist[state].push_back((coef_t)m);
        vlist[state].push_back((coef_t)(m>>8));
        // write non-zeros
        for (int k = 0; k < ISIZE; k++) {
          if ((m & (1 << k)) != 0) {
            vlist[state].push_back(c[k]);
          }
        }
      } else if (cf_4b) {
        for (int k = 0; k < ISIZE/2; k++) {
          vlist[state].push_back((coef_t)((c[2*k]&0xf)|(c[2*k+1]<<4)));
        }
      } else {
        for (int k = 0; k < ISIZE; k++) {
          vlist[state].push_back(c[k]);
        }
      }
      state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
    }
  }
  queue_encode(vlist, obuf, olen, coef_mode);
}

static void NINO(fm8cf8_8x1dws1)(const tensor_t<coef_t,6,xbuffer_t>&     icf,       // input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp], 8b only
                                 const tensor_t<coef_t,1,xbuffer_t>&     izp,       // input zero-points [Cout]
                                 xbuffer_t<coef_t>&                      tbuf,      // temporary xbuf
                                 // attributes
                                 coef_mode_t                             coef_mode, // coefficient compression mode uncompressed or compressed or sparse
                                 bool                                    cf_4b,     // 4b coefficient encoding
                                 bool                                    cf_zp,     // zero-point enable
                                 // outputs, buffers preallocated by caller
                                 xbuffer_t<ixpix_t>&                     obuf,      // output encoded coefficient tensor
                                 size_t&                                 olen       // size of used coefficient buffer in ixpix_t
                                 ) {
  // std::cout<<__FILE__<<" "<<__LINE__<<std::endl;
  assert(icf.get_dim(0) == 1 && icf.get_dim(4) == 1);
  // get shape size
  shape<4> shp0;
  shp0[0] = ((icf.get_dim(1)+7)/8)*8;                         // round to filter size w8
  shp0[1] = ((icf.get_dim(2)+0)/1)*1;                         // round to filter size h1
  shp0[2] = icf.get_dim(3);
  shp0[3] = ((icf.get_dim(5)+ISIZE-1)/ISIZE)*ISIZE;           // round up to ISIZE
  xbuffer_t<coef_t> cbuf = tbuf.split((size_t)get_shape_size(shp0));
  xbuffer_t<coef_t> zbuf = tbuf.split((size_t)shp0[3]             );
  tensor_t<coef_t,4,xbuffer_t> tns0(cbuf, shp0);
  tensor_t<coef_t,1,xbuffer_t> zp0(zbuf, {shp0[3]});
  // initialize to 0
  const_tensor_iterator_t<coef_t,6,xbuffer_t> iit(icf);
  tensor_iterator_t<coef_t,4,xbuffer_t>       cit0(tns0);
  const_tensor_iterator_t<coef_t,1,xbuffer_t> izit(izp);
  tensor_iterator_t<coef_t,1,xbuffer_t>       zit0(zp0);
  for (int g = 0; g < shp0[3]; g++) {
    coef_t zp;
    if (g >= icf.get_dim(5) || (!cf_zp)) {
      zp = (coef_t)0;
    } else {
      zp = izit.read();
      izit.next();
    }
    zit0.write(zp);
    zit0.next();
    for (int fd = 0; fd < shp0[2]; fd++) {
      for (int fh = 0; fh < shp0[1]; fh++) {
        for (int fw = 0; fw < shp0[0]; fw++) {
          if (fw >= icf.get_dim(1) || fh >= icf.get_dim(2) || g >= icf.get_dim(5)) {
            // pad with 0 coefficients
            cit0.write(zp);
          } else {
            cit0.write(iit.read());
            iit.next();
          }
          cit0.next();
        }
      }
    }
  }
  //
  // target shape is [grp/16][fd][fh][fw/8][g16][fw8]
  //
  // [grp][fd][fh][fw] --> [grp/16][g16][fd][fh][fw/8][fw8]
  tensor_t<coef_t,5,xbuffer_t>  tns1(tns0.split(0, shp0[0]/8));
  tensor_t<coef_t,6,xbuffer_t>  tns2(tns1.split(4, shp0[3]/16));
  // transpose [grp/16][g16][fd][fh][fw/8][fw8] --> [grp/16][fd][fh][fw/8][g16][fw8]
  tensor_t<coef_t,6,xbuffer_t>  tnsr(tns2.transpose({0,4,1,2,3,5}));
  // zero-point reorder [grp] --> [grp/16][g16]
  tensor_t<coef_t,2,xbuffer_t>  zpr(zp0.split(0, shp0[3]/16));

  //
  // Get the avail bits identifying which coefficients are equal to the zero-point
  //
  xbuffer_t<uint8_t> availbuf = tbuf.split<uint8_t>((size_t)tnsr.get_tens_size());
  tensor_t<uint8_t,6,xbuffer_t>                availtns(availbuf, tnsr.get_shape());
  tensor_iterator_t<uint8_t,6,xbuffer_t>       availit(availtns);
  const_tensor_iterator_t<coef_t,6,xbuffer_t>  eit(tnsr);
  for (int grp = 0; grp < tnsr.get_dim(5); grp++) {
    for (int f = 0; f < tnsr.get_dim(2)*tnsr.get_dim(3)*tnsr.get_dim(4); f++) {
      for (int o16 = 0; o16 < 16; o16++) {
        coef_t zp = cf_zp ? zpr.read({(int16_t)o16,(int16_t)grp}) : (coef_t)0;
        for (int ii = 0; ii < 8; ii++) {
          availit.write(eit.read() != zp);
          availit.next();
          eit.next();
        }
      }
    }
  }

  //
  // encode
  //
  array<list<coef_t>,NUM_COEF_QUEUE> vlist;
  int state = 0;
  const_tensor_iterator_t<coef_t,6,xbuffer_t>   coit(tnsr);
  const_tensor_iterator_t<coef_t,2,xbuffer_t>   zoit(zpr);
  const_tensor_iterator_t<uint8_t,6,xbuffer_t>  ait(availtns);
  for (int o = 0; o < tnsr.get_dim(5); o++) {
    // new zero-point
    if (cf_zp) {
      for (int k = 0; k < ISIZE; k++) {
        vlist[state].push_back(zoit.read());
        zoit.next();
      }
      state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
    }
    // coefficients
    for (int i = 0; i < (int)tnsr.get_tens_size()/tnsr.get_dim(5)/ISIZE; i++) {
      array<coef_t,16>  c_temp;
      array<uint8_t,16> a_temp;
      array<coef_t,16>  c;
      array<uint8_t,16> a;

      for (int k = 0; k < ISIZE; k++) {
        if (coef_mode == coef_mode_compressed) {
          a_temp[k] = ait.read();
          ait.next();
        }
        c_temp[k] = coit.read();
        coit.next();
      }

      c[0]  = c_temp[0 ];
      c[1]  = c_temp[1 ];
      c[2]  = c_temp[2 ];
      c[3]  = c_temp[3 ];
      c[4]  = c_temp[4 ];
      c[5]  = c_temp[5 ];
      c[6]  = c_temp[6 ];
      c[7]  = c_temp[7 ];
      c[8]  = c_temp[8 ];
      c[9]  = c_temp[9 ];
      c[10] = c_temp[10];
      c[11] = c_temp[11];
      c[12] = c_temp[12];
      c[13] = c_temp[13];
      c[14] = c_temp[14];
      c[15] = c_temp[15];

      a[0]  = a_temp[0 ];
      a[1]  = a_temp[1 ];
      a[2]  = a_temp[2 ];
      a[3]  = a_temp[3 ];
      a[4]  = a_temp[4 ];
      a[5]  = a_temp[5 ];
      a[6]  = a_temp[6 ];
      a[7]  = a_temp[7 ];
      a[8]  = a_temp[8 ];
      a[9]  = a_temp[9 ];
      a[10] = a_temp[10];
      a[11] = a_temp[11];
      a[12] = a_temp[12];
      a[13] = a_temp[13];
      a[14] = a_temp[14];
      a[15] = a_temp[15];

      if (coef_mode == coef_mode_compressed) {
        uint16_t m = 0;
        for (int k = 0; k < ISIZE; k++) {
          m |= a[k] != 0 ? 1<<k : 0;
        }
        // write avail bits
        vlist[state].push_back((coef_t)m);
        vlist[state].push_back((coef_t)(m>>8));
        // write non-zeros
        for (int k = 0; k < ISIZE; k++) {
          if ((m & (1 << k)) != 0) {
            vlist[state].push_back(c[k]);
          }
        }
      } else if (cf_4b) {
        for (int k = 0; k < ISIZE/2; k++) {
          vlist[state].push_back((coef_t)((c[2*k]&0xf)|(c[2*k+1]<<4)));
        }
      } else {
        for (int k = 0; k < ISIZE; k++) {
          vlist[state].push_back(c[k]);
        }
      }
      state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
    }
  }
  queue_encode(vlist, obuf, olen, coef_mode);
}


static void NINO(fm8cf8_2x3dws2)(const tensor_t<coef_t,6,xbuffer_t>&     icf,       // input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp], 8b only
                                 const tensor_t<coef_t,1,xbuffer_t>&     izp,       // input zero-points [Cout]
                                 xbuffer_t<coef_t>&                      tbuf,      // temporary xbuf
                                 // attributes
                                 coef_mode_t                             coef_mode, // coefficient compression mode uncompressed or compressed or sparse
                                 bool                                    cf_4b,     // 4b coefficient encoding
                                 bool                                    cf_zp,     // zero-point enable
                                 // outputs, buffers preallocated by caller
                                 xbuffer_t<ixpix_t>&                     obuf,      // output encoded coefficient tensor
                                 size_t&                                 olen       // size of used coefficient buffer in ixpix_t
                                 ) {
  // std::cout<<__FILE__<<" "<<__LINE__<<std::endl;
  assert(icf.get_dim(0) == 1 && icf.get_dim(4) == 1);
  // get shape size
  shape<4> shp0;
  shp0[0] = ((icf.get_dim(1)+1)/2)*2;                         // round to filter size w2
  shp0[1] = ((icf.get_dim(2)+2)/3)*3;                         // round to filter size h3
  shp0[2] = icf.get_dim(3);
  shp0[3] = ((icf.get_dim(5)+ISIZE-1)/ISIZE)*ISIZE;           // round up to ISIZE
  xbuffer_t<coef_t> cbuf = tbuf.split((size_t)get_shape_size(shp0));
  xbuffer_t<coef_t> zbuf = tbuf.split((size_t)shp0[3]             );
  tensor_t<coef_t,4,xbuffer_t> tns0(cbuf, shp0);
  tensor_t<coef_t,1,xbuffer_t> zp0(zbuf, {shp0[3]});
  // initialize to 0
  const_tensor_iterator_t<coef_t,6,xbuffer_t> iit(icf);
  tensor_iterator_t<coef_t,4,xbuffer_t>       cit0(tns0);
  const_tensor_iterator_t<coef_t,1,xbuffer_t> izit(izp);
  tensor_iterator_t<coef_t,1,xbuffer_t>       zit0(zp0);
  for (int g = 0; g < shp0[3]; g++) {
    coef_t zp;
    if (g >= icf.get_dim(5) || (!cf_zp)) {
      zp = (coef_t)0;
    } else {
      zp = izit.read();
      izit.next();
    }
    zit0.write(zp);
    zit0.next();
    for (int fd = 0; fd < shp0[2]; fd++) {
      for (int fh = 0; fh < shp0[1]; fh++) {
        for (int fw = 0; fw < shp0[0]; fw++) {
          if (fw >= icf.get_dim(1) || fh >= icf.get_dim(2) || g >= icf.get_dim(5)) {
            // pad with 0 coefficients
            cit0.write(zp);
          } else {
            cit0.write(iit.read());
            iit.next();
          }
          cit0.next();
        }
      }
    }
  }
  //
  // target shape is [grp/16][fd][fh/3][fw/2][g16][fw2][fh3]
  //
  // [grp][fd][fh][fw] --> [grp/16][g16][fd][fh/3][fh3][fw/2][fw2]
  tensor_t<coef_t,5,xbuffer_t>  tns1(tns0.split(0, shp0[0]/2));
  tensor_t<coef_t,6,xbuffer_t>  tns2(tns1.split(2, shp0[1]/3));
  tensor_t<coef_t,7,xbuffer_t>  tns3(tns2.split(5, shp0[3]/16));
  // transpose [grp/16][g16][fd][fh/3][fh3][fw/2][fw2] -> [grp/16][fd][fh/3][fw/2][g16][fw2][fh3]
  tensor_t<coef_t,7,xbuffer_t>  tns4(tns3.transpose({2,0,5,1,3,4,6}));
  tensor_t<coef_t,7,xbuffer_t>  tnsr(tns4.reverse(0));
  // zero-point reorder [grp] --> [grp/16][o8][o2]
  tensor_t<coef_t,2,xbuffer_t>  zpr(zp0.split(0, shp0[3]/16));


  //
  // Get the avail bits identifying which coefficients are equal to the zero-point
  //
  xbuffer_t<uint8_t> availbuf = tbuf.split<uint8_t>((size_t)tnsr.get_tens_size());
  tensor_t<uint8_t,7,xbuffer_t>                availtns(availbuf, tnsr.get_shape());
  tensor_iterator_t<uint8_t,7,xbuffer_t>       availit(availtns);
  const_tensor_iterator_t<coef_t,7,xbuffer_t>  eit(tnsr);
  for (int grp = 0; grp < tnsr.get_dim(6); grp++) {
    for (int f = 0; f < tnsr.get_dim(3)*tnsr.get_dim(4)*tnsr.get_dim(5); f++) {
      for (int o16 = 0; o16 < tnsr.get_dim(2); o16++) {
        coef_t zp = cf_zp ? zpr.read({(int16_t)o16,(int16_t)grp}) : (coef_t)0;
        for (int ii = 0; ii < tnsr.get_dim(0)*tnsr.get_dim(1); ii++) {
          availit.write(eit.read() != zp);
          availit.next();
          eit.next();
        }
      }
    }
  }

  //
  // encode
  //
  array<list<coef_t>,NUM_COEF_QUEUE> vlist;
  int state = 0;
  const_tensor_iterator_t<coef_t,7,xbuffer_t>   coit(tnsr);
  const_tensor_iterator_t<coef_t,2,xbuffer_t>   zoit(zpr);
  const_tensor_iterator_t<uint8_t,7,xbuffer_t>  ait(availtns);
  for (int o = 0; o < tnsr.get_dim(6); o++) {
    // new zero-point
    if (cf_zp) {
      for (int k = 0; k < ISIZE; k++) {
        vlist[state].push_back(zoit.read());
        zoit.next();
      }
      state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
    }
    // coefficients
    for (int i = 0; i < (int)tnsr.get_tens_size()/tnsr.get_dim(6)/12; i++) {
      // due to coefs only has 6 each set, padding zeros each group to meet the requirements
      array<coef_t,12>  c_temp;
      array<uint8_t,12> a_temp;
      array<coef_t,16>  c;
      array<uint8_t,16> a;
      for (int j = 0; j < 12; j++) {
        c_temp[j] = coit.read();
        a_temp[j] = ait.read();
        coit.next();
        ait.next();
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
      a[0]  = a_temp[0 ];
      a[1]  = a_temp[1 ];
      a[2]  = a_temp[2 ];
      a[3]  = 0;
      a[4]  = 0;
      a[5]  = a_temp[3 ];
      a[6]  = a_temp[4 ];
      a[7]  = a_temp[5 ];
      a[8]  = a_temp[6 ];
      a[9]  = a_temp[7 ];
      a[10] = a_temp[8 ];
      a[11] = 0;
      a[12] = 0;
      a[13] = a_temp[9 ];
      a[14] = a_temp[10];
      a[15] = a_temp[11];
      if (coef_mode == coef_mode_compressed) {
        uint16_t m = 0;
        for (int k = 0; k < 16; k++) {
          m |= a[k] != 0 ? 1<<k : 0;
        }
        // write avail bits
        vlist[state].push_back((coef_t)m);
        vlist[state].push_back((coef_t)(m>>8));
        // write non-zeros
        for (int k = 0; k < 16; k++) {
          if ((m & (1 << k)) != 0) {
            vlist[state].push_back(c[k]);
          }
        }
      } else if (cf_4b) {
        for (int k = 0; k < 8; k++) {
          vlist[state].push_back((coef_t)((c[2*k]&0xf)|(c[2*k+1]<<4)));
        }
      } else {
        for (int k = 0; k < 16; k++) {
          vlist[state].push_back(c[k]);
        }
      }
      state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
    }
  }
  queue_encode(vlist, obuf, olen, coef_mode);
}

// NINO(3x3dws1dl2), 8b feature-map, 8b coefficient, non-sparse
static void NINO(fm8cf8_3x3dws1dl2)(const tensor_t<coef_t,6,xbuffer_t>&     icf,       // input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp], 8b only
                                    const tensor_t<coef_t,1,xbuffer_t>&     izp,       // input zero-points [Cout]
                                    xbuffer_t<coef_t>&                      tbuf,      // temporary xbuf
                                    // attributes
                                    coef_mode_t                             coef_mode, // coefficient compression mode uncompressed or compressed or sparse
                                    bool                                    cf_4b,     // 4b coefficient encoding
                                    bool                                    cf_zp,     // zero-point enable
                                    // outputs, buffers preallocated by caller
                                    xbuffer_t<ixpix_t>&                     obuf,      // output encoded coefficient tensor
                                    size_t&                                 olen       // size of used coefficient buffer in ixpix_t
                                    ) {
  // std::cout<<__FILE__<<" "<<__LINE__<<std::endl;
  assert(icf.get_dim(0) == 1 && icf.get_dim(4) == 1);
  // get shape size
  shape<4> shp0;
  shp0[0] = ((icf.get_dim(1)+2)/3)*3;                         // round to filter size w3
  shp0[1] = ((icf.get_dim(2)+2)/3)*3;                         // round to filter size h3
  shp0[2] = icf.get_dim(3);
  shp0[3] = ((icf.get_dim(5)+ISIZE-1)/ISIZE)*ISIZE;           // round up to ISIZE
  xbuffer_t<coef_t> cbuf = tbuf.split((size_t)get_shape_size(shp0));
  xbuffer_t<coef_t> zbuf = tbuf.split((size_t)shp0[3]             );
  tensor_t<coef_t,4,xbuffer_t> tns0(cbuf, shp0);
  tensor_t<coef_t,1,xbuffer_t> zp0(zbuf, {shp0[3]});
  // initialize to 0
  const_tensor_iterator_t<coef_t,6,xbuffer_t> iit(icf);
  tensor_iterator_t<coef_t,4,xbuffer_t>       cit0(tns0);
  const_tensor_iterator_t<coef_t,1,xbuffer_t> izit(izp);
  tensor_iterator_t<coef_t,1,xbuffer_t>       zit0(zp0);
  for (int g = 0; g < shp0[3]; g++) {
    coef_t zp;
    if (g >= icf.get_dim(5) || (!cf_zp)) {
      zp = (coef_t)0;
    } else {
      zp = izit.read();
      izit.next();
    }
    zit0.write(zp);
    zit0.next();
    for (int fd = 0; fd < shp0[2]; fd++) {
      for (int fh = 0; fh < shp0[1]; fh++) {
        for (int fw = 0; fw < shp0[0]; fw++) {
          if (fw >= icf.get_dim(1) || fh >= icf.get_dim(2) || g >= icf.get_dim(5)) {
            // pad with 0 coefficients
            cit0.write(zp);
          } else {
            cit0.write(iit.read());
            iit.next();
          }
          cit0.next();
        }
      }
    }
  }
  //
  // target shape is [grp/16][fd][fh/3][fw/3][g16][fw3][fh3]
  //
  // [grp][fd][fh][fw] --> [grp/16][g16][fd][fh/3][fh3][fw/3][fw3]
  tensor_t<coef_t,5,xbuffer_t>  tns1(tns0.split(0, shp0[0]/3));
  tensor_t<coef_t,6,xbuffer_t>  tns2(tns1.split(2, shp0[1]/3));
  tensor_t<coef_t,7,xbuffer_t>  tns3(tns2.split(5, shp0[3]/16));
  // transpose [grp][g16][fd][fh/3][fh3][fw/3][fw3] -->  [grp/16][fd][fh/3][fw/3][g16][fw3][fh3]
  tensor_t<coef_t,7,xbuffer_t>  tns4(tns3.transpose({2,0,5,1,3,4,6}));
  // reverse order of fh3 axis
  tensor_t<coef_t,7,xbuffer_t>  tnsr(tns4.reverse(0));
  // zero-point reorder [grp] --> [grp/16][o16]
  tensor_t<coef_t,2,xbuffer_t>  zpr(zp0.split(0, shp0[3]/16));

  //
  // Get the avail bits identifying which coefficients are equal to the zero-point
  //
  xbuffer_t<uint8_t> availbuf = tbuf.split<uint8_t>((size_t)tnsr.get_tens_size());
  tensor_t<uint8_t,7,xbuffer_t>                availtns(availbuf, tnsr.get_shape());
  tensor_iterator_t<uint8_t,7,xbuffer_t>       availit(availtns);
  const_tensor_iterator_t<coef_t,7,xbuffer_t>  eit(tnsr);
  for (int grp = 0; grp < tnsr.get_dim(6); grp++) {
    for (int f = 0; f < tnsr.get_dim(3)*tnsr.get_dim(4)*tnsr.get_dim(5); f++) {
      for (int o16 = 0; o16 < tnsr.get_dim(2); o16++) {
        coef_t zp = cf_zp ? zpr.read({(int16_t)o16,(int16_t)grp}) : (coef_t)0;
        for (int ii = 0; ii < tnsr.get_dim(0)*tnsr.get_dim(1); ii++) {
          availit.write(eit.read() != zp);
          availit.next();
          eit.next();
        }
      }
    }
  }

  //
  // encode
  //
  array<list<coef_t>,NUM_COEF_QUEUE> vlist;
  int state = 0;
  const_tensor_iterator_t<coef_t,7,xbuffer_t>   coit(tnsr);
  const_tensor_iterator_t<coef_t,2,xbuffer_t>   zoit(zpr);
  const_tensor_iterator_t<uint8_t,7,xbuffer_t>  ait(availtns);
  for (int o = 0; o < tnsr.get_dim(6); o++) {
    // new zero-point
    if (cf_zp) {
      for (int k = 0; k < ISIZE; k++) {
        vlist[state].push_back(zoit.read());
        zoit.next();
      }
      state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
    }
    // coefficients
    for (int i = 0; i < (int)tnsr.get_tens_size()/tnsr.get_dim(6)/18; i++) {
      // read 18 coefficients and avail bits o2*f3xf3
      array<coef_t,18>  c_temp;
      array<uint8_t,18> a_temp;
      array<coef_t,18>  c;
      array<uint8_t,18> a;
      for (int j = 0; j < 18; j++) {
        c_temp[j] = coit.read();
        a_temp[j] = ait.read();
        coit.next();
        ait.next();
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
      a[0]  = a_temp[0 ];
      a[1]  = a_temp[8 ];
      a[2]  = a_temp[1 ];
      a[3]  = a_temp[6 ];
      a[4]  = a_temp[2 ];
      a[5]  = a_temp[3 ];
      a[6]  = a_temp[5 ];
      a[7]  = a_temp[4 ];
      a[8]  = a_temp[9 ];
      a[9]  = a_temp[17];
      a[10] = a_temp[10];
      a[11] = a_temp[15];
      a[12] = a_temp[11];
      a[13] = a_temp[12];
      a[14] = a_temp[14];
      a[15] = a_temp[13];
      if (coef_mode == coef_mode_compressed) {
        uint16_t m = 0;
        for (int k = 0; k < ISIZE; k++) {
          m |= a[k] != 0 ? 1<<k : 0;
        }
        // write avail bits
        vlist[state].push_back((coef_t)m);
        vlist[state].push_back((coef_t)(m>>8));
        // write non-zeros
        for (int k = 0; k < ISIZE; k++) {
          if ((m & (1 << k)) != 0) {
            vlist[state].push_back(c[k]);
          }
        }
        // always write space
        vlist[state].push_back(c[16]);
        vlist[state].push_back(c[17]);
      } else if (cf_4b) {
        for (int k = 0; k < 9; k++) {
          vlist[state].push_back((coef_t)((c[2*k]&0xf)|(c[2*k+1]<<4)));
        }
      } else {
        for (int k = 0; k < 18; k++) {
          vlist[state].push_back(c[k]);
        }
      }
      state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
    }
  }
  queue_encode(vlist, obuf, olen, coef_mode);
}


// NINO(3x3dws1), 8b feature-map, 8b coefficient, non-sparse
static void NINO(fm8cf8_3x3dws1)(const tensor_t<coef_t,6,xbuffer_t>&     icf,       // input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp], 8b only
                                 const tensor_t<coef_t,1,xbuffer_t>&     izp,       // input zero-points [Cout]
                                 xbuffer_t<coef_t>&                      tbuf,      // temporary xbuf
                                 // attributes
                                 coef_mode_t                             coef_mode, // coefficient compression mode uncompressed or compressed or sparse
                                 bool                                    cf_4b,     // 4b coefficient encoding
                                 bool                                    cf_zp,     // zero-point enable
                                 // outputs, buffers preallocated by caller
                                 xbuffer_t<ixpix_t>&                     obuf,      // output encoded coefficient tensor
                                 size_t&                                 olen       // size of used coefficient buffer in ixpix_t
                                 ) {
  // std::cout<<__FILE__<<" "<<__LINE__<<std::endl;
  assert(icf.get_dim(0) == 1 && icf.get_dim(4) == 1);
  // get shape size
  shape<4> shp0;
  shp0[0] = ((icf.get_dim(1)+2)/3)*3;                         // round to filter size w3
  shp0[1] = ((icf.get_dim(2)+2)/3)*3;                         // round to filter size h3
  shp0[2] = icf.get_dim(3);
  shp0[3] = ((icf.get_dim(5)+ISIZE-1)/ISIZE)*ISIZE;           // round up to ISIZE
  xbuffer_t<coef_t> cbuf = tbuf.split((size_t)get_shape_size(shp0));
  xbuffer_t<coef_t> zbuf = tbuf.split((size_t)shp0[3]             );
  tensor_t<coef_t,4,xbuffer_t> tns0(cbuf, shp0);
  tensor_t<coef_t,1,xbuffer_t> zp0(zbuf, {shp0[3]});
  // initialize to 0
  const_tensor_iterator_t<coef_t,6,xbuffer_t> iit(icf);
  tensor_iterator_t<coef_t,4,xbuffer_t>       cit0(tns0);
  const_tensor_iterator_t<coef_t,1,xbuffer_t> izit(izp);
  tensor_iterator_t<coef_t,1,xbuffer_t>       zit0(zp0);
  for (int g = 0; g < shp0[3]; g++) {
    coef_t zp;
    if (g >= icf.get_dim(5) || (!cf_zp)) {
      zp = (coef_t)0;
    } else {
      zp = izit.read();
      izit.next();
    }
    zit0.write(zp);
    zit0.next();
    for (int fd = 0; fd < shp0[2]; fd++) {
      for (int fh = 0; fh < shp0[1]; fh++) {
        for (int fw = 0; fw < shp0[0]; fw++) {
          if (fw >= icf.get_dim(1) || fh >= icf.get_dim(2) || g >= icf.get_dim(5)) {
            // pad with 0 coefficients
            cit0.write(zp);
          } else {
            cit0.write(iit.read());
            iit.next();
          }
          cit0.next();
        }
      }
    }
  }

  //
  // target shape is [grp/16][fd][fh/3][fw/3][g16][fw3][fh3]
  //
  // [grp][fd][fh][fw] --> [grp][g16][fd][fh/3][fh3][fw/3][fw3]
  tensor_t<coef_t,5,xbuffer_t>  tns1(tns0.split(0, shp0[0]/3));
  tensor_t<coef_t,6,xbuffer_t>  tns2(tns1.split(2, shp0[1]/3));
  tensor_t<coef_t,7,xbuffer_t>  tns3(tns2.split(5, shp0[3]/16));
  // transpose [grp/16][g16][fd][fh/3][fh3][fw/3][fw3] -> [grp/16][fd][fh/3][fw/3][g16][fw3][fh3]
  tensor_t<coef_t,7,xbuffer_t>  tns4(tns3.transpose({2,0,5,1,3,4,6}));
  // reverse order of fh3
  tensor_t<coef_t,7,xbuffer_t>  tnsr(tns4.reverse(0));
  // zero-point reorder [grp] --> [grp/16][o16]
  tensor_t<coef_t,2,xbuffer_t>  zpr(zp0.split(0, shp0[3]/16));

  //
  // Get the avail bits identifying which coefficients are equal to the zero-point
  //
  xbuffer_t<uint8_t> availbuf = tbuf.split<uint8_t>((size_t)tnsr.get_tens_size());
  tensor_t<uint8_t,7,xbuffer_t>                availtns(availbuf, tnsr.get_shape());
  tensor_iterator_t<uint8_t,7,xbuffer_t>       availit(availtns);
  const_tensor_iterator_t<coef_t,7,xbuffer_t>  eit(tnsr);
  for (int grp = 0; grp < tnsr.get_dim(6); grp++) {
    for (int f = 0; f < tnsr.get_dim(3)*tnsr.get_dim(4)*tnsr.get_dim(5); f++) {
      for (int o16 = 0; o16 < tnsr.get_dim(2); o16++) {
        coef_t zp = cf_zp ? zpr.read({(int16_t)o16,(int16_t)grp}) : (coef_t)0;
        for (int ii = 0; ii < tnsr.get_dim(0)*tnsr.get_dim(1); ii++) {
          availit.write(eit.read() != zp);
          availit.next();
          eit.next();
        }
      }
    }
  }

  //
  // encode
  //
  array<list<coef_t>,NUM_COEF_QUEUE>            vlist;
  int state = 0;
  const_tensor_iterator_t<coef_t,7,xbuffer_t>   coit(tnsr);
  const_tensor_iterator_t<coef_t,2,xbuffer_t>   zoit(zpr);
  const_tensor_iterator_t<uint8_t,7,xbuffer_t>  ait(availtns);
  for (int o = 0; o < tnsr.get_dim(6); o++) {
    // new zero-point
    if (cf_zp) {
      for (int k = 0; k < ISIZE; k++) {
        vlist[state].push_back(zoit.read());
        zoit.next();
      }
      state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
    }
    // coefficients
    for (int i = 0; i < (int)tnsr.get_tens_size()/tnsr.get_dim(6)/18; i++) {
      // read 18 coefficients and avail bits o2*f3xf3
      array<coef_t,18>  c_temp;
      array<uint8_t,18> a_temp;
      array<coef_t,18>  c;
      array<uint8_t,18> a;
      for (int j = 0; j < 18; j++) {
        c_temp[j] = coit.read();
        a_temp[j] = ait.read();
        coit.next();
        ait.next();
      }
      // shuffle coefficients, moving spare to back
      // reorg coefs order
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
      a[0]  = a_temp[0 ];
      a[1]  = a_temp[1 ];
      a[2]  = a_temp[2 ];
      a[3]  = a_temp[6 ];
      a[4]  = a_temp[7 ];
      a[5]  = a_temp[3 ];
      a[6]  = a_temp[4 ];
      a[7]  = a_temp[5 ];
      a[8]  = a_temp[9 ];
      a[9]  = a_temp[10];
      a[10] = a_temp[11];
      a[11] = a_temp[15];
      a[12] = a_temp[16];
      a[13] = a_temp[12];
      a[14] = a_temp[13];
      a[15] = a_temp[14];
      if (coef_mode == coef_mode_compressed) {
        uint16_t m = 0;
        for (int k = 0; k < ISIZE; k++) {
          m |= a[k] != 0 ? 1<<k : 0;
        }
        // write avail bits
        vlist[state].push_back((coef_t)m);
        vlist[state].push_back((coef_t)(m>>8));
        // write non-zeros
        for (int k = 0; k < ISIZE; k++) {
          if ((m & (1 << k)) != 0) {
            vlist[state].push_back(c[k]);
          }
        }
        // always write space
        vlist[state].push_back(c[16]);
        vlist[state].push_back(c[17]);
      } else if (cf_4b) {
        for (int k = 0; k < 9; k++) {
          vlist[state].push_back((coef_t)((c[2*k]&0xf)|(c[2*k+1]<<4)));
        }
      } else {
        for (int k = 0; k < 18; k++) {
          vlist[state].push_back(c[k]);
        }
      }
      state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
    }
  }
  queue_encode(vlist, obuf, olen, coef_mode);
}


// DINO(1x1), 8b feature-map, 8b coefficient, non-sparse
static void DINO(fm8cf8ns_1x1)(const tensor_t<coef_t,6,xbuffer_t>&     icf,       // input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp], 8b only
                               const tensor_t<coef_t,1,xbuffer_t>&     izp,       // input zero-points [Cout]
                               xbuffer_t<coef_t>&                      tbuf,      // temporary xbuf
                               // attributes
                               coef_mode_t                             coef_mode, // coefficient compression mode uncompressed or compressed or sparse
                               bool                                    cf_4b,     // 4b coefficient encoding
                               bool                                    cf_zp,     // zero-point enable
                               int                                     inn,       // inner input loop
                               int                                     onn,       // inner output loop
                               // outputs, buffers preallocated by caller
                               xbuffer_t<ixpix_t>&                     obuf,      // output encoded coefficient tensor
                               size_t&                                 olen       // size of used coefficient buffer in ixpix_t
                               ) {
  // std::cout<<__FILE__<<" "<<__LINE__<<std::endl;
  // get shape size
  shape<6> shp0;
  shp0[0] = ((icf.get_dim(0)+2*inn*ISIZE-1)/(2*inn*ISIZE))*2*inn*ISIZE;     // round up to multiple of 2*inn*ISIZE
  shp0[1] = icf.get_dim(1);
  shp0[2] = icf.get_dim(2);
  shp0[3] = icf.get_dim(3);
  shp0[4] = ((icf.get_dim(4)+onn*ISIZE-1)/(onn*ISIZE))*onn*ISIZE;           // round up to multiple of onn*ISIZE
  shp0[5] = icf.get_dim(5);
  xbuffer_t<coef_t> cbuf = tbuf.split((size_t)get_shape_size(shp0));
  xbuffer_t<coef_t> zbuf = tbuf.split((size_t)shp0[4]*shp0[5]     );
  tensor_t<coef_t,6,xbuffer_t> tns0(cbuf, shp0);
  tensor_t<coef_t,2,xbuffer_t> zp0(zbuf, {shp0[4],shp0[5]});
  // initialize to 0
  const_tensor_iterator_t<coef_t,6,xbuffer_t> iit(icf);
  tensor_iterator_t<coef_t,6,xbuffer_t>       cit0(tns0);
  const_tensor_iterator_t<coef_t,1,xbuffer_t> izit(izp);
  tensor_iterator_t<coef_t,2,xbuffer_t>       zit0(zp0);
  for (int g = 0; g < shp0[5]; g++) {
    for (int no = 0; no < shp0[4]; no++) {
      coef_t zp;
      if (no >= icf.get_dim(4) || (!cf_zp)) {
        zp = (coef_t)0;
      } else {
        zp = izit.read();
        izit.next();
      }
      zit0.write(zp);
      zit0.next();
      for (int qd = 0; qd < shp0[1]*shp0[2]*shp0[3]; qd++) {
        for (int ni = 0; ni < shp0[0]; ni++) {
          if (ni >= icf.get_dim(0) || no >= icf.get_dim(4)) {
            // pad with 0 coefficient
            cit0.write(zp);
          } else {
            cit0.write(iit.read());
            iit.next();
          }
          cit0.next();
        }
      }
    }
  }
  //
  // target shape is [grp][no/16*onn][ni/32*inn][fd][fh][fw][inn][onn][iodd][i2][o16][i8]
  //
  // [grp][no][fd][fh][fw][ni] --> [grp][no/onn*16][onn][o16][fd][fh][fw][ni/inn*32][inn][i2][i8][iodd]
  tensor_t<coef_t,7,xbuffer_t>  tns1(tns0.split(0, shp0[0]/(inn*32)));
  tensor_t<coef_t,8,xbuffer_t>  tns2(tns1.split(0, inn));
  tensor_t<coef_t,9,xbuffer_t>  tns3(tns2.split(0, 2));
  tensor_t<coef_t,10,xbuffer_t> tns4(tns3.split(0, 8));
  tensor_t<coef_t,11,xbuffer_t> tns5(tns4.split(8, shp0[4]/(onn*16)));  //[no][onn*o8*o2]
  tensor_t<coef_t,12,xbuffer_t> tns6(tns5.split(8, onn));               //[no][onn][o8*o2]
  // transpose [grp][no/onn*16][onn][o16][fd][fh][fw][ni/inn*32][inn][i2][i8][iodd] -> [grp][no/onn*16][ni/inn*32][fd][fh][fw][inn][onn][iodd][i2][o16][i8]
  tensor_t<coef_t,12,xbuffer_t> tnsr(tns6.transpose({1,8,2,0,9,3,5,6,7,4,10,11}));
  // zero-point reorder [grp][no] -->  [grp][no][onn*16]
  tensor_t<coef_t,3,xbuffer_t>  zpr(zp0.split(0, shp0[4]/(onn*ISIZE))); //[grp][no][onn*o8*o2]
  //
  // Get the avail bits identifying which coefficients are equal to the zero-point
  //
  xbuffer_t<uint8_t> availbuf = tbuf.split<uint8_t>((size_t)tnsr.get_tens_size());
  tensor_t<uint8_t,12,xbuffer_t>               availtns(availbuf, tnsr.get_shape());
  tensor_iterator_t<uint8_t,12,xbuffer_t>      availit(availtns);
  const_tensor_iterator_t<coef_t,12,xbuffer_t> eit(tnsr);
  for (int grp = 0; grp < tnsr.get_dim(11); grp++) {
    for (int no = 0; no < tnsr.get_dim(10); no++) {
      for (int ni = 0; ni < tnsr.get_dim(5)*tnsr.get_dim(6)*tnsr.get_dim(7)*tnsr.get_dim(8)*tnsr.get_dim(9); ni++) {
        for (int nno = 0; nno < onn; nno++) {
          for (int iodd = 0; iodd < 2; iodd++) {
            for (int i = 0; i < 2; i++) {
              for (int o16 = 0; o16 < 16; o16++) {
                coef_t zp = cf_zp ? zpr.read({(int16_t)(o16+nno*16),(int16_t)no,(int16_t)grp}) : (coef_t)0;
                for (int ii = 0; ii < 8; ii++) {
                  availit.write(eit.read() != zp);
                  availit.next();
                  eit.next();
                }
              }
            }
          }
        }
      }
    }
  }

  //
  // encode
  //
  array<list<coef_t>,NUM_COEF_QUEUE> vlist;
  int state = 0;
  const_tensor_iterator_t<coef_t,12,xbuffer_t>  coit(tnsr);
  const_tensor_iterator_t<coef_t,3,xbuffer_t>   zoit(zpr);
  const_tensor_iterator_t<uint8_t,12,xbuffer_t> ait(availtns);
  for (int o = 0; o < tnsr.get_dim(10)*tnsr.get_dim(11); o++) {
    // new zero-point
    if (cf_zp) {
      for (int k = 0; k < ISIZE; k++) {
        vlist[state].push_back(zoit.read());
        zoit.next();
      }
      state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
    }
    // coefficients
    for (int i = 0; i < (int)tnsr.get_tens_size()/(tnsr.get_dim(10)*tnsr.get_dim(11))/ISIZE; i++) {
      if (coef_mode == coef_mode_compressed) {
        uint16_t m = 0;
        for (int k = 0; k < ISIZE; k++) {
          m |= ait.read() != 0 ? 1<<k : 0;
          ait.next();
        }
        // write avail bits
        vlist[state].push_back((coef_t)m);
        vlist[state].push_back((coef_t)(m>>8));
        // write non-zeros
        for (int k = 0; k < ISIZE; k++) {
          coef_t v = coit.read();
          coit.next();
          if ((m & (1 << k)) != 0) {
            vlist[state].push_back(v);
          }
        }
      } else if (cf_4b ) {
        for (int k = 0; k < ISIZE/2; k++) {
          coef_t v = (coef_t)(coit.read() & 0xf);
          coit.next();
          v |= coit.read()<<4;
          coit.next();
          vlist[state].push_back(v);
        }
      } else {
        for (int k = 0; k < ISIZE; k++) {
          vlist[state].push_back(coit.read());
          coit.next();
        }
      }
      state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
    }
  }
  queue_encode(vlist, obuf, olen, coef_mode);
}

// DINO(1x1), 8b feature-map, 8b coefficient, non-sparse, grouped
static void DINO(gfm8cf8ns_1x1)(const tensor_t<coef_t,6,xbuffer_t>&     icf,       // input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp], 8b only
                                const tensor_t<coef_t,1,xbuffer_t>&     izp,       // input zero-points [Cout]
                                xbuffer_t<coef_t>&                      tbuf,      // temporary xbuf
                                // attributes
                                coef_mode_t                             coef_mode, // coefficient compression mode uncompressed or compressed
                                bool                                    cf_4b,     // 4b coefficient encoding
                                bool                                    cf_zp,     // zero-point enable
                                // outputs, buffers preallocated by caller
                                xbuffer_t<ixpix_t>&                     obuf,      // output encoded coefficient tensor
                                size_t&                                 olen       // size of used coefficient buffer in ixpix_t
                                ) {
  // std::cout<<__FILE__<<" "<<__LINE__<<std::endl;
  // convert to [Grp=1][Cout][Fd][Fh][Fw][Cin]
  shape<6> shp0;
  shp0[0] = icf.get_dim(0)*icf.get_dim(5);
  shp0[1] = icf.get_dim(1);
  shp0[2] = icf.get_dim(2);
  shp0[3] = icf.get_dim(3);
  shp0[4] = icf.get_dim(4)*icf.get_dim(5);
  shp0[5] = 1;
  xbuffer_t<coef_t> cbuf = tbuf.split((size_t)get_shape_size(shp0));
  tensor_t<coef_t,6,xbuffer_t> tns0(cbuf, shp0);
  // initialize to zero-point
  tensor_iterator_t<coef_t,6,xbuffer_t>       tit0(tns0);
  const_tensor_iterator_t<coef_t,1,xbuffer_t> zit0(izp);
  for (int o = 0; o < shp0[4]; o++) {
    coef_t zp(zit0.read());
    zit0.next();
    if (!cf_zp) zp = 0;
    for (int i = 0; i < shp0[3]*shp0[2]*shp0[1]*shp0[0]; i++) {
      tit0.write(zp);
      tit0.next();
    }
  }
  // copy input
  const_tensor_iterator_t<coef_t,6,xbuffer_t> tit1(icf);
  for (int g = 0; g < icf.get_dim(5); g++) {
    for (int no = 0; no < icf.get_dim(4); no++) {
      for (int fd = 0; fd < icf.get_dim(3); fd++) {
        for (int fh = 0; fh < icf.get_dim(2); fh++) {
          for (int fw = 0; fw < icf.get_dim(1); fw++) {
            for (int ni = 0; ni < icf.get_dim(0); ni++) {
              coef_t cf(tit1.read());
              tit1.next();
              tns0.write({aoffset_t(g*icf.get_dim(0)+ni),
                             aoffset_t(fw),
                             aoffset_t(fh),
                             aoffset_t(fd),
                             aoffset_t(g*icf.get_dim(4)+no),
                             0}, 
                         cf);
            }
          }
        }
      }
    }
  }
  // normal encoder
  DINO(fm8cf8ns_1x1)(tns0, izp, tbuf, coef_mode, cf_4b, cf_zp, 1, 1, obuf, olen);
}

static inline void sparse_enc(coef_t zp,                                                // zero point
                              coef_t c_in0, coef_t c_in1, coef_t c_in2, coef_t c_in3,   // input 4 coefficients
                              coef_t& c_out0, coef_t& c_out1,                           // output 2 coefficients
                              coef_sel_t& c_sel0, coef_sel_t& c_sel1                    // output 2 selectors
                              ) {
  if ((c_in0 == zp) && (c_in1 == zp)) {
    c_sel0 = selfm23;
    c_sel1 = selfm23;
    c_out0 = c_in2;
    c_out1 = c_in3;
  }
  else if ((c_in0 == zp) && (c_in2 == zp)) {
    c_sel0 = selfm12;
    c_sel1 = selfm23;
    c_out0 = c_in1;
    c_out1 = c_in3;
  }
  else if ((c_in0 == zp) && (c_in3 == zp)) {
    c_sel0 = selfm12;
    c_sel1 = selfm12;
    c_out0 = c_in1;
    c_out1 = c_in2;
  }
  else if ((c_in1 == zp) && (c_in2 == zp)) {
    c_sel0 = selfm01;
    c_sel1 = selfm23;
    c_out0 = c_in0;
    c_out1 = c_in3;
  }
  else if ((c_in1 == zp) && (c_in3 == zp)) {
    c_sel0 = selfm01;
    c_sel1 = selfm12;
    c_out0 = c_in0;
    c_out1 = c_in2;
  }
  else if ((c_in2 == zp) && (c_in3 == zp)) {
    c_sel0 = selfm01;
    c_sel1 = selfm01;
    c_out0 = c_in0;
    c_out1 = c_in1;
  }
  else {
    assert(0); // at least two zero coefficients in one block
  }
}

// DINO(1x1), 8b feature-map, 8b coefficient, sparse
static void DINO(fm8cf8s_1x1)(const tensor_t<coef_t,6,xbuffer_t>&     icf,       // input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp], 8b only
                              const tensor_t<coef_t,1,xbuffer_t>&     izp,       // input zero-points [Cout]
                              xbuffer_t<coef_t>&                      tbuf,      // temporary xbuf
                              // attributes
                              bool                                    cf_zp,     // zero-point enable
                              // outputs, buffers preallocated by caller
                              xbuffer_t<ixpix_t>&                     obuf,      // output encoded coefficient tensor
                              size_t&                                 olen       // size of used coefficient buffer in ixpix_t
                              ) {
  // std::cout<<__FILE__<<" "<<__LINE__<<std::endl;
  int onn = 1;
  int inn = 2;
  // get shape size
  shape<6> shp0;
  shp0[0] = ((icf.get_dim(0)+2*inn*ISIZE-1)/(2*inn*ISIZE))*2*inn*ISIZE;     // round up to multiple of 2*inn*ISIZE
  shp0[1] = icf.get_dim(1);
  shp0[2] = icf.get_dim(2);
  shp0[3] = icf.get_dim(3);
  shp0[4] = ((icf.get_dim(4)+2*ISIZE-1)/(2*ISIZE))*2*ISIZE;                 // round up to multiple of 2*ISIZE
  shp0[5] = icf.get_dim(5);
  xbuffer_t<coef_t> cbuf = tbuf.split((size_t)get_shape_size(shp0)*2);
  xbuffer_t<coef_t> zbuf = tbuf.split((size_t)shp0[4]*shp0[5]       );
  tensor_t<coef_t,6,xbuffer_t> tns0(cbuf, shp0);
  tensor_t<coef_t,2,xbuffer_t> zp0(zbuf, {shp0[4],shp0[5]});
  // initialize to 0
  const_tensor_iterator_t<coef_t,6,xbuffer_t> iit(icf);
  tensor_iterator_t<coef_t,6,xbuffer_t>       cit0(tns0);
  const_tensor_iterator_t<coef_t,1,xbuffer_t> izit(izp);
  tensor_iterator_t<coef_t,2,xbuffer_t>       zit0(zp0);
  for (int g = 0; g < shp0[5]; g++) {
    for (int no = 0; no < shp0[4]; no++) {
      coef_t zp;
      if (no >= icf.get_dim(4) || (!cf_zp)) {
        zp = (coef_t)0;
      } else {
        zp = izit.read();
        izit.next();
      }
      zit0.write(zp);
      zit0.next();
      for (int qd = 0; qd < shp0[1]*shp0[2]*shp0[3]; qd++) {
        for (int ni = 0; ni < shp0[0]; ni++) {
          if (ni >= icf.get_dim(0) || no >= icf.get_dim(4)) {
            // pad with 0 coefficient
            cit0.write(zp);
          } else {
            cit0.write(iit.read());
            iit.next();
          }
          cit0.next();
        }
      }
    }
  }
  // [grp][no][fd][fh][fw][ni] --> [grp][no][fd][fh][fw][ni][inn2][b1][i8][iodd2]
  tensor_t<coef_t,7,xbuffer_t>  tns1(tns0.split(0, shp0[0]/(inn*2*8*2)));
  tensor_t<coef_t,8,xbuffer_t>  tns2(tns1.split(0, inn));
  tensor_t<coef_t,9,xbuffer_t>  tns3(tns2.split(0, 2));
  tensor_t<coef_t,10,xbuffer_t> tns4(tns3.split(0, 8));
  // [grp][no][fd][fh][fw][ni][inn][b1][i8][iodd2] --> [grp][no][onn][o2][o8][fd][fh][fw][ni][inn][b1][i8][iodd2]
  tensor_t<coef_t,11,xbuffer_t> tns5(tns4.split(8, shp0[4]/(onn*8*2*2))); //[no][onn*o8*o2*no2]
  tensor_t<coef_t,12,xbuffer_t> tns6(tns5.split(8, onn));                 //[no][onn][o8*o2]
  tensor_t<coef_t,13,xbuffer_t> tns7(tns6.split(8, 2));                   //[no][onn][no2][o8*o2]
  tensor_t<coef_t,14,xbuffer_t> tnst(tns7.split(8, 8));                   //[no][onn][o8][o2]
  // transpose [grp][no][onn][no2][o8][o2][fd][fh][fw][ni][inn][b1][i8][iodd2] -> [grp][no][ni][fd][fh][fw][inn][no2][onn][b1][o8][o2][i8][iodd2]
  tensor_t<coef_t,14,xbuffer_t> tns8(tnst.transpose({0/*iodd*/,1/*i8*/,8/*o2*/,9/*o8*/,2/*b1*/,11/*onn*/,10/*no2*/,3/*inn*/,5/*fw*/,6/*fh*/,7/*fd*/,4/*ni*/,12/*no*/,13/*grp*/}));
  // zero-point reorder [grp][no] -->  [grp][no][onn*o8][o2]
  tensor_t<coef_t,3,xbuffer_t>  zp1(zp0.split(0, shp0[4]/(onn*ISIZE*2))); //[grp][no][onn*o8*o2*no2]
  tensor_t<coef_t,4,xbuffer_t>  zp2(zp1.split(0, onn));                   //[grp][no][onn][o8*o2*no2]
  tensor_t<coef_t,5,xbuffer_t>  zpt(zp2.split(0, 2));                     //[grp][no][onn][no2][o8*o2]
  tensor_t<coef_t,6,xbuffer_t>  zp3(zpt.split(0, 8));                     //[grp][no][onn][no2][o8][o2]
  // zero-point transpose [grp][no][onn][no2][o8][o2] --> [grp][no][onn][no2][o8][o2]
  tensor_t<coef_t,6,xbuffer_t>  zp4(zp3.transpose({0,1,2,3,4,5}));
  //report(cout, tns8);
  //report(cout, zp4);
  //
  // Encode the sparsity bits
  //
  shape<14> encb_shp;
  encb_shp = tns8.get_shape();
  encb_shp[0] = tns8.get_dim(0)/2;  // output sparsity bits per 4 coefficients
  encb_shp[1] = tns8.get_dim(1)/2;
  shape<14> coef_shp;
  coef_shp = tns8.get_shape();
  coef_shp[0] = tns8.get_dim(0)/2; // output half coefficients
  xbuffer_t<uint8_t> encb_buf = tbuf.split<uint8_t>((size_t)get_shape_size(encb_shp)); // encode bits
  xbuffer_t<coef_t>  coef_buf = tbuf.split((size_t)get_shape_size(coef_shp)); // coefficients

  tensor_t<uint8_t,14,xbuffer_t>               encb_tns(encb_buf, encb_shp);
  tensor_t<coef_t,14,xbuffer_t>                coef_tns(coef_buf, coef_shp);
  tensor_iterator_t<uint8_t,14,xbuffer_t>      encb_it(encb_tns);
  tensor_iterator_t<coef_t,14,xbuffer_t>       coef_it(coef_tns);
  const_tensor_iterator_t<coef_t,14,xbuffer_t> eit(tns8);
  coef_t coef_in[8], coef_out[4];
  coef_sel_t sel[4];
  uint8_t encb_out;
  //[grp][ni][no][fd][fh][fw][inn][no2][onn][b1][o8][o2][i8][iodd2]
  for (int grp = 0; grp < tns8.get_dim(13); grp++) {
    for (int no = 0; no < tns8.get_dim(12); no++) {
      for (int ni = 0; ni < tns8.get_dim(11); ni++) {
       for (int fd = 0; fd < tns8.get_dim(10); fd++) {
        for (int fh = 0; fh < tns8.get_dim(9); fh++) {
         for (int fw = 0; fw < tns8.get_dim(8); fw++) {
         for (int inn = 0; inn < tns8.get_dim(7); inn++) {
          for (int no2 = 0; no2 < tns8.get_dim(6); no2++) {
           for (int onn = 0; onn < tns8.get_dim(5); onn++) {
             for (int b1 = 0; b1 < tns8.get_dim(4); b1++) {
               for (int o8 = 0; o8 < tns8.get_dim(3); o8++) {
                 for (int o2 = 0; o2 < tns8.get_dim(2); o2++) {
                   coef_t zp = cf_zp ? zp4.read({(int16_t)o2,(int16_t)o8,(int16_t)no2,(int16_t)onn,(int16_t)no,(int16_t)grp}) : (coef_t)0;
                   int16_t sz = tns8.get_dim(1)*tns8.get_dim(0); // i8*iodd2
                   for (int cg = 0; cg < sz/8; cg++) { // use 8 input coefficients to encode 4 output coefficients and 4 selectors (packed into 1 byte)
                     for (int ii=0; ii<8; ii++) {
                       coef_in[ii] = eit.read();
                       eit.next();
                     }
                     sparse_enc(zp, coef_in[0], coef_in[1], coef_in[2], coef_in[3], coef_out[0], coef_out[1], sel[0], sel[1]);
                     sparse_enc(zp, coef_in[4], coef_in[5], coef_in[6], coef_in[7], coef_out[2], coef_out[3], sel[2], sel[3]);
                     for (int jj=0; jj<4; jj++) {
                       coef_it.write(coef_out[jj]);
                       coef_it.next();
                     }
                     encb_out = ((uint8_t)sel[0] & (uint8_t)0x03) | (((uint8_t)sel[1] << 2) & (uint8_t)0x0c) | (((uint8_t)sel[2] << 4) & (uint8_t)0x30) | (((uint8_t)sel[3] << 6) & (uint8_t)0xc0);
                     encb_it.write(encb_out);
                     encb_it.next();
                   }
                 }
               }
             }
           }
          }
          }
         }
        }
       }
     }
    }
  }
  //report(cout,coef_tns);

  //
  // encode
  //
  array<list<coef_t>,NUM_COEF_QUEUE> vlist;
  int state = 0;
  const_tensor_iterator_t<uint8_t,14,xbuffer_t> encb_oit(encb_tns);
  const_tensor_iterator_t<coef_t,14,xbuffer_t>  coef_oit(coef_tns);
  const_tensor_iterator_t<coef_t,6,xbuffer_t>   zoit(zp4);
  int nnn  = 0;
  //[grp][no/2][ni][fd][fh][fw][inn][no2][onn][b1][o8][o2][i8][iodd2]
  //[grp][no/2][onn][no2][o8][o2]
  for (int grp = 0; grp < encb_tns.get_dim(13); grp++) {
    for (int no = 0; no < coef_tns.get_dim(12); no++) { //since new i64o32 will need zp sent just once
      // new zero-point: [grp][onn][no2][o8][o2][no]
      if (cf_zp) {
        for (int j = 0; j < zp4.get_dim(0)*zp4.get_dim(3)*zp4.get_dim(2)*zp4.get_dim(1)/ISIZE; j++) {
          //encode ISIZE zero-points
          for (int k = 0; k < ISIZE; k++) {
            vlist[state].push_back(zoit.read());
            zoit.next();
          }
          //switch queue
          state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
        }
      }

      // coefficients
      int32_t l_sz = tns8.get_dim(11)*tns8.get_dim(10)*tns8.get_dim(9)*tns8.get_dim(8)*tns8.get_dim(7)*tns8.get_dim(6);
      for (int ni = 0; ni < l_sz; ni++) {
        for (int onn = 0; onn < tns8.get_dim(5); onn++) {
          for (int b1 = 0; b1 < tns8.get_dim(4); b1++) {
            for (int o8 = 0; o8 < tns8.get_dim(3); o8++) {
              int16_t in_grp_sz = tns8.get_dim(2)*tns8.get_dim(1)*tns8.get_dim(0)/2; //(o2*i8*iodd2/2)
              // push 4 encoded sparsity bits (4 bytes) each time
              for (int e = 0; e < in_grp_sz/4; e++) {
                uint8_t encb_bits = encb_oit.read(); encb_oit.next();
                vlist[state].push_back((coef_t)(encb_bits&0xff));
              }
              // sparsity coefs: ISIZE*coefs
              // push 16 sparse coefs each time
              for (int e = 0; e < in_grp_sz; e++) {
                coef_t coef_data = coef_oit.read(); coef_oit.next();
                vlist[state].push_back(coef_data);
              }
              nnn++;
              //switch queue
              state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
            } //o8
          } //b1
        } //onn
      } //ni
    } //no
  } //grp

  queue_encode(vlist, obuf, olen, coef_mode_uncompressed);
}

// NINO(1x1), 8b feature-map, 8b coefficient, non-sparse
static void NINO(fm8cf8ns_1x1)(const tensor_t<coef_t,6,xbuffer_t>&     icf,       // input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp], 8b only
                               const tensor_t<coef_t,1,xbuffer_t>&     izp,       // input zero-points [Cout]
                               xbuffer_t<coef_t>&                      tbuf,      // temporary xbuf
                               // attributes
                               coef_mode_t                             coef_mode, // coefficient compression mode uncompressed or compressed or sparse
                               bool                                    cf_4b,     // 4b coefficient encoding
                               bool                                    cf_zp,     // zero-point enable
                               // outputs, buffers preallocated by caller
                               xbuffer_t<ixpix_t>&                     obuf,      // output encoded coefficient tensor
                               size_t&                                 olen       // size of used coefficient buffer in ixpix_t
                               ) {
  // std::cout<<__FILE__<<" "<<__LINE__<<std::endl;
  // get shape size
  shape<6> shp0;
  shp0[0] = ROUND_UP(icf.get_dim(0), ISIZE);     // round up to multiple of ISIZE
  shp0[1] = icf.get_dim(1);
  shp0[2] = icf.get_dim(2);
  shp0[3] = icf.get_dim(3);
  shp0[4] = ROUND_UP(icf.get_dim(4), ISIZE);     // round up to multiple of ISIZE
  shp0[5] = icf.get_dim(5);
  xbuffer_t<coef_t> cbuf = tbuf.split((size_t)get_shape_size(shp0));
  xbuffer_t<coef_t> zbuf = tbuf.split((size_t)shp0[4]*shp0[5]     );
  tensor_t<coef_t,6,xbuffer_t> tns0(cbuf, shp0);
  tensor_t<coef_t,2,xbuffer_t> zp0(zbuf, {shp0[4],shp0[5]});
  // initialize to 0
  const_tensor_iterator_t<coef_t,6,xbuffer_t>       iit(icf);
  tensor_iterator_t<coef_t,6,xbuffer_t>             cit0(tns0);
  const_tensor_iterator_t<coef_t,1,xbuffer_t>       izit(izp);
  tensor_iterator_t<coef_t,2,xbuffer_t>             zit0(zp0);
  for (int g = 0; g < shp0[5]; g++) {
    for (int no = 0; no < shp0[4]; no++) {
      coef_t zp;
      if (no >= icf.get_dim(4) || (!cf_zp)) {
        zp = (coef_t)0;
      } else {
        zp = izit.read();
        izit.next();
      }
      zit0.write(zp);
      zit0.next();
      for (int qd = 0; qd < shp0[1]*shp0[2]*shp0[3]; qd++) {
        for (int ni = 0; ni < shp0[0]; ni++) {
          coef_t cv;
          if (ni >= icf.get_dim(0) || no >= icf.get_dim(4)) {
            // pad with 0 coefficient
            cv   = zp;
          } else {
            cv   = iit.read();
            iit.next();
          }
          cit0.write(cv);
          cit0.next();
        }
      }
    }
  }
  //
  // target shape is [grp][no/16][ni/16][fd][fh][fw][iodd][o16][i8]
  //
  // [grp][no][fd][fh][fw][ni] --> [grp][no/16][o16][fd][fh][fw][ni/16][i8][iodd]
  tensor_t<coef_t,7,xbuffer_t>  tns1(tns0.split(0, shp0[0]/16));
  tensor_t<coef_t,8,xbuffer_t>  tns2(tns1.split(0, 8));
  tensor_t<coef_t,9,xbuffer_t>  tns3(tns2.split(6, shp0[4]/16));
  // transpose [grp][no/16][o16][fd][fh][fw][ni/16][i8][iodd] --> [grp][no/16][ni/16][fd][fh][fw][iodd][o16][i8]
  tensor_t<coef_t,9,xbuffer_t>  tnsr(tns3.transpose({1,6,0,3,4,5,2,7,8}));
  // zero-point reorder [grp][no] -->  [grp][no][o16]
  tensor_t<coef_t,3,xbuffer_t>  zpr(zp0.split(0, shp0[4]/ISIZE));

  //
  // Get the avail bits identifying which coefficients are equal to the zero-point
  //
  xbuffer_t<uint8_t> availbuf = tbuf.split<uint8_t>((size_t)tnsr.get_tens_size());
  tensor_t<uint8_t,9,xbuffer_t>               availtns(availbuf, tnsr.get_shape());
  tensor_iterator_t<uint8_t,9,xbuffer_t>      availit(availtns);
  const_tensor_iterator_t<coef_t,9,xbuffer_t> eit(tnsr);  // [grp][no/16][ni/16][fd][fh][fw][iodd][o16][i8]
  for (int grp = 0; grp < tnsr.get_dim(8); grp++) {
    for (int no = 0; no < tnsr.get_dim(7); no++) {
      for (int ni = 0; ni < tnsr.get_dim(3)*tnsr.get_dim(4)*tnsr.get_dim(5)*tnsr.get_dim(6); ni++) {
        for (int iodd = 0; iodd < 2; iodd++) {
          for (int o16 = 0; o16 < 16; o16++) {
            coef_t zp = cf_zp ? zpr.read({(int16_t)o16,(int16_t)no,(int16_t)grp}) : (coef_t)0;
            for (int ii = 0; ii < 8; ii++) {
              availit.write(eit.read() != zp);
              availit.next();
              eit.next();
            }
          }
        }
      }
    }
  }

  //
  // encode
  //
  array<list<coef_t>,NUM_COEF_QUEUE> vlist;
  int state = 0;
  const_tensor_iterator_t<coef_t,9,xbuffer_t>  coit(tnsr);
  const_tensor_iterator_t<coef_t,3,xbuffer_t>  zoit(zpr);
  const_tensor_iterator_t<uint8_t,9,xbuffer_t> ait(availtns);
  for (int o = 0; o < tnsr.get_dim(8)*tnsr.get_dim(7); o++) {
    // new zero-point
    if (cf_zp) {
      for (int k = 0; k < ISIZE; k++) {
        vlist[state].push_back(zoit.read());
        zoit.next();
      }
      state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
    }
    // coefficients
    for (int i = 0; i < (int)tnsr.get_tens_size()/(tnsr.get_dim(8)*tnsr.get_dim(7))/ISIZE; i++) {
      if (coef_mode == coef_mode_compressed) {
        uint16_t m = 0;
        for (int k = 0; k < ISIZE; k++) {
          m |= ait.read() != 0 ? 1<<k : 0;
          ait.next();
        }
        // write avail bits
        vlist[state].push_back((coef_t)m);
        vlist[state].push_back((coef_t)(m>>8));
        // write non-zeros
        for (int k = 0; k < ISIZE; k++) {
          coef_t v = coit.read();
          coit.next();
          if ((m & (1 << k)) != 0) {
            vlist[state].push_back(v);
          }
        }
      } else if (cf_4b) {
        for (int k = 0; k < ISIZE/2; k++) {
          coef_t v = (coef_t)(coit.read() & 0xf);
          coit.next();
          v |= coit.read() << 4;
          coit.next();
          vlist[state].push_back(v);
        }
      } else {
        for (int k = 0; k < ISIZE; k++) {
          vlist[state].push_back(coit.read());
          coit.next();
        }
      }
      state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
    }
  }
  queue_encode(vlist, obuf, olen, coef_mode);
}

// NINO(2x1), 8b feature-map, 8b coefficient, non-sparse
static void NINO(fm8cf8ns_2x1)(const tensor_t<coef_t,6,xbuffer_t>&     icf,       // input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp], 8b only
                               const tensor_t<coef_t,1,xbuffer_t>&     izp,       // input zero-points [Cout]
                               xbuffer_t<coef_t>&                      tbuf,      // temporary xbuf
                               // attributes
                               coef_mode_t                             coef_mode, // coefficient compression mode uncompressed or compressed or sparse
                               bool                                    cf_4b,     // 4b coefficient encoding
                               bool                                    cf_zp,     // zero-point enable
                               // outputs, buffers preallocated by caller
                               xbuffer_t<ixpix_t>&                     obuf,      // output encoded coefficient tensor
                               size_t&                                 olen       // size of used coefficient buffer in ixpix_t
                               ) {
  // std::cout<<__FILE__<<" "<<__LINE__<<std::endl;
  // get shape size
  shape<6> shp0;
  shp0[0] = ROUND_UP(icf.get_dim(0), ISIZE);     // round up to multiple of ISIZE
  shp0[1] = ROUND_UP(icf.get_dim(1), 2);         // round up to even
  shp0[2] = icf.get_dim(2);
  shp0[3] = icf.get_dim(3);
  shp0[4] = ROUND_UP(icf.get_dim(4), ISIZE);     // round up to multiple of ISIZE
  shp0[5] = icf.get_dim(5);
  xbuffer_t<coef_t> cbuf = tbuf.split((size_t)get_shape_size(shp0));
  xbuffer_t<coef_t> zbuf = tbuf.split((size_t)shp0[4]*shp0[5]     );
  tensor_t<coef_t,6,xbuffer_t> tns0(cbuf, shp0);
  tensor_t<coef_t,2,xbuffer_t> zp0(zbuf, {shp0[4],shp0[5]});
  // initialize to 0
  const_tensor_iterator_t<coef_t,6,xbuffer_t> iit(icf);
  tensor_iterator_t<coef_t,6,xbuffer_t>       cit0(tns0);
  const_tensor_iterator_t<coef_t,1,xbuffer_t> izit(izp);
  tensor_iterator_t<coef_t,2,xbuffer_t>       zit0(zp0);
  for (int g = 0; g < shp0[5]; g++) {
    for (int no = 0; no < shp0[4]; no++) {
      coef_t zp;
      if (no >= icf.get_dim(4) || (!cf_zp)) {
        zp = (coef_t)0;
      } else {
        zp = izit.read();
        izit.next();
      }
      zit0.write(zp);
      zit0.next();
      for (int qd = 0; qd < shp0[2]*shp0[3]; qd++) {
        for (int fw = 0; fw < shp0[1]; fw++) {
          for (int ni = 0; ni < shp0[0]; ni++) {
            coef_t cv;
            if (ni >= icf.get_dim(0) || fw >= icf.get_dim(1) || no >= icf.get_dim(4)) {
              // pad with 0 coefficient
              cv   = zp;
            } else {
              cv    = iit.read();
              iit.next();
            }
            cit0.write(cv);
            cit0.next();
          }
        }
      }
    }
  }
  //
  // target shape is [grp][no/16][ni/16][fd][fh][fw/2][iodd][w2][o16][i8]
  //
  // [grp][no][fd][fh][fw][ni] --> [grp][no/16][o16][fd][fh][fw/2][w2][ni/16]][i8][iodd]
  tensor_t<coef_t, 7,xbuffer_t>  tns1(tns0.split(0, shp0[0]/16));
  tensor_t<coef_t, 8,xbuffer_t>  tns2(tns1.split(0, 8));
  tensor_t<coef_t, 9,xbuffer_t>  tns3(tns2.split(3, shp0[1]/2));
  tensor_t<coef_t,10,xbuffer_t>  tns4(tns3.split(7, shp0[4]/16));
  // transpose [grp][no/16][o16][fd][fh][fw/2][w2][ni/16][i8][iodd] --> [grp][no][ni][fd][fh][fw/2][iodd][w2][o16][i8]
  tensor_t<coef_t,10,xbuffer_t>  tnsr(tns4.transpose({1,7,3,0,4,5,6,2,8,9}));
  // zero-point reorder [grp][no] -->  [grp][no][o16]
  tensor_t<coef_t,3,xbuffer_t>  zpr(zp0.split(0, shp0[4]/ISIZE));

  //
  // Get the avail bits identifying which coefficients are equal to the zero-point
  //
  xbuffer_t<uint8_t> availbuf = tbuf.split<uint8_t>((size_t)tnsr.get_tens_size());
  tensor_t<uint8_t,10,xbuffer_t>               availtns(availbuf, tnsr.get_shape());
  tensor_iterator_t<uint8_t,10,xbuffer_t>      availit(availtns);
  const_tensor_iterator_t<coef_t,10,xbuffer_t> eit(tnsr);
  for (int grp = 0; grp < tnsr.get_dim(9); grp++) {
    for (int no = 0; no < tnsr.get_dim(8); no++) {
      for (int ni = 0; ni < tnsr.get_dim(4)*tnsr.get_dim(5)*tnsr.get_dim(6)*tnsr.get_dim(7); ni++) {
        for (int iodd = 0; iodd < 2; iodd++) {
          for (int w = 0; w < 2; w++) {
            for (int o16 = 0; o16 < 16; o16++) {
              coef_t zp = cf_zp ? zpr.read({(int16_t)o16,(int16_t)no,(int16_t)grp}) : (coef_t)0;
              for (int ii = 0; ii < 8; ii++) {
                availit.write(eit.read() != zp);
                availit.next();
                eit.next();
              }
            }
          }
        }
      }
    }
  }

  //
  // encode
  //
  array<list<coef_t>,NUM_COEF_QUEUE> vlist;
  int state = 0;
  const_tensor_iterator_t<coef_t,10,xbuffer_t>  coit(tnsr);
  const_tensor_iterator_t<coef_t,3,xbuffer_t>   zoit(zpr);
  const_tensor_iterator_t<uint8_t,10,xbuffer_t> ait(availtns);
  for (int o = 0; o < tnsr.get_dim(9)*tnsr.get_dim(8); o++) {
    // new zero-point
    if (cf_zp) {
      for (int k = 0; k < ISIZE; k++) {
        vlist[state].push_back(zoit.read());
        zoit.next();
      }
      state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
    }
    // coefficients
    for (int i = 0; i < (int)tnsr.get_tens_size()/(tnsr.get_dim(9)*tnsr.get_dim(8))/ISIZE; i++) {
      if (coef_mode == coef_mode_compressed) {
        uint16_t m = 0;
        for (int k = 0; k < ISIZE; k++) {
          m |= ait.read() != 0 ? 1<<k : 0;
          ait.next();
        }
        // write avail bits
        vlist[state].push_back((coef_t)m);
        vlist[state].push_back((coef_t)(m>>8));
        // write non-zeros
        for (int k = 0; k < ISIZE; k++) {
          coef_t v = coit.read();
          coit.next();
          if ((m & (1 << k)) != 0) {
            vlist[state].push_back(v);
          }
        }
      } else if (cf_4b) {
        for (int k = 0; k < ISIZE/2; k++) {
          coef_t v = (coef_t)(coit.read()&0xf);
          coit.next();
          v |= coit.read() << 4;
          coit.next();
          vlist[state].push_back(v);
        }
      } else {
        for (int k = 0; k < ISIZE; k++) {
          coef_t v = coit.read();
          vlist[state].push_back(v);
          coit.next();
        }
      }
      state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
    }
  }

  queue_encode(vlist, obuf, olen, coef_mode);
}

// NINO(2x1), 8b feature-map, 8b coefficient, non-sparse
static void NINO(fm8cf8ns_2x1g2)(const tensor_t<coef_t,6,xbuffer_t>&     icf,       // input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp], 8b only
                                 const tensor_t<coef_t,1,xbuffer_t>&     izp,       // input zero-points [Cout]
                                 xbuffer_t<coef_t>&                      tbuf,      // temporary xbuf
                                 // attributes
                                 coef_mode_t                             coef_mode, // coefficient compression mode uncompressed or compressed or sparse
                                 bool                                    cf_4b,     // 4b coefficient encoding
                                 bool                                    cf_zp,     // zero-point enable
                                 // outputs, buffers preallocated by caller
                                 xbuffer_t<ixpix_t>&                     obuf,      // output encoded coefficient tensor
                                 size_t&                                 olen       // size of used coefficient buffer in ixpix_t
                                 ) {
  // std::cout<<__FILE__<<" "<<__LINE__<<std::endl;
  // get shape size
  shape<6> shp0;
  shp0[0] = ROUND_UP(icf.get_dim(0), 8);           // round up to multiple of 8
  shp0[1] = ROUND_UP(icf.get_dim(1), 2);           // round to even
  shp0[2] = icf.get_dim(2);
  shp0[3] = icf.get_dim(3);
  shp0[4] = ROUND_UP(icf.get_dim(4), 8);           // round up to multiple of 8
  shp0[5] = ROUND_UP(icf.get_dim(5), 2);           // even number of groups
  assert(shp0[0] == 8 && shp0[4] == 8);
  xbuffer_t<coef_t> cbuf = tbuf.split((size_t)get_shape_size(shp0));
  xbuffer_t<coef_t> zbuf = tbuf.split((size_t)shp0[4]*shp0[5]     );
  tensor_t<coef_t,6,xbuffer_t> tns0(cbuf, shp0);
  tensor_t<coef_t,2,xbuffer_t> zp0(zbuf, {shp0[4],shp0[5]});
  // initialize to 0
  const_tensor_iterator_t<coef_t,6,xbuffer_t> iit(icf);
  tensor_iterator_t<coef_t,6,xbuffer_t>       cit0(tns0);
  const_tensor_iterator_t<coef_t,1,xbuffer_t> izit(izp);
  tensor_iterator_t<coef_t,2,xbuffer_t>       zit0(zp0);
  for (int g = 0; g < shp0[5]; g++) {
    for (int no = 0; no < shp0[4]; no++) {
      coef_t zp;
      if (no >= icf.get_dim(4) || g >= icf.get_dim(5) || (!cf_zp)) {
        zp = (coef_t)0;
      } else {
        zp = izit.read();
        izit.next();
      }
      zit0.write(zp);
      zit0.next();
      for (int qd = 0; qd < shp0[2]*shp0[3]; qd++) {
        for (int w = 0; w < shp0[1]; w++) {
          for (int ni = 0; ni < shp0[0]; ni++) {
            coef_t cv;
            if (ni >= icf.get_dim(0) || no >= icf.get_dim(4) || g >= icf.get_dim(5) || w >= icf.get_dim(1)) {
              // pad with 0 coefficient
              cv   = zp;
            } else {
              cv  = iit.read();
              iit.next();
            }
            cit0.write(cv);
            cit0.next();
          }
        }
      }
    }
  }
  //
  // target shape is [grp/2][no/8][ni/8][fd][fh][fw/2][iodd][g2][o8][w2][i4]
  //
  // [grp][no][fd][fh][fw][ni] --> [grp/2][g2][no/8][o8][fd][fh][fw/2][w2][ni/8][i4][iodd]
  tensor_t<coef_t, 7,xbuffer_t>  tns1(tns0.split(0, shp0[0]/8));
  tensor_t<coef_t, 8,xbuffer_t>  tns2(tns1.split(0, 4));
  tensor_t<coef_t, 9,xbuffer_t>  tns3(tns2.split(3, shp0[1]/2));
  tensor_t<coef_t,10,xbuffer_t>  tns4(tns3.split(7, shp0[4]/8));
  tensor_t<coef_t,11,xbuffer_t>  tns5(tns4.split(9, shp0[5]/2));
  // transpose [grp/2][g2][no/8][o8][fd][fh][fw/2][w2][ni/8][i4][iodd] --> [grp/2][no/8][ni/8][fd][fh][fw/2][iodd][g2][o8][w2][i4]
  tensor_t<coef_t,11,xbuffer_t>  tnsr(tns5.transpose({1,3,7,9,0,4,5,6,2,8,10}));
  // zero-point reorder [grp][no] -->  [grp][g2][no/8][o8]
  tensor_t<coef_t,3,xbuffer_t>  zp1(zp0.split(0, shp0[4]/8));
  tensor_t<coef_t,4,xbuffer_t>  zp2(zp1.split(2, shp0[5]/2));
  // zero-point transpose [grp/2][g2][no/8][o8] --> [grp/2][no/8][g2][o8]
  tensor_t<coef_t,4,xbuffer_t>  zpr(zp2.transpose({0,2,1,3}));

  //
  // Get the avail bits identifying which coefficients are equal to the zero-point
  //
  xbuffer_t<uint8_t> availbuf = tbuf.split<uint8_t>((size_t)tnsr.get_tens_size());
  tensor_t<uint8_t,11,xbuffer_t>               availtns(availbuf, tnsr.get_shape());
  tensor_iterator_t<uint8_t,11,xbuffer_t>      availit(availtns);
  const_tensor_iterator_t<coef_t,11,xbuffer_t> eit(tnsr);
  for (int grp = 0; grp < tnsr.get_dim(10); grp++) {
    for (int no = 0; no < tnsr.get_dim(9); no++) {
      for (int ni = 0; ni < 2*tnsr.get_dim(5)*tnsr.get_dim(6)*tnsr.get_dim(7)*tnsr.get_dim(8); ni++) {
        for (int g2 = 0; g2 < 2; g2++) {
          for (int o8 = 0; o8 < 8; o8++) {
            coef_t zp = cf_zp ? zpr.read({(int16_t)o8,(int16_t)g2,(int16_t)no,(int16_t)grp}) : (coef_t)0;
            for (int ii = 0; ii < 8; ii++) {
              availit.write(eit.read() != zp);
              availit.next();
              eit.next();
            }
          }
        }
      }
    }
  }

  //
  // encode
  //
  array<list<coef_t>,NUM_COEF_QUEUE> vlist;
  int state = 0;
  const_tensor_iterator_t<coef_t,11,xbuffer_t>  coit(tnsr);
  const_tensor_iterator_t<coef_t,4,xbuffer_t>   zoit(zpr);
  const_tensor_iterator_t<uint8_t,11,xbuffer_t> ait(availtns);
  for (int o = 0; o < tnsr.get_dim(10)*tnsr.get_dim(9); o++) {
    // new zero-point
    if (cf_zp) {
      for (int k = 0; k < ISIZE; k++) {
        vlist[state].push_back(zoit.read());
        zoit.next();
      }
      state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
    }
    // coefficients
    for (int i = 0; i < (int)tnsr.get_tens_size()/(tnsr.get_dim(10)*tnsr.get_dim(9))/ISIZE; i++) {
      if (coef_mode == coef_mode_compressed) {
        uint16_t m = 0;
        for (int k = 0; k < ISIZE; k++) {
          m |= ait.read() != 0 ? 1<<k : 0;
          ait.next();
        }
        // write avail bits
        vlist[state].push_back((coef_t)m);
        vlist[state].push_back((coef_t)(m>>8));
        // write non-zeros
        for (int k = 0; k < ISIZE; k++) {
          coef_t v = coit.read();
          coit.next();
          if ((m & (1 << k)) != 0) {
            vlist[state].push_back(v);
          }
        }
      } else if (cf_4b) {
        for (int k = 0; k < ISIZE/2; k++) {
          coef_t v = (coef_t)(coit.read() & 0xf);
          coit.next();
          v |= coit.read() << 4;
          coit.next();
          vlist[state].push_back(v);
        }
      } else {
        for (int k = 0; k < ISIZE; k++) {
          coef_t v = coit.read();
          vlist[state].push_back(v);
          coit.next();
        }
      }
      state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
    }
  }
  queue_encode(vlist, obuf, olen, coef_mode);
}

// NINO(4x1), 8b feature-map, 8b coefficient, non-sparse
static void NINO(fm8cf8ns_4x1g2)(const tensor_t<coef_t,6,xbuffer_t>&     icf,       // input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp], 8b only
                                 const tensor_t<coef_t,1,xbuffer_t>&     izp,       // input zero-points [Cout]
                                 xbuffer_t<coef_t>&                      tbuf,      // temporary xbuf
                                 // attributes
                                 coef_mode_t                             coef_mode, // coefficient compression mode uncompressed or compressed or sparse
                                 bool                                    cf_4b,     // 4b coefficient encoding
                                 bool                                    cf_zp,     // zero-point enable
                                 // outputs, buffers preallocated by caller
                                 xbuffer_t<ixpix_t>&                     obuf,      // output encoded coefficient tensor
                                 size_t&                                 olen       // size of used coefficient buffer in ixpix_t
                                 ) {
  // std::cout<<__FILE__<<" "<<__LINE__<<std::endl;
  // get shape size
  shape<6> shp0;
  shp0[0] = ROUND_UP(icf.get_dim(0), 8);     // round up to 8
  shp0[1] = ROUND_UP(icf.get_dim(1), 4);     // round up to 4
  shp0[2] = icf.get_dim(2);
  shp0[3] = icf.get_dim(3);
  shp0[4] = ROUND_UP(icf.get_dim(4), 8);     // round up to 8
  shp0[5] = ROUND_UP(icf.get_dim(5), 2);     // round up to even
  xbuffer_t<coef_t> cbuf = tbuf.split((size_t)get_shape_size(shp0));
  xbuffer_t<coef_t> zbuf = tbuf.split((size_t)shp0[4]*shp0[5]     );
  tensor_t<coef_t,6,xbuffer_t> tns0(cbuf, shp0);
  tensor_t<coef_t,2,xbuffer_t> zp0(zbuf, {shp0[4],shp0[5]});
  // initialize to 0
  const_tensor_iterator_t<coef_t,6,xbuffer_t> iit(icf);
  tensor_iterator_t<coef_t,6,xbuffer_t>       cit0(tns0);
  const_tensor_iterator_t<coef_t,1,xbuffer_t> izit(izp);
  tensor_iterator_t<coef_t,2,xbuffer_t>       zit0(zp0);
  for (int g = 0; g < shp0[5]; g++) {
    for (int no = 0; no < shp0[4]; no++) {
      coef_t zp;
      if (no >= icf.get_dim(4) || g >= icf.get_dim(5) || (!cf_zp)) {
        zp = (coef_t)0;
      } else {
        zp = izit.read();
        izit.next();
      }
      zit0.write(zp);
      zit0.next();
      for (int qd = 0; qd < shp0[2]*shp0[3]; qd++) {
        for (int w = 0; w < shp0[1]; w++) {
          for (int ni = 0; ni < shp0[0]; ni++) {
            coef_t cv;
            if (ni >= icf.get_dim(0) || no >= icf.get_dim(4) || g >= icf.get_dim(5) || w >= icf.get_dim(1)) {
              // pad with 0 coefficient
              cv   = zp;
            } else {
              cv   = iit.read();
              iit.next();
            }
            cit0.write(cv);
            cit0.next();
          }
        }
      }
    }
  }

  //
  // target shape is [grp/2][no/8][ni/8][fd][fh][fw/4][iodd][wo2][g2][o8][wi2][i4]
  //
  // [grp][no][fd][fh][fw][ni] --> [grp/2][g2][no/8][o8][fd][fh][fw/4][wo2][wi2][ni/8][i4][iodd]
  tensor_t<coef_t, 7,xbuffer_t>  tns1(tns0.split(0, shp0[0]/8));
  tensor_t<coef_t, 8,xbuffer_t>  tns2(tns1.split(0, 4));
  tensor_t<coef_t, 9,xbuffer_t>  tns3(tns2.split(3, shp0[1]/4));
  tensor_t<coef_t,10,xbuffer_t>  tns4(tns3.split(3, 2));
  tensor_t<coef_t,11,xbuffer_t>  tns5(tns4.split(8, shp0[4]/8));
  tensor_t<coef_t,12,xbuffer_t>  tns6(tns5.split(10, shp0[5]/2));
  // transpose [grp/2][g2][no/8][o8][fd][fh][fw/4][wo2][wi2][ni/8][i4][iodd] --> [grp/2][no/8][ni/8][fd][fh][fw/4][iodd][wo2][g2][o8][wi2][i4]
  tensor_t<coef_t,12,xbuffer_t>  tnsr(tns6.transpose({1,3,8,10,4,0,5,6,7,2,9,11}));
  // zero-point reorder [grp][no] -->  [grp/2][g2][no/8][o8]
  tensor_t<coef_t,3,xbuffer_t>  zp1(zp0.split(0, shp0[4]/8));
  tensor_t<coef_t,4,xbuffer_t>  zp2(zp1.split(2, shp0[5]/2));
  // zero-point transpose [grp/2][g2][no/8][o8] --> [grp/2][no/8][g2][o8]
  tensor_t<coef_t,4,xbuffer_t>  zpr(zp2.transpose({0,2,1,3}));

  //
  // Get the avail bits identifying which coefficients are equal to the zero-point
  //
  xbuffer_t<uint8_t> availbuf = tbuf.split<uint8_t>((size_t)tnsr.get_tens_size());
  tensor_t<uint8_t,12,xbuffer_t>               availtns(availbuf, tnsr.get_shape());
  tensor_iterator_t<uint8_t,12,xbuffer_t>      availit(availtns);
  const_tensor_iterator_t<coef_t,12,xbuffer_t> eit(tnsr);
  for (int grp = 0; grp < tnsr.get_dim(11); grp++) {
    for (int no = 0; no < tnsr.get_dim(10); no++) {
      for (int ni = 0; ni < tnsr.get_dim(4)*tnsr.get_dim(5)*tnsr.get_dim(6)*tnsr.get_dim(7)*tnsr.get_dim(8)*tnsr.get_dim(9); ni++) {
        for (int g2 = 0; g2 < 2; g2++) {
          for (int o8 = 0; o8 < 8; o8++) {
            coef_t zp = cf_zp ? zpr.read({(int16_t)o8,(int16_t)g2,(int16_t)no,(int16_t)grp}) : (coef_t)0;
            for (int ii = 0; ii < 8; ii++) {
              availit.write(eit.read() != zp);
              availit.next();
              eit.next();
            }
          }
        }
      }
    }
  }

  //
  // encode
  //
  array<list<coef_t>,NUM_COEF_QUEUE> vlist;
  int state = 0;
  const_tensor_iterator_t<coef_t,12,xbuffer_t>  coit(tnsr);
  const_tensor_iterator_t<coef_t,4,xbuffer_t>   zoit(zpr);
  const_tensor_iterator_t<uint8_t,12,xbuffer_t> ait(availtns);
  for (int o = 0; o < tnsr.get_dim(11)*tnsr.get_dim(10); o++) {
    // new zero-point
    if (cf_zp) {
      for (int k = 0; k < ISIZE; k++) {
        vlist[state].push_back(zoit.read());
        zoit.next();
      }
      state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
    }
    // coefficients
    for (int i = 0; i < (int)tnsr.get_tens_size()/(tnsr.get_dim(11)*tnsr.get_dim(10))/ISIZE; i++) {
      if (coef_mode == coef_mode_compressed) {
        uint16_t m = 0;
        for (int k = 0; k < ISIZE; k++) {
          m |= ait.read() != 0 ? 1<<k : 0;
          ait.next();
        }
        // write avail bits
        vlist[state].push_back((coef_t)m);
        vlist[state].push_back((coef_t)(m>>8));
        // write non-zeros
        for (int k = 0; k < ISIZE; k++) {
          coef_t v = coit.read();
          coit.next();
          if ((m & (1 << k)) != 0) {
            vlist[state].push_back(v);
          }
        }
      } else if (cf_4b) {
        for (int k = 0; k < ISIZE/2; k++) {
          coef_t v = (coef_t)(coit.read() & 0xf);
          coit.next();
          v |= coit.read()<<4;
          coit.next();
          vlist[state].push_back(v);
        }
      } else {
        for (int k = 0; k < ISIZE; k++) {
          coef_t v = coit.read();
          vlist[state].push_back(v);
          coit.next();
        }
      }
      state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
    }
  }
  queue_encode(vlist, obuf, olen, coef_mode);
}

static void FC(fm8cf8ns)(const tensor_t<coef_t,3,xbuffer_t>&     icf,       // input coefficients [Grp][Cout][Cin], 8b only
                         const tensor_t<coef_t,1,xbuffer_t>&     izp,       // input zero-points [Cout]
                         xbuffer_t<coef_t>&                      tbuf,      // temporary xbuf
                         // attributes
                         int                                     vs,        // VSIZE
                         coef_mode_t                             coef_mode, // coefficient compression mode uncompressed or compressed or sparse
                         bool                                    cf_4b,     // 4b coefficient encoding
                         bool                                    cf_zp,     // zero-point enable
                         // outputs, buffers preallocated by caller
                         xbuffer_t<ixpix_t>&                     obuf,      // output encoded coefficient tensor
                         size_t&                                 olen       // size of used coefficient buffer in ixpix_t
                         ) {
  // get shape size
  shape<3> shp0;
  shp0[0] = ROUND_UP(icf.get_dim(0), ISIZE);         // round up to multiple of ISIZE
  shp0[1] = ROUND_UP(icf.get_dim(1), vs*ISIZE);      // round up to multiple of VSIZE*ISIZE
  shp0[2] = icf.get_dim(2);
  xbuffer_t<coef_t> cbuf = tbuf.split((size_t)get_shape_size(shp0));
  xbuffer_t<coef_t> zbuf = tbuf.split((size_t)shp0[1]*shp0[2]     );
  tensor_t<coef_t,3,xbuffer_t> tns0(cbuf, shp0);
  tensor_t<coef_t,2,xbuffer_t> zp0(zbuf, {shp0[1],shp0[2]});
  // initialize to 0
  const_tensor_iterator_t<coef_t,3,xbuffer_t> iit(icf);
  tensor_iterator_t<coef_t,3,xbuffer_t>       cit0(tns0);
  const_tensor_iterator_t<coef_t,1,xbuffer_t> izit(izp);
  tensor_iterator_t<coef_t,2,xbuffer_t>       zit0(zp0);
  for (int g = 0; g < shp0[2]; g++) {
    for (int no = 0; no < shp0[1]; no++) {
      coef_t zp;
      if (no >= icf.get_dim(1) || (!cf_zp)) {
        zp = (coef_t)0;
      } else {
        zp = izit.read();
        izit.next();
      }
      zit0.write(zp);
      zit0.next();
      for (int ni = 0; ni < shp0[0]; ni++) {
        coef_t cv;
        if (ni >= icf.get_dim(0) || no >= icf.get_dim(1)) {
          // pad with 0 coefficient
          cv   = zp;
        } else {
          cv = iit.read();
          iit.next();
        }
        cit0.write(cv);
        cit0.next();
      }
    }
  }

  //
  // target shape is [grp][no/(VSIZE*ISIZE)][ni/16][vo8][iodd][o16][i8]
  //
  // [grp][no][ni] --> [grp][no/(VSIZE*ISIZE)][vo8][o16][ni/16][i8][iodd]
  tensor_t<coef_t,4,xbuffer_t>  tns1(tns0.split(0, shp0[0]/16));
  tensor_t<coef_t,5,xbuffer_t>  tns2(tns1.split(0, 8));
  tensor_t<coef_t,6,xbuffer_t>  tns3(tns2.split(3, shp0[1]/(vs*ISIZE)));
  tensor_t<coef_t,7,xbuffer_t>  tns4(tns3.split(3, vs));
  // transpose [grp][no/(VSIZE*ISIZE)][vo8][o16][ni/16][i8][iodd] --> [grp][no/(VSIZE*ISIZE)][ni/16][vo8][iodd][o16][i8]
  tensor_t<coef_t,7,xbuffer_t>  tnsr(tns4.transpose({1,3,0,4,2,5,6}));
  // zero-point reorder [grp][no] -->  [grp][no/(VSIZE*ISIZE)][vo8][o16]
  tensor_t<coef_t,3,xbuffer_t>  zp1(zp0.split(0, shp0[1]/(vs*ISIZE)));
  tensor_t<coef_t,4,xbuffer_t>  zpr(zp1.split(0, vs));

  xbuffer_t<uint8_t> availbuf = tbuf.split<uint8_t>((size_t)tnsr.get_tens_size());
  tensor_t<uint8_t,7,xbuffer_t>               availtns(availbuf, tnsr.get_shape());
  tensor_iterator_t<uint8_t,7,xbuffer_t>      availit(availtns);
  const_tensor_iterator_t<coef_t,7,xbuffer_t> eit(tnsr);
  for (int g = 0; g < tnsr.get_dim(6); g++) {
    for (int no = 0; no < tnsr.get_dim(5); no++) {
      for (int ni = 0; ni < tnsr.get_dim(4); ni++) {
        for (int vo8 = 0; vo8 < vs; vo8++) {
          for (int iodd = 0; iodd < 2; iodd++) {
            for (int o16 = 0; o16 < 16; o16++) {
              coef_t zp = cf_zp ? zpr.read({(int16_t)o16,(int16_t)vo8,(int16_t)no,(int16_t)g}) : (coef_t)0;
              for (int ii = 0; ii < 8; ii++) {
                availit.write(eit.read() != zp);
                availit.next();
                eit.next();
              }
            }
          }
        }
      }
    }
  }

  //
  // encode
  //
  array<list<coef_t>,NUM_COEF_QUEUE> vlist;
  int state = 0;
  const_tensor_iterator_t<coef_t,7,xbuffer_t>  coit(tnsr);
  const_tensor_iterator_t<coef_t,4,xbuffer_t>  zoit(zpr);
  const_tensor_iterator_t<uint8_t,7,xbuffer_t> ait(availtns);
  for (int o = 0; o < tnsr.get_dim(6)*tnsr.get_dim(5); o++) {
    if (cf_zp) {
      for (int c = 0; c < vs; c++) {
        for (int k = 0; k < ISIZE; k++) {
          vlist[state].push_back(zoit.read());
          zoit.next();
        }
        state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
      }
    }
    
    // coefficients
    for (int i = 0; i < (int)tnsr.get_tens_size()/(tnsr.get_dim(6)*tnsr.get_dim(5))/ISIZE; i++) {
      if (coef_mode == coef_mode_compressed) {
        uint16_t m = 0;
        for (int k = 0; k < ISIZE; k++) {
          m |= ait.read() != 0 ? 1<<k : 0;
          ait.next();
        }
        // write avail bits
        vlist[state].push_back((coef_t)m);
        vlist[state].push_back((coef_t)(m>>8));
        // write non-zeros
        for (int k = 0; k < ISIZE; k++) {
          coef_t v = coit.read();
          coit.next();
          if ((m & (1 << k)) != 0) {
            vlist[state].push_back(v);
          }
        }
      } else if (cf_4b) {
        for (int k = 0; k < ISIZE/2; k++) {
          coef_t v = (coef_t)(coit.read() & 0xf);
          coit.next();
          v |= coit.read()<<4;
          coit.next();
          vlist[state].push_back(v);
        }
      } else {
        for (int k = 0; k < ISIZE; k++) {
          vlist[state].push_back(coit.read());
          coit.next();
        }
      }
      state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
    }
  }
  queue_encode(vlist, obuf, olen, coef_mode);
}

// sparse encoder
static void FC(fm8cf8s)(const tensor_t<coef_t,3,xbuffer_t>&     icf,       // input coefficients [Grp][Cout][Cin], 8b only
                        const tensor_t<coef_t,1,xbuffer_t>&     izp,       // input zero-points [Cout]
                        xbuffer_t<coef_t>&                      tbuf,      // temporary xbuf
                        // attributes
                        int                                     vs,        // VSIZE
                        bool                                    cf_zp,     // zero-point enable
                        // outputs, buffers preallocated by caller
                        xbuffer_t<ixpix_t>&                     obuf,      // output encoded coefficient tensor
                        size_t&                                 olen       // size of used coefficient buffer in ixpix_t
                        ) {
  shape<3> shp0;
  shp0[0] = ROUND_UP(icf.get_dim(0), ISIZE);         // round up to multiple of ISIZE
  shp0[1] = ROUND_UP(icf.get_dim(1), vs*ISIZE);      // round up to multiple of (VSIZE*ISIZE)
  shp0[2] = icf.get_dim(2);
  xbuffer_t<coef_t> cbuf = tbuf.split((size_t)get_shape_size(shp0));
  xbuffer_t<coef_t> zbuf = tbuf.split((size_t)shp0[1]*shp0[2]       );

  tensor_t<coef_t,3,xbuffer_t> tns0(cbuf, shp0);
  tensor_t<coef_t,2,xbuffer_t> zp0(zbuf, {shp0[1],shp0[2]});
  // initialize to 0
  const_tensor_iterator_t<coef_t,3,xbuffer_t> iit(icf);
  tensor_iterator_t<coef_t,3,xbuffer_t>       cit0(tns0);
  const_tensor_iterator_t<coef_t,1,xbuffer_t> izit(izp);
  tensor_iterator_t<coef_t,2,xbuffer_t>       zit0(zp0);
  for (int g = 0; g < shp0[2]; g++) {
    for (int no = 0; no < shp0[1]; no++) {
      coef_t zp;
      if (no >= icf.get_dim(1) || (!cf_zp)) {
        zp = (coef_t)0;
      } else {
        zp = izit.read();
        izit.next();
      }
      zit0.write(zp);
      zit0.next();
      for (int ni = 0; ni < shp0[0]; ni++) {
        coef_t cv;
        if (ni >= icf.get_dim(0) || no >= icf.get_dim(1)) {
          // pad with 0 coefficient
          cv   = zp;
        } else {
          cv = iit.read();
          iit.next();
        }
        cit0.write(cv);
        cit0.next();
      }

    }
  }
  //
  // target shape is [grp][no/256][ni/16][vo8][osparse][b1][o8][o2][i8][iodd]
  //

  // [grp][no][ni] --> [grp][no/256][ni/16][vo8][osparse][b1][o8][o2][i8][iodd]
  tensor_t<coef_t,4,xbuffer_t>  tns1(tns0.split(0, shp0[0]/(1*8*2)));
  tensor_t<coef_t,5,xbuffer_t>  tns2(tns1.split(0, 1));
  tensor_t<coef_t,6,xbuffer_t>  tns3(tns2.split(0, 8)); // [grp][no][ni/16][b1][i8][iodd]
  tensor_t<coef_t,7,xbuffer_t>  tns4(tns3.split(4, shp0[1]/(vs*ISIZE*2))); // [grp][no/256][o256][ni/16][b1][i8][iodd]
  tensor_t<coef_t,8,xbuffer_t>  tns5(tns4.split(4, 2)); // [grp][no/256][ospase][o128][ni/16][b1][i8][iodd]
  tensor_t<coef_t,9,xbuffer_t>  tns6(tns5.split(4, vs));
  tensor_t<coef_t,10,xbuffer_t>  tns7(tns6.split(4, 8));   // [grp][no/256][osparse][vo8][o8][o2][ni/16][b1][i8][iodd]
  // transpose [grp][no/256][osparse][vo8][o8][o2][ni/16][b1][i8][iodd] --> [grp][no/256][ni/16][vo8][osparse][b1][o8][o2][i8][iodd]
  tensor_t<coef_t,10,xbuffer_t>  tnsr(tns7.transpose({0,1,4,5,2,7,6,3,8,9}));
  // zero-point reorder [grp][no] -->  [grp][no/256][vo8][osparse][o16]
  tensor_t<coef_t,3,xbuffer_t>  zp1(zp0.split(0, shp0[1]/(vs*ISIZE*2))); // [grp][no/256][o256]
  tensor_t<coef_t,4,xbuffer_t>  zp2(zp1.split(0, 2));  // [grp][no/256][osparse][o128]
  tensor_t<coef_t,5,xbuffer_t>  zp3(zp2.split(0, vs));  // [grp][no/256][osparse][vo8][o16]
  tensor_t<coef_t,5,xbuffer_t>  zpr(zp3.transpose({0,2,1,3,4}));  // [grp][no/256][vo8][osparse][o16]

  //report(cout, zpr);
  //report(cout, tnsr);
  //
  // Encode the sparsity bits
  //
  shape<10> encb_shp;
  encb_shp = tnsr.get_shape();
  encb_shp[0] = tnsr.get_dim(0)/2;  // output sparsity bits per 4 coefficients
  encb_shp[1] = tnsr.get_dim(1)/2;
  shape<10> coef_shp;
  coef_shp = tnsr.get_shape();
  coef_shp[0] = tnsr.get_dim(0)/2; // output half coefficients
  xbuffer_t<uint8_t> encb_buf = tbuf.split<uint8_t>((size_t)get_shape_size(encb_shp)); // encode bits
  xbuffer_t<coef_t>  coef_buf = tbuf.split((size_t)get_shape_size(coef_shp)); // coefficients

  tensor_t<uint8_t,10,xbuffer_t>               encb_tns(encb_buf, encb_shp);
  tensor_t<coef_t,10,xbuffer_t>                coef_tns(coef_buf, coef_shp);
  tensor_iterator_t<uint8_t,10,xbuffer_t>      encb_it(encb_tns);
  tensor_iterator_t<coef_t,10,xbuffer_t>       coef_it(coef_tns);
  const_tensor_iterator_t<coef_t,10,xbuffer_t> eit(tnsr);
  coef_t coef_in[9], coef_out[4];
  coef_sel_t sel[4];
  uint8_t encb_out;
  //[grp][no/256][ni/16][vo8][osparse][b1][o8][o2][i8][iodd]
  for (int g = 0; g < tnsr.get_dim(9); g++) {
    for (int no = 0; no < tnsr.get_dim(8); no++) {
      for (int ni = 0; ni < tnsr.get_dim(7); ni++) {
        for (int vo8 = 0; vo8 < tnsr.get_dim(6); vo8++) {
          for (int os = 0; os < tnsr.get_dim(5); os++) {
            for (int b1 = 0; b1 < tnsr.get_dim(4); b1++) {
              for (int o16 = 0; o16 < tnsr.get_dim(3)*tnsr.get_dim(2); o16++) {
                coef_t zp = cf_zp ? zpr.read({(int16_t)o16,(int16_t)os,(int16_t)vo8,(int16_t)no,(int16_t)g}) : (coef_t)0;
                int16_t sz = tnsr.get_dim(1)*tnsr.get_dim(0); // i8*iodd2
                for (int cg = 0; cg < sz/8; cg++) { // use 8 input coefficients to encode 4 output coefficients and 4 selectors (packed into 1 byte)
                  for (int ii=0; ii<8; ii++) {
                    coef_in[ii] = eit.read();
                    eit.next();
                  }
                  sparse_enc(zp, coef_in[0], coef_in[1], coef_in[2], coef_in[3], coef_out[0], coef_out[1], sel[0], sel[1]);
                  sparse_enc(zp, coef_in[4], coef_in[5], coef_in[6], coef_in[7], coef_out[2], coef_out[3], sel[2], sel[3]);
                  for (int jj=0; jj<4; jj++) {
                    coef_it.write(coef_out[jj]);
                    coef_it.next();
                  }
                  encb_out = ((uint8_t)sel[0] & (uint8_t)0x03) | (((uint8_t)sel[1] << 2) & (uint8_t)0x0c) | (((uint8_t)sel[2] << 4) & (uint8_t)0x30) | (((uint8_t)sel[3] << 6) & (uint8_t)0xc0);
                  encb_it.write(encb_out);
                  encb_it.next();
                }
              }
            }
          }
        }
      }
    }
  }
  
 

  //
  // encode
  //
  array<list<coef_t>,NUM_COEF_QUEUE> vlist;
  int state = 0;
  const_tensor_iterator_t<uint8_t,10,xbuffer_t> encb_oit(encb_tns);
  const_tensor_iterator_t<coef_t,10,xbuffer_t>  coef_oit(coef_tns);
  const_tensor_iterator_t<coef_t,5,xbuffer_t>  zoit(zpr);
  for (int o = 0; o < tnsr.get_dim(9)*tnsr.get_dim(8); o++) {
    if (cf_zp) {
      for (int c = 0; c < 2*vs; c++) {
        for (int k = 0; k < ISIZE; k++) {
          vlist[state].push_back(zoit.read());
          zoit.next();
        }
        state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
      }
    }
    
    // coefficients
    int32_t l_sz = tnsr.get_dim(7)*tnsr.get_dim(6)*tnsr.get_dim(5)*tnsr.get_dim(4)*tnsr.get_dim(3);
    for (int i = 0; i < l_sz; i++) {
        int16_t in_grp_sz = tnsr.get_dim(2)*tnsr.get_dim(1)*tnsr.get_dim(0)/2; //(o2*i8*iodd2/2)
        for (int e = 0; e < in_grp_sz/4; e++) {
          uint8_t encb_bits = encb_oit.read(); encb_oit.next();
          vlist[state].push_back((coef_t)(encb_bits&0xff));
        }

        for (int k = 0; k < in_grp_sz; k++) {
          coef_t coef_data = coef_oit.read(); coef_oit.next();
          vlist[state].push_back(coef_data);
        }
      state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
    }
  }
  queue_encode(vlist, obuf, olen, coef_mode_uncompressed);

}




