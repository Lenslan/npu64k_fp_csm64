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
// fm16cf8 does support:
// - compression
// - 4b
// - coefficient zero-points
// fm16cf8 does not support:
// - sparse
// - inn&onn
// DW functios same as NINO(fm8cf16_...)

// DINO(1x1), 16b feature-map, 8b coefficient, non-sparse
static void DINO(fm16cf8ns_1x1)(const tensor_t<coef_t,6,xbuffer_t>&     icf,       // input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp], 8b cf only
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
  // target shape is [grp][no/16][ni/16][fd][fh][fw][i2][o16][i8]
  //
  // [grp][no][fd][fh][fw][ni] --> [grp][no/16][o16][fd][fh][fw][ni/16][i2][i8]
  tensor_t<coef_t,7,xbuffer_t>  tns1(tns0.split(0, shp0[0]/16));
  tensor_t<coef_t,8,xbuffer_t>  tns2(tns1.split(0, 2));
  tensor_t<coef_t,9,xbuffer_t>  tns3(tns2.split(6, shp0[4]/16));
  // transpose [grp][no/16][o16][fd][fh][fw][ni/16][i2][i8] -> [grp][no/16][ni/16][fd][fh][fw][i2][o16][i8]
  tensor_t<coef_t,9,xbuffer_t>  tnsr(tns3.transpose({0,6,1,3,4,5,2,7,8}));
  // zero-point reorder [grp][no] -->  [grp][no][o16]
  tensor_t<coef_t,3,xbuffer_t>  zpr(zp0.split(0, shp0[4]/ISIZE));
  //
  // Get the avail bits identifying which coefficients are equal to the zero-point
  //
  xbuffer_t<uint8_t> availbuf = tbuf.split<uint8_t>((size_t)tnsr.get_tens_size());
  tensor_t<uint8_t,9,xbuffer_t>                availtns(availbuf, tnsr.get_shape());
  tensor_iterator_t<uint8_t,9,xbuffer_t>       availit(availtns);
  const_tensor_iterator_t<coef_t,9,xbuffer_t>  eit(tnsr);
  for (int grp = 0; grp < tnsr.get_dim(8); grp++) {
    for (int no = 0; no < tnsr.get_dim(7); no++) {
      for (int ni = 0; ni < tnsr.get_dim(2)*tnsr.get_dim(3)*tnsr.get_dim(4)*tnsr.get_dim(5)*tnsr.get_dim(6); ni++) {
        for (int o16 = 0; o16 < 16; o16++) {
          coef_t zp = cf_zp ? zpr.read({(int16_t)o16,(int16_t)no,(int16_t)grp}) : (coef_t)0;
          for (int i8 = 0; i8 < 8; i8++) {
            availit.write(eit.read() != zp);
            availit.next();
            eit.next();
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
  for (int o = 0; o < tnsr.get_dim(7)*tnsr.get_dim(8); o++) {
    // new zero-point
    if (cf_zp) {
      for (int k = 0; k < ISIZE; k++) {
        vlist[state].push_back(zoit.read());
        zoit.next();
      }
      state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
    }
    // coefficients
    for (int i = 0; i < (int)tnsr.get_tens_size()/(tnsr.get_dim(7)*tnsr.get_dim(8))/ISIZE; i++) {
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
          coef_t w = (coef_t)(coit.read() & 0xf);
          coit.next();
          w |= coit.read() << 4;
          coit.next();
          vlist[state].push_back(w);
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

// DINO(1x1), 16b feature-map, 8b coefficient, non-sparse, grouped
static void DINO(gfm16cf8ns_1x1)(const tensor_t<coef_t,6,xbuffer_t>&     icf,       // input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp], 8b cf only
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
  // transcode coefficients to [1][Cout*Grp][Fd][Fh][Fw][Cin*Grp]
  int grp = icf.get_dim(5);
  shape<6> shp0;
  shp0[0] = icf.get_dim(0)*grp;  // input channels
  shp0[1] = icf.get_dim(1);
  shp0[2] = icf.get_dim(2);
  shp0[3] = icf.get_dim(3);
  shp0[4] = icf.get_dim(4)*grp;  // output channels
  shp0[5] = 1;
  xbuffer_t<coef_t> cbuf = tbuf.split((size_t)get_shape_size(shp0));
  tensor_t<coef_t,6,xbuffer_t> otns(cbuf, shp0);
  const_tensor_iterator_t<coef_t,6,xbuffer_t>  iit(icf);
  const_tensor_iterator_t<coef_t,1,xbuffer_t>  zit(izp);
  tensor_iterator_t<coef_t,6,xbuffer_t>        oit(otns);
  // copy tensor
  for (int og = 0; og < grp; og++) {
    for (int oc = 0; oc < icf.get_dim(4); oc++) {
      coef_t zp = zit.read();
      zit.next();
      for (int fd = 0; fd < icf.get_dim(3); fd++) {
        for (int fh = 0; fh < icf.get_dim(2); fh++) {
          for (int fw = 0; fw < icf.get_dim(1); fw++) {
            for (int ig = 0; ig < grp; ig++) {
              for (int ic = 0; ic < icf.get_dim(0); ic++) {
                coef_t cf;
                if (ig == og) {
                  cf = iit.read();
                  iit.next();
                } else {
                  cf = zp;
                }
                oit.write(cf);
                oit.next();
              }
            }
          }
        }
      }
    }
  }
  // encode as 1x1
  DINO(fm16cf8ns_1x1)(otns, izp, tbuf, coef_mode, cf_4b, cf_zp, obuf, olen);  
}

// NINO(2x1), 16b feature-map, 8b coefficient, non-sparse
static void NINO(fm16cf8ns_2x1)(const tensor_t<coef_t,6,xbuffer_t>&     icf,       // input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp], 8b only
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
  shp0[0] = ROUND_UP(icf.get_dim(0), ISIZE/2);     // round up to multiple of ISIZE
  shp0[1] = ROUND_UP(icf.get_dim(1), 2);           // round up to even
  shp0[2] = icf.get_dim(2);
  shp0[3] = icf.get_dim(3);
  shp0[4] = ROUND_UP(icf.get_dim(4), ISIZE);       // round up to multiple of ISIZE
  shp0[5] = icf.get_dim(5);
  // increase size of tensor
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
        for (int w = 0; w < shp0[1]; w++) {
          for (int ni = 0; ni < shp0[0]; ni++) {
            coef_t cv;
            if (ni >= icf.get_dim(0) || w >= icf.get_dim(1) || no >= icf.get_dim(4)) {
              // pad with 0 coefficient
              cv  = zp;
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
  // target shape is [grp][no/16][ni/8][fd][fh][fw/2][w2][o16][i8]
  //
  // [grp][no][fd][fh][fw][ni] --> [grp][no/16][o16][fd][fh][fw/2][w2][ni][i8]
  tensor_t<coef_t,7,xbuffer_t>  tns1(tns0.split(0, shp0[0]/8));
  tensor_t<coef_t,8,xbuffer_t>  tns2(tns1.split(2, shp0[1]/2));
  tensor_t<coef_t,9,xbuffer_t>  tns3(tns2.split(6, shp0[4]/16));
  // transpose [grp][no/16][o16][fd][fh][fw/2][w2][ni][i8] --> [grp][no][ni][fd][fh][fw/2][w2][o16][i8]
  tensor_t<coef_t,9,xbuffer_t>  tnsr(tns3.transpose({0,6,2,3,4,5,1,7,8}));
  // zero-point reorder [grp][no] -->  [grp][no][o16]
  tensor_t<coef_t,3,xbuffer_t>  zpr(zp0.split(0, shp0[4]/ISIZE));

  //
  // Get the avail bits identifying which coefficients are equal to the zero-point
  //
  xbuffer_t<uint8_t> availbuf = tbuf.split<uint8_t>((size_t)tnsr.get_tens_size());
  tensor_t<uint8_t,9,xbuffer_t>               availtns(availbuf, tnsr.get_shape());
  tensor_iterator_t<uint8_t,9,xbuffer_t>      availit(availtns);
  const_tensor_iterator_t<coef_t,9,xbuffer_t> eit(tnsr);  // [grp][no/16][ni/8][fd][fh][fw/2][w2][o16][i8]
  for (int grp = 0; grp < tnsr.get_dim(8); grp++) {
    for (int no = 0; no < tnsr.get_dim(7); no++) {
      for (int ni = 0; ni < tnsr.get_dim(2)*tnsr.get_dim(3)*tnsr.get_dim(4)*tnsr.get_dim(5)*tnsr.get_dim(6); ni++) {
        for (int o16 = 0; o16 < tnsr.get_dim(1); o16++) {
          coef_t zp = cf_zp ? zpr.read({(int16_t)o16,(int16_t)no,(int16_t)grp}) : (coef_t)0;
          for (int ii = 0; ii < tnsr.get_dim(0); ii++) {
            availit.write(eit.read() != zp);
            availit.next();
            eit.next();
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
  const_tensor_iterator_t<coef_t,9,xbuffer_t>   coit(tnsr);
  const_tensor_iterator_t<coef_t,3,xbuffer_t>   zoit(zpr);
  const_tensor_iterator_t<uint8_t,9,xbuffer_t>  ait(availtns);
  for (int o = 0; o < tnsr.get_dim(7)*tnsr.get_dim(8); o++) { // [grp][no/16][ni/8][fd][fh][fw/2][w2][o16][i8]
    // new zero-point
    if (cf_zp) {
      for (int j = 0; j < zpr.get_dim(0)/ISIZE; j++) {
        for (int k = 0; k < ISIZE; k++) {
          vlist[state].push_back(zoit.read());
          zoit.next();
        }
        state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
      }
    }
    // coefficients
    for (int i = 0; i < (int)(tnsr.get_tens_size()/(tnsr.get_dim(7)*tnsr.get_dim(8))/ISIZE); i++) {
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

static void FC(fm16cf8ns)(const tensor_t<coef_t,3,xbuffer_t>&      icf,       // input coefficients [Grp][Cout][Cin], 8b only
                          const tensor_t<coef_t,1,xbuffer_t>&      izp,       // input zero-points [Cout]
                          xbuffer_t<coef_t>&                       tbuf,      // temporary xbuf
                          int                                      vs,        // VSIZE
                          // attributes
                          coef_mode_t                              coef_mode, // coefficient compression mode uncompressed or compressed or sparse
                          bool                                     cf_4b,     // 4b coefficient encoding
                          bool                                     cf_zp,     // zero-point enable
                          // outputs, buffers preallocated by caller
                          xbuffer_t<ixpix_t>&                      obuf,      // output encoded coefficient tensor
                          size_t&                                  olen       // size of used coefficient buffer in ixpix_t
                          ) {
  // get shape size
  shape<3> shp0;
  shp0[0] = ROUND_UP(icf.get_dim(0), ISIZE/2);      // round up to multiple of ISIZE/2
  shp0[1] = ROUND_UP(icf.get_dim(1), vs*ISIZE);     // round up to multiple of VSIZE*ISIZE
  shp0[2] = icf.get_dim(2);                         // groups
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
  // target shape is [grp][no/(VSIZE*ISIZE)][ni/8][o(VSIZE*ISIZE)][i8]
  //
  // [grp][no][ni] --> [grp][no/16][o8][o16][ni/8][i8]
  tensor_t<coef_t,4,xbuffer_t>  tns1(tns0.split(0, shp0[0]/8));
  tensor_t<coef_t,5,xbuffer_t>  tns2(tns1.split(2, shp0[1]/(vs*ISIZE)));
  // transpose [grp][no/16][o(VSIZE*ISIZE)][ni/16][i8] -->[grp][no/(VSIZE*ISIZE)][ni/8][o(VSIZE*ISIZE)][i8]
  tensor_t<coef_t,5,xbuffer_t>  tnsr(tns2.transpose({0,2,1,3,4}));
  // zero-point reorder [grp][no] -->  [grp][no/(VSIZE*ISIZE)][o(VSIZE*ISIZE)]
  tensor_t<coef_t,3,xbuffer_t>  zpr(zp0.split(0, shp0[1]/(vs*ISIZE)));

  xbuffer_t<uint8_t> availbuf = tbuf.split<uint8_t>((size_t)tnsr.get_tens_size());
  tensor_t<uint8_t,5,xbuffer_t>               availtns(availbuf, tnsr.get_shape());
  tensor_iterator_t<uint8_t,5,xbuffer_t>      availit(availtns);
  const_tensor_iterator_t<coef_t,5,xbuffer_t> eit(tnsr);
  for (int grp = 0; grp < tnsr.get_dim(4); grp++) {
    for (int no = 0; no < tnsr.get_dim(3); no++) {
      for (int ni = 0; ni < tnsr.get_dim(2); ni++) {
        for (int o128 = 0; o128 < (vs*ISIZE); o128++) {
          coef_t zp = cf_zp ? zpr.read({(int16_t)o128,(int16_t)no,(int16_t)grp}) : (coef_t)0;
          for (int i8 = 0; i8 < 8; i8++) {
            availit.write(eit.read() != zp);
                availit.next();
                eit.next();
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
  const_tensor_iterator_t<coef_t,5,xbuffer_t>  coit(tnsr);
  const_tensor_iterator_t<coef_t,3,xbuffer_t>  zoit(zpr);
  const_tensor_iterator_t<uint8_t,5,xbuffer_t> ait(availtns);
  for (int o = 0; o < tnsr.get_dim(3)*tnsr.get_dim(4); o++) {
    if (cf_zp) {
      // encode 128 zero-points
      for (int c = 0; c < vs; c++) {
        for (int k = 0; k < ISIZE; k++) {
          vlist[state].push_back(zoit.read());
          zoit.next();
        }
        state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
      }
    }
    // encode coefficients
    if (coef_mode == coef_mode_compressed) {
      for (int i = 0; i < (int)tnsr.get_tens_size()/(tnsr.get_dim(3)*tnsr.get_dim(4))/ISIZE; i++) {
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
        state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
      }
    } else if (cf_4b) {
      for (int i = 0; i < (int)tnsr.get_tens_size()/(tnsr.get_dim(3)*tnsr.get_dim(4))/ISIZE; i++) {
        for (int k = 0; k < ISIZE/2; k++) {
          coef_t v = (coef_t)(coit.read() & 0xf);
          coit.next();
          v |= coit.read() << 4;
          coit.next();
          vlist[state].push_back(v);
        }
        state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
      }
    } else {
      for (int i = 0; i < (int)tnsr.get_tens_size()/(tnsr.get_dim(3)*tnsr.get_dim(4))/ISIZE; i++) {
        for (int k = 0; k < ISIZE; k++) {
          vlist[state].push_back(coit.read());
          coit.next();
        }
        state = state == NUM_COEF_QUEUE-1 ? 0 : state+1;
      }
    }
  }
  queue_encode(vlist, obuf, olen, coef_mode);
}

