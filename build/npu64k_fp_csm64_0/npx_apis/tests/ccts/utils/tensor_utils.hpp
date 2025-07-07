/*************************************************************************/
/**                                                                     **/
/** Copyright (C) 2021-2022 Synopsys, Inc.                              **/
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

#ifdef SYSTEMC
#include "npu_act_hl_top.hpp"
using namespace npu_act;
#endif


#include "tensor.hpp"
using namespace tensor::v200;

// initialize a tensor with incrementing values
template<typename T, size_t R, template<typename> class B=buffer_t>
void tensor_init_incr(
                      T              st, // start value
                      tensor_t<T,R,B>& tns, // output tensor
                      int            stp=1, // increment stap
                      bool           dbl=false // 16b
                      ) {
  tensor_iterator_t<T,R,B> tit(tns);
  if (dbl) {
    int v = st;
    do {
      tit.write((T)v);
      tit.next();
      tit.write((T)(v>>8));
      v = v + stp;
    } while (tit.next());
  } else {
    do {
      tit.write(st);
      st = (T)(st + stp);
    } while (tit.next());
  }
}

// initialize a tensor with fixed values
template<typename T, int R, template<typename> class B=buffer_t> void tensor_init_fixed(
                                                   T              st, // fixed value
                                                   tensor_t<T,R,B>& tns // output tensor
                                                   ) {
  tensor_iterator_t<T,R,B> tit(tns);
  do {
    tit.write(st);
  } while (tit.next());
}

// initialize a tensor with incrementing values
template<int R, template<typename> class B=buffer_t> void tensor_vinit_incr(
                                       size_t               nc, // channel limit
                                       pix_t                st, // start value
                                       tensor_t<ixpix_t,R,B>& tns // output tensor
                                       ) {
  ixpix_t v;
  bool active;
#ifdef SYSTEMC
  cout << "chan: " << nc << " " << (int)tns.get_dim(0) << endl;
  report(cout, tns.get_shape());
#endif
  tensor_iterator_t<ixpix_t,R,B> tit(tns);
  do {
    size_t c = 0;
    for (int j = 0; j < tns.get_dim(0)*tns.get_dim(1); j++) {
      for (int i = 0; i < ISIZE; i++) {
        if (c < nc) {
          v[i] = (pix_t)st++;
        } else {
          v[i] = (pix_t)0xFF; // garbage
        }
        c++;
      }
      tit.write(v);
      active = tit.next();
    }
  } while (active);
}

// initialize a tensor with fixed values
template<int R, template<typename> class B=buffer_t> void tensor_vinit_fixed(
                                        size_t               nc, // channel limit
                                        pix_t                st, // fixed value
                                        tensor_t<ixpix_t,R,B>& tns // output tensor
                                        ) {
  ixpix_t v;
  bool active;
  tensor_iterator_t<ixpix_t,R,B> tit(tns);
  do {
    size_t c = 0;
    for (int j = 0; j < tns.get_dim(0); j++) {
      for (int i = 0; i < ISIZE; i++) {
        if (c < nc) {
          v[i] = st;
        } else {
          v[i] = (pix_t)0xFF; // garbage
        }
        c++;
      }
      tit.write(v);
      active = tit.next();
    }
  } while (active);
}
