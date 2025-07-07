#include "tensor_dma.hpp"

using namespace tensor::v200;

// initialize a tensor with incrementing values
template<typename T, int R, template<typename> class B=buffer_t>
void tensor_init_incr( T              st, // start value
                       tensor_t<T,R,B>& tns // output tensor
                     ) {
  tensor_iterator_t<T,R,B> tit(tns);
  do {
    tit.write((T)st++);
  } while (tit.next());
}

// initialize a tensor with fixed values
template<typename T, int R, template<typename> class B=buffer_t>
void tensor_init_fixed( T              st, // fixed value
                        tensor_t<T,R,B>& tns // output tensor
                      ) {
  tensor_iterator_t<T,R,B> tit(tns);
  do {
    tit.write(st);
  } while (tit.next());
}

// initialize a tensor from array
template<typename T, int R, template<typename> class B=buffer_t>
void tensor_init_from( T*    p          , // pointer
                       tensor_t<T,R,B>& tns // output tensor
                     ) {
  tensor_iterator_t<T,R,B> tit(tns);
  do {
    tit.write(*p++);
  } while (tit.next());
}


// initialize a tensor with incrementing values
template<typename T, int R, template<typename> class B=buffer_t>
void tensor_vinit_incr( size_t               nc, // channel limit
                        pix_t                st, // start value
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

#if defined SYSTEMC || defined RTL_DPI || defined RTL_ARC
// initialize a tensor with fixed values
template<template<typename> class B=buffer_t>
inline void tensor_init_fixed(pix_t st, impl_spec_container_t<B>& d) {
  ixpix_t v;
  tensor_iterator_t<ixpix_t,5,B> tit(d.data);
  for (int i = 0; i < ISIZE; i++) {
    v[i] = st;
  }
  do {
    tit.write(v);
  } while (tit.next());
}
#else
template<template<typename> class B=buffer_t>
inline void tensor_init_fixed(pix_t v, impl_spec_container_t<B>& d) {
  tensor_init_fixed<pix_t,4,B>(v, d.data);
}
template<template<typename> class B=buffer_t>
inline void report(ostream& os, const impl_spec_container_t<B>& d) {
  report<pix_t,4,B>(os, d.data);
}
#endif
