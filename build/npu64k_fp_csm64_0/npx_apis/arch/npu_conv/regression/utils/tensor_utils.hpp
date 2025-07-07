#include "tensor.hpp"

using namespace tensor::v200;

// initialize a tensor with incrementing values
template<typename T, size_t R, template<typename> class B=buffer_t> 
void tensor_init_incr(
                      T                st, // start value
                      tensor_t<T,R,B>& tns // output tensor
                      ) {
  tensor_iterator_t<T,R,B> tit(tns);
  do {
    tit.write((T)st++);
  } while (tit.next());
}

// initialize a floating-point tensor with incrementing values
template<typename T, size_t R, template<typename> class B=buffer_t> 
void tensor_init_incr_fp(
                         float            st,      // start value
                         tensor_t<T,R,B>& tns,     // output tensor
                         float            inc=1.0  // increment
                         ) {
  tensor_iterator_t<T,R,B> tit(tns);
  do {
    tit.write(T(st));
    st = st + inc;
  } while (tit.next());
}

// initialize a tensor with fixed values
template<typename T, size_t R, template<typename> class B=buffer_t>
void tensor_init_fixed(
                       T              st, // fixed value
                       tensor_t<T,R,B>& tns // output tensor
                       ) {
  tensor_iterator_t<T,R,B> tit(tns);
  do {
    tit.write(st);
  } while (tit.next());
}

// initialize a floating-point tensor with fixed values
template<typename T, size_t R, template<typename> class B=buffer_t>
void tensor_init_fixed_fp(
                          float            st,      // start value
                          tensor_t<T,R,B>& tns      // output tensor
                          ) {
  tensor_iterator_t<T,R,B> tit(tns);
  do {
    tit.write(T(st));
  } while (tit.next());
}

// initialize a tensor with incrementing values
template<size_t R, template<typename> class B=buffer_t> 
void tensor_vinit_incr(
                       size_t               nc,  // channel limit per group
                       pix_t                st,  // start value
                       tensor_t<ixpix_t,R,B>& tns  // output tensor
                       ) {
  bool    active;
  ixpix_t v;
  tensor_iterator_t<ixpix_t,R,B> tit(tns);
  do {
    size_t c = 0;
    for (int j = 0; j < tns.get_dim(0); j++) { // channels per group (padded)
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

// initialize a tensor with incrementing values
template<typename T, size_t R, template<typename> class B=buffer_t>
void tensor_vinit_incr_fp(
                          size_t               nc,  // channel limit per group
                          float                st,  // start value
                          tensor_t<ixpix_t,R,B>& tns  // output tensor
                          ) {
  bool    active;
  ixpix_t v;
  tensor_iterator_t<ixpix_t,R,B> tit(tns);
  do {
    size_t c = 0;
    for (int j = 0; j < tns.get_dim(0); j++) { // channels per group (padded)
      for (int i = 0; i < ISIZE; i+=2) {
        if (c < nc) {
          T d(st);
          v[i+0] = d.data[0];
          v[i+1] = d.data[1];
          st = st + 1.0;
        } else {
          v[i+0] = (pix_t)0xFF; // garbage
          v[i+1] = (pix_t)0xFF; // garbage
        }
        c++;
      }
      tit.write(v);
      active = tit.next();
    }
  } while (active);
}

// initialize a tensor with incrementing values, no garbage at end
template<size_t R, template<typename> class B=buffer_t>
void tensor_vinit_incr0(
                        size_t               nc,  // channel limit per group
                        pix_t                st,  // start value
                        tensor_t<ixpix_t,R,B>& tns  // output tensor
                        ) {
  bool    active;
  ixpix_t v;
  tensor_iterator_t<ixpix_t,R,B> tit(tns);
  do {
    size_t c = 0;
    for (int j = 0; j < tns.get_dim(0); j++) { // channels per group (padded)
      for (int i = 0; i < ISIZE; i++) {
        if (c < nc) {
          v[i] = (pix_t)st++;
        } else {
          v[i] = (pix_t)0x00; // set to 0
        }
        c++;
      }
      tit.write(v);
      active = tit.next();
    }
  } while (active);
}

// initialize a tensor with fixed values
template<size_t R, template<typename> class B=buffer_t>
void tensor_vinit_fixed(
                        size_t               nc,  // channel limit per group
                        pix_t                st,  // fixed value
                        tensor_t<ixpix_t,R,B>& tns  // output tensor
                        ) {
  ixpix_t v;
  tensor_iterator_t<ixpix_t,R,B> tit(tns);
  for (int i = 0; i < ISIZE; i++) {
    v[i] = (pix_t)0xFF; // garbage
  }
  do {
    tit.write(v);
  } while (tit.next());
}

