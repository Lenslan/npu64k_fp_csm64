#ifdef SYSTEMC
#include "npu_act_hl_top.hpp"
using namespace npu_act;
#endif


#include "tensor.hpp"
using namespace tensor::v200;

// initialize a tensor with incrementing values
template<typename T, size_t R, template<typename> class B=buffer_t> void tensor_init_incr(
                                                  T              st, // start value
                                                  tensor_t<T,R,B>& tns // output tensor
                                                  ) {
  tensor_iterator_t<T,R,B> tit(tns);
  do {
    tit.write((T)st++);
  } while (tit.next());
}

// initialize a double width tensor with incrementing values
template<typename T, size_t R, template<typename> class B=buffer_t> void tensor_init_incr(
                                                  int64_t        st, // start value
                                                  tensor_t<T,R,B>& tns // output tensor
                                                  ) {
  tensor_iterator_t<T,R,B> tit(tns);
  do {
    tit.write((T)st);
    tit.next();
    tit.write((T)(st>>32));
    st++;
  } while (tit.next());
}

// initialize a tensor with fixed values
template<typename T, size_t R, template<typename> class B=buffer_t> void tensor_init_fixed(
                                                   T              st, // fixed value
                                                   tensor_t<T,R,B>& tns // output tensor
                                                   ) {
  tensor_iterator_t<T,R,B> tit(tns);
  do {
    tit.write(st);
  } while (tit.next());
}

#ifdef SYSTEMC
// initialize a tensor with incrementing values
template<size_t R, template<typename> class B=buffer_t> void tensor_vinit_incr(
                                       size_t               nc, // channel limit
                                       pix_t                st, // start value
                                       tensor_t<ixpix_t,R,B>& tns // output tensor
                                       ) {
  ixpix_t v;
  bool active;
  cout << "chan: " << nc << " " << (int)tns.get_dim(0) << endl;
  report(cout, tns.get_shape());
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
template<size_t R, template<typename> class B=buffer_t> void tensor_vinit_fixed(
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
#endif
