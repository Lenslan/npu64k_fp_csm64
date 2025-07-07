#include "tensor_dma.hpp"

using namespace tensor::v200;

// initialize a tensor with incrementing values
template<typename T, int R, template<typename> class B=buffer_t> void tensor_init_incr(
                          T              st, // start value
                          tensor_t<T,R,B>& tns // output tensor
                          ) {
  tensor_iterator_t<T,R,B> tit(tns);
  do {
    tit.write((T)st++);
  } while (tit.next());
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
