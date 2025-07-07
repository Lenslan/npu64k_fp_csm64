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

/*
 * tensor_gtoa_gather.hpp
 *
 * File defining a tensor level gather API base on the generic tensor operation API
 *
 */

///////////////////////////////////////////////////////////////////////////////////////////////
//
// the gather tensor API performs the following function, gathering subtensors [C2][C1][C0]
// from a two dimensional dictionary into a five dimensional result
//
// ixpix_t[Y][X][C2][C1][C0] gather(ixpix_t dict[H][W][C2][C1][C0], aoffset_t idx[Y][X][2]) {
//   ixpix_t[Y][X][C2][C1][C0] result;
//   foreach r,c,c2,c1,c0 in H,W,C2,C1,C0 {
//     idxh = idx[r][c][1]
//     idxw = idx[r][c][0]
//     result[y][x][c2][c1][c0] = dict[idxh][idxw][c2][c1][c0]
//   }
// }
//
// The operation will be vectorized over the W dimension
// 
///////////////////////////////////////////////////////////////////////////////////////////////

#ifndef TENSOR_API_TENSOR_GTOA_GATHER_HPP_
#define TENSOR_API_TENSOR_GTOA_GATHER_HPP_

// include interface datatypes
#include "./tensor_gtoa.hpp"
#include "./npu_act_lib.hpp"

//
// All identifiers related to the tensor API go into namespace tensor::v200
//
namespace tensor::v200 {
template <template <typename> class B = buffer_t>
class gtoa_gather_params : public gtoa_params<B> {
  public:
  //
  // Constructor
  //
  gtoa_gather_params(
                     const shape<3>& inner,    // shape of inner tensor [C2][C1][C0]
                     const shape<2>& ishpi,    // shape of the outer dictionary tensor [H][W]
                     const shape<2>& oshpi     // shape of the outer index and output tensor [Y][X]
                     );

  inline gtoa_gather_params() = default;
  inline gtoa_gather_params(const gtoa_gather_params &) = default;

  //
  // Get the implementation specific minimum buffer shapes
  //
  // structure with implementation specific minimum buffer sizes
  void get_shapes(
                  gtoa_act_params_impl_shapes& s // NOLINT [runtime/references]
                  );
  //
  // Assign L1 memory buffer addresses
  //
  // input0 is the dictionary, shape [H][W][C2][C1][C0]
  template <template <typename> class BD = B>
  void init_l1_input0(const impl_spec_container_t<BD> &p);
  // input1 is the index tensor, shape [Y][X][2]
  template <template <typename> class BD = B>
  void init_l1_input1(const impl_spec_container_t<BD> &p);
  // output is the result, shape [Y][X][C2][C1][C0]
  template <template <typename> class BD = B>
  void init_l1_output(const impl_spec_container_t<BD> &p);


  private:
  // include implementation specific private members
#include "./tensor_gtoa_gather_param_priv.hpp"
};
// include implementation specific inline
#include "./tensor_gtoa_gather_inline.hpp"
}   // namespace tensor::v200
#endif    // TENSOR_API_TENSOR_GTOA_GATHER_HPP_
