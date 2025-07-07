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
 * tensor_dma_gather.hpp
 *
 * File defining a tensor level gather API base on the input DMA
 *
 */

///////////////////////////////////////////////////////////////////////////////////////////////
//
// the gather tensor API performs the following function, gathering subtensors [C2][C1][C0]
// from a two dimensional dictionary into a five dimensional result
//
// ixpix_t[Y][X][C2][C1][C0] gather(pix_t dict[H][W][C2][C1][C0], aoffset_t idx[Y][X][2]) {
//   ixpix_t[Y][X][C2][C1][C0] result;
//   foreach y,c in Y,X {
//     idxh = idx[y][x][1]
//     idxw = idx[y][x][0]
//     foreach c2,c1,c0 in C2,C1,C0 {
//       result[y][x][c2][c1][c0] = dict[idxh][idxw][c2][c1][c0]
//     }
//   }
// }
//
///////////////////////////////////////////////////////////////////////////////////////////////

#ifndef TENSOR_API_TENSOR_IDMA_GATHER_HPP_
#define TENSOR_API_TENSOR_IDMA_GATHER_HPP_

// include interface datatypes
#include "tensor.hpp"


///////////////////////////////////////////////////////////////////////////////////////////////
//
// Include implementation specific data structures
//
///////////////////////////////////////////////////////////////////////////////////////////////
#include "tensor_dma.hpp"

//
// All identifiers related to the tensor API go into namespace tensor::v200
//
namespace tensor::v200 {
template <template <typename> class B = buffer_t>
class dma_gather_params {
  public:
  //
  // Constructor
  //
  dma_gather_params(
                    const shape<3>& inner,    // shape of inner tensor [C2][C1][C0], C0 in multiples of ISIZE
                    const shape<2>& ishpi,    // shape of the outer dictionary tensor [H][W]
                    const shape<2>& oshpi     // shape of the outer index and output tensor [Y][X]
                    );

  inline dma_gather_params() = default;
  inline dma_gather_params(const dma_gather_params &) = default;

  //
  // Set implementation specific parameters, optional else use default
  //
  void set_impl_params(
                       const dma_params_impl_spec& p // structure with implementation specific parameters
                       );
  void get_impl_params(
                       dma_params_impl_spec&       p // return structure with implementation specific parameters
                       );    
  
  //
  // Get the implementation specific minimum buffer shapes
  //
  // structure with implementation specific minimum buffer sizes
  void get_shapes(
                  dma_params_impl_shapes& s  // NOLINT [runtime/references]
                  );
  //
  // Assign L1 memory buffer addresses
  //
  // input0 is the XM dictionary, shape [H][W][C2][C1][C0]
  void set_src(const tensor_t<pix_t,5,B>& p);
  // input1 is the index tensor, shape [Y][X][2]
  void set_src(const impl_spec_container_t<B> &p);
  // output is the result, shape [Y][X][C2][C1][C0]
  void set_dst(const impl_spec_container_t<B> &p);

  // get run-time parameters
  void get_rt_params(dma_params_impl_main&);

  private:
  // include implementation specific private members
#include "./tensor_dma_gather_param_priv.hpp"
};
}   // namespace tensor::v200
// include implementation specific inline
#include "./tensor_dma_gather_inline.hpp"
#endif    // TENSOR_API_TENSOR_DMA_GATHER_HPP_
