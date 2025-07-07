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
 * tensor_conv_matmat.hpp
 *
 * File defining a tensor level matrix multiply API
 *
 */


///////////////////////////////////////////////////////////////////////////////////////////////
//
// Using the convolution tensor API
// 
// The convolution tensor API support depthwise, grouped and normal convolutions
// - grouped convolutions:   grp != ni
// - depthwise convolutions: grp == ni
// - normal convolutions:    grp == 1
// Deconvolutions (transposed) convolutions can be supported by decomposing into multiple normal 
// convolutions with strided output
// Filters can be 1D, 2D, 3D
//
// Steps:
// -1-  The AOT/JIT compiler will create a conv_params object with the convolution parameters
// -2-  Optionally the compiler may pass implementation specific parameters through the 
//      set_impl_params method
//      Alternatively the compiler may rely on the default parameters, which can be queried 
//      through get_impl_params method
// -3-  The compiler can query the expected buffer/tensor sizes through the get_shapes method
// -4-  The compiler will allocate buffers in L1 memory and pass the information through the 
//      init_l1 method
// -5-  The compiler will encode coefficients and zero-points through the coef_enc method into
//      a data-strucutre allocated by the compiler
//      Similarly the compiler will encode the input feature-map zero-points/padding values
// -6-  The AOT compiler will dump the conv_param object into a binary stream
// -7-  The AOT run-time will restore the conv_param object from a binary stream
// -8-  The run-time will create one or multiple conv_rt objects from the parameter object,
//      one for each tile
// -9- The run-time will assign run-time specific parameters through the set_impl_params
//      method of the conv_rt object.
// -10- The run-time will assign tile specific parameters through the init_tile_params method
// -11- The run-time needs to assure input feature-map, padding array, control information, 
//      coefficients have been loading into the L1 memory tensors
// -12- The run-time may prepare for execution using the prepare method which may implement
//      prefetching
// -13- The run-time uses the execute method to start actual execution of the convolution
// -14- In case of asynchronous execution, run-time needs to use an implementation dependent
//      method to wait for completion (see step 10)
//
///////////////////////////////////////////////////////////////////////////////////////////////


#ifndef TENSOR_API_TENSOR_CONV_MATMAT_HPP_
#define TENSOR_API_TENSOR_CONV_MATMAT_HPP_


// include interface datatypes
#include "tensor_conv.hpp"


//
// All identifiers related to the tensor API go into namespace tensor::v200
//
namespace tensor::v200 {

//
// Matrix*transposed matrix multiplication class
// Two input matrices:
//  A[v][ni]
//  B[no][ni]
// output matrix
//  C[v][no]
// operation
// C[v][no] = A[v][ni] * tranpose(B[no][ni])
template<template<typename> class B=buffer_t>
class matmat_params : public conv_base<B> {
#include "tensor_conv_matmat_priv.hpp"
  public:
  //
  // Constructors
  //
  // constructor for 1D/2D/3D convolution object, supporting various datatypes
  matmat_params(
                aoffset_t                 nii,           // number input channels (not vectors), in units of 8b or 16b feature-map pixels
                aoffset_t                 noi,           // number output channels (not vectors)
                aoffset_t                 vi,            // spatial dimension of input and output
                bool                      use_acci,      // use input accumulator from AM else 0
                bool                      keep_acci,     // keep output accumulator in AM else stream
                fm_cfg_t                  fma_tpi,       // feature-map type: fm_cfg_8b_e, fm_cfg_16b_e, fm_cfg_bf16_e, fm_cfg_fp16_e
                fm_cfg_t                  fmb_tpi,       // feature-map type: fm_cfg_8b_e, fm_cfg_16b_e, fm_cfg_bf16_e, fm_cfg_fp16_e
                aoffset_t                 bi=1           // batch size
                );
  matmat_params(
                aoffset_t                 nii,           // number input channels (not vectors), in units of 8b or 16b feature-map pixels
                aoffset_t                 noi,           // number output channels (not vectors)
                aoffset_t                 vi,            // spatial dimension of input and output
                const shape<2>&           padlim,        // padding limit for tiled matrix multiply
                bool                      use_acci,      // use input accumulator from AM else 0
                bool                      keep_acci,     // keep output accumulator in AM else stream
                fm_cfg_t                  fma_tpi,       // feature-map type: fm_cfg_8b_e, fm_cfg_16b_e, fm_cfg_bf16_e, fm_cfg_fp16_e
                fm_cfg_t                  fmb_tpi,       // feature-map type: fm_cfg_8b_e, fm_cfg_16b_e, fm_cfg_bf16_e, fm_cfg_fp16_e
                aoffset_t                 bi=1           // batch size
                );
  // V1 legacy constructors
  matmat_params(
                aoffset_t                          nii,           // number input channels (not vectors), in units of 8b or 16b feature-map pixels
                aoffset_t                          noi,           // number output channels (not vectors), in units of 8b or 16b feature-map pixels
                aoffset_t                          vi,            // spatial dimension of input and output
                bool                               use_acci,      // use input accumulator to accumulate over multiple tiles
                bool                               keep_acci,     // keep output accumulator to accumulate over multiple tiles
                bool                               fma_dbli,      // 8b or 16b matrix A
                bool                               fmb_dbli       // 8b or 16b matrix B
                );
  matmat_params(
                aoffset_t                          nii,           // number input channels (not vectors), in units of 8b or 16b feature-map pixels
                aoffset_t                          noi,           // number output channels (not vectors), in units of 8b or 16b feature-map pixels
                aoffset_t                          vi,            // spatial dimension of input and output
                const shape<2>&                    padlim,        // padding limit for tiled matrix multiply
                bool                               use_acci,      // use input accumulator to accumulate over multiple tiles
                bool                               keep_acci,     // keep output accumulator to accumulate over multiple tiles
                bool                               fma_dbli,      // 8b or 16b matrix A
                bool                               fmb_dbli       // 8b or 16b matrix B
                );
  inline matmat_params()  = default;
  inline matmat_params(const matmat_params&)  = default;

  //
  // Set a smaller, alternative tile shape e.g. for the boundaries of the feature-map
  //
  void set_alt_shape(
                     aoffset_t                nii,       // number input channels (not vectors), in units of 8b or 16b feature-map pixels
                     aoffset_t                noi,       // number output channels (not vectors)
                     aoffset_t                vi,        // number spatial elements (not vectors)
                     bool                     use_acci,  // use input accumulator
                     bool                     keep_acci, // keep output accumulator
                     conv_params_impl_alt&    alt        // encoded alternative shape
                     );

  //
  // Get the implementation specific shape of the minimum buffer sizes for the matmat convolution
  //
  void get_shapes(
                  conv_params_impl_shapes&    p       // structure with implementation specific minimum buffer sizes
                  );

  //
  // Assign L1 memory buffer addresses for A and B
  //
  template<template<typename> class BD=B>
  void init_l1_a(
                 const impl_spec_container_t<BD>&   p       // set the input matrix A
                 );

  template<template<typename> class BD=B>
  void init_l1_b(
                 const impl_spec_container_t<BD>&   p       // set the input matrix B
                 );

  //
  // Precompute the pointer offset when updating an input matrix A and B tensor pointer
  //
  poffset_t update_ptra(
                        aoffset_t              spat_offset, // spatial offset
                        aoffset_t              chan_offset  // channel offset
                        );

  poffset_t update_ptrb(
                        aoffset_t              spat_offset, // spatial offset
                        aoffset_t              chan_offset  // channel offset
                        );
};
}  // namespace tensor::v200
// include implementation specific inline functions
#include "tensor_conv_matmat_inline.hpp"
#endif  // TENSOR_API_TENSOR_CONV_MATMAT_HPP_
