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
 * tensor_gtoa_aligned_interp.hpp
 *
 * File defining a tensor level linear interpolation tensor operation API
 *
 */


///////////////////////////////////////////////////////////////////////////////////////////////
//
// Using the tensor operation API
//
// Steps:
// -1-  The AOT/JIT compiler will create a object with a base class gtoa_params
// -2-  Optionally the compiler may pass implementation specific parameters through the
//      set_impl_params method
//      Alternatively the compiler may rely on the default parameters, which can be queried
//      through get_impl_params method
// -3-  The compiler can query the expected buffer/tensor sizes through the get_shapes method
// -4-  The compiler will allocate buffers in L1 memory and pass the information through the
//      init_l1 method
// -5-  The compiler will call the ctrl_enc method to fill the control strucutre allocated by
//      the compiler
// -6-  The compiler will encode function specific parameters through the param_enc method into
//      a data-strucutre allocated by the compiler
// -7-  The AOT compiler will dump the conv_param object into a binary stream
// -8-  The AOT run-time will restore the conv_param object from a binary stream
// -9-  The run-time will create one or multiple gtoa_rt objects from the parameter object,
//      one for each tile
// -10- The run-time will assign run-time specific parameters through the set_impl_params
//      method of the gtoa_rt object.
// -11- The run-time will assign tile specific parameters through the init_tile_params method
// -12- The run-time needs to assure accumulators, control information,
//      and activtion parameters have been loading into the L1 memory
// -13- The run-time may prepare for execution using the prepare method which may implement
//      prefetching
// -14- The run-time uses the execute method to start actual execution of the activation function
// -15- In case of asynchronous execution, run-time needs to use an implementation dependent
//      method to wait for completion (see step 10)
//
///////////////////////////////////////////////////////////////////////////////////////////////


#ifndef TENSOR_API_TENSOR_GTOA_INTERP_HPP_
#define TENSOR_API_TENSOR_GTOA_INTERP_HPP_


//
// include interface datatypes
//
#include "./tensor_gtoa.hpp"
#include "./npu_act_lib.hpp"


//
// All identifiers related to the tensor API go into namespace tensor::v200
//
namespace tensor::v200 {

///////////////////////////////////////////////////////////////////////////////////////////////
//
// Corner_aligned_interp
//
// This class is doing a interpolation and supports floating-point ratios between
// input and output tensor.
// The parameter object can be reused across multiple tiles of the same layer.
// The start height position is passed through hstart and can be run-time updated through SR0
// The up/downsampling ratio is passed as an argument in hdelta and at run-time through SR1
//
///////////////////////////////////////////////////////////////////////////////////////////////
template<template<typename> class B = buffer_t>
class gtoa_interp_params : public gtoa_params<B> {
 public:
  //
  // Constructors
  //
  // VM(int8/int16/fp16/bf16) to VM(int8/int16/fp16/bf16)
  gtoa_interp_params(
     aoffset_t                  noi,           // number input&output channels (not vectors)
     float                      hstart,        // height index start, passed through SR0
     float                      hdelta,        // height index increment per output, passed through SR1
     const shape<3>&            oshpi,         // tile output shape, indexed by spatial_axis_t
     act_dtype_t                intp,          // input datatype: int8, int16, fp16, bf16
     act_dtype_t                outtp          // output datatype: int8, int16, fp16, bf16
  );
  // Legacy: VM(8b/16b) to VM(8b/16b)
  gtoa_interp_params(
     aoffset_t                  noi,           // number output channels (not vectors)
     float                      delta,         // increment per output
     aoffset_t                  hout,          // total feature-map output height
     const shape<3>&            ishpi,         // tile input shape, indexed by spatial_axis_t
     const shape<3>&            oshpi,         // tile output shape, indexed by spatial_axis_t
     bool                       fmidbli,       // 8b/16b input feature-map
     bool                       fmodbli);      // 8b/16b output feature-map
  // Default constructor
  inline gtoa_interp_params() = default;
  inline gtoa_interp_params(const gtoa_interp_params&)  = default;

  //
  // Get the implementation specific minimum buffer shapes
  //
  void get_shapes(gtoa_act_params_impl_shapes& s);     // NOLINT [runtime/references]

  //
  // Assign L1 memory buffer addresses
  //
  template<template<typename> class BD = B>
  void init_l1_output(
    const impl_spec_container_t<BD>& p);   // buffers and tensors in L1 memory
  template<template<typename> class BD = B>
  void init_l1_input(
    const impl_spec_container_t<BD>& p);   // buffers and tensors in L1 memory

 private:
// include implementation specific private members
#include "./tensor_gtoa_interp_param_priv.hpp"
};

// include implementation specific inline functions
#include "./tensor_gtoa_interp_inline.hpp"
}  // namespace tensor::v200

#endif  // TENSOR_API_TENSOR_GTOA_INTERP_HPP_
