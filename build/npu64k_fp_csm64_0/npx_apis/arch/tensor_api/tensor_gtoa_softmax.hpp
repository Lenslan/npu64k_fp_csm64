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
 * tensor_gtoa_softmax.hpp
 *
 * File defining a tensor softgmax operation on the generic tensor operation API
 * Steps:
 *  1 - ARGMAX to scalar 0 and MAX in VR7
 *  2 - exp(x-max) to output and reciprocal in VR7
 *  3 - scale exp(x-max)*recip
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

#ifndef TENSOR_API_TENSOR_GTOA_SOFTMAX_HPP_
#define TENSOR_API_TENSOR_GTOA_SOFTMAX_HPP_


// include interface datatypes
#include "tensor_gtoa.hpp"  // NOLINT [build/include_subdir]
#include "npu_act_lib.hpp"  // NOLINT [build/include_subdir]


//
// All identifiers related to the tensor API go into namespace tensor::v200
//
namespace tensor::v200 {

///////////////////////////////////////////////////////////////////////////////////////////////
//
// Softmax 1st step: ARGMAX and MAX parameter class; ARGMAX returned as salar 0; MAX in VR7
//
///////////////////////////////////////////////////////////////////////////////////////////////
template<template<typename> class B = buffer_t>
class gtoa_softmax_max_params : public gtoa_params<B> {
 public:
  //
  // Constructor
  //
  gtoa_softmax_max_params(
    aoffset_t noi);           // number output channels (not vectors), always 16b input
  inline gtoa_softmax_max_params() = default;
  inline gtoa_softmax_max_params(const gtoa_softmax_max_params&) = default;

  //
  // Get the implementation specific minimum buffer shapes
  //
  void get_shapes(
    gtoa_act_params_impl_shapes& s);  // NOLINT [runtime/reference]

  //
  // Assign L1 memory buffer addresses
  //
  // tensor to be normalized
  template<template<typename> class BD = B>
  void init_l1_input(
    const impl_spec_container_t<BD>&    p);  // structure with allocated tensors in L1 memory

 private:
  // include implementation specific private members
#include "tensor_gtoa_softmax_max_param_priv.hpp"    // NOLINT [build/include_subdir]
};


///////////////////////////////////////////////////////////////////////////////////////////////
//
// Softmax 2nd step: output tensor exp(x-max), reciprocal 1/sum(exp(x-max)) returned in VR6 and VR7
//
///////////////////////////////////////////////////////////////////////////////////////////////
template<template<typename> class B = buffer_t>
class gtoa_softmax_exp_params : public gtoa_params<B> {
 public:
  //
  // Constructor from max object
  //
  explicit gtoa_softmax_exp_params(const gtoa_softmax_max_params<B>&);
  inline gtoa_softmax_exp_params() = default;
  inline gtoa_softmax_exp_params(const gtoa_softmax_exp_params&) = default;

  //
  // Get the implementation specific minimum buffer shapes
  //
  void get_shapes(
    gtoa_act_params_impl_shapes& s);  // NOLINT [runtime/references]

  //
  // Assign L1 memory buffer addresses
  //
  // exp output
  template<template<typename> class BD = B>
  void init_l1_output(
    const impl_spec_container_t<BD>&    p);   // structure with allocated tensors in L1 memory
  // same input as step 1
  template<template<typename> class BD = B>
  void init_l1_input(
    const impl_spec_container_t<BD>&    p);  // structure with allocated tensors in L1 memory

 private:
  // include implementation specific private members
#include "tensor_gtoa_softmax_exp_param_priv.hpp"    // NOLINT [build/include_subdir]
};
///////////////////////////////////////////////////////////////////////////////////////////////
//
// Softmax 3rd step: mulitply by reciprocal
//
///////////////////////////////////////////////////////////////////////////////////////////////
template<template<typename> class B = buffer_t>
class gtoa_softmax_scale_params : public gtoa_params<B> {
 public:
  //
  // Constructor
  //
  explicit gtoa_softmax_scale_params(const gtoa_softmax_max_params<B>&);
  inline gtoa_softmax_scale_params() = default;
  inline gtoa_softmax_scale_params(const gtoa_softmax_scale_params&) = default;

  //
  // Get the implementation specific minimum buffer shapes
  //
  void get_shapes(
    gtoa_act_params_impl_shapes& s);    // NOLINT [runtime/references]

  //
  // Assign L1 memory buffer addresses
  //
  // scaled output
  template<template<typename> class BD = B>
  void init_l1_output(
    const impl_spec_container_t<BD>&    p);  // structure with allocated tensors in L1 memory
  // output of step 2
  template<template<typename> class BD = B>
  void init_l1_input(
    const impl_spec_container_t<BD>&    p);  // structure with allocated tensors in L1 memory

 private:
  // include implementation specific private members
#include "tensor_gtoa_softmax_scale_param_priv.hpp"    // NOLINT [build/include_subdir]
};

// include implementation specific inline functionsi
#include "tensor_gtoa_softmax_inline.hpp"    // NOLINT [build/include_subdir]
}  // namespace tensor::v200
#endif  // TENSOR_API_TENSOR_GTOA_SOFTMAX_HPP_
