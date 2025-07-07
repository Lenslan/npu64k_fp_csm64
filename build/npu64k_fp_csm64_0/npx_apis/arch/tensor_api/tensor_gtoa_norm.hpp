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
 * tensor_gtoa_norm.hpp
 *
 * File defining a tensor level normalization operations on the generic tensor operation API
 * Normalization is done per channel, across all spatial dimensions
 *
 * All normalization layers compute a per channel reciprocal scaling factor 
 * The output channel vector is encoded as a pseudo floating-point format consisting of a mantissa (multiplier) and an exponent (shift)
 * A subsequent binary SCALE layer can be used to scale to inputs
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

#ifndef TENSOR_GTOA_NORM_INCLUDED
#define TENSOR_GTOA_NORM_INCLUDED


// include interface datatypes
#include "tensor_gtoa.hpp"
#include "npu_act_lib.hpp"


//
// All identifiers related to the tensor API go into namespace tensor::v200
//
namespace tensor::v200 {
  
  ///////////////////////////////////////////////////////////////////////////////////////////////
  //
  // L1 normalization parameter class, computes to reciprocal scaling facts
  // in a pseudo floating-point format consisting of a mantissa multiplier() and an exponent (shift)
  //
  ///////////////////////////////////////////////////////////////////////////////////////////////
  template<template<typename> class B=buffer_t>
  class gtoa_l1norm_params : public gtoa_params<B> {
  public:
    //
    // Constructor
    //
    gtoa_l1norm_params(
                         aoffset_t                noi,          // number output channels (not vectors)
                         const shape<3>&          ishpi,        // input shape, indexed by spatial_axis_t
                         bool                     fmdbli        // 8b/16b input feature-map
                         );
    inline gtoa_l1norm_params() = default;
    inline gtoa_l1norm_params(const gtoa_l1norm_params<B>&) = default;

    //
    // Get the implementation specific minimum buffer shapes
    //
    void get_shapes(
                    gtoa_act_params_impl_shapes& s            // structure with implementation specific minimum buffer sizes
                    );
    
    //
    // Assign L1 memory buffer addresses
    //
    template<template<typename> class BD=B>
    void init_l1_output(
                 const impl_spec_container_t<BD>&    p            // structure with allocated buffers and tensors in L1 memory
                 );
    template<template<typename> class BD=B>
    void init_l1_input(
                 const impl_spec_container_t<BD>&    p            // structure with allocated buffers and tensors in L1 memory
                 );
    
  private:
    // include implementation specific private members
#include "tensor_gtoa_l1norm_param_priv.hpp"
  };

  ///////////////////////////////////////////////////////////////////////////////////////////////
  //
  // L2 normalization parameter class, computes to reciprocal scaling facts
  // in a pseudo floating-point format consisting of a mantissa multiplier() and an exponent (shift)
  //
  ///////////////////////////////////////////////////////////////////////////////////////////////
  template<template<typename> class B=buffer_t>
  class gtoa_l2norm_params : public gtoa_params<B> {
  public:
    //
    // Constructor
    //
    gtoa_l2norm_params(
                         aoffset_t                noi,          // number output channels (not vectors)
                         const shape<3>&          ishpi,        // input shape, indexed by spatial_axis_t
                         bool                     fmdbli        // 8b/16b input feature-map
                         );
    inline gtoa_l2norm_params() = default;
    inline gtoa_l2norm_params(const gtoa_l2norm_params&) = default;

    //
    // Get the implementation specific minimum buffer shapes
    //
    void get_shapes(
                    gtoa_act_params_impl_shapes& s            // structure with implementation specific minimum buffer sizes
                    );
    
    //
    // Assign L1 memory buffer addresses
    //
    template<template<typename> class BD=B>
    void init_l1_output(
                 const impl_spec_container_t<BD>&    p            // structure with allocated buffers and tensors in L1 memory
                 );
    template<template<typename> class BD=B>
    void init_l1_input(
                 const impl_spec_container_t<BD>&    p            // structure with allocated buffers and tensors in L1 memory
                 );
    
  private:
    // include implementation specific private members
#include "tensor_gtoa_l2norm_param_priv.hpp"
  };

  ///////////////////////////////////////////////////////////////////////////////////////////////
  //
  // Normalization scaling parameter class, multiply the input by the reciprocal computed by the norm classes
  //
  ///////////////////////////////////////////////////////////////////////////////////////////////
  template<template<typename> class B=buffer_t>
  class gtoa_scale_params : public gtoa_params<B> {
  public:
    //
    // Constructor
    //
    gtoa_scale_params(
                      aoffset_t                noi,           // number output channels (not vectors)
                      const shape<3>&          ishpi,         // input shape, indexed by spatial_axis_t
                      bool                     ifmdbli,       // 8b/16b input feature-map
                      bool                     ofmdbli,       // 8b/16b output feature-map
                      int32_t                  scale          // output scale
                      );
    inline gtoa_scale_params() = default;
    inline gtoa_scale_params(const gtoa_scale_params&) = default;

    //
    // Get the implementation specific minimum buffer shapes
    //
    void get_shapes(
                    gtoa_act_params_impl_shapes& s            // structure with implementation specific minimum buffer sizes
                    );
    
    //
    // Assign L1 memory buffer addresses
    //
    template<template<typename> class BD=B>
    void init_l1_output(
                 const impl_spec_container_t<BD>&    p            // structure with allocated buffers and tensors in L1 memory
                 );
    template<template<typename> class BD=B>
    void init_l1_input0(
                 const impl_spec_container_t<BD>&    p            // structure with allocated buffers and tensors in L1 memory
                 );
    // input reciprocals
    template<template<typename> class BD=B>
    void init_l1_input1(
                 const impl_spec_container_t<BD>&    p            // structure with allocated buffers and tensors in L1 memory
                 );
    static const int32_t l1scale_16to16; // L1 normalization input 16b, output 16b scaling factor
    static const int32_t l1scale_16to8;  // L1 normalization input 16b, output 8b scaling factor
    static const int32_t l1scale_8to16;  // L1 normalization input 8b, output 16b scaling factor
    static const int32_t l1scale_8to8;   // L1 normalization input 8b, output 8b scaling factor
    static const int32_t l2scale_16to16; // L2 normalization input 16b, output 16b scaling factor
    static const int32_t l2scale_16to8;  // L2 normalization input 16b, output 8b scaling factor
    static const int32_t l2scale_8to16;  // L2 normalization input 8b, output 16b scaling factor
    static const int32_t l2scale_8to8;   // L2 normalization input 8b, output 8b scaling factor
  private:
    // include implementation specific private members
#include "tensor_gtoa_scale_param_priv.hpp"
  };
  // include implementation specific inline functionsi
#include "tensor_gtoa_norm_inline.hpp"
}
#endif
