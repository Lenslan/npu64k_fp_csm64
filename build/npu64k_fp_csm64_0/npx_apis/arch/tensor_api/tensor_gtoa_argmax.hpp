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
 * tensor_gtoa_argmax.hpp
 *
 * File defining a tensor argmax operation on the generic tensor operation API
 * ARGMAX reduces the inner spatial dimension to 1, returning the index of the maximum value of the elements in that dimension
 * so: out[d][w][0][c] = max(in[d][h][w][c], 0 <= w < W);
 * the output is encoded as 16b feature-map
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

#ifndef TENSOR_GTOA_ARGMAX_INCLUDED
#define TENSOR_GTOA_ARGMAX_INCLUDED


// include interface datatypes
#include "tensor_gtoa.hpp"
#include "npu_act_lib.hpp"


//
// All identifiers related to the tensor API go into namespace tensor::v200
//
namespace tensor::v200 {
  
  ///////////////////////////////////////////////////////////////////////////////////////////////
  //
  // Spatial ARGMAX parameter class
  //
  ///////////////////////////////////////////////////////////////////////////////////////////////
  template<template<typename> class B=buffer_t>
  class gtoa_argmax_params : public gtoa_params<B> {
  public:
    //
    // Generic constructor for ARGMAX reduction over inner spatial
    //
    gtoa_argmax_params(
                       aoffset_t                noi,          // number input channels (not vectors)
                       const shape<3>&          ishpi,        // input shape, indexed by spatial_axis_t
                       act_dtype_t              fmtpi         // feature-map data type
                       );

    //
    // Constructor for ARGMAX reduction of inner spatial dimension
    //
    gtoa_argmax_params(
                       aoffset_t                noi,          // number output channels (not vectors)
                       const shape<3>&          ishpi,        // input shape, indexed by spatial_axis_t
                       bool                     fmdbli        // 8b/16b input feature-map
                       );
    inline gtoa_argmax_params() = default;
    inline gtoa_argmax_params(const gtoa_argmax_params&) = default;

    //
    // Set packing mode
    //
    void set_pack_mode(
                    pack_mode_t   pm  // packing mode (i4/i8/i16)
                    );

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
#include "tensor_gtoa_argmax_param_priv.hpp"
  };

  ///////////////////////////////////////////////////////////////////////////////////////////////
  //
  // Channel ARGMAX parameter classes, two HLAPI steps
  //
  ///////////////////////////////////////////////////////////////////////////////////////////////
  template<template<typename> class B=buffer_t>
  class gtoa_cargmax0_params : public gtoa_params<B> {
     template<template<typename> class U> friend class gtoa_cargmax1_params;
  public:
    //
    // Generic constructor for ARGMAX reduction over channel
    //
    gtoa_cargmax0_params(
                         aoffset_t                noi,          // number input channels (not vectors)
                         const shape<3>&          ishpi,        // input shape, indexed by spatial_axis_t
                         act_dtype_t              fmtpi         // feature-map data type
                         );

    inline gtoa_cargmax0_params() = default;
    inline gtoa_cargmax0_params(const gtoa_cargmax0_params&) = default;

    //
    // Get the implementation specific minimum buffer shapes
    //
    void get_shapes(
                    gtoa_act_params_impl_shapes& s            // structure with implementation specific minimum buffer sizes
                    );
    
    //
    // Assign L1 memory buffer addresses, output to AM
    //
    template<template<typename> class BD=B>
    void init_l1_input(
                 const impl_spec_container_t<BD>&    p            // structure with allocated buffers and tensors in L1 memory
                 );
                 template<template<typename> class BD=B>
    void init_l1_output(
                 const impl_spec_container_t<BD>&    p            // structure with allocated buffers and tensors in L1 memory
                 );
  private:
    // include implementation specific private members
#include "tensor_gtoa_cargmax0_param_priv.hpp"
  };
  template<template<typename> class B=buffer_t>
  class gtoa_cargmax1_params : public gtoa_params<B> {
  public:
    //
    // Generic constructor for ARGMAX reduction over channel
    //
    gtoa_cargmax1_params(
                         const gtoa_cargmax0_params<B>&    p0   // constructed from 0 object
                         );

    inline gtoa_cargmax1_params() = default;
    inline gtoa_cargmax1_params(const gtoa_cargmax1_params&) = default;

    //
    // Get the implementation specific minimum buffer shapes
    //
    void get_shapes(
                    gtoa_act_params_impl_shapes& s            // structure with implementation specific minimum buffer sizes
                    );
    
    //
    // Assign L1 memory buffer addresses, input from AM
    //
    template<template<typename> class BD=B>
    void init_l1_input(
                 const impl_spec_container_t<BD>&    p            // structure with allocated buffers and tensors in L1 memory
                 );
    template<template<typename> class BD=B>
    void init_l1_output(
                 const impl_spec_container_t<BD>&    p            // structure with allocated buffers and tensors in L1 memory
                 );
  private:
    // include implementation specific private members
#include "tensor_gtoa_cargmax1_param_priv.hpp"
  };
  // include implementation specific inline functionsi
#include "tensor_gtoa_argmax_inline.hpp"
#include "tensor_gtoa_cargmax_inline.hpp"
}
#endif
