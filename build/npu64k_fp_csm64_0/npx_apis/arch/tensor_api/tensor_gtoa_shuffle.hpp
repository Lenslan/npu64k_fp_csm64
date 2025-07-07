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
 * tensor_gtoa_shuffle.hpp
 *
 * File defining a tensor level shuffle operation on the generic tensor operation API
 * The transpose operation transposes groups of spatial pixels from tns [D][H][G*W][C] to [D][H][W*G][C] layout
 * the NPX tensor API implementation will round-up the groups size W to a multiple of 8
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

#ifndef TENSOR_GTOA_SHUFFLE_INCLUDED
#define TENSOR_GTOA_SHUFFLE_INCLUDED


// include interface datatypes
#include "tensor_gtoa.hpp"
#include "npu_act_lib.hpp"


//
// All identifiers related to the tensor API go into namespace tensor::v200
//
namespace tensor::v200 {
  
  ///////////////////////////////////////////////////////////////////////////////////////////////
  //
  // Shuffle parameter class
  //
  ///////////////////////////////////////////////////////////////////////////////////////////////
  template<template<typename> class B=buffer_t>
  class gtoa_shuffle_params : public gtoa_params<B> {
  public:
    //
    // Constructor
    //
    gtoa_shuffle_params(
                         aoffset_t                noi,          // number output channels (not vectors)
                         const shape<3>&          ishpi,        // input shape, indexed by spatial_axis_t
                         aoffset_t                grpi,         // number of groups
                         bool                     fmdbli        // 8b/16b input feature-map
                         );
    inline gtoa_shuffle_params() = default;
    inline gtoa_shuffle_params(const gtoa_shuffle_params<B>&) = default;

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
#include "tensor_gtoa_shuffle_param_priv.hpp"
  };

  ///////////////////////////////////////////////////////////////////////////////////////////////
  //
  // Shuffle parameter class, for group 2 shuffle layers
  //
  ///////////////////////////////////////////////////////////////////////////////////////////////
  template<template<typename> class B=buffer_t>
  class gtoa_shuffle_g2_params : public gtoa_params<B> {
  public:
    //
    // Constructor
    //
    gtoa_shuffle_g2_params(
                         aoffset_t                noi,          // number output channels (not vectors)
                         const shape<3>&          ishpi,        // input shape, indexed by spatial_axis_t
                         bool                     odd,          // even or odd outputs
                         bool                     fmdbli        // 8b/16b input feature-map
                         );
    inline gtoa_shuffle_g2_params() = default;
    inline gtoa_shuffle_g2_params(const gtoa_shuffle_g2_params<B>&) = default;

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
#include "tensor_gtoa_shuffle_g2_param_priv.hpp"
  };

  // include implementation specific inline functionsi
#include "tensor_gtoa_shuffle_inline.hpp"
}
#endif
