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
 * tensor_gtoa_pad.hpp
 *
 * File defining a tensor level padding API base on the generic tensor operation API
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

#ifndef TENSOR_GTOA_PAD_INCLUDED
#define TENSOR_GTOA_PAD_INCLUDED


// include interface datatypes
#include "tensor_gtoa.hpp"
#include "npu_act_lib.hpp"


//
// All identifiers related to the tensor API go into namespace tensor::v200
//
namespace tensor::v200 {
  
  ///////////////////////////////////////////////////////////////////////////////////////////////
  //
  // Activation parameter base class
  //
  // This class is used by the AOT/JIT compiler to define the implementation specific parameters for an 
  // activation function. The parameter class is used in the construction of the accompanying run-time object.
  // 
  // The parameter object can be reused across multiple tiles of the same layer.
  // Tile specific parameters like coefficients and padding positions are not encoded in the paramter object
  ///////////////////////////////////////////////////////////////////////////////////////////////
  template<template<typename> class B=buffer_t>
  class gtoa_pad_params : public gtoa_params<B> {
  public:
    //
    // Constructor
    //
    // type parameterizable
    gtoa_pad_params(
                      aoffset_t                  noi,           // number output channels (not vectors)
                      const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                      aoffset_t                  padstri,       // padding stride
                      const shape<2>&            padposi,       // input padding position
                      const shape<2>&            padlimi,       // input padding boundaries
                      act_pmode_t                padmodei,      // padding mode
                      act_pinc_t                 padinci,       // padding increment mode
                      bool                       keepint,       // keep integer input when padding
                      act_dtype_t                intp,          // type of primary input
                      act_dtype_t                outtp          // type of output
                      );
    gtoa_pad_params(
                      aoffset_t                  noi,           // number output channels (not vectors)
                      const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                      aoffset_t                  padstri,       // padding stride
                      const shape<2>&            padposi,       // input padding position
                      const shape<2>&            padlimi,       // input padding boundaries
                      act_pmode_t                padmodei,      // padding mode
                      //act_pinc_t               padinci,       // padding increment mode, use the default value pinc_i16
                      bool                       keepint,       // keep integer input when padding
                      act_dtype_t                intp,          // type of primary input
                      act_dtype_t                outtp          // type of output
                      );


    inline gtoa_pad_params() = default;
    inline gtoa_pad_params(const gtoa_pad_params&)  = default;

    //
    // Get the implementation specific minimum buffer shapes
    //
    void get_shapes(
                    gtoa_act_params_impl_shapes&   s            // structure with implementation specific minimum buffer sizes
                    );
    
    //
    // Assign L1 memory buffer addresses
    //
    template<template<typename> class BD=B>
    void init_l1_output(
                 const impl_spec_container_t<BD>&      p            // structure with allocated buffers and tensors in L1 memory
                 );
    template<template<typename> class BD=B>
    void init_l1_input(
                 const impl_spec_container_t<BD>&      p            // structure with allocated buffers and tensors in L1 memory
                 );

  private:
    // include implementation specific private members
#include "tensor_gtoa_pad_param_priv.hpp"
  };

  // include implementation specific inline functions
#include "tensor_gtoa_pad_inline.hpp"
}
#endif
