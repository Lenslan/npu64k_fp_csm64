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
 * tensor_gtoa_act.hpp
 *
 * File defining a tensor level base class for all activation functions
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
// -5-  The compiler will encode function specific parameters through the param_enc method into
//      a data-strucutre allocated by the compiler
// -6-  The AOT compiler will dump the conv_param object into a binary stream
// -7-  The AOT run-time will restore the conv_param object from a binary stream
// -8-  The run-time will create one or multiple gtoa_rt objects from the parameter object,
//      one for each tile
// -9-  The run-time will assign run-time specific parameters through the set_impl_params
//      method of the gtoa_rt object.
// -10- The run-time will assign tile specific parameters through the init_tile_params method
// -11- The run-time needs to assure accumulators, control information, 
//      and activtion parameters have been loading into the L1 memory
// -12- The run-time may prepare for execution using the prepare method which may implement
//      prefetching
// -13- The run-time uses the execute method to start actual execution of the activation function
// -14- In case of asynchronous execution, run-time needs to use an implementation dependent
//      method to wait for completion (see step 10)
//
///////////////////////////////////////////////////////////////////////////////////////////////

#ifndef TENSOR_GTOA_ACT_INCLUDED
#define TENSOR_GTOA_ACT_INCLUDED


// include interface datatypes
#include "tensor_gtoa.hpp"


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
  class gtoa_act_params : public gtoa_params<B> {
  public:
    //
    // Constructors
    //
    gtoa_act_params(
            aoffset_t                  noi,             // number output channels (not vectors)
            const shape<3>&            oshpi,           // output shape, indexed by spatial_axis_t
            const shape<3>&            ostr,            // output stride
            act_dtype_t                intp,            // type of primary input
            act_dtype_t                outtp,           // type of output
            act_dtype_t                sctp,            // type of scale fp16 or bf16
            bool                       inastri          // if true then stream directly from convolution
            );
    // legacy constructor
    gtoa_act_params(
            aoffset_t                  noi,             // number output channels (not vectors)
            const shape<3>&            oshpi,           // output shape, indexed by spatial_axis_t
            const shape<3>&            ostr,            // output stride
            act_dtype_t                intp,            // type of primary input
            act_dtype_t                outtp,           // type of output
            bool                       inastri          // if true then stream directly from convolution
            );
    // default constructors
    inline gtoa_act_params() = default;
    inline gtoa_act_params(const gtoa_act_params&)  = default;

    //
    // Set implementation specific parameters, optional else use default (ONN)
    //
    void set_impl_params(
                         const gtoa_act_params_impl_spec& p   // structure with implementation specific parameters
                         );
    void get_impl_params(
                         gtoa_act_params_impl_spec& p         // return structure with implementation specific parameters
                         );

    //
    // Fused maxpooling parameters
    //
    void maxpool_enable(
            bool            twod,     // false: 1D (horizontally) or true: 2D
            bool            filter3,  // false: 2x2 (2) or true: 3x3 (3) maxpooling 2D (1D) filter size
            bool            stride2,  // false: stride 1 or true stride 2
            const shape<2>& padlim    // maxpool padding limits
            );

    //
    // Get the implementation specific minimum buffer shapes
    //
    void get_shapes(
                    gtoa_act_params_impl_shapes&   s          // structure with implementation specific minimum buffer sizes
                    );
    //
    // Reshape the ofm iterator
    //
    void reshape_ofm_iter(
                          const shape<5>& oshape             // new shape
                          );
    //
    // Assign L1 input memory buffer addresses
    //
    template<template<typename> class BD=B>
    void init_l1_input(
                        const impl_spec_container_t<BD>&      p      // structure with allocated buffers and tensors in L1 memory
                        );
    //
    // Assign L1 memory buffer addresses
    //
    template<template<typename> class BD=B>
    void init_l1(
                 const impl_spec_container_t<BD>&      p      // structure with allocated buffers and tensors in L1 memory
                 );

    //
    // Set the cmax with the last tile channel shape.
    //
   void set_tile_channel(aoffset_t noc);

    // include legacy interface
#include "./legacy/tensor_gtoa_act_legacy.hpp"

  protected:
    // include implementation specific private members
#include "tensor_gtoa_act_param_priv.hpp"
  };

  // include implementation specific inline functions
#include "tensor_gtoa_act_inline.hpp"
}
#endif
