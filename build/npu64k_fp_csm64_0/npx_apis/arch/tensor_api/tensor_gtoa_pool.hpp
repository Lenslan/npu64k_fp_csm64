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
 * tensor_gtoa_pool.hpp
 *
 * File defining a tensor level pooling operations on the generic tensor operation API
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

#ifndef TENSOR_GTOA_POOL_INCLUDED
#define TENSOR_GTOA_POOL_INCLUDED


// include interface datatypes
#include "tensor_gtoa.hpp"
#include "npu_act_lib.hpp"


//
// All identifiers related to the tensor API go into namespace tensor::v200
//
namespace tensor::v200 {
  
  ///////////////////////////////////////////////////////////////////////////////////////////////
  //
  // Max-pooling 2D parameter class
  //
  ///////////////////////////////////////////////////////////////////////////////////////////////
  template<template<typename> class B=buffer_t>
  class gtoa_maxpool_params : public gtoa_params<B> {
  public:
    //
    // Constructor
    //
    // VM(8b/16b) to VM(8b/16b)
    gtoa_maxpool_params(
                        aoffset_t                noi,         // number output channels (not vectors)
                        const shape<2>&          oshpi,       // output shape, indexed by spatial_axis_t
                        const shape<2>&          kshpi,       // kernel shape
                        const shape<2>&          kstri,       // kernel stride
                        const shape<2>&          padlimi,     // input padding boundaries
                        act_dtype_t              intp,        // type of input
                        act_dtype_t              outtp        // type of output
                        );
    inline gtoa_maxpool_params() = default;
    inline gtoa_maxpool_params(const gtoa_maxpool_params<B>&) = default;

    //
    // Get the implementation specific minimum buffer shapes
    //
    void get_shapes(
                    gtoa_act_params_impl_shapes& s            // structure with implementation specific minimum buffer sizes
                    );

    //
    // Set packing mode
    //
    void set_pack_mode(
                    pack_mode_t   pm  // packing mode (i4/i8/i16)
                    );
    
    //
    // Assign L1 memory buffer addresses
    //
    template<template<typename> class BD=B>
    void init_l1_output(
                 const impl_spec_container_t<BD>&    p        // structure with allocated buffers and tensors in L1 memory
                 );
    template<template<typename> class BD=B>
    void init_l1_input(
                 const impl_spec_container_t<BD>&    p        // structure with allocated buffers and tensors in L1 memory
                 );
  // include legacy interface
#include "./legacy/tensor_gtoa_maxpool_legacy.hpp"
  private:
    // include implementation specific private members
#include "tensor_gtoa_maxpool_param_priv.hpp"
  };

  ///////////////////////////////////////////////////////////////////////////////////////////////
  //
  // Average pooling class, returns sum of inputs in filter
  //
  ///////////////////////////////////////////////////////////////////////////////////////////////
  template<template<typename> class B=buffer_t>
  class gtoa_avgpool_params : public gtoa_params<B> {
  public:
    //
    // Constructor
    //
    // Generic average pooling
    gtoa_avgpool_params(
                        aoffset_t                noi,           // number output channels (not vectors)
                        const shape<2>&          oshpi,         // output shape, indexed by spatial_axis_t
                        const shape<2>&          kshpi,         // kernel shape
                        const shape<2>&          kstri,         // kernel stride
                        const shape<2>&          padlimi,       // input padding boundaries
                        act_dtype_t              intp,          // type of input
                        act_dtype_t              outtp,         // type of output
                        bool                     excl_pad=true  // exclude padding, divide by non-padded number
                        );
    inline gtoa_avgpool_params() = default;
    inline gtoa_avgpool_params(const gtoa_avgpool_params&) = default;

    //
    // Get the implementation specific minimum buffer shapes
    //
    void get_shapes(
                    gtoa_act_params_impl_shapes& s            // structure with implementation specific minimum buffer sizes
                    );

    //
    // Set packing mode
    //
    void set_pack_mode(
                    pack_mode_t   pm  // packing mode (i4/i8/i16)
                    );

    //
    // Assign L1 memory buffer offsets for input feature-map
    //
    template<template<typename> class BD=B>
    void init_l1_input0(
                 const impl_spec_container_t<BD>&    p            // structure with allocated buffers and tensors in L1 memory
                 );

    //
    // Assign L1 memory buffer offsets for output
    //
    template<template<typename> class BD=B>
    void init_l1_output(
                 const impl_spec_container_t<BD>&    p            // structure with allocated buffers and tensors in L1 memory
                 );
  // include legacy interface
#include "./legacy/tensor_gtoa_avgpool_legacy.hpp"
  private:
    // include implementation specific private members
#include "tensor_gtoa_avgpool_param_priv.hpp"
  };

  ///////////////////////////////////////////////////////////////////////////////////////////////
  //
  // Sum-pooling 2D parameter class
  //
  ///////////////////////////////////////////////////////////////////////////////////////////////
  template<template<typename> class B=buffer_t>
  class gtoa_sumpool_params : public gtoa_params<B> {
  public:
    //
    // Constructor
    //
    // VM(8b/16b) to AM(32b)
    gtoa_sumpool_params(
                        aoffset_t                noi,         // number output channels (not vectors)
                        const shape<2>&          oshpi,       // output shape, indexed by spatial_axis_t
                        const shape<2>&          kshpi,       // kernel shape
                        const shape<2>&          kstri,       // kernel stride
                        const shape<2>&          padlimi,     // input padding boundaries
                        act_dtype_t              intp,        // type of input
                        act_dtype_t              outtp        // type of output
                        );
    inline gtoa_sumpool_params() = default;
    inline gtoa_sumpool_params(const gtoa_sumpool_params&) = default;

    //
    // Get the implementation specific minimum buffer shapes
    //
    void get_shapes(
                    gtoa_act_params_impl_shapes& s            // structure with implementation specific minimum buffer sizes
                    );

    //
    // Set packing mode
    //
    void set_pack_mode(
                    pack_mode_t   pm  // packing mode (i4/i8/i16)
                    );

    //
    // Assign L1 memory buffer offsets for scales, from scale_enc
    //
    template<template<typename> class BD=B>
    void init_l1_input(
                 const impl_spec_container_t<BD>&    scales       // structure with allocated buffers and tensors in L1 memory
                 );
  // include legacy interface
#include "./legacy/tensor_gtoa_sumpool_legacy.hpp"
  private:
    gtoa_act_params_impl_shapes shapes;  // buffer shapes
    aoffset_t                   cmax;    // number of channels
    bool                        ifmdbl;
    shape<2>                    str;     // kernel stride
  };

  // include implementation specific inline functionsi
#include "tensor_gtoa_pool_inline.hpp"
}
#endif
