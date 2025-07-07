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
 * tensor_conv.hpp
 *
 * File defining a tensor level convolution API
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


#ifndef TENSOR_API_TENSOR_CONV_HPP_
#define TENSOR_API_TENSOR_CONV_HPP_


///////////////////////////////////////////////////////////////////////////////////////////////
//
// Include implementation specific data structures
//
///////////////////////////////////////////////////////////////////////////////////////////////
#include "tensor_conv_types.hpp"


//
// All identifiers related to the tensor API go into namespace tensor::v200
//
namespace tensor::v200 {

///////////////////////////////////////////////////////////////////////////////////////////////
//
// Base class for all running on convolution HW accelerator
//
///////////////////////////////////////////////////////////////////////////////////////////////
template<template<typename> class B=buffer_t>
class conv_base {
#include "tensor_conv_param_priv.hpp"
  public:
  friend class conv_rt;
  //
  // Constructor
  //
  inline conv_base()  = default;
  inline conv_base(const conv_base&)  = default;

  //
  // Set implementation specific parameters, optional else use default
  //
  void set_impl_params(
                       const conv_params_impl_spec& p // structure with implementation specific parameters
                       );
  void get_impl_params(
                       conv_params_impl_spec& p       // return structure with implementation specific parameters
                       );


  //
  // Return an opaque structure with run-time parameters
  //
  void get_rt_params(conv_params_impl_main&);
};
  
///////////////////////////////////////////////////////////////////////////////////////////////
//
// Convolution run-time class
//
///////////////////////////////////////////////////////////////////////////////////////////////
class conv_rt {
  friend class conv_rt_list;
#include "tensor_conv_rt_priv.hpp"
  public:
  //
  // Constructor
  //
  conv_rt() = default;
  conv_rt(
          conv_params_impl_main&                 p  // convolution parameter class object
          );

  //
  // Set input feature-map
  //
  void set_input(
                 impl_spec_container_t<buffer_t>&          b  // tensor L1 allocation information
                 );
  void set_inputb(
                  impl_spec_container_t<buffer_t>&          b  // tensor L1 allocation information for secondary matrix in matrix mulply
                  );

  //
  // Set implementation specific run-time attributes
  //
  void set_impl_params(
                       const conv_rt_impl_spec&  p  // structure with run-time specific parameters
                       );
  void get_impl_params(
                       conv_rt_impl_spec&        p  // return structure with run-time specific parameters
                       );

  //
  // Initialize the tile specific parameters (padding array, coefficients, padding position)
  //
  void init_tile_params(
                        conv_params_impl_coef<buffer_t>&   cf  // coefficients for tile for FC layer
                        );
  void init_tile_params(
                        const shape<3>&          pp, // padding start position
                        conv_params_impl_coef<buffer_t>&   cf, // coefficients for tile
                        conv_params_impl_pad<buffer_t>&    pd  // input feature-map zero-point padding values
                        );
  void init_tile_paramsb(
                         const shape<3>&          pp, // padding start position
                         conv_params_impl_coef<buffer_t>&   cf, // coefficients for tile
                         conv_params_impl_pad<buffer_t>&    pd  // input feature-map zero-point padding values
                         );

  //
  // Optionally prepare for HW execution (prefetch)
  //
  void prepare();

  //
  // Start execution of HLAPI
  //
  void execute();

  //
  // Update the input tensor pointer with the value precomputed by the compiler
  //
  template <bool neg_check_only = false>
  void update_ptr(
                  const poffset_t&               ofs   // pointer offset for next input tile
                  );
  void update_ptrb(
                   const poffset_t&              ofs   // pointer offset for next input tile
                   );

  //
  // Update the input padding position
  //
  void update_padpos(
                     const shape<3>&             ofs   // padding offset for dimension
                     );

  //
  // Change the shape of the convolution
  //
  void set_alt_shape(
                     const conv_params_impl_alt& alt   // set and alternative convolution shape
                     );
  void set_alt_shapeb(
                      const conv_params_impl_alt& alt   // set and alternative convolution shape
                      );

  //
  // Overwrite useAcc/KeepAcc
  //
  void set_use_keep_acc(bool use_acc,     // new value for useAcc
                        bool keep_acc);   // new value for keepAcc

  //
  // Assign an output buffer
  //
  void set_output(acc_buf_impl_t<buffer_t>&);

  //
  // Update output with offset
  //
  void update_output(const poffset_t& o);

  //
  // Set implementation specific status field
  //
  void set_impl_status(
                       uint16_t sel,                        // select a particular status field
                       uint32_t val                         // value to be written
                       );
    
  //
  // Return implementation specific status fields
  //
  uint32_t get_impl_status(
                           uint16_t sel                     // select a particular status field
                           );

  //
  // Return input pointer 
  //
  uint64_t get_input_ptr();
    
  //
  // Return output pointer 
  //
  uint64_t get_output_ptr();

  //
  // Assign an input buffer
  //
  void set_input(localptr_t<ixpix_t> iptr);

  //
  // Assign an output buffer
  //
  void set_output(localptr_t<ixacc_t> optr);
  void set_output(localptr_t<vyixacc_t> optr);
};
//
// Create a run-time object in a target memory
//
conv_rt* create(mem_alloc_t& al, conv_params_impl_main& p);


// list object for conv_rt objects
class conv_rt_list {
  public:
  // constructor
  conv_rt_list();
  // append a descriptor to the end of the list
  void append(conv_rt* p);
  // prefetch the head of the list
  void prepare();
  // execute the list of descriptors
  void execute();
  // include implementation specific private members
#include "tensor_conv_rt_list_priv.hpp"
};
}  // namespace tensor::v200

#include "tensor_conv_inline.hpp"

// include derived classes
#include "tensor_conv_conv.hpp"
#include "tensor_conv_fc.hpp"
#include "tensor_conv_matmat.hpp"
#endif  // TENSOR_API_TENSOR_CONV_HPP_
