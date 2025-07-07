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
 * tensor_gtoa.hpp
 *
 * File defining a tensor level generic tensor operation API
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
// -5-  The compiler will call the ctrl_enc method to fill the control structure allocated by 
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

#ifndef TENSOR_GTOA_INCLUDED
#define TENSOR_GTOA_INCLUDED


// include interface datatypes
#include "tensor.hpp"

///////////////////////////////////////////////////////////////////////////////////////////////
//
// Include implementation specific data structures
//
///////////////////////////////////////////////////////////////////////////////////////////////
#include "tensor_gtoa_types.hpp"

constexpr uint8_t  kPreScaleOneShiftBias =  31;
constexpr uint8_t  kPreScaleShiftBias    =  33;

//
// All identifiers related to the tensor API go into namespace tensor::v200
//
namespace tensor::v200 {

///////////////////////////////////////////////////////////////////////////////////////////////
//
// Generic tensor operation parameter base class
//
// This class is used by the AOT/JIT compiler to define the implementation specific parameters for 
// an activation function. The parameter class is used in the construction of the accompanying 
// run-time object.
// 
// The parameter object can be reused across multiple tiles of the same layer.
// Tile specific parameters like coefficients and padding positions are not encoded in the paramter 
// object
///////////////////////////////////////////////////////////////////////////////////////////////
template<template<typename> class B=buffer_t>
class gtoa_params {
 public:
  friend class gtoa_rt;
  //
  // Constructor
  //
  inline gtoa_params();
  inline gtoa_params(const gtoa_params&)  = default;
    
  //
  // Precompute the pointer offset when updating an input feature-map tensor pointer
  //
  poffset_t update_iptr0(
                         const shape<3>&        spat_offset, // spatial offset
                         aoffset_t              chan_offset  // channel offset
                         );
  poffset_t update_iptr1(
                         const shape<3>&        spat_offset, // spatial offset
                         aoffset_t              chan_offset  // channel offset
                         );
  poffset_t update_optr(
                        const shape<3>&         spat_offset, // spatial offset
                        aoffset_t               chan_offset  // channel offset
                        );
    
  //
  // Set a smaller, alternative tile shape e.g. for the boundaries of the feature-map
  //
  void set_alt_shape(
    aoffset_t                  noi,         // number channels (not vectors)
    const shape<3>&            oshpi,       // output shape, indexed by spatial_axis_t
    gtoa_params_impl_alt&      alt          // encoded alternative shape
                 );

  //
  // set per channel write mask
  //
  void set_channel_mask(
                        const uint16_t   cmaskn // channel mask inverted
                        );

  //
  // Return an opaque structure with run-time parameters
  //
  void get_rt_params(gtoa_params_impl_main&);

 protected:
  // input parameters
#include "tensor_gtoa_param_priv.hpp"
};



///////////////////////////////////////////////////////////////////////////////////////////////
//
// Generic tensor-operation run-time class
//
///////////////////////////////////////////////////////////////////////////////////////////////
class gtoa_rt {
 public:
  //
  // Constructor
  //
  gtoa_rt(
          gtoa_params_impl_main&       p     // generic tensor operation parameter class object
          );
    
  //
  // Set implementation specific run-time attributes
  //
  void set_impl_params(
                const gtoa_rt_impl_spec&  p     // structure with run-time specific parameters
                       );
  void get_impl_params(
           gtoa_rt_impl_spec&        p     // return structure with run-time specific parameters
                       ) const;

  //
  // Set/get scalar input/output values
  //
  void set_scalar(
                  const aoffset_t&               i,    // index of scalar to pass
                  const int32_t&                 s     // scalar value to pass
                  );
  int32_t get_scalar() const;                          // return value of scalar 0

  //
  // Set an alternative function
  //
  void set_alt_func(const gtoa_params_impl_modif&);

  //
  // Set an alternative output feature-map/accumulator type
  //
  void set_alt_output_fm(const gtoa_params_impl_alt_fm&, impl_spec_container_t<buffer_t>& l);
  void set_alt_output_acc(const gtoa_params_impl_alt_acc&, acc_buf_impl_t<buffer_t>& b);

  //
  // Overwrite inastr
  //
  void set_inastr(bool inastr);   // new value for inastr

  //
  // Initialize the tile specific parameters (per channel parameters)
  //
  void init_tile_params(
     const gtoa_params_impl_pchan<buffer_t>& p  // structure with run-time tile specific parameters
                        );

  //
  // Optionally initialize the tile specific maxpooling parameters
  //
  void set_maxpool_buffer(
                const gtoa_maxpool_buffer&  obuf   // maxpooling tile overlap buffer
                          );

  //
  // Set absolute padding position
  //
  void set_padpos(
                  const shape<2>&                padpos // input padding position
                  );

  //
  // Update the input padding position
  //
  void update_padpos(
                     const shape<2>&             ofs   // padding offset for dimension
                     );

  //
  // set per channel mask
  //
  void set_channel_mask(
                        const uint16_t           cmaskn // channel mask inverted
                        );

    
  //
  // Set input and output feature-map tensors
  //
  void set_input0(impl_spec_container_t<buffer_t>& l); // primary L1 feature-map tensor information
  void set_input1(impl_spec_container_t<buffer_t>& l); // secondary L1 feature-map tensor information
  void set_inputs(impl_spec_container_t<buffer_t>& l, aoffset_t s = TNSVSIZE);   
  // primary/secondary L1 feature-map tensor information
  void set_output(impl_spec_container_t<buffer_t>& l);   // output L1 feature-map tensor information

  //
  // Set accumulator input buffer and output buffer
  //
  void set_acc_input0(const acc_buf_impl_t<buffer_t>&      b);
  void set_acc_input1(const acc_buf_impl_t<buffer_t>&      b);
  void set_acc_output(acc_buf_impl_t<buffer_t>&            b);

  //
  // Slide input or output tensor input window of the underlying buffer as precomputed by compiler
  //
  // Update the tensor pointers with the value precomputed by the compiler
  template <bool neg_check_only = false>
  void update_iptr0(const poffset_t&             o);   // pointer offset for next input 0 tile
  template <bool neg_check_only = false>
  void update_iptr1(const poffset_t&             o);   // pointer offset for next input 1 tile
  void update_iptrs(const poffset_t&             o);   // pointer offset for next input 0&1 tile
  template <bool neg_check_only = false>
  void update_optr(const poffset_t&              o);   // pointer offset for next output tile
  void update_gather_iptr0(const poffset_t&      o);   // update the pointer for gather operations

  //
  // Change the shape of the input and output tensors as precomputed
  //
  void set_alt_shape(
        const gtoa_params_impl_alt& alt   // set and alternative generic tensor operation shape
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
  uint64_t get_acc_input0_ptr();
  uint64_t get_acc_input1_ptr();
  uint64_t get_fm_input0_ptr();
  uint64_t get_fm_input1_ptr();

  //
  // Return output pointer 
  //
  uint64_t get_acc_output_ptr();
  uint64_t get_fm_output_ptr();

  //
  // Set input and output accumulator buffers
  //
  void set_acc_input0(localptr_t<ixacc_t> iptr);
  void set_acc_input1(localptr_t<ixacc_t> iptr);
  void set_acc_output(localptr_t<ixacc_t> optr);
  void set_acc_input0(localptr_t<vyixacc_t> iptr);
  void set_acc_input1(localptr_t<vyixacc_t> iptr);
  void set_acc_output(localptr_t<vyixacc_t> optr);

  //
  // Set input and output feature-map buffers
  //
  void set_input0(localptr_t<ixpix_t> iptr);
  void set_input1(localptr_t<ixpix_t> iptr);
  void set_output(localptr_t<ixpix_t> optr);

 protected:
  // include implementation specific private members
#include "tensor_gtoa_rt_priv.hpp"
};

// list object for gtoa_rt objects
class gtoa_rt_list {
 public:
  // constructor
  gtoa_rt_list();
  // append a descriptor to the end of the list
  void append(gtoa_rt* p);
  // prefetch the head of the list
  void prepare();
  // execute the list of descriptors
  void execute();
 private:
  // include implementation specific private members
#include "tensor_gtoa_rt_list_priv.hpp"
};

//
// Create a run-time object in a target memory
//
gtoa_rt* create(mem_alloc_t& al, gtoa_params_impl_main& p);
  
// include implementation specific inline functions
#include "tensor_gtoa_inline.hpp"
}
#endif
