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
 * tensor_WMSE.hpp
 *
 * File defining a tensor level reduce API base on the generic tensor operation API
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

#ifndef TENSOR_API_TENSOR_WMSE_HPP_
#define TENSOR_API_TENSOR_WMSE_HPP_

// include interface datatypes
#include "./tensor_gtoa.hpp"
#include "./npu_act_lib.hpp"

//
// All identifiers related to the tensor API go into namespace tensor::v200
//
namespace tensor::v200 {
///////////////////////////////////////////////////////////////////////////////////////////////
//
// Activation parameter base class
//
// This class is used by the AOT/JIT compiler to define the implementation
// specific parameters for an activation function. The parameter class is
//  used in the construction of the accompanying run-time object.
//
// The parameter object can be reused across multiple tiles of the same layer.
// Tile specific parameters like coefficients and padding positions are not
// encoded in the paramter object
///////////////////////////////////////////////////////////////////////////////////////////////

template <template <typename> class B = buffer_t>
class gtoa_wmse_params : public gtoa_params<B> {
 public:
    //
    // Constructor
    //
    gtoa_wmse_params(
        aoffset_t       noi,      // number output channels (not vectors)
        const shape<3>& ishpi,    // input shape, output inner is 1
        const shape<2>& padlim,   // padding window
        size_t num,               // number of elements to be pooled
        act_dtype_t in0tp,        // 16b input feature-map
        act_dtype_t outtp,        // 16b output feature-map
        bool useAcc);             // use previous accumulator value



    inline gtoa_wmse_params() = default;
    inline gtoa_wmse_params(const gtoa_wmse_params &) = default;

    //
    // Get the implementation specific minimum buffer shapes
    //
    // structure with implementation specific minimum buffer sizes
    void get_shapes(gtoa_act_params_impl_shapes& s); // NOLINT [runtime/references]
    //
    // Assign L1 memory buffer addresses
    //
    // structure with allocated buffers and tensors in L1 memory
    template <template <typename> class BD = B>
    void init_l1_output(const impl_spec_container_t<BD> &p);
     // structure with allocated buffers and tensors in L1 memory
    template <template <typename> class BD = B>
    void init_l1_input(const impl_spec_container_t<BD> &p);

    //
    // Switch function between initial tile accumulations (keepAcc=true)
    // and final tile average (keepAcc=false)
    //
    void modif_func(bool keepAcc, gtoa_params_impl_modif&);

    //
    // Switch to feature-map output
    //
    template <template <typename> class BD = B>
    void modif_out_fm(
      aoffset_t                        noi,               // number output channels
      act_dtype_t                      outtp,             // 16b output feature-map
      bool                             sati,              // saturate output
      bool                             use_opt_vm_layout, // use layout opt
      gtoa_params_impl_alt_fm&         a);                // NOLINT [runtime/references]

    //
    // Switch to accumulator output
    //
    void modif_out_acc(
      aoffset_t                        noi,      // number output channels
      gtoa_params_impl_alt_acc&        a);       // NOLINT [runtime/references]

    //
    // initialize the scale and shift parameters for mse
    //
    void init_wmse_scale(
      int16_t  scale,     // common scaling factor for all channels
      uint8_t  shift);    // common shift left amount for all channels

 private:
        // include implementation specific private members
        #include "./tensor_gtoa_wmse_param_priv.hpp"
};
// include implementation specific inline
#include "./tensor_gtoa_wmse_inline.hpp"
}   // namespace tensor::v200
#endif    // TENSOR_API_TENSOR_WMSE_HPP_
