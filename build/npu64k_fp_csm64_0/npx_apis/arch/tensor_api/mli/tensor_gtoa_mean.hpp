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
 * tensor_gtoa_mean.hpp
 *
 * File defining a channel wise reduce mean API base on the generic tensor operation API
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

#ifndef TENSOR_API_TENSOR_GTOA_MEAN_HPP_
#define TENSOR_API_TENSOR_GTOA_MEAN_HPP_

// include interface datatypes
#include "./tensor_gtoa.hpp"
#include "./npu_act_lib.hpp"
#include "./tensor_gtoa_creduce_base.hpp"

//
// All identifiers related to the tensor API go into namespace tensor
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
class gtoa_mean_params : public gtoa_creduce_base_params<B> {
 public:
    gtoa_mean_params(
    aoffset_t       noi,               // number output channels (not vectors)
    const shape<3>& ishpi,             // input shape
    size_t          num,               // total number of elements
    act_dtype_t     intp,              // type of primary inputt
    act_dtype_t     outtp,             // type of outpu
    bool            bfp32scl,           // Whether use fp32 as prescale or fp8)
    bool            chnpad = true);    // If true, will do chnpad during mean
                                       // eitherwise use dedicated chnpad tapi
                                       // Only for compatibity, please set to false
                                       // for better performance


    inline gtoa_mean_params() = default;
    inline gtoa_mean_params(const gtoa_mean_params &) = default;

    void param_enc(
                const tensor_t<prescale_t,1,xbuffer_t>&   prescale,    // Input tensor scale value.
                const tensor_t<fp_e8m23_t,1,xbuffer_t>&   bias,        // nput tensor bias value (used for both asym and bias).
                // outputs, buffers preallocated by caller
                gtoa_params_impl_pchan<xbuffer_t>&        obuf         // output encoded parameters
                );

    void param_enc(
                const tensor_t<fp_e8m23_t,1,xbuffer_t>&   prescale,    // Input tensor scale value.
                const tensor_t<fp_e8m23_t,1,xbuffer_t>&   bias,        // nput tensor bias value (used for both asym and bias).
                // outputs, buffers preallocated by caller
                gtoa_params_impl_pchan<xbuffer_t>&        obuf         // output encoded parameters
                );

    // Set true for fp32 prescale, false for fp8 prescale
    void set_prescale_format(bool bfp32scl);

 private:
        // include implementation specific private members
        #include "./tensor_gtoa_mean_param_priv.hpp"
};
// include implementation specific inline
#include "./tensor_gtoa_mean_inline.hpp"
}   // namespace tensor
#endif    // TENSOR_API_TENSOR_GTOA_MEAN_HPP_
