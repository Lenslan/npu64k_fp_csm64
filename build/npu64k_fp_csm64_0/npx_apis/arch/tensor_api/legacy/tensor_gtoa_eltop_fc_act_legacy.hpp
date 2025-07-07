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
 * tensor_gtoa_eltop_fc_act_legacy.hpp
 *
 * File defining a tensor level prelu API base on the generic tensor operation API
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

#ifndef TENSOR_API_LEGACY_TENSOR_GTOA_ELTOP_FC_ACT_LEGACY_HPP_
#define TENSOR_API_LEGACY_TENSOR_GTOA_ELTOP_FC_ACT_LEGACY_HPP_

// include interface datatypes
#include "./tensor_gtoa.hpp"


//
// All identifiers related to the tensor API go into namespace tensor::v200
//
gtoa_eltop_fc_act_params(
    aoffset_t      noi,       // number output channels (not vectors)
    bool           fmidbli,   // 16b input feature-map
    bool           fmodbli,   // 16b output feature-map
    act_bin_op_t   opi,       // eltwise binary operation to perform
    bool           eltact,    // first eltop then activ
    bool           inastri);  // if true then stream directly from convolution
#endif  // TENSOR_API_LEGACY_TENSOR_GTOA_ELTOP_FC_ACT_LEGACY_HPP_
