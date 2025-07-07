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
 * tensor_gtoa_relu.hpp
 *
 * File defining a tensor level relu API base on the generic tensor operation API
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

#ifndef TENSOR_API_LEGACY_TENSOR_GTOA_RELU_LEGACY_HPP_
#define TENSOR_API_LEGACY_TENSOR_GTOA_RELU_LEGACY_HPP_

//
// Constructor
//
// Input AM32/48, output FM8/16
gtoa_relu_params(
  aoffset_t       noi,               // number output channels (not vectors)
  const shape<3>& oshpi,             // output shape, indexed by spatial_axis_t
  const shape<3>& ostr,              // output stride
  bool            accdbli,           // double wide input accumulator
  bool            fmdbli,            // 16b output feature-map
  bool            inastri = false);  // if true then stream directly from convolution
// Input AM32/48, output AM32
gtoa_relu_params(
  aoffset_t       noi,               // number output channels (not vectors)
  const shape<3>& oshpi,             // output shape, indexed by spatial_axis_t
  bool            accdbli,           // double wide input accumulator
  bool            inastri = false);  // if true then stream directly from convolution

//
// Parameter encoding functions
//
// 32b input, 8b output
void param_enc(
  const tensor_t<int32_t, 1, xbuffer_t>&      bias,      // per channel bias [Cout]
  const tensor_t<int16_t, 1, xbuffer_t>&      posscale,  // per channel positive
                                                         // scaling factor [Cout]
  const tensor_t<uint8_t, 1, xbuffer_t>&      posshift,  // per channel positive
                                                         // shift right amount [Cout]
  const tensor_t<int8_t, 1, xbuffer_t>&       asymm,     // per channel output
                                                         // quantization offset [Cout]
  // outputs, buffers preallocated by caller
  gtoa_params_impl_pchan<xbuffer_t>&          obuf);     // NOLINT [runtime/references]
// 48b input, 8b output
void param_enc(
  const tensor_t<prescale_t, 1, xbuffer_t>&   prescale,  // per channel 2b+6b prescale for
                                                         // scaling down wide accumulators (pse
  const tensor_t<int32_t, 1, xbuffer_t>&      bias,      // per channel bias [Cout]
  const tensor_t<int16_t, 1, xbuffer_t>&      posscale,  // per channel positive
                                                         // scaling factor [Cout]
  const tensor_t<uint8_t, 1, xbuffer_t>&      posshift,  // per channel positive
                                                         // shift right amount [Cout]
  const tensor_t<int8_t, 1, xbuffer_t>&       asymm,     // per channel output
                                                         // quantization offset [Cout]
  // outputs, buffers preallocated by caller
  gtoa_params_impl_pchan<xbuffer_t>&          obuf);     // NOLINT [runtime/references]
// 32b input, 16b output
void param_enc(
  const tensor_t<int32_t, 1, xbuffer_t>&      bias,      // per channel bias [Cout]
  const tensor_t<int16_t, 1, xbuffer_t>&      posscale,  // per channel positive
                                                         // scaling factor [Cout]
  const tensor_t<uint8_t, 1, xbuffer_t>&      posshift,  // per channel positive shift
                                                         // right amount [Cout]
  // outputs, buffers preallocated by caller
  gtoa_params_impl_pchan<xbuffer_t>&          obuf);     // NOLINT [runtime/references]
// 48b input, 16b output
void param_enc(
  const tensor_t<prescale_t, 1, xbuffer_t>&   prescale,  // per channel 2b+6b prescale for
                                                         // scaling down wide accumulators
  const tensor_t<int32_t, 1, xbuffer_t>&      bias,      // per channel bias [Cout]
  const tensor_t<int16_t, 1, xbuffer_t>&      posscale,  // per channel positive
                                                         // scaling factor [Cout]
  const tensor_t<uint8_t, 1, xbuffer_t>&      posshift,  // per channel positive shift
                                                         // right amount [Cout]
  // outputs, buffers preallocated by caller
  gtoa_params_impl_pchan<xbuffer_t>&          obuf);     // NOLINT [runtime/references]

#endif  // TENSOR_API_LEGACY_TENSOR_GTOA_RELU_LEGACY_HPP_
