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
 * tensor_gtoa_clip.hpp
 *
 * File defining a tensor level clip API base on the generic tensor operation API
 *
 */

////////////////////////////////////////////////////////////////////////////////////////////////////
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

#ifndef TENSOR_API_LEGACY_TENSOR_GTOA_CLIP_LEGACY_HPP_
#define TENSOR_API_LEGACY_TENSOR_GTOA_CLIP_LEGACY_HPP_

//
// Constructor
//
// Input AM32/48, output FM8/16
gtoa_clip_params(
                  // number output channels (not vectors)
                  aoffset_t noi,
                  // output shape
                  const shape<3>& oshpi,
                  // output stride
                  const shape<3>& ostr,
                  // double wide input accumulator
                  bool accdbli,
                  // 16b output feature-map
                  bool fmdbli,
                  // if true then input stream directly from convolution
                  bool  inastri = false);

// Input AM32/48, output AM32
gtoa_clip_params(
                  // number output channels (not vectors)
                  aoffset_t noi,
                  // output shape
                  const shape<3>& oshpi,
                  // double wide input accumulator
                  bool accdbli,
                  // if true then input stream
                  bool inastri = false);

//
// Parameter encoding functions
//
// 16b/8b input, 8b output
template<typename T>
void param_enc(
                // per tensor output maximum clip value [Cout]
                const tensor_t<T, 1, xbuffer_t>& clipmax,
                // per tensor output minimum clip value [Cout]
                const tensor_t<T, 1, xbuffer_t>& clipmin,
                // outputs, buffers preallocated by caller
                // output encoded parameters
                const gtoa_params_impl_pchan<xbuffer_t>& obuf);
// 48b input, 8b output
void param_enc(
                // per channel 2b+6b prescale for scaling down wide acc
                const tensor_t<prescale_t, 1, xbuffer_t>& prescale,
                // per channel output maximum clip value [Cout]
                const tensor_t<int16_t, 1, xbuffer_t>& clipmax,
                // per channel output minimum clip value [Cout]
                const tensor_t<int16_t, 1, xbuffer_t>& clipmin,
                // outputs, buffers preallocated by caller
                // output encoded parameters
                const gtoa_params_impl_pchan<xbuffer_t>& obuf);

#endif  // TENSOR_API_LEGACY_TENSOR_GTOA_CLIP_LEGACY_HPP_

