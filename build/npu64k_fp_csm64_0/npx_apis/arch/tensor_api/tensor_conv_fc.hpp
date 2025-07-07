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
 * tensor_conv_fc.hpp
 *
 * File defining a tensor level fully-connected layer API
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

#ifndef TENSOR_API_TENSOR_CONV_FC_HPP_
#define TENSOR_API_TENSOR_CONV_FC_HPP_


// include interface datatypes
#include "tensor_conv.hpp"


//
// All identifiers related to the tensor API go into namespace tensor::v200
//
namespace tensor::v200 {

template<template<typename> class B=buffer_t>
class fc_params : public conv_base<B> {
#include "tensor_conv_fc_priv.hpp"
  public:
  //
  // Constructor
  //
  // V2 constructor supporting various datatypes
  fc_params(aoffset_t                          grp,           // number of groups
            aoffset_t                          nii,           // number input channels (not vectors), in units of 8b or 16b feature-map pixels
            aoffset_t                          noi,           // number output channels (not vectors)
            bool                               use_acci,      // use input accumulator
            bool                               keep_acci,     // keep output accumulator
            fm_cfg_t                           fm_tpi,        // feature-map type: fm_cfg_8b_e, fm_cfg_16b_e, fm_cfg_bf16_e, fm_cfg_fp16_e
            cf_cfg_t                           cf_tpi         // coefficient type: cf_cfg_4b_zp_e, cf_cfg_4b_nozp_e, cf_cfg_8b_zp_e, 
            // cf_cfg_8b_nozp_e, cf_cfg_16b_e, cf_cfg_bf16_e, cf_cfg_fp16_e
            );
  // V1 legacy constructors
  fc_params(aoffset_t                          grp,           // number of groups
            aoffset_t                          nii,           // number input channels (not vectors), in units of 8b or 16b feature-map pixels
            aoffset_t                          noi,           // number output channels (not vectors)
            bool                               use_acci,      // use input accumulator
            bool                               keep_acci,     // keep output accumulator
            bool                               fm_dbli,       // 8b or 16b feature-maps
            bool                               cf_dbli,       // 8b or 16b coefficients
            bool                               cf_zpi         // coefficients include a zero-point
            );    
  fc_params(aoffset_t                          nii,           // number input channels (not vectors), in units of 8b or 16b feature-map pixels
            aoffset_t                          noi,           // number output channels (not vectors)
            bool                               use_acci,      // use input accumulator
            bool                               keep_acci,     // keep output accumulator
            bool                               fm_dbli,       // 8b or 16b feature-maps
            bool                               cf_dbli,       // 8b or 16b coefficients
            bool                               cf_zpi         // coefficients include a zero-point
            );    
  inline fc_params()  = default;
  inline fc_params(const fc_params&)  = default;
    
  //
  // Get the implementation specific minimum buffer shapes
  //
  void get_shapes(
                  conv_params_impl_shapes&    p       // structure with implementation specific minimum buffer sizes
                  );
  
  //
  // Assign L1 memory buffer addresses
  //
  template<template<typename> class BD=B>
  void init_l1(
               const impl_spec_container_t<BD>&   p       // structure with allocated buffers and tensors in L1 memory
               );

  //
  // Precompute the pointer offset when updating an input feature-map tensor pointer
  //
  poffset_t update_ptr(
                       aoffset_t              chan_offset  // channel offset
                       );

  //
  // Coefficient encoding functions, can be called for multiple chunks; with and without zero-points
  //
  void coef_enc(const tensor_t<coef_t,4,xbuffer_t>&     icf,    // input coefficients [Grp][Cout/Grp][Cin/Grp][Coef h/l], h/l only for cf16 mode
                // outputs, buffers preallocated by caller
                conv_params_impl_coef<xbuffer_t>&       obuf,   // output encoded coefficients
                xbuffer_t<coef_t>&                      tbuf    // temporary xbuf
                );
  void coef_enc(const tensor_t<coef_t,3,xbuffer_t>&     icf,    // input coefficients [Grp][Cout/Grp][Cin/Grp], 8b only
                const tensor_t<coef_t,1,xbuffer_t>&     izp,    // input zero-points [Cout]
                // outputs, buffers preallocated by caller
                conv_params_impl_coef<xbuffer_t>&       obuf,   // output encoded coefficients
                xbuffer_t<coef_t>&                      tbuf    // temporary xbuf
                );
  void coef_enc(const tensor_t<fp_e5m10_t,3,xbuffer_t>& icf,    // fp16 input coefficients [Grp][Cout/Grp][Cin/Grp]
                // outputs, buffers preallocated by caller
                conv_params_impl_coef<xbuffer_t>&       obuf,   // output encoded coefficients
                xbuffer_t<coef_t>&                      tbuf    // temporary xbuf
                );
  void coef_enc(const tensor_t<fp_e8m7_t,3,xbuffer_t>&  icf,    // bf16 input coefficients [Grp][Cout/Grp][Cin/Grp]
                // outputs, buffers preallocated by caller
                conv_params_impl_coef<xbuffer_t>&       obuf,   // output encoded coefficients
                xbuffer_t<coef_t>&                      tbuf    // temporary xbuf
                );
  // wrappers for single group
  inline void coef_enc(const tensor_t<coef_t,3,xbuffer_t>&     icf,    // input coefficients [Cout/Grp][Cin/Grp][Coef h/l], h/l only for cf16 mode
                       // outputs, buffers preallocated by caller
                       conv_params_impl_coef<xbuffer_t>&       obuf,   // output encoded coefficients
                       xbuffer_t<coef_t>&                      tbuf    // temporary xbuf
                       ) {
    coef_enc(icf.split(2, 1), obuf, tbuf);
  }
  inline void coef_enc(const tensor_t<coef_t,2,xbuffer_t>&     icf,    // input coefficients [Cout/Grp][Cin/Grp], 8b only
                       const tensor_t<coef_t,1,xbuffer_t>&     izp,    // input zero-points [Cout]
                       // outputs, buffers preallocated by caller
                       conv_params_impl_coef<xbuffer_t>&       obuf,   // output encoded coefficients
                       xbuffer_t<coef_t>&                      tbuf    // temporary xbuf
                       ) {
    coef_enc(icf.split(1, 1), izp, obuf, tbuf);
  }
};
}  // namespace tensor::v200
// include implementation specific inline functions
#include "tensor_conv_fc_inline.hpp"
#endif  // TENSOR_API_TENSOR_CONV_FC_HPP_
