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
 * tensor_conv_conv.hpp
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


#ifndef TENSOR_API_TENSOR_CONV_CONV_HPP_
#define TENSOR_API_TENSOR_CONV_CONV_HPP_


// include interface datatypes
#include "tensor_conv.hpp"


//
// All identifiers related to the tensor API go into namespace tensor::v200
//
namespace tensor::v200 {

///////////////////////////////////////////////////////////////////////////////////////////////
//
// Convolution parameter class
//
// This class is used by the AOT/JIT compiler to define the implementation specific parameters for a 
// convolution. The parameter class is used in the construction of the accompanying run-time object.
//
// The parameter object can be reused across multiple tiles of the same layer.
// Tile specific parameters like coefficients and padding positions are not encoded in the paramter object
///////////////////////////////////////////////////////////////////////////////////////////////
template<template<typename> class B=buffer_t>
class conv_params : public conv_base<B> {
#include "tensor_conv_conv_priv.hpp"
  public:
  //
  // Constructor
  //
  // constructor for 1D/2D/3D convolution object, supporting various datatypes
  conv_params(
              aoffset_t                 grpi,          // number of groups in convolution 
              aoffset_t                 nii,           // number input channels (not vectors), in units of 8b or 16b feature-map pixels
              aoffset_t                 noi,           // number output channels (not vectors)
              const shape<3>&           oshpi,         // output shape
              const shape<3>&           filteri,       // filter dimension
              const shape<3>&           stridei,       // filter stride
              const shape<3>&           dili,          // filter dilation
              const shape<3>&           padlimi,       // right&bottom limit of padding window
              bool                      use_acci,      // use input accumulator from AM else 0
              bool                      keep_acci,     // keep output accumulator in AM else stream
              fm_cfg_t                  fm_tpi,        // feature-map type: fm_cfg_8b_e, fm_cfg_16b_e, fm_cfg_bf16_e, fm_cfg_fp16_e
              cf_cfg_t                  cf_tpi,        // coefficient type: cf_cfg_4b_zp_e, cf_cfg_4b_nozp_e, cf_cfg_8b_zp_e, 
                                                       // cf_cfg_8b_nozp_e, cf_cfg_16b_e, cf_cfg_bf16_e, cf_cfg_fp16_e
              pack_mode_t               pcki=pack_mode_i16_e // packed mode, 4*i4, 2*i8, 1*i16
              );
    
  conv_params(
              aoffset_t                 grpi,            // number of groups in convolution
              aoffset_t                 nii,             // number input channels (not vectors), in units of 8b or 16b feature-map pixels
              aoffset_t                 noi,             // number output channels (not vectors)
              const shape<3>&           oshpi,           // output shape, indexed by spatial_axis_t
              const shape<3>&           filteri,         // filter dimension, indexed by spatial_axis_t
              const shape<3>&           stridei,         // filter stride, indexed by spatial_axis_t
              const shape<3>&           dili,            // filter dilation, indexed by spatial_axis_t
              const shape<3>&           padlimi,         // right&bottom limit of padding window, indexed by spatial_axis_t
              bool                      use_acci,        // use input accumulator
              bool                      keep_acci,       // keep output accumulator
              bool                      fm_dbli,         // 8b or 16b feature-maps
              bool                      cf_dbli,         // 8b or 16b coefficients
              bool                      cf_zpi           // coefficients include a zero-point
              );

  inline conv_params()  = default;
  inline conv_params(const conv_params&)  = default;

  //
  // Set a smaller, alternative tile shape e.g. for the boundaries of the feature-map
  //
  void set_alt_shape(
                     aoffset_t                grpi,      // number of groups in convolution
                     aoffset_t                nii,       // number input channels (not vectors), in units of 8b or 16b feature-map pixels
                     aoffset_t                noi,       // number output channels (not vectors)
                     const shape<3>&          oshpi,     // output shape, indexed by spatial_axis_t
                     bool                     use_acci,  // use input accumulator
                     bool                     keep_acci, // keep output accumulator
                     conv_params_impl_alt&    alt        // encoded alternative shape
                     );

  //
  // Get the implementation specific minimum buffer shapes
  //
  void get_shapes(
                  conv_params_impl_shapes&    s       // structure with implementation specific minimum buffer sizes
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
                       const shape<3>&        spat_offset, // spatial offset
                       aoffset_t              chan_offset  // channel offset
                       );

  //
  // Coefficient encoding functions, can be called for multiple chunks; with and without zero-points
  //
  void coef_enc(const tensor_t<coef_t,7,xbuffer_t>&      icf,    // input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp][Coef h/l], h/l only for cf16 mode
                // outputs, buffers preallocated by caller
                conv_params_impl_coef<xbuffer_t>&        obuf,   // output encoded coefficients
                xbuffer_t<coef_t>&                       tbuf    // temporary xbuf
                );
  void coef_enc(const tensor_t<coef_t,6,xbuffer_t>&      icf,    // input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp], 8b only
                const tensor_t<coef_t,1,xbuffer_t>&      izp,    // input zero-points [Cout]
                // outputs, buffers preallocated by caller
                conv_params_impl_coef<xbuffer_t>&        obuf,   // output encoded coefficients
                xbuffer_t<coef_t>&                       tbuf    // temporary xbuf
                ); 
  void coef_enc(const tensor_t<fp_e5m10_t,6,xbuffer_t>&  icf,    // fp16 input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp]
                // outputs, buffers preallocated by caller
                conv_params_impl_coef<xbuffer_t>&        obuf,   // output encoded coefficients
                xbuffer_t<coef_t>&                       tbuf    // temporary xbuf
                );
  void coef_enc(const tensor_t<fp_e8m7_t,6,xbuffer_t>&   icf,    // bf16 input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp]
                // outputs, buffers preallocated by caller
                conv_params_impl_coef<xbuffer_t>&        obuf,   // output encoded coefficients
                xbuffer_t<coef_t>&                       tbuf    // temporary xbuf
                );
  
  //
  // Input zero-point encoding for input feature-map padding
  //
  void pad_enc(const tensor_t<pix_t,2,xbuffer_t>&       ipd,    // input feature-map zero-points [Cin/Grp][h/l], h/l only for fm16 mode
               // outputs, buffers preallocated by caller
               conv_params_impl_pad<xbuffer_t>&         obuf    // output encoded zero-points
               );
  void pad_enc(const tensor_t<fp_e5m10_t,1,xbuffer_t>&  ipd,    // fp16 input feature-map zero-points [Cin/Grp]
               // outputs, buffers preallocated by caller
               conv_params_impl_pad<xbuffer_t>&         obuf    // output encoded zero-points
               );
  void pad_enc(const tensor_t<fp_e8m7_t,1,xbuffer_t>&   ipd,    // bf16 input feature-map zero-points [Cin/Grp]
               // outputs, buffers preallocated by caller
               conv_params_impl_pad<xbuffer_t>&         obuf    // output encoded zero-points
               );
};
}  // namespace tensor::v200
// include implementation specific inline functions
#include "tensor_conv_conv_inline.hpp"
#endif  // TENSOR_API_TENSOR_CONV_CONV_HPP_
