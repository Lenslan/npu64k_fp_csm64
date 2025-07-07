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
 * tensor_conv_types.hpp
 *
 * File defining  the implementation specific types for the tensor level convolution API
 *
 */

#ifndef NPU_CONV_COMMON_TENSOR_API_IMPL_TENSOR_CONV_TYPES_HPP_
#define NPU_CONV_COMMON_TENSOR_API_IMPL_TENSOR_CONV_TYPES_HPP_

// include interface datatypes
#include "tensor.hpp"
#include "npu_conv_hlapi.hpp"

//
// All identifiers related to the convolution engine go into namespace npu_conv
//
namespace tensor::v200 {
using namespace npu_conv;

//
// Implementation specific parameters to select modes
//
struct conv_params_impl_spec {
  conv_mode_t                  conv_mode;      // convolution mode
  aoffset_t                    inn;            // inner input loop multiplier
  aoffset_t                    onn;            // inner output loop multiplier
  coef_mode_t                  cf_mode;        // coefficient compression mode
  bool                         cf_4b;          // 4b coefficient encoding
};

//
// Implementation specific shapes
//
struct conv_params_impl_shapes {
  shape<5>                     ishape;         // input feature-map shape                       : ixpix_t    [D][H][W][Grp][Ci*mlsb]
  shape<5>                     ishapeb;        // input shape of secondary matrix in matmat     : ixpix_t    [D][H][W][Grp][Ci*mlsb]
  shape<1>                     pshape;         // input padding shape in                        : ixpix_t    [Ci*mlsb]
  shape<5>                     oshape;         // output accumulator shape, triple buffered     : vyixacc_t  [Co][D][H][W][msb|lsb|onn]
  uint32_t                     cshape;         // worst-case coefficient&zero-point buffer size : ixpix_t    [...]
};
  
//
// Datatype for a alternative shape
//
struct conv_params_impl_alt {
  inline conv_params_impl_alt() = default;
  inline conv_params_impl_alt(const conv_params_impl_alt& c) = default;
  inline conv_params_impl_alt(aoffset_t       grpi,
                              aoffset_t       nii,
                              aoffset_t       noi,
                              const shape<3>& oshpi,
                              bool            use_acci,
                              bool            keep_acci) {
    assert(0 && "not implemented yet");
  }
};

//
// Datatype for encoded coefficient buffer pointer and zero-point
// 
// initially size if cshape, after encoding buffer size is shrunk to actual compressed coefficient size
template<template<typename> class B=buffer_t> struct conv_params_impl_coef {
  inline conv_params_impl_coef() = default;
  inline conv_params_impl_coef(const conv_params_impl_coef<B>&) = default;
  inline conv_params_impl_coef(mem_alloc_t&                   vm,
                               const conv_params_impl_shapes& shp) {
    vm.alloc(cbuf, shp.cshape);
  }
  inline conv_params_impl_coef(mem_alloc_t&                   vm,
                               const size_t                   sz) {
    vm.alloc(cbuf, sz);
  }
  inline conv_params_impl_coef(const B<coef_t>&        vmbuf,
                               const conv_params_impl_shapes& shp) {
    assert(vmbuf.get_size() >= shp.cshape);
    cbuf = B<ixpix_t>(reinterpret_cast<ixpix_t*>(vmbuf.get_base()), shp.cshape);
  }
  inline void get_buffer(B<pix_t>& b) {
    pix_t* p = reinterpret_cast<pix_t*>(cbuf.get_base());
    size_t s = cbuf.get_size() * sizeof(ixpix_t) / sizeof(pix_t);
    b = B<pix_t>(p, s);
  }
  inline size_t get_size() {
    return cbuf.get_size();
  }
  B<ixpix_t> cbuf;
};

//
// Datatype for encoded input feature-map zero-points/padding values
//
template<template<typename> class B=buffer_t> struct conv_params_impl_pad {
  inline conv_params_impl_pad() = default;
  inline conv_params_impl_pad(const conv_params_impl_pad<B>& c) = default;
  inline conv_params_impl_pad(mem_alloc_t&                   vm,
                              const conv_params_impl_shapes& shp) {
    B<ixpix_t> pbuf;
    vm.alloc(pbuf, get_shape_size(shp.pshape));
    ptns = tensor_t<ixpix_t,1,B>(pbuf, shp.pshape);
  }
  inline conv_params_impl_pad(const B<pix_t>&         vmbuf,
                              const conv_params_impl_shapes& shp) {
    assert(vmbuf.get_size() >= get_shape_size(shp.pshape));
    B<ixpix_t> pbuf = B<ixpix_t>(reinterpret_cast<ixpix_t*>(vmbuf.get_base()), get_shape_size(shp.pshape));
    ptns = tensor_t<ixpix_t,1,B>(pbuf, shp.pshape);
  }
  inline void get_buffer(B<pix_t>& b) {
    pix_t* p = reinterpret_cast<pix_t*>(ptns.get_base());
    size_t s = ptns.get_size() * sizeof(ixpix_t) / sizeof(pix_t);
    b = B<pix_t>(p, s);
  }
  tensor_t<ixpix_t,1,B> ptns;
};

//
// Opaque main parameter type
//
typedef conv_hlapi_t conv_params_impl_main; // HLAPI

//
// Implementation specific parameters to run-time
//
struct conv_rt_impl_spec {
  ctrl_dma_regs<conv_hlapi_t>* mmio;          // base address of accelerator MMIO registers
  uint32_t                     ctrl;          // interrupt and event flags [0] devent, [8] ievent, [16] interrupt
  trace_id_t                   id;            // real-time trace ID
};


//
// Copy parameters between xbuffer and buffer
//
inline void deep_copy(conv_params_impl_pad<buffer_t>& d,  // NOLINT [runtime/references]
    const conv_params_impl_pad<xbuffer_t>& s) {
  deep_copy_tensor(d.ptns, s.ptns);
}

inline void deep_copy(conv_params_impl_coef<buffer_t>& d,  // NOLINT [runtime/references]
    const conv_params_impl_coef<xbuffer_t>& s) {
  s.cbuf.deep_copy(d.cbuf);
}

}
#endif  // NPU_CONV_COMMON_TENSOR_API_IMPL_TENSOR_CONV_TYPES_HPP_
