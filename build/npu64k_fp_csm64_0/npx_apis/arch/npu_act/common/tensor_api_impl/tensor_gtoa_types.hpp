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
 * tensor_gtoa_types.hpp
 *
 * Generic tensor accelerator type definitions
 *
 */

#ifndef TENSOR_GTOA_TYPES_INCLUDED
#define TENSOR_GTOA_TYPES_INCLUDED

#include "npu_act_hlapi.hpp"
namespace npu_act::uc::v200 {
  // WA to see the new namespace
}

namespace tensor::v200 {
  using namespace npu_act;
  using namespace npu_act::uc::v200;

  typedef act_hlapi_t gtoa_params_impl_main;

  typedef enum { gtoa_lut_tanh, gtoa_lut_sigmoid, gtoa_lut_mish, gtoa_lut_swish, gtoa_lut_hswish, gtoa_lut_gelu } gtoa_lut_type_t;
  typedef enum { fpmode_int32, fpmode_fp32, fpmode_fp16, fpmode_bf16, fpmode_fp8} act_fp_cfg_t;
  typedef enum { dtype_int48, dtype_int32, dtype_fp32, dtype_fp16, dtype_bf16, dtype_int8, dtype_int16} act_dtype_t;
  typedef enum { pmode_zero, pmode_mone, pmode_min, pmode_max} act_pmode_t;
  typedef enum { pinc_i16, pinc_v2i8, pinc_v4i4} act_pinc_t;
  typedef enum { pad_zero, pad_edge, pad_mirror, pad_replic } act_pad_t;

  //
  // Implementation specific shapes
  //
  // shapes for activation functions
  struct gtoa_act_params_impl_shapes {
    shape<5>                     ishape;         // input accumulator shape:  vyixacc_t [D][H][W][C][msb/lsb/onn]
    shape<5>                     i1shape;        // input accumulator shape:  vyixacc_t [D][H][W][C][msb/lsb/onn]
    shape<5>                     oshape;         // output feature-map shape: ixpix_t   [D][H][W][Grp][C]
    shape<1>                     pshape;         // input parameter shape:    ixpix_t   [C]
    shape<1>                     mpshape;        // maxpool overlap buffer shape: ixpix_t  [sz]
  };

  //
  // Implementation specific parameters
  //
  struct gtoa_act_params_impl_spec {
    aoffset_t                    onn;           // accumulator output multiplier
  };

  //
  // Alternative microcode
  //
  typedef array<uint8_t,5*ACT_PROG_LEN> gtoa_params_impl_modif;

  //
  // Datatype for alterative feature-map output parameters to update
  //
  struct gtoa_params_impl_alt_fm {
    hlapi_vm_agu_t<ACT_FM_LOOPS>  fm_agu;  // feature-map AGU
    tmask_t                       io_en;   // IO mask bits
    int8_t                        enable;  // write enable mask
    uint32_t                      bf;      // common bitfieds (need update odbl, osat)
  };

  //
  // Datatype for alterative accumulator output parameters to update
  //
  struct gtoa_params_impl_alt_acc {
    hlapi_am_agu_t<ACT_AM_LOOPS>       acc_agu; // accumulator AGU
    tmask_t                            io_en;   // IO mask bits
  };

  //
  // Datatype for an alternative shape
  // 
  struct gtoa_params_impl_alt {
    inline gtoa_params_impl_alt() = default;
    inline gtoa_params_impl_alt(const gtoa_params_impl_alt& c) = default;
    inline gtoa_params_impl_alt(aoffset_t       noi,
                                const shape<3>& oshpi) {
      no       = noi;
      oshp     = oshpi;
    }
    aoffset_t          no;       // number output channels (not vectors)
    shape<3>           oshp;     // output shape, indexed by spatial_axis_t
  };

  //
  // GTOA encoded parameter structure
  //
  template<template<typename> class B=buffer_t>
  struct gtoa_params_impl_pchan {
    inline gtoa_params_impl_pchan() = default;
    inline gtoa_params_impl_pchan(const gtoa_params_impl_pchan<B>& c) = default;
    inline gtoa_params_impl_pchan(mem_alloc_t&                       vm,
                                  const gtoa_act_params_impl_shapes& shp) {
      B<ixpix_t> buf;
      vm.alloc(buf, shp.pshape[0]);
      tns = tensor_t<ixpix_t,1,B>(buf, {shp.pshape[0]});
    }
    inline gtoa_params_impl_pchan(const B<pix_t>&             vmbuf,
                                  const gtoa_act_params_impl_shapes& shp) {
      assert(vmbuf.get_size() >= get_shape_size(shp.pshape));
      B<ixpix_t> buf = B<ixpix_t>(reinterpret_cast<ixpix_t*>(vmbuf.get_base()), get_shape_size(shp.pshape));
      tns = tensor_t<ixpix_t,1,B>(buf, shp.pshape);
    }
    inline void get_buffer(B<pix_t>& b) {
      pix_t* p = reinterpret_cast<pix_t*>(tns.get_base());
      size_t s = tns.get_size() * sizeof(ixpix_t) / sizeof(pix_t);
      b = B<pix_t>(p, s);
    }
    tensor_t<ixpix_t,1,B>         tns;           // tensor mapped to buffer
  };

  inline void deep_copy(gtoa_params_impl_pchan<buffer_t>& d, gtoa_params_impl_pchan<xbuffer_t>& s) {
    deep_copy_tensor(d.tns, s.tns);
  }

  //
  // Maxpooling overlap buffer
  //
  struct gtoa_maxpool_buffer {
    inline gtoa_maxpool_buffer() = default;
    inline gtoa_maxpool_buffer(const gtoa_maxpool_buffer&) = default;
    inline gtoa_maxpool_buffer(mem_alloc_t&                         vm,
                               const gtoa_act_params_impl_shapes&   shp) {
      int sz = get_shape_size(shp.mpshape);
      vm.alloc(buf, sz);
    }
    inline gtoa_maxpool_buffer(const buffer_t<ixpix_t>&           vmbuf) {
      buf =  vmbuf;
    }
    buffer_t<ixpix_t>                 buf;
  };

  //
  // Implementation specific parameters to run-time
  //
  struct gtoa_rt_impl_spec {
    ctrl_dma_regs<act_hlapi_t>* mmio;          // base address of accelerator MMIO registers
    uint32_t                    ctrl;          // interrupt and event flags [0] devent, [8] ievent, [16] interrupt
    trace_id_t                  id;            // trace id
  };
}
#endif
