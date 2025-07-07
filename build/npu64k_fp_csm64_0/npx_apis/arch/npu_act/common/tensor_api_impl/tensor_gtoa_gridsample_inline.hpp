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
 * tensor_gtoa_gridsample_inline.hpp
 *
 * File defining a tensor level gridsample API base on the generic tensor operation API
 *
 */

#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_GRIDSAMPLE_INLINE_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_GRIDSAMPLE_INLINE_HPP_

#define HLAPI gtoa_params<B>::hlapi

// constructor
// gridsample operation from feature-map (8b/16b) to feature-map (8b/16b)
template<template<typename> class B>
gtoa_gridsample_params<B>::gtoa_gridsample_params(
                 aoffset_t                  noi,           // number input/output channels [C] (not vectors)
                 const shape<2>&            dictshpi,      // dictionary shape [H_in][W_in]
                 const shape<3>&            idxshpi,       // index shape [D2][D1][D0]
                 act_dtype_t                idxtp          // type of index input (BF16 or FP16 only)
                 ) : gtoa_params<B>() {

  // enable accumulator input and accumulator output
  HLAPI.i.bf            = 0;       // function, not LUT init
  // in1 index input is always bf16/fp16 from VM
  // in0 dictionary input is always int8 from VM, gathered so not enabled
  // out is always int8 to VM
  HLAPI.i.u.op.io_en    = ACT_IO_EN_GTH | ACT_IO_EN_FM1 | ACT_IO_EN_OFM;
  HLAPI.i.u.op.bf       = (1<<ACT_BF_OP_IN1DBL_START);
  HLAPI.i.u.op.bf      |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
  switch (idxtp) {
    case dtype_fp16:
      HLAPI.i.u.op.bf  |= ACT_BF_OP_IN1FP16_MASK;
      break;
    case dtype_bf16:
      HLAPI.i.u.op.bf  |= ACT_BF_OP_IN1BF16_MASK;
      break;
    default: assert(0 && "unsupported index input datatype!");
  }

  // round the channels and x
  aoffset_t crnd  = NRND_UP(noi, ISIZE);
  aoffset_t vrnd  = NRND_UP(idxshpi[1], TNSVSIZE);
  aoffset_t vrndc = NRND_UP(idxshpi[1], ISIZE/2);

  // input dictionary in ixpix_t [1][H][W][1][C] format
  shapes.ishape = {(aoffset_t)(crnd/ISIZE),       // C/ISIZE
                   1,
                   dictshpi[0],                   // W_in
                   dictshpi[1],                   // H_in
                   1};
  // input index in ixpix_t [1][D2][D1][D0][2] format
  shapes.i1shape = {2,                            // x&y
                    idxshpi[0],                   // D0 (FSw*FSh)
                    (aoffset_t)(vrndc/(ISIZE/2)), // D1/(ISIZE/2) (W_out)
                    idxshpi[2],                   // D2 (H_out)
                    1};
  // output feature-map in ixpix_t [1][D2][D1][D0][C] format
  shapes.oshape = {(aoffset_t)(crnd/ISIZE),       // C/ISIZE
                   idxshpi[0],                    // D0 (FSw*FSh)
                   vrnd,                          // D1 (W_out)
                   idxshpi[2],                    // D2 (H_out)
                   1};
  // per channel shape, used to pass fixed parameters
  shapes.pshape = { 0 };

  // init microcode
  init_gridsample(HLAPI);

  // no parameter
  HLAPI.i.u.op.bnum = 0;

  // main iterators
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 1] = 3;
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 2] = crnd/ISIZE;
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 3] = idxshpi[0]*vrnd/TNSVSIZE*idxshpi[2];

  // dictionary feature-map input
  for (int i = 0; i < ACT_FM_LOOPS - 3; i++) {
    HLAPI.i.u.op.primary.fm_agu.iter[i] = 1;
  }
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1] = 2; // left/right
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2] = 2; // top/bottom
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3] = crnd/ISIZE;
  HLAPI.i.u.op.primary.fm_agu.iter[0]                = idxshpi[0]*vrnd/TNSVSIZE*idxshpi[2];
  
  // index feature-map input
  for (int i = 0; i < ACT_FM_LOOPS - 4; i++) {
    HLAPI.i.u.op.secondary.fm_agu.iter[i] = 1;
  }
  HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 1] = 2;
  HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 2] = idxshpi[0];
  HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 3] = vrndc/(ISIZE/2);
  HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 4] = idxshpi[2];

  // output feature-map
  for (int i = 0; i < ACT_FM_LOOPS - 4; i++) {
    HLAPI.i.u.op.out.fm.fm_agu.iter[i] = 1;
  }
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1] = crnd/ISIZE;
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 2] = idxshpi[0];
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 3] = vrnd/TNSVSIZE;
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 4] = idxshpi[2];
  // pooling parameters
  HLAPI.i.u.op.out.fm.pool.bf       = 0;  // disable maxpooling
  // writeback all lines
  HLAPI.i.u.op.out.fm.enable        = (int8_t)((1 << TNSVSIZE)-1);
}

// initialize the output tensors
template <template <typename> class B>
template <template <typename> class BD>
void gtoa_gridsample_params<B>::init_l1_output(
  // output tensor in L1 memory [B][D2][D1][D0][C]
  const impl_spec_container_t<BD> &p
) {
  gtoa_params<B>::tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [1][D2][D1][D0][C] --> [1][D2][D1/8][D1_8][D0][C]
  tensor_t<ixpix_t, 6, BD> t0(p.data.split(2, HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 3]));
  // transpose to [1][D2][D1/8][D1_8][D0][C] to [D1_8][1][D2][D1/8][D0][C]
  tensor_t<ixpix_t, 6, BD> t1(t0.transpose({0, 1, 3, 4, 5, 2}));

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.out.fm.fm_agu.ptr      = t1.get_ptr();
  HLAPI.i.u.op.out.fm.fm_agu.buf.base = t1.get_base();
  HLAPI.i.u.op.out.fm.fm_agu.buf.len  = t1.get_size();
  HLAPI.i.u.op.out.fm.fm_agu.stride   = t1.get_offset(5);                        // D1_8
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 1] = t1.get_offset_last(0);  // C
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 2] = t1.get_offset_last(1);  // D0
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 3] = t1.get_offset_last(2);  // D1/8
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 4] = t1.get_offset_last(3);  // D2
}

// initialize the dictionary input tensor
template <template <typename> class B>
template <template <typename> class BD>
void gtoa_gridsample_params<B>::init_l1_input0(
    // input dictionary in L1 memory [B][H][W][1][C]
    const impl_spec_container_t<BD> &p
) {
  gtoa_params<B>::itens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.primary.fm_agu.ptr      = p.data.get_ptr();
  HLAPI.i.u.op.primary.fm_agu.buf.base = p.data.get_base();
  HLAPI.i.u.op.primary.fm_agu.buf.len  = p.data.get_size();
  HLAPI.i.u.op.primary.fm_agu.stride   = p.data.get_offset(2);                    // D1_8
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 1] = p.data.get_offset(2);   // 1 pixel left
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 2] = p.data.get_offset(3) +
   (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1])*p.data.get_offset(2);   // 1 pixel right and 1 pixel down
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 3] = p.data.get_offset(0) +
   (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1])*p.data.get_offset(2) +
   (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2])*p.data.get_offset(3);   //  1 pixel right, 1 pixel up and next channel vector
  HLAPI.i.u.op.primary.fm_agu.offsets[1] = p.data.get_offset(3);   // Y offset
  HLAPI.i.u.op.primary.fm_agu.offsets[0] = p.data.get_offset(2);   // X offset
}

// initialize the index input tensor
template <template <typename> class B>
template <template <typename> class BD>
void gtoa_gridsample_params<B>::init_l1_input1(
    // input index tensor in L1 memory [B][D2][D1/8][D0][2]
    const impl_spec_container_t<BD> &p
) {
  gtoa_params<B>::i1tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.secondary.fm_agu.ptr      = p.data.get_ptr();
  HLAPI.i.u.op.secondary.fm_agu.buf.base = p.data.get_base();
  HLAPI.i.u.op.secondary.fm_agu.buf.len  = p.data.get_size();
  HLAPI.i.u.op.secondary.fm_agu.stride   = 0;
  HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS - 1] = p.data.get_offset_last(0);   // X&Y
  HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS - 2] = p.data.get_offset_last(1);   // D0
  HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS - 3] = p.data.get_offset_last(2);   // D1/(ISIZE/2)
  HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS - 4] = p.data.get_offset_last(3);   // D2
}

template<template<typename> class B>
inline void gtoa_gridsample_params<B>::get_shapes(
  gtoa_act_params_impl_shapes& s   // implementation specific minimum buffer sizes
                      ) {
  s = shapes;
}

#undef HLAPI

#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_GRIDSAMPLE_INLINE_HPP_
