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
 * tensor_gtoa_griddmaidx_inline.hpp
 *
 * File defining a tensor level griddmaidx API based on the generic tensor operation API
 *
 */

#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_GRIDDMAIDX_INLINE_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_GRIDDMAIDX_INLINE_HPP_

#define HLAPI gtoa_params<B>::hlapi

// constructor
// griddmaidx operation from grid (float 16b) to index (int 16b)
template<template<typename> class B>
gtoa_griddmaidx_params<B>::gtoa_griddmaidx_params(
                    const shape<3>&  idxshpi,       // index shape [D2][D1][D0]
                    act_dtype_t      idxtp          // type of input (BF16 or FP16 only)
                    ) : gtoa_params<B>() {

  // enable accumulator input and accumulator output
  HLAPI.i.bf            = 0;       // function, not LUT init
  // in0 grid input is always bf16/fp16 from VM
  // out index is always int16 to VM
  HLAPI.i.u.op.io_en    = ACT_IO_EN_FM0 | ACT_IO_EN_OFM;
  HLAPI.i.u.op.bf       = (1<<ACT_BF_OP_IN0DBL_START) | (1<<ACT_BF_OP_OUTDBL_START) | ACT_BF_OP_OUTINT32_MASK;
  switch (idxtp) {
    case dtype_fp16:
      HLAPI.i.u.op.bf  |= ACT_BF_OP_IN0FP16_MASK;
      break;
    case dtype_bf16:
      HLAPI.i.u.op.bf  |= ACT_BF_OP_IN0BF16_MASK;
      break;
    default: assert(0 && "unsupported input datatype!");
  }

  // find the optimal processing chunks
  aoffset_t wsize  = NRDIV_UP(idxshpi[1], TNSVSIZE);
  aoffset_t wchunk = NRDIV_UP(wsize, NRDIV_UP(wsize, TNSVSIZE));
  aoffset_t chunks = NRDIV_UP(wsize, wchunk);

  // input index in ixpix_t [1][D2][D1][D0][2] format
  shapes.ishape = {2,                            // x&y
                   idxshpi[0],                   // D0 (FSw*FSh)
                   (aoffset_t)(wchunk*chunks),   // D1/TNSVSIZE (W_out)
                   idxshpi[2],                   // D2 (H_out)
                   1};
  // output feature-map in ixpix_t [1][D2][D1][D0][C] format
  shapes.oshape = {2,                            // x&y
                   idxshpi[0],                   // D0 (FSw*FSh)
#if 1
                   (aoffset_t)(wchunk*chunks),   // D1/TNSVSIZE (W_out)
#else
                   (aoffset_t)(wchunk*chunks*4), // D1/TNSVSIZE*4 (W_out)
#endif
                   idxshpi[2],                   // D2 (H_out)
                   1};
  // per channel shape, used to pass fixed parameters
  shapes.pshape = { 0 };
  
  // init microcode
  init_grid_dmaidx(HLAPI);

  // no parameter
  HLAPI.i.u.op.bnum = 0;

  // main iterators
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 1] = idxshpi[0];
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 2] = chunks;
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 3] = idxshpi[2];

  // index feature-map input
  for (int i = 0; i < ACT_FM_LOOPS - 4; i++) {
    HLAPI.i.u.op.primary.fm_agu.iter[i] = 1;
  }
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1] = 2;
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2] = idxshpi[0];
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3] = chunks;
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 4] = idxshpi[2];

  // output feature-map
#if 1
  for (int i = 0; i < ACT_FM_LOOPS - 4; i++) {
#else
  for (int i = 0; i < ACT_FM_LOOPS - 5; i++) {
#endif
    HLAPI.i.u.op.out.fm.fm_agu.iter[i] = 1;
  }
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1] = 2;
#if 1
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 2] = idxshpi[0];
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 3] = chunks;
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 4] = idxshpi[2];
#else
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 2] = 4;
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 3] = idxshpi[0];
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 4] = chunks;
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 5] = idxshpi[2];
#endif
  // pooling parameters
  HLAPI.i.u.op.out.fm.pool.bf       = 0;  // disable maxpooling
  // writeback all lines
  HLAPI.i.u.op.out.fm.enable        = (int8_t)((1 << wchunk)-1);
}

// initialize the index output tensor
template <template <typename> class B>
template <template <typename> class BD>
void gtoa_griddmaidx_params<B>::init_l1_output(
  // output tensor in L1 memory [1][D2][D1/8*4][D0][2]
  const impl_spec_container_t<BD> &p
) {
  gtoa_params<B>::tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
#if 1
  // [1][D2][D1/8][D0][2] --> [1][D2][D1/8/wch][D1_wch][D0][2]
  tensor_t<ixpix_t, 6, BD> t0(p.data.split(2, HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 3]));
  // transpose [1][D2][D1/8/wch][D1_wch][D0][2] to [D1_wch][1][D2][D1/8/wch][D0][2]
  tensor_t<ixpix_t, 6, BD> t1(t0.transpose({0, 1, 3, 4, 5, 2}));

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.out.fm.fm_agu.ptr      = t1.get_ptr();
  HLAPI.i.u.op.out.fm.fm_agu.buf.base = t1.get_base();
  HLAPI.i.u.op.out.fm.fm_agu.buf.len  = t1.get_size();
  HLAPI.i.u.op.out.fm.fm_agu.stride   = t1.get_offset(5);                        // D1_wch
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 1] = t1.get_offset_last(0);  // 2 (X&Y)
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 2] = t1.get_offset_last(1);  // D0
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 3] = t1.get_offset_last(2);  // D1/8/wch
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 4] = t1.get_offset_last(3);  // D2
#else
  // [1][D2][D1/8*4][D0][2] --> [1][D2][D1/8/wch][D1_wch*4][D0][2]
  tensor_t<ixpix_t, 6, BD> t0(p.data.split(2, HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 4]));
  // [1][D2][D1/8/wch][D1_wch*4][D0][2] --> [1][D2][D1/8/wch][D1_wch][4][D0][2]
  tensor_t<ixpix_t, 7, BD> t1(t0.split(2, t0.get_dim(2)/4));
  // transpose [1][D2][D1/8/wch][D1_wch][4][D0][2] to [D1_wch][1][D2][D1/8/wch][D0][4][2]
  tensor_t<ixpix_t, 7, BD> t2(t1.transpose({0, 2, 1, 4, 5, 6, 3}));

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.out.fm.fm_agu.ptr      = t2.get_ptr();
  HLAPI.i.u.op.out.fm.fm_agu.buf.base = t2.get_base();
  HLAPI.i.u.op.out.fm.fm_agu.buf.len  = t2.get_size();
  HLAPI.i.u.op.out.fm.fm_agu.stride   = t2.get_offset(6);                        // D1_wch
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 1] = t2.get_offset_last(0);  // 2 (X&Y)
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 2] = t2.get_offset_last(1);  // 4
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 3] = t2.get_offset_last(2);  // D0
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 4] = t2.get_offset_last(3);  // D1/8/wch
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 5] = t2.get_offset_last(4);  // D2
#endif
}

// initialize the index input tensor
template <template <typename> class B>
template <template <typename> class BD>
void gtoa_griddmaidx_params<B>::init_l1_input0(
    // input index tensor in L1 memory [1][D2][D1/8][D0][2]
    const impl_spec_container_t<BD> &p
) {
  gtoa_params<B>::itens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [1][D2][D1/8][D0][2] --> [1][D2][D1/8/wch][D1_wch][D0][2]
  tensor_t<ixpix_t, 6, BD> t0(p.data.split(2, HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3]));
  // transpose [1][D2][D1/8/wch][D1_wch][D0][2] to [D1_wch][1][D2][D1/8/wch][D0][2]
  tensor_t<ixpix_t, 6, BD> t1(t0.transpose({0, 1, 3, 4, 5, 2}));

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.primary.fm_agu.ptr      = t1.get_ptr();
  HLAPI.i.u.op.primary.fm_agu.buf.base = t1.get_base();
  HLAPI.i.u.op.primary.fm_agu.buf.len  = t1.get_size();
  HLAPI.i.u.op.primary.fm_agu.stride   = t1.get_offset(5);                        // D1_wch
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 1] = t1.get_offset_last(0);  // 2 (X&Y)
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 2] = t1.get_offset_last(1);  // D0
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 3] = t1.get_offset_last(2);  // D1/8/wch
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 4] = t1.get_offset_last(3);  // D2
}

template<template<typename> class B>
inline void gtoa_griddmaidx_params<B>::get_shapes(
  gtoa_act_params_impl_shapes& s   // implementation specific minimum buffer sizes
                      ) {
  s = shapes;
}

#undef HLAPI

#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_GRIDDMAIDX_INLINE_HPP_
