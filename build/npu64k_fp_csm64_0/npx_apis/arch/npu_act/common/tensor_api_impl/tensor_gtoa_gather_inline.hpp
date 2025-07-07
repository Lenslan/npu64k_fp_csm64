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
 * tensor_gtoa_gather_inline.hpp
 *
 * File defining a tensor level gather API base on the generic tensor operation API
 *
 */
#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_GATHER_INLINE_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_GATHER_INLINE_HPP_
#define HLAPI gtoa_params<B>::hlapi

// constructor


// 2D gather operation from 8b feature-map to 8b feature-map with 16b indices
template <template <typename> class B>
gtoa_gather_params<B>::gtoa_gather_params(
                     const shape<3>& inneri,   // shape of inner tensor [C2][C1][C0]
                     const shape<2>& ishpi,    // shape of the outer dictionary tensor [H][W]
                     const shape<2>& oshpi     // shape of the outer index and output tensor [Y][X]
                     ) : gtoa_params<B>() {
  // copy inputs
  inner = inneri;
  ishp  = ishpi;
  oshp  = oshpi;
  // round the channels and x
  crnd  = NRND_UP(inner[0], ISIZE);
  vrnd  = NRND_UP(oshp[0], TNSVSIZE);
  vrndc = NRND_UP(oshp[0], TNSVSIZE);
  // enable accumulator input and accumulator output
  HLAPI.i.bf         = 0;       // function, not LUT init
  // in1 index input is always int16 from VM
  // in0 dictionary input is always int8 from VM, gathered so not enabled
  // out is always int8 to VM
  HLAPI.i.u.op.io_en = ACT_IO_EN_GTH | ACT_IO_EN_FM1 | ACT_IO_EN_OFM;
  HLAPI.i.u.op.bf    = ACT_BF_OP_IN0INT32_MASK |
    (1<<ACT_BF_OP_IN1DBL_START) |
    ACT_BF_OP_IN1INT32_MASK |
    ACT_BF_OP_OUTINT32_MASK;
  shapes.ishape = {(aoffset_t)(crnd/ISIZE),
                   inner[1],
                   inner[2],
                   ishp[0],
                   ishp[1]};
  shapes.i1shape = {2,                            // x&y
                    (aoffset_t)(vrndc/TNSVSIZE),  // ox
                    oshp[1],                      // oy
                    1,
                    1};
  shapes.oshape = {(aoffset_t)(crnd/ISIZE),
                   inner[1],
                   inner[2],
                   vrnd,
                   oshp[1]};

  // main iterators
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 1] = crnd*inner[1]*inner[2]/ISIZE;
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 2] = vrnd/TNSVSIZE;
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 3] = oshp[1];

  // dictionary feature-map input
  for (int i = 0; i < ACT_FM_LOOPS - 3; i++) {
    HLAPI.i.u.op.primary.fm_agu.iter[i] = 1;
  }
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1] = crnd/ISIZE;
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2] = inner[1];
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3] = inner[2];
  HLAPI.i.u.op.primary.fm_agu.iter[1]                = vrnd/TNSVSIZE;
  HLAPI.i.u.op.primary.fm_agu.iter[0]                = oshp[1];
  HLAPI.i.u.op.out.fm.enable = 0xff;

  // index feature-map input
  for (int i = 0; i < ACT_FM_LOOPS - 3; i++) {
    HLAPI.i.u.op.secondary.fm_agu.iter[i] = 1;
  }
  HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 1] = 2;
  HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 2] = vrndc/TNSVSIZE;
  HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 3] = oshp[1];

  // output feature-map
  for (int i = 0; i < ACT_FM_LOOPS - 5; i++) {
    HLAPI.i.u.op.out.fm.fm_agu.iter[i] = 1;
  }
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1] = crnd/ISIZE;
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 2] = inner[1];
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 3] = inner[2];
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 4] = vrnd/TNSVSIZE;
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 5] = oshp[1];

  // microcode
  init_gather2d(HLAPI);
}

// initialize the output tensors
template <template <typename> class B>
template <template <typename> class BD>
void gtoa_gather_params<B>::init_l1_output(
  // output tensor in L1 memory [Y][X][C2][C1][C0]
  const impl_spec_container_t<BD> &p
) {
  gtoa_params<B>::tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [Y][X][C2][C1][C0] --> [Y][X/8][X8][C2][C1][C0]
  tensor_t<ixpix_t, 6, BD> t0(p.data.split(3, HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 4]));
  // transpose to [Y][X/8][X8][C2][C1][C0] to [X8][Y][X/8][C2][C1][C0]
  tensor_t<ixpix_t, 6, BD> t1(t0.transpose({0, 1, 2, 4, 5, 3}));

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.out.fm.fm_agu.ptr      = t1.get_ptr();
  HLAPI.i.u.op.out.fm.fm_agu.buf.base = t1.get_base();
  HLAPI.i.u.op.out.fm.fm_agu.buf.len  = t1.get_size();
  HLAPI.i.u.op.out.fm.fm_agu.stride   = t1.get_offset(5);                        // X
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 1] = t1.get_offset_last(0);  // C0
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 2] = t1.get_offset_last(1);  // C1
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 3] = t1.get_offset_last(2);  // C2
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 4] = t1.get_offset_last(3);  // X/8
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 5] = t1.get_offset_last(4);  // Y
}

// initialize the primary input tensor
template <template <typename> class B>
template <template <typename> class BD>
void gtoa_gather_params<B>::init_l1_input0(
    // input dictionary in L1 memory [H][W][C2][C1][C0]
    const impl_spec_container_t<BD> &p
) {
  gtoa_params<B>::itens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.primary.fm_agu.ptr      = p.data.get_ptr();
  HLAPI.i.u.op.primary.fm_agu.buf.base = p.data.get_base();
  HLAPI.i.u.op.primary.fm_agu.buf.len  = p.data.get_size();
  HLAPI.i.u.op.primary.fm_agu.stride   = p.data.get_offset(3);
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 1] = p.data.get_offset_last(0);   // C0
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 2] = p.data.get_offset_last(1);   // C1
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 3] = p.data.get_offset_last(2);   // C2
  HLAPI.i.u.op.primary.fm_agu.offsets[1] = p.data.get_offset(4);   // Y offset
  HLAPI.i.u.op.primary.fm_agu.offsets[0] = p.data.get_offset(3);   // X offset
}

// initialize the primary input tensor
template <template <typename> class B>
template <template <typename> class BD>
void gtoa_gather_params<B>::init_l1_input1(
    // input index tensor in L1 memory [Y][X/ISIZE][2]
    const impl_spec_container_t<BD> &p
) {
  gtoa_params<B>::i1tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.secondary.fm_agu.ptr      = p.data.get_ptr();
  HLAPI.i.u.op.secondary.fm_agu.buf.base = p.data.get_base();
  HLAPI.i.u.op.secondary.fm_agu.buf.len  = p.data.get_size();
  HLAPI.i.u.op.secondary.fm_agu.stride   = 0;
  HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS - 1] = p.data.get_offset_last(0);   // X&Y
  HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS - 2] = p.data.get_offset_last(1);   // X/ISIZE
  HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS - 3] = p.data.get_offset_last(2);   // Y
}

template <template <typename> class B>
inline void gtoa_gather_params<B>::get_shapes(
    gtoa_act_params_impl_shapes& s  // structure with implementation specific minimum buffer sizes
) {
  s = shapes;
}

#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_GATHER_INLINE_HPP_
