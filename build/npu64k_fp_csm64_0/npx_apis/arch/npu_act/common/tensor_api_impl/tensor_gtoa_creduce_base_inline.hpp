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
 * tensor_gtoa_creduce_inline.hpp
 *
 * File defining channelwise reduce creduce API base on the generic tensor
 * operation API
 *
 */
#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_CREDUCE_BASE_INLINE_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_CREDUCE_BASE_INLINE_HPP_

#define HLAPI gtoa_params<B>::hlapi

// chanel wise reduce base class for feature-map (8b/16b) input
template <template <typename> class B>
gtoa_creduce_base_params<B>::gtoa_creduce_base_params(
    aoffset_t noi,         // number output channels (not vectors)
    const shape<3> &ishpi, // input shape
    act_dtype_t intp,      // type of primary input
    act_dtype_t outtp)     // type of output
    : gtoa_params<B>() {
  // enable accumulator input and accumulator/feature-map output
  HLAPI.i.bf = 0; // function, not LUT init
  HLAPI.i.u.op.io_en = 0;

  // TODO add int48
  bool idbl =
      (intp == dtype_int16) || (intp == dtype_fp16) || (intp == dtype_bf16);
  bool odbl =
      (outtp == dtype_int16) || (outtp == dtype_fp16) || (outtp == dtype_bf16);
  HLAPI.i.u.op.bf = (idbl ? 1 << ACT_BF_OP_IN0DBL_START : 0) |
                    (odbl ? 1 << ACT_BF_OP_OUTDBL_START : 0);

  // update mask and floating mode field based on input/output type
  switch (intp) {
    case dtype_int8:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_FM0;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN0INT32_MASK;
      break;
    case dtype_int16:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_FM0;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN0INT32_MASK;
      break;
    case dtype_fp16:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_FM0;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN0FP16_MASK;
      break;
    case dtype_bf16:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_FM0;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN0BF16_MASK;
      break;
    case dtype_int32:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_AC0;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN0INT32_MASK;
      break;
    case dtype_fp32:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_AC0;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN0FP32_MASK;
      break;
    default: assert(0 && "unsupported input datatype!");
  }
  switch (outtp) {
    case dtype_int8:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_OFM;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTSAT_MASK;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTINT32_MASK;
      break;
    case dtype_int16:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_OFM;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTSAT_MASK;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTINT32_MASK;
      break;
    case dtype_fp16:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_OFM;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTFP16_MASK;
      break;
    case dtype_bf16:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_OFM;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTBF16_MASK;
      break;
    case dtype_int32:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_OAC;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTINT32_MASK;
      break;
    case dtype_fp32:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_OAC;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTFP32_MASK;
      break;
    default: assert(0 && "unsupported output datatype!");
  }

  int c = RDIV_UP(noi, ISIZE);
  int w = RDIV_UP(ishpi[SPATIAL_W], TNSVSIZE);

  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0) {
    // input feature-map in ixpix_t [D][1][H][W][C] format
    shapes.ishape = {(aoffset_t)(idbl ? 2 * c : c),
                    1,
                    (aoffset_t)(w * TNSVSIZE),
                    ishpi[SPATIAL_H],
                    ishpi[SPATIAL_D]};
  } else {
    // input accumulator in vyixacc_t [D][H][W/TNSVSIZE][C/ISIZE*dbl] format
    shapes.ishape = {1,
                    ishpi[SPATIAL_H],
                    (aoffset_t)w,
                    ishpi[SPATIAL_D],
                    (aoffset_t)c};
  }
  // input1 accumulator in vyixacc_t [C] format
  shapes.i1shape = {0};
  
  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_OFM) != 0) {
    // output feature-map in ixpix_t [D][1][H][W][1] format
    shapes.oshape = {(aoffset_t)(odbl ? 2 : 1),
                    1,
                    (aoffset_t)(w * TNSVSIZE),
                    ishpi[SPATIAL_H],
                    ishpi[SPATIAL_D]};
  } else {
    // output accumulator in vyixacc_t [D][H][W/TNSVSIZE][1] format
    shapes.oshape = {1,
                    ishpi[SPATIAL_H],
                    (aoffset_t)w,
                    ishpi[SPATIAL_D],
                    1};
  }
  // parameter dimension
  shapes.pshape = {0};

  set_creduce_params();
}

// set iterators
template <template <typename> class B>
void gtoa_creduce_base_params<B>::set_creduce_params() {
  int fmidbl = (HLAPI.i.u.op.bf & ACT_BF_OP_IN0DBL_MASK) != 0 ? 2 : 1;
  int fmodbl = (HLAPI.i.u.op.bf & ACT_BF_OP_OUTDBL_MASK) != 0 ? 2 : 1;
  bool ifm_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0;
  bool iac_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_AC0) != 0;
  bool ofm_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_OFM) != 0;
  bool oac_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_OAC) != 0;

  //  Channel/ISIZE
  int i_c = shapes.ishape[0] / fmidbl;

  // H*W*D/TNSVSIZE
  int i_spatial;
  if (ifm_en) {
    i_spatial = RDIV_UP(shapes.ishape[2], TNSVSIZE) * shapes.ishape[3] * shapes.ishape[4];
  } else {
    i_spatial = shapes.ishape[1] * shapes.ishape[2] * shapes.ishape[3];
  }
  // iterators
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 1] = i_c;       // inner channel loop
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 2] = i_spatial; // middle spatial loop
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 3] = 1;         // outer

  // primary feature-map input
  if (ifm_en) {
    for (int i = 0; i < ACT_FM_LOOPS - 5; i++) {
      HLAPI.i.u.op.primary.fm_agu.iter[i] = 1;
      HLAPI.i.u.op.primary.fm_agu.offsets[i] = 0;
    }
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1] = shapes.ishape[0];                 // C
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2] = 1;
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3] = RDIV_UP(shapes.ishape[2], TNSVSIZE); // w/8
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 4] = shapes.ishape[3];                 // H
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 5] = shapes.ishape[4];                 // D
  }
  // primary accumulator input
  if (iac_en) {
    for (int i = 0; i < ACT_AM_LOOPS - 1; i++) {
      HLAPI.i.u.op.primary.acc_agu.offsets[i] = 1;
      HLAPI.i.u.op.primary.acc_agu.iter[i] = 1;
    }
    HLAPI.i.u.op.primary.acc_agu.offsets[ACT_AM_LOOPS - 1] = 1;
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS - 1] = shapes.ishape[0]; // C
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS - 2] = shapes.ishape[1]; // W
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS - 3] = shapes.ishape[2]; // H
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS - 4] = shapes.ishape[3]; // D
  }

  // secondary accumulator input
  for (int i = 0; i < ACT_AM_LOOPS - 1; i++) {
    HLAPI.i.u.op.secondary.acc_agu.offsets[i] = 1;
    HLAPI.i.u.op.secondary.acc_agu.iter[i] = 1;
  }
  HLAPI.i.u.op.secondary.acc_agu.offsets[ACT_AM_LOOPS - 1] = 1;
  HLAPI.i.u.op.secondary.acc_agu.iter[ACT_AM_LOOPS - 1] = 1;

  // feature-map output
  if (ofm_en) {
    for (int i = 0; i < ACT_FM_LOOPS - 5; i++) {
      HLAPI.i.u.op.out.fm.fm_agu.iter[i] = 1;
      HLAPI.i.u.op.out.fm.fm_agu.offsets[i] = 0;
    }
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1] = fmodbl;                   // mlsb
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 2] = 1;                        // C
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 3] = shapes.oshape[2] / TNSVSIZE; // W/8
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 4] = shapes.oshape[3];         // H
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 5] = shapes.oshape[4];         // D
    // pooling parameters
    HLAPI.i.u.op.out.fm.pool.bf = 0; // disable maxpooling
    // writeback all lines as it reduction over the channel dim
    HLAPI.i.u.op.out.fm.enable = (int8_t)0xff;
  }
  // accumulator output
  if (oac_en) {
    for (int i = 0; i < ACT_AM_LOOPS - 1; i++) {
      HLAPI.i.u.op.out.acc_agu.offsets[i] = 1;
      HLAPI.i.u.op.out.acc_agu.iter[i] = 1;
    }
    HLAPI.i.u.op.out.acc_agu.offsets[ACT_AM_LOOPS - 1] = 1;
    HLAPI.i.u.op.out.acc_agu.iter[ACT_AM_LOOPS - 1] = fmodbl; // 48bits if supported
    HLAPI.i.u.op.out.acc_agu.iter[ACT_AM_LOOPS - 2] = shapes.oshape[1];
    HLAPI.i.u.op.out.acc_agu.iter[ACT_AM_LOOPS - 3] = shapes.oshape[2];
    HLAPI.i.u.op.out.acc_agu.iter[ACT_AM_LOOPS - 4] = shapes.oshape[3];
  }
}

// initialize the input tensors
template <template <typename> class B>
template <template <typename> class BD>
void gtoa_creduce_base_params<B>::init_l1_input(
  // structure with allocated buffers and tensors in L1 memory [D][H][W][Grp][C]
  const impl_spec_container_t<BD> &p) {
  // fill the HLAPI offset parameters
  HLAPI.i.u.op.primary.fm_agu.ptr = p.data.get_ptr();
  HLAPI.i.u.op.primary.fm_agu.buf.base = p.data.get_base();
  HLAPI.i.u.op.primary.fm_agu.buf.len = p.data.get_size();
  HLAPI.i.u.op.primary.fm_agu.stride = p.data.get_offset(2); // W
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 1] = p.data.get_offset(0); // C
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 2] = p.data.get_offset(1); // 1
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 3] = p.data.get_offset(2) * TNSVSIZE +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1]) * p.data.get_offset(0); // W
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 4] = p.data.get_offset(3) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3]) * p.data.get_offset(2) * TNSVSIZE +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1]) * p.data.get_offset(0); // H
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 5] = p.data.get_offset(4) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 4]) * p.data.get_offset(3) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3]) * p.data.get_offset(2) * TNSVSIZE +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1]) * p.data.get_offset(0); // D
}

// initialize the output tensors
template <template <typename> class B>
template <template <typename> class BD>
void gtoa_creduce_base_params<B>::init_l1_output(
        // structure with allocated buffers and tensors in L1 memory
  const impl_spec_container_t<BD>& p) {

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.out.fm.fm_agu.ptr = localptr_t<ixpix_t>(p.data.get_ptr());
  HLAPI.i.u.op.out.fm.fm_agu.buf.base = localptr_t<ixpix_t>(p.data.get_base());
  HLAPI.i.u.op.out.fm.fm_agu.buf.len = p.data.get_size();
  HLAPI.i.u.op.out.fm.fm_agu.stride = p.data.get_offset(2);
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 1] = p.data.get_offset(0); // C
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 2] = p.data.get_offset(1); // 1
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 3] = p.data.get_offset(2) * TNSVSIZE +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]) * p.data.get_offset(0); // W
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 4] = p.data.get_offset(3) +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 3]) * p.data.get_offset(2) * TNSVSIZE +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]) *  p.data.get_offset(0); // H
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 5] = p.data.get_offset(4) +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 4]) * p.data.get_offset(3) +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 3]) * p.data.get_offset(2) * TNSVSIZE +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]) * p.data.get_offset(0); // D
}

template <template <typename> class B>
inline void gtoa_creduce_base_params<B>::get_shapes(
    gtoa_act_params_impl_shapes& s  // structure with implementation specific minimum buffer sizes
) {
  s = shapes;
}

#undef HLAPI

#endif // NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_CREDUCE_BASE_INLINE_HPP_
