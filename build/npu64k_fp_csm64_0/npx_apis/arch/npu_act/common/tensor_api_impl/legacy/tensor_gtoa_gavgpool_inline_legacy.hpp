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
 * tensor_gtoa_gavgpool_inline_legacy.hpp
 *
 * File defining a tensor level global average pool API base on the generic tensor operation API
 *
 */
#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_LEGACY_TENSOR_GTOA_GAVGPOOL_INLINE_LEGACY_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_LEGACY_TENSOR_GTOA_GAVGPOOL_INLINE_LEGACY_HPP_
#define HLAPI gtoa_params<B>::hlapi

// constructor
// global average pooling operation for accumulator (32b) input
// output to AM (32b) if keepAcc, or VM (8b/16b) if not keepAcc
template <template <typename> class B>
gtoa_gavgpool_params<B>::gtoa_gavgpool_params(
    aoffset_t noi,          // number output channels (not vectors)
    const shape<3> &ishpi,  // input shape
    bool fmodbli,           // 16b output feature-map
    bool sati,              // do saturation
    bool useAcc,            // use previous accumulator value
    bool keepAcc) :         // keep result in accumulator instead of output to VM
    gtoa_params<B>() {
  mode = false;  // legacy
  // enable accumulator input and accumulator/feature-map output
  HLAPI.i.bf = 0;           // function, not LUT init
  HLAPI.i.u.op.io_en = ACT_IO_EN_AC0 |
    ACT_IO_EN_AC1 |
    (keepAcc ? ACT_IO_EN_OAC : ACT_IO_EN_OFM);

  HLAPI.i.u.op.bf = (0 << ACT_BF_OP_IN0DBL_START) |
    (fmodbli ? 1 << ACT_BF_OP_OUTDBL_START : 0) |
    (sati ? 1 << ACT_BF_OP_OUTSAT_START : 0);
  HLAPI.i.u.op.bf |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_IN1INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
  // enable padding with zero
  HLAPI.i.u.op.bf |= (ACT_BF_OP_IN0PEN_MASK);
  // set padding window
  HLAPI.i.u.op.padpos[SPATIAL_W] = 0;
  HLAPI.i.u.op.padpos[SPATIAL_H] = 0;
  HLAPI.i.u.op.padlim[SPATIAL_W] = ishpi[SPATIAL_W] - 1;
  HLAPI.i.u.op.padlim[SPATIAL_H] = (aoffset_t)0x7fff;
  cmax = noi;
  int c = RDIV_UP(noi, ISIZE);
  int w = RDIV_UP(ishpi[SPATIAL_W], TNSVSIZE);
  // input0 accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN/lsb/msb] format
  shapes.ishape = {1,
                   ishpi[SPATIAL_H],
                   (aoffset_t)w,
                   ishpi[SPATIAL_D],
                   (aoffset_t)c};
  // input1 accumulator in vyixacc_t [C] format
  shapes.i1shape = {1, 1, 1, 1, (aoffset_t)c};
  // output feature-map in ixpix_t [C] format
  if (keepAcc)
    shapes.oshape = {1, 1, 1, 1, (aoffset_t)c};
  else
    shapes.oshape = {(aoffset_t)(fmodbli ? 2 * c : c), 1, 1, 1, 1};
  // parameter dimension ixpix_t [C]
  shapes.pshape = {(aoffset_t)(4 * c)};
  // set padding window
  HLAPI.i.u.op.pad_stride = 1;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_W] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_W] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_W] = TNSVSIZE;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_W] = (1 - w) * TNSVSIZE;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_W] = (1 - w) * TNSVSIZE;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_W] = (1 - w) * TNSVSIZE;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_H] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_H] = 1;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_H] = 1 - ishpi[SPATIAL_H];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_H] = 1 - ishpi[SPATIAL_H];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_H] = 1 - ishpi[SPATIAL_H];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_H] = 1 - ishpi[SPATIAL_H];
  init_gavgpool(HLAPI, useAcc, keepAcc);
  set_gavgpool_params();
}

// global average pooling operation for feature-map (8b/16b) input
// output to AM (32b) if keepAcc, or VM (8b/16b) if not keepAcc
template <template <typename> class B>
gtoa_gavgpool_params<B>::gtoa_gavgpool_params(
    aoffset_t noi,          // number output channels (not vectors)
    const shape<3> &ishpi,  // input shape
    bool fmidbli,           // 16b input feature-map
    bool fmodbli,           // 16b output feature-map
    bool sati,              // do saturation
    bool useAcc,            // use previous accumulator value
    bool keepAcc) :         // keep result in accumulator instead of output to VM
    gtoa_params<B>() {
  mode = false;  // legacy
  // enable accumulator input and accumulator/feature-map output
  HLAPI.i.bf = 0;           // function, not LUT init
  HLAPI.i.u.op.io_en = ACT_IO_EN_FM0 |
    ACT_IO_EN_AC1 |
    (keepAcc ? ACT_IO_EN_OAC : ACT_IO_EN_OFM);

  HLAPI.i.u.op.bf = (0 << ACT_BF_OP_IN0DBL_START) |
    (fmodbli ? 1 << ACT_BF_OP_OUTDBL_START : 0) |
    (sati ? 1 << ACT_BF_OP_OUTSAT_START : 0);
  HLAPI.i.u.op.bf |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_IN1INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
  // enable padding with zero
  HLAPI.i.u.op.bf |= (ACT_BF_OP_IN0PEN_MASK);
  // set padding window
  HLAPI.i.u.op.padpos[SPATIAL_W] = 0;
  HLAPI.i.u.op.padpos[SPATIAL_H] = 0;
  HLAPI.i.u.op.padlim[SPATIAL_W] = ishpi[SPATIAL_W] - 1;
  HLAPI.i.u.op.padlim[SPATIAL_H] = (aoffset_t)0x7fff;
  cmax = noi;
  int c = (noi + ISIZE - 1) / ISIZE;
  int w = (ishpi[SPATIAL_W] + TNSVSIZE - 1) / TNSVSIZE;
  // input feature-map in ixpix_t [D][H][W][C] format
  shapes.ishape = {(aoffset_t)(fmidbli ? 2 * c : c),
                   1,
                   (aoffset_t)(w * TNSVSIZE),
                   ishpi[SPATIAL_H],
                   ishpi[SPATIAL_D]};
  // input1 accumulator in vyixacc_t [C] format
  shapes.i1shape = {1, 1, 1, 1, (aoffset_t)c};
  // output feature-map in ixpix_t [C] format
  shapes.oshape = {(aoffset_t)(fmodbli ? 2 * c : c), 1, 1, 1, 1};
  // parameter dimension ixpix_t [C]
  shapes.pshape = {(aoffset_t)(4 * c)};
  // set padding window
  HLAPI.i.u.op.pad_stride = 1;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_W] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_W] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_W] = TNSVSIZE;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_W] = (1 - w) * TNSVSIZE;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_W] = (1 - w) * TNSVSIZE;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_W] = (1 - w) * TNSVSIZE;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_H] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_H] = 1;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_H] = 1 - ishpi[SPATIAL_H];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_H] = 1 - ishpi[SPATIAL_H];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_H] = 1 - ishpi[SPATIAL_H];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_H] = 1 - ishpi[SPATIAL_H];
  init_gavgpool(HLAPI, useAcc, keepAcc);
  set_gavgpool_params();
}

// global average pooling operation for feature-map (8b/16b) input
// accumulator output to AM (32b) if keepAcc
// accumulator output to AM (32) if final tile not keepAcc average
template <template <typename> class B>
gtoa_gavgpool_params<B>::gtoa_gavgpool_params(
    aoffset_t       noi,        // number output channels (not vectors)
    const shape<3>& ishpi,      // input shape
    const shape<2>& padlimi,    // input shape
    size_t          num,        // total number of elements in pool
    bool            fmidbli,    // 16b input feature-map
    bool            useAcc,     // use previous accumulator value
    bool            keepAcc) :  // keep result in accumulator instead of output to VM
  gtoa_params<B>() {
  mode = false;  // legacy
  // enable accumulator input and accumulator/feature-map output
  HLAPI.i.bf = 0;           // function, not LUT init
  HLAPI.i.u.op.io_en = ACT_IO_EN_FM0 |
    ACT_IO_EN_AC1 |
    ACT_IO_EN_OAC;
  HLAPI.i.u.op.bf = fmidbli ? ACT_BF_OP_IN0DBL_MASK : 0;
  HLAPI.i.u.op.bf |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_IN1INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
  // enable padding with zero
  HLAPI.i.u.op.bf |= (ACT_BF_OP_IN0PEN_MASK);
  // set padding window
  HLAPI.i.u.op.padpos[SPATIAL_W] = 0;
  HLAPI.i.u.op.padpos[SPATIAL_H] = 0;
  HLAPI.i.u.op.padlim[SPATIAL_W] = padlimi[0];
  HLAPI.i.u.op.padlim[SPATIAL_H] = padlimi[1];
  cmax = noi;
  int c = RDIV_UP(noi, ISIZE);
  int w = RDIV_UP(ishpi[SPATIAL_W], TNSVSIZE);
  // input feature-map in ixpix_t [D][H][W][C] format
  shapes.ishape = {(aoffset_t)(fmidbli ? 2 * c : c),
                   1,
                   ishpi[SPATIAL_W],
                   ishpi[SPATIAL_H],
                   ishpi[SPATIAL_D]};
  // input1 accumulator in vyixacc_t [C] format
  shapes.i1shape = {1, 1, 1, 1, (aoffset_t)c};
  // output accumulator in vyixacc_t [C] format
  shapes.oshape  = {1, 1, 1, 1, (aoffset_t)c};
  // parameter dimension
  shapes.pshape = {0};
  // set padding window
  HLAPI.i.u.op.pad_stride = 1;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_W] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_W] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_W] = TNSVSIZE;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_W] = (1 - w) * TNSVSIZE;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_W] = (1 - w) * TNSVSIZE;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_W] = (1 - w) * TNSVSIZE;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_H] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_H] = 1;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_H] = 1 - ishpi[SPATIAL_H];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_H] = 1 - ishpi[SPATIAL_H];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_H] = 1 - ishpi[SPATIAL_H];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_H] = 1 - ishpi[SPATIAL_H];
  init_gavgpool_new(HLAPI, useAcc, keepAcc);
  set_gavgpool_params();

  // set scale from number of elements
  //// quantize 1/num as 16b signed number in SR2
  //int32_t frc = static_cast<int>((static_cast<double>(0x40000000)/num)+0.5);
  //// normalize fraction
  //int i = 0;
  //while ((((frc << i) & 0xc0000000) != 0x80000000) && (((frc << i) & 0xc0000000) != 0x40000000)) {
  //  i++;
  //}
  //if (i >= 16) {
  //  HLAPI.i.u.op.scl[2] = frc << (i-16);
  //} else {
  //  HLAPI.i.u.op.scl[2] = frc >> (16-i);
  //}
  //// set extra right shift in SR3
  //HLAPI.i.u.op.scl[3] = i+14;
  // 1/num as fp32 number in SR2
  float recip = 1.0/(float)num;
  fp_e8m23_t frecip(recip);
  HLAPI.i.u.op.scl[2] = frecip.data;
}

// set iterators
template <template <typename> class B>
void gtoa_gavgpool_params<B>::set_gavgpool_params() {
  int fmidbl = (HLAPI.i.u.op.bf & ACT_BF_OP_IN0DBL_MASK) != 0 ? 2 : 1;
  int fmodbl = (HLAPI.i.u.op.bf & ACT_BF_OP_OUTDBL_MASK) != 0 ? 2 : 1;
  bool ifm_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0;
  bool iac_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_AC0) != 0;
  bool ofm_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_OFM) != 0;
  bool oac_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_OAC) != 0;

  int i_c = oac_en ? shapes.oshape[4] : shapes.oshape[0]/fmodbl;
  int i_spatial;
  if (ifm_en) {
    i_spatial = RDIV_UP(shapes.ishape[2], TNSVSIZE) * shapes.ishape[3] * shapes.ishape[4];
  } else {
    i_spatial = shapes.ishape[1] * shapes.ishape[2] * shapes.ishape[3];
  }
  // iterators
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 3] = i_c;          // channel loop
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 2] = i_spatial;    // spatial loop
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 1] = 1;            // inner loop is 1
  // primary feature-map input
  if (ifm_en) {
    for (int i = 0; i < ACT_FM_LOOPS - 5; i++) {
      HLAPI.i.u.op.primary.fm_agu.iter[i] = 1;
      HLAPI.i.u.op.primary.fm_agu.offsets[i] = 0;
    }
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1] = fmidbl;                            // mlsb
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2] = shapes.ishape[3];                  // H
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3] = RDIV_UP(shapes.ishape[2], TNSVSIZE);  // W/8
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 4] = shapes.ishape[4];                  // D
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 5] = shapes.ishape[0] / fmidbl;         // C
  }
  // primary accumulator input
  if (iac_en) {
    for (int i = 0; i < ACT_AM_LOOPS - 1; i++) {
      HLAPI.i.u.op.primary.acc_agu.offsets[i] = 1;
      HLAPI.i.u.op.primary.acc_agu.iter[i] = 1;
    }
    HLAPI.i.u.op.primary.acc_agu.offsets[ACT_AM_LOOPS - 1] = 1;
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS - 1] = 1;
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS - 2] = shapes.ishape[1];           // H
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS - 3] = shapes.ishape[2];           // W
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS - 4] = shapes.ishape[3] *
                                                          shapes.ishape[4];           // D*C
  }
  // secondary accumulator input
  for (int i = 0; i < ACT_AM_LOOPS - 1; i++) {
    HLAPI.i.u.op.secondary.acc_agu.offsets[i] = 1;
    HLAPI.i.u.op.secondary.acc_agu.iter[i] = 1;
  }
  HLAPI.i.u.op.secondary.acc_agu.offsets[ACT_AM_LOOPS-1] = 1;
  HLAPI.i.u.op.secondary.acc_agu.iter[ACT_AM_LOOPS-1] = i_c;
  // feature-map output
  if (ofm_en) {
    for (int i = 0; i < ACT_FM_LOOPS - 5; i++) {
      HLAPI.i.u.op.out.fm.fm_agu.iter[i] = 1;
      HLAPI.i.u.op.out.fm.fm_agu.offsets[i] = 0;
    }
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1] = fmodbl;                       // mlsb
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 2] = 1;                            // H
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 3] = 1;                            // W/8
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 4] = 1;                            // D
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 5] = shapes.oshape[0]/fmodbl;      // C
    // pooling parameters
    HLAPI.i.u.op.out.fm.pool.bf = 0;  // disable maxpooling
    // writeback one line
    HLAPI.i.u.op.out.fm.enable = (int8_t)0x1;
  }
  // accumulator output
  if (oac_en) {
    for (int i = 0; i < ACT_AM_LOOPS - 1; i++) {
      HLAPI.i.u.op.out.acc_agu.offsets[i] = 1;
      HLAPI.i.u.op.out.acc_agu.iter[i] = 1;
    }
    HLAPI.i.u.op.out.acc_agu.offsets[ACT_AM_LOOPS - 1] = 1;
    HLAPI.i.u.op.out.acc_agu.iter[ACT_AM_LOOPS - 1] = i_c;
  }
}

// change the function microcode
template <template <typename> class B>
inline void gtoa_gavgpool_params<B>::modif_func(bool keepAcc, gtoa_params_impl_modif& m) {  // NOLINT [runtime/references]
  act_hlapi_t h;
  init_gavgpool_new(h, false, keepAcc);
  m = h.i.u.op.act_prog;
}

// change the paramters required by the feature-map output type
template <template <typename> class B>
template <template <typename> class BD>
inline void gtoa_gavgpool_params<B>::modif_out_fm(
  aoffset_t                        noi,      // number output channels
  bool                             fmodbli,  // 16b output feature-map
  bool                             sati,     // saturate output
  gtoa_params_impl_alt_fm&         a) {      // NOLINT [runtime/references]
  int c = RDIV_UP(noi, ISIZE);
  // enable one lane for gavgpool output
  a.enable = 0x1;
  // clear acc output bit and set fm output bit
  a.io_en = (HLAPI.i.u.op.io_en & ~ACT_IO_EN_OAC) | ACT_IO_EN_OFM;
  // clear and set dbl/sat bits
  a.bf = (HLAPI.i.u.op.bf & ~(ACT_BF_OP_OUTSAT_MASK | ACT_BF_OP_OUTDBL_MASK))
                          | (fmodbli ? ACT_BF_OP_OUTDBL_MASK : 0)
                          | (sati    ? ACT_BF_OP_OUTSAT_MASK : 0);
  // set output feature-map AGU
  for (int i = 0; i < ACT_FM_LOOPS - 5; i++) {
    a.fm_agu.iter[i] = 1;
    a.fm_agu.offsets[i] = 0;
  }
  a.fm_agu.iter[ACT_FM_LOOPS - 1] = fmodbli ? 2 : 1;
  a.fm_agu.iter[ACT_FM_LOOPS - 2] = 1;
  a.fm_agu.iter[ACT_FM_LOOPS - 3] = 1;
  a.fm_agu.iter[ACT_FM_LOOPS - 4] = 1;
  a.fm_agu.iter[ACT_FM_LOOPS - 5] = c;
  impl_spec_container_t<BD> p(nullptr, {(aoffset_t)(fmodbli ? 2 * c : c), 1, 1, 1, 1});
  gtoa_params<B>::tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp][C] --> [D][H][W][Grp][C/mlsb][mlsb]
  tensor_t<ixpix_t, 6, B> t0(p.data.split(0, a.fm_agu.iter[ACT_FM_LOOPS - 5]));
  // transpose to [Grp][C][D=1][W=1][H=1][mlsb]
  tensor_t<ixpix_t, 6, B> t1(t0.transpose({0, 4, 3, 5, 1, 2}));
  // fill the HLAPI offset parameters
  a.fm_agu.stride   = 1;
  a.fm_agu.offsets[ACT_FM_LOOPS - 1] = t1.get_offset(0);   // mlsb
  a.fm_agu.offsets[ACT_FM_LOOPS - 2] = t1.get_offset(1) +
    (1 - a.fm_agu.iter[ACT_FM_LOOPS - 1]) * t1.get_offset(0);  // H
  a.fm_agu.offsets[ACT_FM_LOOPS - 3] = t1.get_offset(2) +
    (1 - a.fm_agu.iter[ACT_FM_LOOPS - 1]) * t1.get_offset(0);  // W
  a.fm_agu.offsets[ACT_FM_LOOPS - 4] = t1.get_offset(3) +
    (1 - a.fm_agu.iter[ACT_FM_LOOPS - 1]) * t1.get_offset(0);  // D
  a.fm_agu.offsets[ACT_FM_LOOPS - 5] = t1.get_offset(4) +
    (1 - a.fm_agu.iter[ACT_FM_LOOPS - 1]) * t1.get_offset(0);  // Grp*C
  // set pointer and buffer (dummy)
  a.fm_agu.ptr      = localptr_t<ixpix_t>(t1.get_ptr());
  a.fm_agu.buf.base = localptr_t<ixpix_t>(t1.get_base());
  a.fm_agu.buf.len  = t1.get_size();
}

// change the parameters required by the accumulator output type
template <template <typename> class B>
inline void gtoa_gavgpool_params<B>::modif_out_acc(
  aoffset_t                 noi,  // number output channels
  gtoa_params_impl_alt_acc& a) {  // NOLINT [runtime/references]
  int c = RDIV_UP(noi, ISIZE);
  // clear fm output bit and set acc output bit
  a.io_en = (HLAPI.i.u.op.io_en & ~ACT_IO_EN_OFM) | ACT_IO_EN_OAC;
  for (int i = 0; i < ACT_AM_LOOPS - 1; i++) {
    a.acc_agu.offsets[i] = 1;
    a.acc_agu.iter[i] = 1;
  }
  a.acc_agu.offsets[ACT_AM_LOOPS - 1] = 1;
  a.acc_agu.iter[ACT_AM_LOOPS - 1] = c;
  // set pointer (dummy)
  a.acc_agu.ptr = 0;
}

// initialize the scale and shift parameters for global average pooling
template <template <typename> class B>
void gtoa_gavgpool_params<B>::init_gavgpool_scale(
  int16_t scale,     // common scaling factor for all channels
  uint8_t shift) {   // common shift left amount for all channels
  float f = scl_fix2flt(scale, shift);
  int32_t val = *(int32_t*)(void*)&f;
  
  HLAPI.i.u.op.scl[2] = val;  // put in SR2
}

#undef HLAPI

#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_LEGACY_TENSOR_GTOA_GAVGPOOL_INLINE_LEGACY_HPP_
