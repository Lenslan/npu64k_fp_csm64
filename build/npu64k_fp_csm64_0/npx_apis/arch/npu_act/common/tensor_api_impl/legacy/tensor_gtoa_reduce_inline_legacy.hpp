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
 * tensor_gtoa_reduce_inline_legacy.hpp
 *
 * File defining a tensor level reduce API base on the generic tensor operation API
 *
 */
#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_LEGACY_TENSOR_GTOA_REDUCE_INLINE_LEGACY_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_LEGACY_TENSOR_GTOA_REDUCE_INLINE_LEGACY_HPP_
#define HLAPI gtoa_params<B>::hlapi

// constructor
// reduce operation from accumulator (32b) to feature-map (8b/16b)
template <template <typename> class B>
gtoa_reduce_params<B>::gtoa_reduce_params(
    aoffset_t noi,          // number output channels (not vectors)
    const shape<3> &ishpi,  // input shape, output inner is 1
    bool fmodbli,           // 16b output feature-map
    bool sati,              // do saturation
    act_red_op_t opi,       // reduction operation to perform
    const int dimi) :       // spatial dimensions to reduce
    gtoa_params<B>() {
      // enable accumulator input and feature-map output
      HLAPI.i.bf = 0;           // function, not LUT init
      HLAPI.i.u.op.io_en = ACT_IO_EN_AC0 | ACT_IO_EN_OFM;
      HLAPI.i.u.op.bf = (0 << ACT_BF_OP_IN0DBL_START) |
                        (fmodbli ? 1 << ACT_BF_OP_OUTDBL_START : 0) |
                        (sati ? 1 << ACT_BF_OP_OUTSAT_START : 0);
      HLAPI.i.u.op.bf |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
      cmax = noi;
      red_dim = dimi;
      red_accum = false;
      assert((dimi >= 1 && dimi <= 3) && "dimi out of supported range");
      int c = (noi + ISIZE - 1) / ISIZE;
      int w = (ishpi[SPATIAL_W] + TNSVSIZE - 1) / TNSVSIZE;
      // input accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN/lsb/msb] format
      shapes.ishape = {1,
                      ishpi[SPATIAL_H],
                      (aoffset_t)w,
                      ishpi[SPATIAL_D],
                      (aoffset_t)c};
      // output feature-map in ixpix_t [D][H][W][C] format
      shapes.oshape = {(aoffset_t)(fmodbli ? 2 * c : c),
                      1,
                      (aoffset_t)TNSVSIZE,
                      (dimi >= 2) ? (aoffset_t)1 : ishpi[SPATIAL_H],
                      (dimi >= 3) ? (aoffset_t)1 : ishpi[SPATIAL_D]};
      // parameter dimension ixpix_t [C]
      shapes.pshape = {noi};
      // set padding window
      HLAPI.i.u.op.padpos[SPATIAL_W] = 0;
      HLAPI.i.u.op.padpos[SPATIAL_H] = 0;
      HLAPI.i.u.op.padlim[SPATIAL_W] = ishpi[SPATIAL_W] - 1;
      HLAPI.i.u.op.padlim[SPATIAL_H] = (aoffset_t)0x7fff;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_W] = TNSVSIZE;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_W] = (1 - shapes.ishape[2]) * TNSVSIZE;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_W] = (1 - shapes.ishape[2]) * TNSVSIZE;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_W] = (1 - shapes.ishape[2]) * TNSVSIZE;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_W] = 0;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_W] = 0;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_H] = 0;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_H] = 1;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_H] = 1 - shapes.ishape[1];
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_H] = 1 - shapes.ishape[1];
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_H] = 0;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_H] = 0;
      init_reduce_i(opi, false);
      set_reduce_params();
}

// reduce operation from accumulator (32b) to accumulator (32b)
template <template <typename> class B>
gtoa_reduce_params<B>::gtoa_reduce_params(
    aoffset_t noi,          // number output channels (not vectors)
    const shape<3> &ishpi,  // input shape, output inner is 1
    act_red_op_t opi,       // reduce operation to perform
    const int dimi) :       // spatial dimensions to reduce
    gtoa_params<B>() {
      // enable accumulator input and accumulator output
      HLAPI.i.bf = 0;   // function, not LUT init
      HLAPI.i.u.op.io_en = ACT_IO_EN_AC0 | ACT_IO_EN_OAC;
      HLAPI.i.u.op.bf = (0 << ACT_BF_OP_IN0DBL_START) |
                        (0 << ACT_BF_OP_OUTDBL_START) |
                        (0 << ACT_BF_OP_OUTSAT_START);
      HLAPI.i.u.op.bf |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
      cmax = noi;
      red_dim = dimi;
      red_accum = false;
      assert((dimi >= 1 && dimi <= 3) && "dimi out of supported range");
      int c = (noi + ISIZE - 1) / ISIZE;
      int w = (ishpi[SPATIAL_W] + TNSVSIZE - 1) / TNSVSIZE;
      // input accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN/lsb/msb] format
      shapes.ishape = {1,
                       ishpi[SPATIAL_H],
                       (aoffset_t)w,
                       ishpi[SPATIAL_D],
                       (aoffset_t)c};
      // output accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN] format
      shapes.oshape = {1,
                       (dimi >= 2) ? (aoffset_t)1 : ishpi[SPATIAL_H],
                       1,
                       (dimi >= 3) ? (aoffset_t)1 : ishpi[SPATIAL_D],
                       (aoffset_t)c};
      // parameter dimension ixpix_t [C]
      shapes.pshape = {noi};
      // set padding window
      HLAPI.i.u.op.padpos[SPATIAL_W] = 0;
      HLAPI.i.u.op.padpos[SPATIAL_H] = 0;
      HLAPI.i.u.op.padlim[SPATIAL_W] = ishpi[SPATIAL_W] - 1;
      HLAPI.i.u.op.padlim[SPATIAL_H] = (aoffset_t)0x7fff;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_W] = TNSVSIZE;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_W] = (1 - shapes.ishape[2]) * TNSVSIZE;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_W] = (1 - shapes.ishape[2]) * TNSVSIZE;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_W] = (1 - shapes.ishape[2]) * TNSVSIZE;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_W] = 0;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_W] = 0;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_H] = 0;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_H] = 1;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_H] = 1 - shapes.ishape[1];
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_H] = 1 - shapes.ishape[1];
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_H] = 0;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_H] = 0;
      init_reduce_i(opi, false);
      set_reduce_params();
}

// reduce operation from feature-map (8b/16b) to feature-map (8b/16b)
template <template <typename> class B>
gtoa_reduce_params<B>::gtoa_reduce_params(
    aoffset_t noi,          // number output channels (not vectors)
    const shape<3> &ishpi,  // input shape, output inner is 1
    bool fmidbli,           // 8b/16b input feature-map
    bool fmodbli,           // 8b/16b output feature-map
    bool sati,              // do saturation
    act_red_op_t opi,       // reduction operation to perform
    const int dimi) :       // spatial dimensions to reduce
    gtoa_params<B>() {
      // enable accumulator input and accumulator output
      HLAPI.i.bf = 0;   // function, not LUT init
      HLAPI.i.u.op.io_en = ACT_IO_EN_FM0 | ACT_IO_EN_OFM;
      HLAPI.i.u.op.bf = (fmidbli ? 1 << ACT_BF_OP_IN0DBL_START : 0) |
                        (fmodbli ? 1 << ACT_BF_OP_OUTDBL_START : 0) |
                        (sati ? 1 << ACT_BF_OP_OUTSAT_START : 0);
      HLAPI.i.u.op.bf |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
      cmax = noi;
      red_dim = dimi;
      red_accum = false;
      assert((dimi >= 1 && dimi <= 3) && "dimi out of supported range");
      int c = (noi + ISIZE - 1) / ISIZE;
      int w = (ishpi[SPATIAL_W] + TNSVSIZE - 1) / TNSVSIZE;
      // input feature-map in ixpix_t [D][H][W][C] format
      shapes.ishape = {(aoffset_t)(fmidbli ? 2 * c : c),
                      1,
                      (aoffset_t)(w * TNSVSIZE),
                      ishpi[SPATIAL_H],
                      ishpi[SPATIAL_D]};
      // output feature-map in ixpix_t [D][H][W][C] format
      shapes.oshape = {(aoffset_t)(fmodbli ? 2 * c : c),
                      1,
                      (aoffset_t)TNSVSIZE,
                      (dimi >= 2) ? (aoffset_t)1 : ishpi[SPATIAL_H],
                      (dimi >= 3) ? (aoffset_t)1 : ishpi[SPATIAL_D]};
      // parameter dimension ixpix_t [C]
      shapes.pshape = {noi};
      // set padding windo
      HLAPI.i.u.op.padpos[SPATIAL_W] = 0;
      HLAPI.i.u.op.padpos[SPATIAL_H] = 0;
      HLAPI.i.u.op.padlim[SPATIAL_W] = ishpi[SPATIAL_W] - 1;
      HLAPI.i.u.op.padlim[SPATIAL_H] = 0x7fff;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_W] = 0;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_W] = TNSVSIZE;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_W] = -(TNSVSIZE * (w - 1));
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_W] = -(TNSVSIZE * (w - 1));
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_W] = -(TNSVSIZE * (w - 1));
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_W] = 0;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_H] = 0;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_H] = 0;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_H] = 1;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_H] = 1 - shapes.ishape[3];
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_H] = 1 - shapes.ishape[3];
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_H] = 0;
      init_reduce_i(opi, false);
      set_reduce_params();
}

// reduce operation from feature-map (8b/16b) to accumulator (32b)
template <template <typename> class B>
gtoa_reduce_params<B>::gtoa_reduce_params(
    aoffset_t noi,          // number output channels (not vectors)
    const shape<3> &ishpi,  // input shape, output inner is 1
    bool fmidbli,           // 8b/16b input feature-map
    act_red_op_t opi,       // reduce operation to perform
    const int dimi) :       // spatial dimensions to reduce
    gtoa_params<B>() {
      // enable accumulator input and accumulator output
      HLAPI.i.bf = 0;   // function, not LUT init
      HLAPI.i.u.op.io_en = ACT_IO_EN_FM0 | ACT_IO_EN_OAC;
      HLAPI.i.u.op.bf = (fmidbli ? 1 << ACT_BF_OP_IN0DBL_START : 0) |
                        (0 << ACT_BF_OP_OUTDBL_START) |
                        (0 << ACT_BF_OP_OUTSAT_START);
      HLAPI.i.u.op.bf |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
      cmax = noi;
      red_dim = dimi;
      red_accum = false;
      assert((dimi >= 1 && dimi <= 3) && "dimi out of supported range");
      int c = (noi + ISIZE - 1) / ISIZE;
      int w = (ishpi[SPATIAL_W] + TNSVSIZE - 1) / TNSVSIZE;
      // input feature-map in ixpix_t [D][H][W][C] format
      shapes.ishape = {(aoffset_t)(fmidbli ? 2 * c : c),
                      1,
                      (aoffset_t)(w * TNSVSIZE),
                      ishpi[SPATIAL_H],
                      ishpi[SPATIAL_D]};
      // output accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN] format
      shapes.oshape = {1,
                      (dimi >= 2) ? (aoffset_t)1 : ishpi[SPATIAL_H],
                      1,
                      (dimi >= 3) ? (aoffset_t)1 : ishpi[SPATIAL_D],
                      (aoffset_t)c};
      // parameter dimension ixpix_t [C]
      // set padding window
      HLAPI.i.u.op.padpos[SPATIAL_W] = 0;
      HLAPI.i.u.op.padpos[SPATIAL_H] = 0;
      HLAPI.i.u.op.padlim[SPATIAL_W] = ishpi[SPATIAL_W] - 1;
      HLAPI.i.u.op.padlim[SPATIAL_H] = 0x7fff;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_W] = 0;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_W] = TNSVSIZE;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_W] = -(TNSVSIZE * (w - 1));
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_W] = -(TNSVSIZE * (w - 1));
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_W] = -(TNSVSIZE * (w - 1));
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_W] = 0;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_H] = 0;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_H] = 0;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_H] = 1;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_H] = 1 - shapes.ishape[3];
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_H] = 1 - shapes.ishape[3];
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_H] = 0;
      init_reduce_i(opi, false);
      set_reduce_params();
}

// reduce operation for feature-map (8b/16b) input
// secondary input is accumulator (32b) if useAcc = true; 0 if useAcc = false
// output to VM (8b/16b) if keepAcc = false; to AM (32b) if keepAcc = true
template <template <typename> class B>
gtoa_reduce_params<B>::gtoa_reduce_params(
    aoffset_t noi,            // number output channels (not vectors)
    const shape<3>& ishpi,    // input shape, output inner is 1
    const shape<2>& padlimi,  // padding shape
    bool fmidbli,             // 8b/16b input feature-map
    bool fmodbli,             // 8b/16b output feature-map
    bool sati,                // do saturation
    act_red_op_t opi,         // reduction operation to perform
    bool useAcc,              // use accumulator input
    bool keepAcc,             // keep result in accumulator
    const int dimi) :         // spatial dimensions to reduce
    gtoa_params<B>() {
      // enable accumulator input and accumulator output
      HLAPI.i.bf = 0;   // function, not LUT init
      HLAPI.i.u.op.io_en = ACT_IO_EN_FM0 | ACT_IO_EN_AC1 |
        (keepAcc ? ACT_IO_EN_OAC : ACT_IO_EN_OFM);
      HLAPI.i.u.op.bf = (fmidbli ? 1 << ACT_BF_OP_IN0DBL_START : 0) |
                        (!keepAcc && fmodbli ? 1 << ACT_BF_OP_OUTDBL_START : 0) |
                        (!keepAcc && sati ? 1 << ACT_BF_OP_OUTSAT_START : 0);
      HLAPI.i.u.op.bf |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_IN1INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
      cmax = noi;
      red_dim = dimi;
      red_accum = true;
      assert((dimi >= 1 && dimi <= 3) && "dimi out of supported range");
      int c = (noi + ISIZE - 1) / ISIZE;
      int w = (ishpi[SPATIAL_W] + TNSVSIZE - 1) / TNSVSIZE;
      // input feature-map in ixpix_t [D][H][W][C] format
      shapes.ishape = {(aoffset_t)(fmidbli ? 2 * c : c),
                      1,
                      (aoffset_t)(w * TNSVSIZE),
                      ishpi[SPATIAL_H],
                      ishpi[SPATIAL_D]};
      // input1 accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN] format
      shapes.i1shape = {1,
                       (dimi >= 2) ? (aoffset_t)1 : ishpi[SPATIAL_H],
                       1,
                       (dimi >= 3) ? (aoffset_t)1 : ishpi[SPATIAL_D],
                       (aoffset_t)c};
      if (keepAcc)
        // output accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN] format
        shapes.oshape = {1,
                        (dimi >= 2) ? (aoffset_t)1 : ishpi[SPATIAL_H],
                        1,
                        (dimi >= 3) ? (aoffset_t)1 : ishpi[SPATIAL_D],
                        (aoffset_t)c};
      else
        // output feature-map in ixpix_t [D][H][W][C] format
        shapes.oshape = {(aoffset_t)(fmodbli ? 2 * c : c),
                        1,
                         aoffset_t(TNSVSIZE),
                        (dimi >= 2) ? (aoffset_t)1 : ishpi[SPATIAL_H],
                        (dimi >= 3) ? (aoffset_t)1 : ishpi[SPATIAL_D]};
      // parameter dimension ixpix_t [C]
      shapes.pshape = {noi};
      // set padding windo
      HLAPI.i.u.op.padpos[SPATIAL_W] = 0;
      HLAPI.i.u.op.padpos[SPATIAL_H] = 0;
      HLAPI.i.u.op.padlim[SPATIAL_W] = padlimi[0];
      HLAPI.i.u.op.padlim[SPATIAL_H] = padlimi[1];
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_W] = 0;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_W] = TNSVSIZE;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_W] = -(TNSVSIZE * (w - 1));
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_W] = -(TNSVSIZE * (w - 1));
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_W] = -(TNSVSIZE * (w - 1));
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_W] = 0;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_H] = 0;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_H] = 0;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_H] = 1;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_H] = 1 - shapes.ishape[3];
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_H] = 1 - shapes.ishape[3];
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_H] = 0;
      init_reduce_i(opi, useAcc);
      set_reduce_params();
}

// reduce operation for accumulator (32b) input
// secondary input is accumulator (32b) if useAcc = true; 0 if useAcc = false
// output to VM (8b/16b) if keepAcc = false; to AM (32b) if keepAcc = true
template <template <typename> class B>
gtoa_reduce_params<B>::gtoa_reduce_params(
    aoffset_t noi,            // number output channels (not vectors)
    const shape<3>& ishpi,    // input shape, output inner is 1
    const shape<2>& padlimi,  // padding shape
    bool fmodbli,             // 8b/16b output feature-map
    bool sati,                // do saturation
    act_red_op_t opi,         // reduction operation to perform
    bool useAcc,              // use accumulator input
    bool keepAcc,             // keep result in accumulator
    const int dimi) :         // spatial dimensions to reduce
    gtoa_params<B>() {
      // enable accumulator input and accumulator output
      HLAPI.i.bf = 0;   // function, not LUT init
      HLAPI.i.u.op.io_en = ACT_IO_EN_AC0 | ACT_IO_EN_AC1 |
        (keepAcc ? ACT_IO_EN_OAC : ACT_IO_EN_OFM);
      HLAPI.i.u.op.bf = (!keepAcc && fmodbli ? 1 << ACT_BF_OP_OUTDBL_START : 0) |
                        (!keepAcc && sati ? 1 << ACT_BF_OP_OUTSAT_START : 0);
      HLAPI.i.u.op.bf |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_IN1INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
      cmax = noi;
      red_dim = dimi;
      red_accum = true;
      assert((dimi >= 1 && dimi <= 3) && "dimi out of supported range");
      int c = (noi + ISIZE - 1) / ISIZE;
      int w = (ishpi[SPATIAL_W] + TNSVSIZE - 1) / TNSVSIZE;
      // input accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN/lsb/msb] format
      shapes.ishape = {1,
                      ishpi[SPATIAL_H],
                      (aoffset_t)w,
                      ishpi[SPATIAL_D],
                      (aoffset_t)c};
      // input1 accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN] format
      shapes.i1shape = {1,
                       (dimi >= 2) ? (aoffset_t)1 : ishpi[SPATIAL_H],
                       1,
                       (dimi >= 3) ? (aoffset_t)1 : ishpi[SPATIAL_D],
                       (aoffset_t)c};
      if (keepAcc)
        // output accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN] format
        shapes.oshape = {1,
                        (dimi >= 2) ? (aoffset_t)1 : ishpi[SPATIAL_H],
                        1,
                        (dimi >= 3) ? (aoffset_t)1 : ishpi[SPATIAL_D],
                        (aoffset_t)c};
      else
        // output feature-map in ixpix_t [D][H][W][C] format
        shapes.oshape = {(aoffset_t)(fmodbli ? 2 * c : c),
                        1,
                         (aoffset_t)TNSVSIZE,
                        (dimi >= 2) ? (aoffset_t)1 : ishpi[SPATIAL_H],
                        (dimi >= 3) ? (aoffset_t)1 : ishpi[SPATIAL_D]};
      // parameter dimension ixpix_t [C]
      shapes.pshape = {noi};
      // set padding windo
      HLAPI.i.u.op.padpos[SPATIAL_W] = 0;
      HLAPI.i.u.op.padpos[SPATIAL_H] = 0;
      HLAPI.i.u.op.padlim[SPATIAL_W] = padlimi[0];
      HLAPI.i.u.op.padlim[SPATIAL_H] = padlimi[1];
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_W] = 0;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_W] = TNSVSIZE;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_W] = -(TNSVSIZE * (w - 1));
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_W] = -(TNSVSIZE * (w - 1));
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_W] = -(TNSVSIZE * (w - 1));
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_W] = 0;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_H] = 0;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_H] = 0;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_H] = 1;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_H] = 1 - shapes.ishape[3];
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_H] = 1 - shapes.ishape[3];
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_H] = 0;
      init_reduce_i(opi, useAcc);
      set_reduce_params();
}

// reduce operation for feature-map (8b/16b) input
// secondary input is feature-map (8b/16b) if useAcc = true; 0 if useAcc = false
// output to VM (8b/16b) if keepAcc = false; to AM (32b) if keepAcc = true
template <template <typename> class B>
gtoa_reduce_params<B>::gtoa_reduce_params(
    aoffset_t noi,            // number output channels (not vectors)
    const shape<3>& ishpi,    // input shape, output inner is 1
    const shape<2>& padlimi,  // padding shape
    bool fmidbli,             // 8b/16b input feature-map
    bool fmodbli,             // 8b/16b output feature-map
    bool sati,                // do saturation
    act_red_op_t opi,         // reduction operation to perform
    bool fmi1dbli,            // 8b/16b secondary feature-map
    bool useAcc,              // use accumulator input
    bool keepAcc,             // keep result in accumulator
    const int dimi) :         // spatial dimensions to reduce
    gtoa_params<B>() {
      // enable accumulator input and accumulator output
      HLAPI.i.bf = 0;   // function, not LUT init
      HLAPI.i.u.op.io_en = ACT_IO_EN_FM0 | ACT_IO_EN_FM1 |
        (keepAcc ? ACT_IO_EN_OAC : ACT_IO_EN_OFM);
      HLAPI.i.u.op.bf = (fmidbli  ? 1 << ACT_BF_OP_IN0DBL_START : 0) |
                        (fmi1dbli ? 1 << ACT_BF_OP_IN1DBL_START : 0) |
                        (!keepAcc && fmodbli ? 1 << ACT_BF_OP_OUTDBL_START : 0) |
                        (!keepAcc && sati ? 1 << ACT_BF_OP_OUTSAT_START : 0);
      cmax = noi;
      red_dim = dimi;
      red_accum = true;
      assert((dimi >= 1 && dimi <= 3) && "dimi out of supported range");
      int c = (noi + ISIZE - 1) / ISIZE;
      int w = (ishpi[SPATIAL_W] + TNSVSIZE - 1) / TNSVSIZE;
      // input feature-map in ixpix_t [D][H][W][C] format
      shapes.ishape = {(aoffset_t)(fmidbli ? 2 * c : c),
                      1,
                      (aoffset_t)(w * TNSVSIZE),
                      ishpi[SPATIAL_H],
                      ishpi[SPATIAL_D]};
      // input1 feature-map in ixpix_t [D][H][W][C] format
      shapes.i1shape = {(aoffset_t)(fmi1dbli ? 2 * c : c),
                      1,
                      (aoffset_t)TNSVSIZE,
                      (dimi >= 2) ? (aoffset_t)1 : ishpi[SPATIAL_H],
                      (dimi >= 3) ? (aoffset_t)1 : ishpi[SPATIAL_D]};
      if (keepAcc)
        // output accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN] format
        shapes.oshape = {1,
                        (dimi >= 2) ? (aoffset_t)1 : ishpi[SPATIAL_H],
                        1,
                        (dimi >= 3) ? (aoffset_t)1 : ishpi[SPATIAL_D],
                        (aoffset_t)c};
      else
        // output feature-map in ixpix_t [D][H][W][C] format
        shapes.oshape = {(aoffset_t)(fmodbli ? 2 * c : c),
                        1,
                        (aoffset_t)TNSVSIZE,
                        (dimi >= 2) ? (aoffset_t)1 : ishpi[SPATIAL_H],
                        (dimi >= 3) ? (aoffset_t)1 : ishpi[SPATIAL_D]};
      // parameter dimension ixpix_t [C]
      shapes.pshape = {noi};
      // set padding windo
      HLAPI.i.u.op.padpos[SPATIAL_W] = 0;
      HLAPI.i.u.op.padpos[SPATIAL_H] = 0;
      HLAPI.i.u.op.padlim[SPATIAL_W] = padlimi[0];
      HLAPI.i.u.op.padlim[SPATIAL_H] = padlimi[1];
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_W] = 0;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_W] = TNSVSIZE;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_W] = -(TNSVSIZE * (w - 1));
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_W] = -(TNSVSIZE * (w - 1));
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_W] = -(TNSVSIZE * (w - 1));
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_W] = 0;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_H] = 0;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_H] = 0;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_H] = 1;
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_H] = 1 - shapes.ishape[3];
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_H] = 1 - shapes.ishape[3];
      HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_H] = 0;
      init_reduce_i(opi, useAcc);
      set_reduce_params();
}

#undef HLAPI
#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_LEGACY_TENSOR_GTOA_REDUCE_INLINE_LEGACY_HPP_
