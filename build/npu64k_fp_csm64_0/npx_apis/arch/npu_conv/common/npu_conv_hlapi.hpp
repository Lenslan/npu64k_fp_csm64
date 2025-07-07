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
 * npu_conv_hlapi.h
 *
 * File defining the convolution HLAPI structure
 *
 */
#ifndef NPU_CONV_HLAPI_INCLUDED
#define NPU_CONV_HLAPI_INCLUDED


#include "npu_hlapi.hpp"
#include "npu_conv_types.hpp"


#define CONV_MAJOR 0x02
#define CONV_MINOR 0x00


namespace npu_conv {
//
// import global NPU types
//
using namespace npu;


/////////////////////////////////////////////////////////////////////////////////////////////////////
//
// Convolution HLAPI top-level
//
/////////////////////////////////////////////////////////////////////////////////////////////////////
// main iterator indices
const uint32_t CONV_ITER_ONN = CONV_HLAPI_LOOPS-1;
const uint32_t CONV_ITER_INN = CONV_HLAPI_LOOPS-2;
const uint32_t CONV_ITER_ROW = CONV_HLAPI_LOOPS-3;
const uint32_t CONV_ITER_COL = CONV_HLAPI_LOOPS-4;
const uint32_t CONV_ITER_QD  = CONV_HLAPI_LOOPS-5;
const uint32_t CONV_ITER_NI  = CONV_HLAPI_LOOPS-6;
const uint32_t CONV_ITER_NO  = CONV_HLAPI_LOOPS-7;
const uint32_t CONV_ITER_GRP = CONV_HLAPI_LOOPS-8;
// Feature-map padding offsets
const uint32_t CONV_FM_PDOFF_COL  = 1;
const uint32_t CONV_FM_PDOFF_ROW  = 2;
// Feature-map pointer offsets
const uint32_t CONV_FM_DOFF_CHAN = 0;
const uint32_t CONV_FM_DOFF_COL  = 1;
const uint32_t CONV_FM_DOFF_ROW  = 2;  
// bitfields
const uint32_t CONV_BF_CONV_MODE_START = 0;
const uint32_t CONV_BF_CF_MODE_START   = 8;
const uint32_t CONV_BF_FM_CFG_START    = 12;
const uint32_t CONV_BF_CF_CFG_START    = 16;
const uint32_t CONV_BF_USE_ACC_START   = 20;
const uint32_t CONV_BF_KEEP_ACC_START  = 21;
const uint32_t CONV_BF_PACK_MODE_START = 24;
const uint32_t CONV_BF_CONV_MODE_MASK  = 0x0000000f;
const uint32_t CONV_BF_CF_MODE_MASK    = 0x00000300;
const uint32_t CONV_BF_FM_CFG_MASK     = 0x00003000;
const uint32_t CONV_BF_CF_CFG_MASK     = 0x00070000;
const uint32_t CONV_BF_USE_ACC_MASK    = 0x00100000;
const uint32_t CONV_BF_KEEP_ACC_MASK   = 0x00200000;
const uint32_t CONV_BF_PACK_MODE_MASK  = 0x03000000;

// CF iteration
const uint32_t CONV_CF_ITER_IN  = 3;
const uint32_t CONV_CF_ITER_NI  = 2;
const uint32_t CONV_CF_ITER_NO  = 1;
const uint32_t CONV_CF_ITER_GRP = 0;


struct conv_hlapi_i_t {
  hlapi_i_t                        common;          // common HLAPI parameters
  // multiplier array controls
  shape<CONV_HLAPI_LOOPS>          iter;            // loop iteration counts [grp][no][ni][qd][col][row][inn][onn], indexed by CONV_ITER*
  localptr_t<ixpix_t>              fm_ptr;          // feature-map pointer
  buf_t<ixpix_t>                   fm_buf;          // cyclic buffer descriptor
  shape<3>                         fm_padlim;       // position of last pixel not padded, indexed by CONV_PAD*
  shape<3>                         fm_padpos;       // starting position of convolution, indexed by CONV_PAD*
  shape<3>                         fm_pdoffsets;    // padding offset per dimension, indexed by CONV_FM_POFF*
  shape<3>                         fm_doffsets;     // pointer offset from one element to next per dimension, indexed by CONV_FM_OFF*
  localptr_t<ixpix_t>              pad_ptr;         // pointer to padding array
  shape<3>                         quad_iter;       // quadrant iterator per filter dimension
  array<quadrant_t,4>              quad_data;       // quadrant offsets from end of axis to first of next (0=next col, 1=next row, 2 = next depth, 3=next chan)
  uint16_t                         pd0;             // pad quadrant info to 32b aligned
  shape<4>                         cf_iter;         // coefficient iterator, 4*16b
  shape<4>                         cf_offsets;      // coefficient offset from end of one axis to start of next, 4*16b
  localptr_t<ixpix_t>              cf_ptr;          // start of coefficient array
  amptr_t                          acc_ptr;         // pointer to input&output accumulator array
  uint32_t                         bf;              // bitfields as below:
  /*
    struct {
    conv_mode_t                     conv_mode : 4;   // convolution mode
    pad                                       : 4    // pad to 8
    coef_mode_t                     cf_mode   : 2;   // coefficient compression mode
    pad                                       : 2    // pad to 12
    fm_cfg_t                        fm_cfg    : 2    // feature-map type
    pad                                       : 2    // pad to 16
    cf_cfg_t                        cf_cfg    : 3;   // coefficient type
    pad                                       : 1    // pad to 20
    bool                            use_acc   : 1;   // use input accumulator from memory
    bool                            keep_acc  : 1;   // keep output accumulator from memory else stream
    pad                                       : 2;   // pad to 23
    pack_mode_t                     pack_mode : 2;   // spatial packing padding mode
    pad                                       : 10   // pad to 32
    }
  */
};

#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(push, 1)
#endif
struct  packed_conv_hlapi_i_t {
  packed_hlapi_i_t                 common;          // 16B: common HLAPI parameters
  // multiplier array controls
  shape<CONV_HLAPI_LOOPS>          iter;            // 16B/16: loop iteration counts 
  // [grp][no][ni][qd][col][row][inn][onn], indexed by CONV_ITER*
  lptr_t                           fm_ptr;          //  2B/18: feature-map pointer
  lbuf_t                           fm_buf;          //  4B/22: cyclic buffer descriptor
  shape<3>                         fm_padlim;       //  6B/28: position of last pixel not padded, 
                                                    // indexed by CONV_PAD*
  shape<3>                         fm_padpos;       //  6B/34: starting position of convolution, 
                                                    // indexed by CONV_PAD*
  shape<3>                         fm_pdoffsets;    //  4B/38: padding offset per dimension, 
                                                    // indexed by CONV_FM_POFF*
  shape<3>                         fm_doffsets;     //  6B/44: pointer offset from one element 
  // to next per dimensio, indexed by CONV_FM_OFF*
  lptr_t                           pad_ptr;         //  2B/46: pointer to padding array
  shape<3>                         quad_iter;       //  6B/52: quadrant iterator per filter dimension
  array<quadrant_t,4>              quad_data;       // 32B/84: quadrant offsets from end of 
  // axis to first of next (0=next col, 1=next row, 2 = next depth, 3=next chan)
  uint16_t                         pd0;             //  2B/86: pad quadrant info to 32b aligned
  shape<4>                         cf_iter;         //  8B/94: coefficient iterator, 4*16b
  shape<4>                         cf_offsets;      //  8B/102: coefficient offset from end of 
                                                    // one axis to start of next, 4*16b
  lptr_t                           cf_ptr;          //  2B/104: start of coefficient array
  lptr_t                           acc_ptr;         //  2B/106: pointer to input&output accumulator 
                                                    // array
  uint32_t                         bf;              //  4B/110: bitfields as below:
  /*
    struct {
    conv_mode_t                     conv_mode : 4;   // convolution mode
    pad                                       : 4    // pad to 8
    coef_mode_t                     cf_mode   : 2;   // coefficient compression mode
    pad                                       : 2    // pad to 12
    fm_cfg_t                        fm_cfg    : 2    // feature-map type
    pad                                       : 2    // pad to 16
    cf_cfg_t                        cf_cfg    : 3;   // coefficient type
    pad                                       : 1    // pad to 20
    bool                            use_acc   : 1;   // use input accumulator from memory
    bool                            keep_acc  : 1;   // keep output accumulator from memory else stream
    pad                                       : 2;   // pad to 24
    pack_mode_t                     pack      : 2;   // spatial packing mode
    pad                                       : 6;   // pad to 32
    }
  */
} __PALIGNED(__AN);
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(pop)
#endif

// convolution HLAPI
struct conv_hlapi_t {
  conv_hlapi_i_t                          i;  // inputs at the lowest address
  hlapi_io_t                              io; // input&outputs in between input only and output only
  hlapi_o_t                               o;  // outputs only at highest address
};
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(push, 1)
#endif
struct packed_conv_hlapi_t {
  packed_conv_hlapi_i_t                   i;   // inputs at the lowest address
  packed_hlapi_io_t                       io;  // input&outputs in between input only and output only
  packed_hlapi_o_t                        o;   // outputs only at highest address
  uint64_t                                pd_end; // padding to avoid descriptor axi 
                                                  // load over the boundary
} __PALIGNED(__AN);
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(pop)
#endif

// ensure all conv HLAPIs have same size on all platforms
static_assert(sizeof(conv_hlapi_t) == 144, "unexpected convolution HLAPI size");

//
// Convolution coefficient encoding functions
//

// encode 16b coefficients without zero-point
void coef_enc(
              const tensor_t<coef_t,7,xbuffer_t>& icf,        // input coefficients 
              // [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp][Coef h/l]
              xbuffer_t<coef_t>&                  tbuf,       // temporary xbuf
              // attributes
              conv_mode_t                         conv_mode,  // convolution mode
              bool                                fm_dbl,     // 16b feature-map
              // outputs, buffers preallocated by caller
              xbuffer_t<ixpix_t>&                 obuf,       // output encoded coefficient tensor
              size_t&                             olen);      // size of used coefficient buffer in bytes
// encode 8b coefficients without zero-point
void coef_enc(
              const tensor_t<coef_t,6,xbuffer_t>& icf,       // input coefficients 
              // [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp], 8b only
              xbuffer_t<coef_t>&                  tbuf,      // temporary xbuf
              // attributes
              conv_mode_t                         conv_mode, // convolution mode
              coef_mode_t                         coef_mode, // coefficient compression mode 
              // uncompressed or compressed or sparse
              bool                                fm_dbl,    // 16b feature-map
              bool                                cf_4b,     // 4b coefficient encoding
              int                                 inn,       // inner input loop
              int                                 onn,       // inner output loop
              // outputs, buffers preallocated by caller
              xbuffer_t<ixpix_t>&                 obuf,      // output encoded coefficient tensor
              size_t&                             olen);     // size of used coefficient buffer in bytes
// encode 8b coefficients with zero-point
void coef_enc(
              const tensor_t<coef_t,6,xbuffer_t>& icf,       // input coefficients 
              // [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp], 8b only
              const tensor_t<coef_t,1,xbuffer_t>& izp,       // input zero-points [Cout]
              xbuffer_t<coef_t>&                  tbuf,      // temporary xbuf
              // attributes
              conv_mode_t                         conv_mode, // convolution mode
              coef_mode_t                         coef_mode, // coefficient compression mode uncompressed or 
              // compressed or sparse
              bool                                fm_dbl,    // 16b feature-map
              bool                                cf_4b,     // 4b coefficient encoding
              int                                 inn,       // inner input loop
              int                                 onn,       // inner output loop
              // outputs, buffers preallocated by caller
              xbuffer_t<ixpix_t>&                 obuf,      // output encoded coefficient tensor
              size_t&                             olen);     // size of used coefficient buffer in bytes


//
// Fully-connected layer coefficient encoding functions
//
// encode 16b coefficients
void coef_enc(
              const tensor_t<coef_t,4,xbuffer_t>& icf,       // input coefficients [Grp][Cout][Cin][Coef h/l]
              xbuffer_t<coef_t>&                  tbuf,
              // attributes
              int                                 vs,        // VSIZE
              bool                                fm_dbl,    // 16b feature-map
              // outputs, buffers preallocated by caller
              xbuffer_t<ixpix_t>&                 obuf,      // output encoded coefficient tensor
              size_t&                             olen);     // size of used coefficient buffer in bytes
// encode 8b coefficients without zero-point
void coef_enc(
              const tensor_t<coef_t,3,xbuffer_t>& icf,       // input coefficients [Grp][Cout][Cin], 8b only
              xbuffer_t<coef_t>&                  tbuf,
              // attributes
              int                                 vs,        // VSIZE
              coef_mode_t                         coef_mode, // coefficient compression mode uncompressed or 
              // compressed, not sparse
              bool                                fm_dbl,    // 16b feature-map
              bool                                cf_4b,     // 4b coefficient encoding
              // outputs, buffers preallocated by caller
              xbuffer_t<ixpix_t>&                 obuf,      // output encoded coefficient tensor
              size_t&                             olen);     // size of used coefficient buffer in bytes
// encode 8b coefficients with zero-point
void coef_enc(
              const tensor_t<coef_t,3,xbuffer_t>& icf,       // input coefficients [Grp][Cout][Cin], 8b only
              const tensor_t<coef_t,1,xbuffer_t>& izp,       // input zero-points [Cout]
              xbuffer_t<coef_t>&                  tbuf,
              // attributes
              int                                 vs,        // VSIZE
              coef_mode_t                         coef_mode, // coefficient compression mode uncompressed 
              // or compressed or sparse
              bool                                fm_dbl,    // 16b feature-map
              bool                                cf_4b,     // 4b coefficient encoding
              // outputs, buffers preallocated by caller
              xbuffer_t<ixpix_t>&                 obuf,      // output encoded coefficient tensor
              size_t&                             olen);     // size of used coefficient buffer in bytes
}
#endif
