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
 * npu_act_hlapi.h
 *
 * File defining the activation HLAPI structure
 *
 */
#ifndef NPU_ACT_COMMON_NPU_ACT_HLAPI_HPP_
#define NPU_ACT_COMMON_NPU_ACT_HLAPI_HPP_

#include "npu_hlapi.hpp"        // [NOLINT] [build/include_subdir]
#include "npu_act_isa.hpp"      // [NOLINT] [build/include_subdir]


#define ACT_MAJOR 0x02
#define ACT_MINOR 0x00


// mask for IO interface enables
#define ACT_IO_EN_FM0   0x001
#define ACT_IO_EN_AC0   0x002
#define ACT_IO_EN_ASTR0 0x004
#define ACT_IO_EN_FM1   0x008
#define ACT_IO_EN_AC1   0x010
#define ACT_IO_EN_FSTR1 0x020
#define ACT_IO_EN_OAC   0x040
#define ACT_IO_EN_OFM   0x080
#define ACT_IO_EN_GTH   0x100

#define ACT_BF_OP_FMODE_INT  0x00
#define ACT_BF_OP_FMODE_FP32 0x01
#define ACT_BF_OP_FMODE_FP16 0x02
#define ACT_BF_OP_FMODE_BF16 0x03
#define ACT_BF_OP_FMODE_FP8  0x04  // future


namespace npu_act {
//
// import global NPU types
//
using namespace npu;  // [NOLINT]
using namespace npu_act::uc::v200;


///////////////////////////////////////////////////////////////////////////////////////////////////
//
// pooling
//
///////////////////////////////////////////////////////////////////////////////////////////////////
enum act_pool_size_t { p2s1, p2s2, p3s1, p3s2 };
enum act_pool_mode_t { pnone, prow, pcol, prowcol };
// bitfield start and mask
#define ACT_BF_PL_MODE_START  0
#define ACT_BF_PL_SIZE_START  2
#define ACT_BF_PL_MODE_MASK   0x0003
#define ACT_BF_PL_SIZE_MASK   0x000c
#define ACT_POOL_LOOPS 4
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(push, 1)
#endif
struct act_pool_t {
  array<aoffset_t, ACT_POOL_LOOPS> iter;      // pooling loop iterators: onn, row, col, chan
  localptr_t<ixpix_t>             st_base;   // pointer to base of overlap stash
  uint16_t                        bf;        // concatenate bitfields, as below
  /*
    struct {
    act_pool_mode_t              mode      : 2;   // pooling mode
    act_pool_size_t              size      : 2;   // pooling size
    uint32_t                     pad       :12;   // pad to 16b
    } bf;
  */
} __PALIGNED(__AN);
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(pop)
#endif

#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(push, 1)
#endif
struct act_fm_t {
  hlapi_vm_agu_t<ACT_FM_LOOPS>     fm_agu;          // secondary feature-map AGU parameters
  act_pool_t                       pool;            // pooling attributes
  int8_t                           enable;          // write enable mask
  array<int8_t, 3>                 pad;
} __PALIGNED(__AN);
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(pop)
#endif

// scalar activation program type
typedef int32_t act_scalar_t;

///////////////////////////////////////////////////////////////////////////////////////////
//
// Activation HLAPI top-level
//
//////////////////////////////////////////////////////////////////////////////////////////

// bitfield start and mask
#define ACT_BF_TYP_START         0
#define ACT_BF_TYP_MASK          0x1
#define ACT_BF_OP_IN0DBL_START   0
#define ACT_BF_OP_IN0PEN_START   1
#define ACT_BF_OP_IN0PMIN_START  2
#define ACT_BF_OP_IN0FMODE_START 4
#define ACT_BF_OP_IN1DBL_START   8
#define ACT_BF_OP_IN1FMODE_START 9
#define ACT_BF_OP_OUTDBL_START   16
#define ACT_BF_OP_OUTSAT_START   17
#define ACT_BF_OP_OUTFMODE_START 18
#define ACT_BF_OP_ALAY_START     24
#define ACT_BF_OP_IN0DBL_MASK    0x00000001
#define ACT_BF_OP_IN0PEN_MASK    0x00000002
#define ACT_BF_OP_IN0PZERO_MASK  0x00000000
#define ACT_BF_OP_IN0PMONE_MASK  0x00000004
#define ACT_BF_OP_IN0PMIN_MASK   0x00000008
#define ACT_BF_OP_IN0PMAX_MASK   0x0000000c
#define ACT_BF_OP_IN0FMODE_MASK  0x00000070
#define ACT_BF_OP_IN0INT32_MASK  0x00000000
#define ACT_BF_OP_IN0FP32_MASK   0x00000010
#define ACT_BF_OP_IN0FP16_MASK   0x00000020
#define ACT_BF_OP_IN0BF16_MASK   0x00000030
#define ACT_BF_OP_IN0FP8_MASK    0X00000040
#define ACT_BF_OP_IN1DBL_MASK    0x00000100
#define ACT_BF_OP_IN1FMODE_MASK  0x00000e00
#define ACT_BF_OP_IN1INT32_MASK  0x00000000
#define ACT_BF_OP_IN1FP32_MASK   0x00000200
#define ACT_BF_OP_IN1FP16_MASK   0x00000400
#define ACT_BF_OP_IN1BF16_MASK   0x00000600
#define ACT_BF_OP_IN1FP8_MASK    0X00000800
#define ACT_BF_OP_OUTDBL_MASK    0x00010000
#define ACT_BF_OP_OUTSAT_MASK    0x00020000
#define ACT_BF_OP_OUTFMODE_MASK  0x001c0000
#define ACT_BF_OP_OUTINT32_MASK  0x00000000
#define ACT_BF_OP_OUTFP32_MASK   0x00040000
#define ACT_BF_OP_OUTFP16_MASK   0x00080000
#define ACT_BF_OP_OUTBF16_MASK   0x000c0000
#define ACT_BF_OP_OUTFP8_MASK    0x00100000
#define ACT_BF_OP_ALAY_MASK      0x03000000
#define ACT_BF_OP_PADINC_MASK    0x06000000
#define ACT_BF_OP_PADI16_MASK    0x00000000
#define ACT_BF_OP_PADV2I8_MASK   0x02000000
#define ACT_BF_OP_PADV4I4_MASK   0x04000000
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(push, 1)
#endif
struct act_hlapi_i_t {
 public:
  hlapi_i_t                                  common;          // Common input parameters
  uint32_t                                   bf;              // bitfields as below:
  /*
    struct {
    uint8_t                                  typ      : 1;    // type of operation
    uint32_t                                 pad      : 31;   // pad to 32b
    }                                        bf;
  */
  union {
    struct {
      // scalar input/output parameters
      array<act_scalar_t, ACT_SREG_SAVE>     scl;             // input/output values
      array<aoffset_t, ACT_HLAPI_LOOPS>      iter;            // activation loop iterators
      // per channel activation parameters
      aoffset_t                              bnum;            // number of per channel
                                              //  parameters to read in ixpix_t units
      localptr_t<ixpix_t>                    bptr;            // pointer to per channel
                                              // parameters
      // actual activation function program
      array<uint8_t, 5 * ACT_PROG_LEN>       act_prog;        // array of instructions
                                                // encoded as groups of 5 bytes
      array<uint8_t, 6>                      ppad;
      uint16_t                               cmaskn;          // channel mask inverted
      union {
        // primary accumulator input
        hlapi_am_agu_t<ACT_AM_LOOPS>         acc_agu;         // accumulator AGU parameters
        // primary feature-map input
        hlapi_vm_agu_t<ACT_FM_LOOPS>         fm_agu;          // feature-map AGU parameters
      }                                      primary;
      // secondary input feature-map or accumulator
      union {
        hlapi_am_agu_t<ACT_AM_LOOPS>         acc_agu;         // secondary accumulator
                                                        // AGU parameters
        hlapi_vm_agu_t<ACT_FM_LOOPS>         fm_agu;          // secondary feature-map
                                                        // AGU parameters
      }                                      secondary;
      // output feature-map or accumulator
      union {
        hlapi_am_agu_t<ACT_AM_LOOPS>         acc_agu;         // secondary accumulator
                                                         // AGU parameters
        act_fm_t                             fm;
      }                                      out;
      // padding parameters for pooling and reductions
      shape<2>                               padpos;          // padding start position
      shape<2>                               padlim;          // 2D maxpooling window
                                                              // boundaries
      array<array<aoffset_t, 2>, ACT_FM_LOOPS> pad_offs;       // input padding offsets
      aoffset_t                              pad_stride;      // input padding column stride
      // active input and output units
      tmask_t                                io_en;           // mask for input and
                                                          // output enables
      // common primary and secondary input feature-map properties
      uint32_t                               bf;              // bitfields as below:
      /*
        struct {
        uint8_t                            in_dbl0    : 1;    // double width inputs (for int mode 8b/16b, 32b/48b)
        uint8_t                            in_pen0    : 1;    // input pad enable
        uint8_t                            in_pmode   : 2;    // input pad mode:  to 0, -1, MININT or MAXINT
        uint8_t                            in_fmode0  : 3;    // float mode cfg (0-int, 1-fp32, 2-fp16, 3-bf16, 4-fp8/future)
        uint8_t                            pad        : 1;    // pad to 8b
     //------------------------------------------------------------------------------------------
        uint8_t                            in_dbl1    : 1;    // double width inputs (for int mode 8b/16b, 32b/48b)
        uint8_t                            in_fmode1  : 3;    // float mode cfg (0-int, 1-fp32, 2-fp16, 3-bf16, 4-fp8/future)
        uint8_t                            pad        : 4;    // pad to 8b
     //------------------------------------------------------------------------------------------
        uint8_t                            out_satdbl : 2;    // saturate [1] and double width output [0]
        uint8_t                            out_fmode  : 3;    // float mode cfg
        uint8_t                            pad        : 3;    // pad to 8b
      //--------------------------------------------------------------------------------------
        act_alay_t                         acc_lay    : 1;    // accumulator layout
        pad_inc_t                          pad_inc    : 2;    // padding increment mode
        uint32_t                           pad        : 5;    // pad to 32b
        }                                    bf;
      */
    }                                        op;
    act_lut_t                                lut;             // look-up table parameters
  }                                          u;
} __PALIGNED(__AN);
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(pop)
#endif

// activation HLAPI
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(push, 1)
#endif
struct act_hlapi_t {
  act_hlapi_i_t                 i;   // inputs at the lowest address
  hlapi_io_t                    io;  //  input&outputs in between input only and output only
  hlapi_o_t                     o;   // outputs only at highest address
} __PALIGNED(__AN);
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(pop)
#endif

// ensure all GTA HLAPIs have same size on all platforms
static_assert(sizeof(act_hlapi_t) == 312, "unexpected GTA HLAPI size");

}  // namespace npu_act
#endif  // NPU_ACT_COMMON_NPU_ACT_HLAPI_HPP_
