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
 * File defining the idma and odma HLAPI structure
 *
 */
#ifndef NPU_DMA_HLAPI_INCLUDED
#define NPU_DMA_HLAPI_INCLUDED


#include "npu_hlapi.hpp"


#define DMA_MAJOR 0x02
#define DMA_MINOR 0x00


namespace npu_dma {
//
// import global NPU types
//
using namespace npu;


//
// Field defines
//
#define NPU_IDMA_ATTR_MASK_CONST  1
#define NPU_IDMA_ATTR_MASK_GATHER 2


/////////////////////////////////////////////////////////////////////////////////////////////////////
//
// DMA HLAPI auxiliary types
//
/////////////////////////////////////////////////////////////////////////////////////////////////////

// DMA broadcasting flags, zero for non-broadcast
typedef uint32_t dma_bc_t;


/////////////////////////////////////////////////////////////////////////////////////////////////////
//
// DMA HLAPI top-level for iDMA and oDMA
//
/////////////////////////////////////////////////////////////////////////////////////////////////////

#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(push, 1)
#endif
struct dma_hlapi_i_t {
  public:
  hlapi_i_t                        common;          // Common input parameters
  // VM AGU sequence
  hlapi_vm_agu_t<NUM_FM_LOOPS>     vm_seq;          // VM access parameters
  // XM AGU sequence
  hlapi_xm_agu_t                   xm_seq;          // XM access parameters
  uint8_t                          attrb;           // bit[0]: cnst; bit[1]: gather; if bit 0 
                            // is true then write a constant value, do not read; used only in iDMA
  uint8_t                          padc;            // Reserved 
  // Other parameters
  int8_t                           zero_point;      // zero point for channel padding for XM to VM copy
  uint8_t                          pad8;
  dma_bc_t                         bc;              // broadcast flags for read data and 
                                        // write response broadcast
  aoffset_t                        planar_stride;   // VM pix_t channel stride for planar mode, 
  //log2 encoded; value 0 means no planar mode
  aoffset_t                        planar_offset;   // pix_t channel offset in planar mode
  uint16_t                         vm_wmsk;         // VM byte write mask: 0-> write into VM; 1-> skip write
  uint16_t                         pad16;
} __PALIGNED(__AN);
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(pop)
#endif

#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(push, 1)
#endif
struct dma_hlapi_t {
  dma_hlapi_i_t                    i;               // inputs at the lowest address
  hlapi_io_t                       io;              // input&outputs in between input only and output
  hlapi_o_t                        o;               // outputs only at highest address
} __PALIGNED(__AN);
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(pop)
#endif

// ensure all iDMA/oDMA HLAPIs have same size on all platforms
static_assert(sizeof(dma_hlapi_t) == 184, "unexpected iDMA/oDMA HLAPI size");

}

#endif
