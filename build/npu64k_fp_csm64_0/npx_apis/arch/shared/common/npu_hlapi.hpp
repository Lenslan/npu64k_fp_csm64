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
 * npu_hlapi.h
 *
 * File defining the common HLAPI structure
 *
 */
#ifndef NPU_HLAPI_INCLUDED
#define NPU_HLAPI_INCLUDED


#include "npu_types.hpp"


//
// Tensor API status selection
//
// accumulated cycles spent in the HLAPI
#define HLAPI_STATUS_SEL_IO_CYCLES 0
// accumulated number of invocations of the HLAPI
#define HLAPI_STATUS_SEL_IO_COUNT  1
// HLAPI return status (OK, ERROR??)
#define HLAPI_STATUS_SEL_O_STATUS  2
// HLAPI result = scalar[0] from GTOA
#define HLAPI_STATUS_SEL_O_RES     3

namespace npu {

  /////////////////////////////////////////////////////////////////////////////////////////////////////
  //
  // Datatypes used in HLAPI
  //
  /////////////////////////////////////////////////////////////////////////////////////////////////////


  //
  // VM load/store datatype
  //
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(push, 1)
#endif
  template<int L> struct hlapi_vm_agu_t {
    localptr_t<ixpix_t>            ptr;             // pointer into buffer
    buf_t<ixpix_t>                 buf;             // buffer
    aoffset_t                      stride;          // vector stride
    array<aoffset_t,L>             offsets;         // AGU offsets
    array<aoffset_t,L>             iter;            // AGU iterations
  } __PALIGNED(__AN);
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(pop)
#endif


  //
  // AM load/store datatype
  //
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(push, 1)
#endif
  template<int N> struct hlapi_am_agu_t {
    lptr_t                         ptr;             // pointer to array of accumulator vectors, as 16b integer
    array<aoffset_t,N>             offsets;         // address offsets
    array<aoffset_t,N>             iter;            // iteration counts
  } __PALIGNED(__AN);
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(pop)
#endif


  //
  // XM load/store datatype for DMA
  //
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(push, 1)
#endif
  struct hlapi_xm_agu_t {
    uint16_t                       compress;        // layout as below
    // struct {
    //  bool  compressed  : 1;                      if true then compressed mode, only bit 0 used
    //  bool  boost_read  : 1;                      if true then read in boost mode
    //  bool  boost_write : 1;                      if true then write in boost mode
    //  int2  rd_ost      : 2;                      Configure AXI read outstanding limit: 2'b00->32;2'b01->16;2'b10->8;2'b11->4
    //  int2  wr_ost      : 2;                      Configure AXI write outstanding limit: 2'b00->32;2'b01->16;2'b10->8;2'b11->4
    //  int9  pad         : 9;                      pad to 16b
    //  
    // }
    aoffset_t                      cblen;           // compressed block length in ixpix_t units
    globalptr_t<pix_t>             ptr;             // pointer into XM data buffer
    union {    
      globalptr_t<char>            mptr;            // pointer into XM metadata buffer
      struct {
        localptr_t<ixpix_t>        gptr;            // pointer into VM gather index buffer
        int16_t                    pad0;            // pad to size of mptr
        int32_t                    pad1;
      } __PALIGNED(__AN)           g;
    } __PALIGNED(__AN) p;
    xm_buf_t<pix_t>                buf;             // cyclic data buffer
    union {
      xm_buf_t<char>               mbuf;            // cyclic metadata buffer
      struct {
        buf_t<ixpix_t>             gbuf;            // gather index buffer        
        int64_t                    pad2;
      } __PALIGNED(__AN)           g;
    } __PALIGNED(__AN) b;
    array<poffset_t,NUM_FM_LOOPS>  offsets;         // Data AGU offsets
    union {
      array<poffset_t,NUM_FM_LOOPS> moffsets;       // Metadata AGU offsets
      struct {
        array<aoffset_t,2*NUM_FM_LOOPS-3> pad3;     // Pad to size of moffsets
        array<aoffset_t,3>         goffsets;        // Gather index AGU offsets
      } g;
    } o;
    array<aoffset_t,NUM_FM_LOOPS>  iter;            // AGU iterations
  } __PALIGNED(__AN);
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(pop)
#endif

  //
  // XM load/store datatype for STU
  //
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(push, 1)
#endif
  struct hlapi_stu_agu_t {
    uint32_t                       boost;           //Boost mode
    // struct {
    //   bool  boost : 1
    //   int2  rd/wr_ost      : 2;                  // Configure AXI read outstanding limit: 2'b00->32;2'b01->16;2'b10->8;2'b11->4
    //   intb: padb  : 29
    // }
    globalptr_t<pix_t>             ptr;             // pointer into XM data buffer
    xm_buf_t<pix_t>                buf;             // cyclic data buffer
    array<poffset_t,NUM_FM_LOOPS>  offsets;         // Data AGU offsets
    array<aoffset_t,NUM_FM_LOOPS>  iter;            // AGU iterations
  } __PALIGNED(__AN);
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(pop)
#endif

  //
  // Real-time trace ID
  //
  typedef int32_t trace_id_t;


  /////////////////////////////////////////////////////////////////////////////////////////////////////
  //
  // HLAPI parameter structures
  //
  /////////////////////////////////////////////////////////////////////////////////////////////////////

  // HLAPI common input parameter
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(push, 1)
#endif
  struct hlapi_i_t {
  public:
    globalptr_t<hlapi_i_t>         next;            // pointer to next HLAPI                addr 0x00-0x07
    uint32_t                       ctrl;            // interrupt and event control as below struct
    /*
    struct {
      uint8_t                      devent;          // if true send event on completion     addr 0x08
      uint8_t                      ievent;          // if true send event on issue          addr 0x09
      uint8_t                      interrupt;       // if true send interrupt on completion addr 0x0a
      uint8_t                      pad;             //                                      addr 0x0b
    } ctrl;
    */
    trace_id_t                     id;              // unique descriptor ID for tracing     addr 0x0c-0x0f
  } __PALIGNED(__AN);
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(pop)
#endif

#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(push, 1)
#endif
  struct packed_hlapi_i_t {
    globalptr_t<hlapi_i_t>         next;            // pointer to next HLAPI                addr 0x00-0x07
    uint32_t                       ctrl;            // interrupt and event control as below struct
    /*
    struct {
      uint8_t                      devent;          // if true send event on completion     addr 0x08
      uint8_t                      ievent;          // if true send event on issue          addr 0x09
      uint8_t                      interrupt;       // if true send interrupt on completion addr 0x0a
      uint8_t                      pad;             //                                      addr 0x0b
    } ctrl;
    */
    trace_id_t                     id;              // unique descriptor ID for tracing     addr 0x0c-0x0f
  } __PALIGNED(__AN);
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(pop)
#endif

#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(push, 1)
#endif
  struct hlapi_io_t {
    // input&outputs
    uint32_t                       cycles;          // aggregated cycle-count               addr 0x10-0x13
    uint32_t                       count;           // aggregated completion count          addr 0x14-0x17
  } __PALIGNED(__AN);
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(pop)
#endif

  struct packed_hlapi_io_t {
    // input&outputs
    uint32_t                       cycles;          // aggregated cycle-count               addr 0x10-0x13
    uint32_t                       count;           // aggregated completion count          addr 0x14-0x17
  } __PACKED;

#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(push, 1)
#endif
  struct hlapi_o_t {
    // outputs
    uint32_t                       res;             // return result                        addr 0x18-0x1b
    uint32_t                       status;          // return status                        addr 0x1c-0x1f
  } __PALIGNED(__AN);
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(pop)
#endif

  struct packed_hlapi_o_t {
    // outputs
    uint32_t                       res;             // return result                        addr 0x18-0x1b
    uint32_t                       status;          // return status                        addr 0x1c-0x1f
  } __PACKED;

  struct dummy_hlapi_i_t {
    hlapi_i_t                      common;
    // add other input parameters here
  };
  struct dummy_hlapi_t {
    dummy_hlapi_i_t                i;               // inputs at the lowest address
    hlapi_io_t                     io;              // input&outputs in between input only and output only
    hlapi_o_t                      o;               // outputs only at highest address
  };
}
#endif
