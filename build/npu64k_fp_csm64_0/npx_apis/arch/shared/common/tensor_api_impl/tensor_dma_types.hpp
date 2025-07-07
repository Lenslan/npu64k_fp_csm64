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
 * tensor_dma_types.hpp
 *
 * DMA type definitions
 *
 */

#ifndef TENSOR_DMA_TYPES_INCLUDED
#define TENSOR_DMA_TYPES_INCLUDED

#include "npu_dma_hlapi.hpp"
#include "npu_stu_hlapi.hpp"

//
// All identifiers related to the tensor API go into namespace tensor::v200
//
namespace tensor::v200 {

  using namespace npu_dma;
  using namespace npu_stu;

  //
  // Implementation specific shapes
  //
  struct dma_params_impl_shapes {
    shape<5>                     idxshape;       // gather input index tensor shape               : ixpix_t    [1][Y][X][1][2]
    shape<5>                     dictshape;      // gather dictionary shape                       : pix_t      [H][W][C2][C1][C0]
    shape<5>                     oshape;         // gather output tensor shape                    : ixpix_t    [Y][X][C2][C1][C0]
  };

  // compression container
  template<int B> struct compressed_tensor_t {
    array<uint8_t, (B+7)/8> avail;   // 1 bit for each data in the block; false means data is zero; true means data is non-zero
    array<pix_t, B>         nonzero; // compressed non-zero data
    inline compressed_tensor_t() {
      assert(B > 0 && B < 256 && "compression container size exceeded");
    }
  };
  typedef uint8_t metadata_t;

  // DMA implementation specific parameters
  typedef enum : uint16_t {dma_impl_idma, dma_impl_odma, dma_impl_stu} dma_params_impl_hw_spec;
  struct dma_params_impl_spec {
    inline dma_params_impl_spec() {
      hw = dma_impl_idma;
      bf = (uint16_t)0;
    }
    inline dma_params_impl_spec(const dma_params_impl_spec&) = default;
    inline dma_params_impl_spec(const dma_params_impl_hw_spec& h) {
      hw = h;
      bf = (uint16_t)0;
    }
    inline dma_params_impl_spec(dma_params_impl_hw_spec h, bool rboost, bool wboost) {
      hw = h;
      bf = (uint16_t)(rboost ? 2 : 0) | (wboost ? 4 : 0);
    }
    inline dma_params_impl_spec(dma_params_impl_hw_spec h, bool rboost, bool wboost, uint16_t rd_ost, uint16_t wr_ost) {
      hw = h;
      bf = (uint16_t)((rboost ? 2 : 0) | (wboost ? 4 : 0) | (rd_ost << 3) | (wr_ost << 5));
    }
    //inline dma_params_impl_spec(dma_params_impl_hw_spec h, bool rboost, bool wboost, uint16_t rd_ost, uint16_t wr_ost) {
    //  hw = h;
    //  bf = (uint16_t)((rboost ? 2 : 0) | (wboost ? 4 : 0) | (rd_ost << 3) | (wr_ost << 5));
    //}
    inline bool operator==(const dma_params_impl_hw_spec& h) {
      return hw == h;
    }
    dma_params_impl_hw_spec hw; // select accelerator type
    uint16_t                bf; // bitfields, layout as below
    // struct {
    //   compressed mode  : 1;
    //   read_boost_mode  : 1;
    //   write_boost_mode : 1;
    //   int2  rd_ost     : 2;                      Configure AXI read outstanding limit: 2'b00->32;2'b01->16;2'b10->8;2'b11->4
    //   int2  wr_ost     : 2;                      Configure AXI write outstanding limit: 2'b00->32;2'b01->16;2'b10->8;2'b11->4
    //   pad              : 9;
    // }
  };

  // DMA source and destination types
  typedef enum : uint32_t {sd_type_con, sd_type_tns} dma_params_sd_type;

  // parameter object
  template <template<typename> class B> class dma_params;
  struct dma_params_impl_main {
    inline dma_params_impl_main() = default;
    inline dma_params_impl_main(dma_params_impl_main& a) {
      mem_write(&sel, mem_read(&a.sel));
      mem_write(&styp, mem_read(&a.styp));
      mem_write(&dtyp, mem_read(&a.dtyp));
      if (mem_read(&sel) == dma_impl_stu) {
        // STU HLAPI/MMIO
        mem_write(&hlapi.s, mem_read(&a.hlapi.s));
      } else {
        // iDMA/oDMA HLAPI/MMIO
        mem_write(&hlapi.d, mem_read(&a.hlapi.d));
      }
    }
    //dma_params_impl_main(const dma_params<B>&);
    union {
    dma_hlapi_t                  d;
      stu_hlapi_t                s;
    } hlapi;
    dma_params_sd_type           styp; // source type
    dma_params_sd_type           dtyp; // destination type
    dma_params_impl_spec         sel;  // select accelerator
  };

  // parameter modifier
  struct dma_params_impl_modif {
    inline dma_params_impl_modif() = default;
    inline dma_params_impl_modif(const dma_params_impl_modif&) = default;
    // updated iterators and offsets
    array<aoffset_t,NUM_FM_LOOPS> iter;
    array<poffset_t,NUM_FM_LOOPS> offsets;
  };

  //
  // Implementation specific parameters to run-time
  //
  struct dma_rt_impl_spec {
    inline dma_rt_impl_spec() {
      mmio.d = nullptr;
      ctrl   = 0;
      id     = 0;
    }
    union {
      ctrl_dma_regs<dma_hlapi_t>* d;           // base address of iDMA/oDMA accelerator MMIO registers
      ctrl_dma_regs<stu_hlapi_t>* s;           // base address of STU accelerator MMIO registers
    } mmio;
    uint32_t                      ctrl;        // interrupt and event flags [0] devent, [8] ievent, [16] interrupt
    trace_id_t                    id;          // real-time trace ID
  };
}
#endif
