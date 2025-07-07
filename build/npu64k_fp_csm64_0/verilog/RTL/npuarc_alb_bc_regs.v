// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2013 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary 
// work of Synopsys, Inc., and is fully protected under copyright and 
// trade secret laws. You may not view, use, disclose, copy, or distribute 
// this file or any information contained herein except pursuant to a 
// valid written license from Synopsys, Inc.
//
// Certain materials incorporated herein are copyright (C) 2010 - 2011, The
// University Court of the University of Edinburgh. All Rights Reserved.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
// ######    #####          ######   #######   #####    #####
// #     #  #     #         #     #  #        #     #  #     #
// #     #  #               #     #  #        #        #
// ######   #               ######   #####    #  ####   #####
// #     #  #               #   #    #        #     #        #
// #     #  #     #         #    #   #        #     #  #     #
// ######    #####   #####  #     #  #######   #####    #####
//
// ===========================================================================
//
// Description:
//
//  This module implements the optional Build Configuration Registers for
//  an ARCv2HS processor.
//
// ==========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

`include "const.def"


`include "npuarc_pct_defines.v"
`include "npuarc_npu_exported_defines.v"

module npuarc_alb_bc_regs (

  input [7:0]                 rtt_src_num,

  input [21:0]                      intvbase_in_r, // ext vector base at reset

  ////////// Interface for LR instructions to write aux regs ///////////////
  //
  input                       aux_bcr_ren_r,    // address is in BCR range
  input                       aux_write,        // aux write operation
  input      [`npuarc_BCR_REG_RANGE] aux_bcr_raddr_r,  // Aux address for read/write

  ////////// Interface for aux address / perm checks and LR reads //////////
  //
  output reg [`npuarc_DATA_RANGE]    bcr_aux_rdata,    // LR read data
  output reg                  bcr_aux_illegal,  // LR/SR op is illegal
  output reg                  bcr_aux_k_rd      // op needs Kernel R perm
);

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Asynchronous logic for selecting BCR register values for LR operations //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : bcr_sel_PROC

  bcr_aux_rdata     = `npuarc_DATA_SIZE'd0;              // return 0 by default
  bcr_aux_k_rd      = 1'b0;                       // Kernel R perm needed

  bcr_aux_illegal   = aux_bcr_ren_r
                    & aux_write                   // writes are illegal
                    ;

  if (aux_bcr_ren_r == 1'b1)
  begin
    bcr_aux_k_rd = 1'b1;

    bcr_aux_illegal = aux_bcr_ren_r
                    & aux_write                   // writes are illegal
                    ;
    
    case (aux_bcr_raddr_r)

  // -------------------------------------------------------------------------
  // `BCR_VER_AUX
  //

        `npuarc_BCR_VER_AUX:
        begin
          bcr_aux_rdata   = 32'd3; // All Three  BCR regions implemented
//!BCR { num: 96, val: 2, name: "BCR_VER" }
        end



  // -------------------------------------------------------------------------
  // `VECBASE_AC_BUILD_AUX
  //

        `npuarc_VECBASE_AC_BUILD_AUX:
        begin
          bcr_aux_rdata   = { intvbase_in_r,  // ext input Vector base at reset
                              8'h04,  // ARCompact V2 interrupt unit
                              2'd1
                            };
//!BCR { num: 104, val: 17, name: "VECBASE_AC_BUILD" }
        end

  // -------------------------------------------------------------------------
  // `MPU_BUILD_AUX
  //
      `npuarc_MPU_BUILD_AUX:
      begin
        bcr_aux_rdata     = { 16'd0,                    // 
                               8'd`npuarc_MPU_NUM_REGIONS,     // 
                               8'd3              // HS
                            };
//!BCR { num: 109, val: 2051, name: "MPU_BUILD" }
      end

  // -------------------------------------------------------------------------
  // `MMU_BUILD_AUX
  //





      `npuarc_MMU_BUILD_AUX:
      begin
        bcr_aux_rdata     = {  8'd4,              // 31:24 - Version 4 mmu
                               1'd`npuarc_MMU_SHARED_LIB,       // 23    - Shared Lib ASID support
                               4'd12,             // 22:19 - page size of size1 pages
                               4'd3,             // 18:15 - page size of size0 pages
                               1'd`npuarc_MMU_DYNAMIC_LOADING,  // 14 dyn ld
                               1'd`npuarc_MMU_CCM_TRANSLATION,  // 13 ccm transl en
                               1'd`npuarc_MMU_PAE_ENABLED,      // 12    - PAE supported
                               2'd2,                   // 11:10 - joint-NTLB ways (2 => 4-way)
                               2'd0,                   //  9:8  - joint-NTLB entries/way (Normal page)
                               2'd1,                  //  7:6  - joint-STLB entries (Super Page)
                               3'd1,                //  5:3  - micro-ITLB entries (instruction)
                               3'd2                 //  2:0  - micro-DTLB entries (Data)
                            };
//!BCR { num: 111, val: 81893450, name: "MMU_BUILD" }
      end

  // -------------------------------------------------------------------------
  // `RF_BUILD_AUX
  //
        `npuarc_RF_BUILD_AUX:
        begin
  /// Notice: this is a departure from EM, which computes banked regs
  /// even if num_banks == 1.
          bcr_aux_rdata   = { 16'd0,           // Unused bits [31:11] are RAZ
                              2'd0,           // Registers per additional bank
                              3'd0,           // Number of additional banks
                              1'b0,            // R = 0: not cleared on reset
                              1'b0,           // 16 or 32 registers defined
                              1'b1,           // 3 or 4 port register file
                              8'd2             // Current version number
                            };
//!BCR { num: 110, val: 258, name: "RF_BUILD" }
        end

  // -------------------------------------------------------------------------
  // `D_CACHE_BUILD_AUX
  //

        `npuarc_D_CACHE_BUILD_AUX:
        begin
  
          bcr_aux_rdata   = { 2'd0,                     // Unused bits [31:30] are RAZ
                              3'd`npuarc_DC_MEM_CYCLES,        // 29-27
                              1'd`npuarc_DC_UNCACHED_REGION,   // 26
                              3'd0,                     // 25-23
                              1'b0,                     // 22
                              2'd`npuarc_DC_FEATURE_LEVEL,     // 21-20
                              4'd2,
                              4'd6,
                              4'd1,
                              8'h05                     // Version 8'h05
                            };
//!BCR { num: 114, val: 270688517, name: "D_CACHE_BUILD" }
        end

  // -------------------------------------------------------------------------
  // `DCCM_BUILD_AUX
  //

        `npuarc_DCCM_BUILD_AUX:
        begin
          
          bcr_aux_rdata   = { 11'd0,
                              1'b1,
                              3'd2,
                              1'b0,
                              4'd0,
                              4'd7,
                              8'h04
                            };
//!BCR { num: 116, val: 1312516, name: "DCCM_BUILD" }
        end

  // -------------------------------------------------------------------------
  // `TIMER_BUILD_AUX
  //

        `npuarc_TIMER_BUILD_AUX:
        begin


          bcr_aux_rdata   = { 8'd0,            // Unused bits [31:24] are RAZ
                              4'd0,
                              4'd0,
                              5'd0,            // Unused bits [15:11] are RAZ
                              1'b`npuarc_HAS_RTC,
                              1'b`npuarc_HAS_TIMER_1,
                              1'b`npuarc_HAS_TIMER_0,
                              8'h06            // ARCompact V2 timers with TD bit implementation
                            };
//!BCR { num: 117, val: 1286, name: "TIMER_BUILD" }
        end
        `npuarc_AP_BUILD_AUX:     // K_RW
        begin
          bcr_aux_rdata   = { 20'd0, 1'b0, 1'b1, 2'd2, 8'd5};
//!BCR { num: 118, val: 1541, name: "AP_BUILD" }
        end

  // -------------------------------------------------------------------------
  // `SRT_BUILD_AUX
  //

        `npuarc_SRT_BUILD_AUX:
        begin
          bcr_aux_rdata   = {22'd`npuarc_SMART_STACK_ENTRIES,    // Stack size
                             2'd0,
                             8'd4};                       // Version 4
//!BCR { num: 255, val: 131076, name: "SMART_BUILD" }
        end


  // -------------------------------------------------------------------------
  // `CC_BUILD_AUX
  //

        `npuarc_CC_BUILD_AUX:
        begin
          bcr_aux_rdata       = {
                                    16'd`npuarc_PCT_NUM_CONFIGS,
                                    8'd0,     // Reserved
                                    8'd2      // Version = 0x2
                                  };
//!BCR { num: 246, val: 8323074, name: "CC_BUILD" }
        end

  // -------------------------------------------------------------------------
  // `PCT_BUILD_AUX
  //

        `npuarc_PCT_BUILD_AUX:
        begin
          bcr_aux_rdata   = { 8'd0,                // # of Counters with min/max capability
                              8'd`npuarc_PCT_COUNTERS,    // # of Counters
                              5'd0,                // Reserved
                              1'b`npuarc_PCT_INTERRUPT,   // PCT interrupts
                              2'd1,                // Counter Size
                              8'd`npuarc_PCT_VERSION      // Current PCT version
                            };
//!BCR { num: 245, val: 525571, name: "PCT_BUILD" }
        end

  // -------------------------------------------------------------------------
  // `RTT_BUILD_AUX
  //

        `npuarc_RTT_BUILD_AUX:
        begin
          bcr_aux_rdata   = {11'd0,
                             2'd1,
                             rtt_src_num,
                             2'd`npuarc_RTT_FEATURE_LEVEL,
                             1'd`npuarc_RTT_PGMINT_OPTION,
                             `npuarc_ARC_RTT_VERSION};                       // Version 5
//!BCR { num: 242, val: 524552, name: "RTT_BUILD" }
        end

  // -------------------------------------------------------------------------
  // `I_CACHE_BUILD_AUX
  //

        `npuarc_I_CACHE_BUILD_AUX:
        begin
          bcr_aux_rdata   = { 9'd0,                          // Unused bits [31:24] are RAZ
                              1'b`npuarc_IC_DISABLE_ON_RESET,
                              2'd`npuarc_IC_FEATURE_LEVEL,
                              4'd3,
                              4'd6,
                              4'd2,
                              8'd4
                            };
//!BCR { num: 119, val: 2318852, name: "I_CACHE_BUILD" }
        end

//`if (`ANY_ECC_OPTION==1)
  // -------------------------------------------------------------------------
  // `ERP_BUILD_AUX
  //

        `npuarc_ERP_BUILD_AUX:
        begin
           bcr_aux_rdata   = {5'd0,                // Reserved
                              3'd`npuarc_BCR_MMU_ECC_OPTION,
                              1'd`npuarc_BCR_PIPELINE_COMPONENT, //pipeline EDC
                              3'd0,
                              3'd`npuarc_BCR_IC_ECC_OPTION,
                              3'd`npuarc_BCR_DC_ECC_OPTION,
                              3'd`npuarc_BCR_ICCM0_ECC_OPTION,
                              3'd`npuarc_BCR_DCCM_ECC_OPTION,
                              8'h05                // Version
                             };
//!BCR { num: 199, val: 84624645, name: "ERP_BUILD" }
        end

//`endif





   
        `npuarc_EWDT_BUILD_AUX:
        begin
          bcr_aux_rdata = {1'b`npuarc_WATCHDOG_CLK, 1'b`npuarc_WATCHDOG_PARITY,8'b0,4'd0,4'd1,4'd1 ,2'd0, 8'h02}; 
        end

//!BCR { num: 238, val: 3221242882, name: "EWDT_BUILD" }

        `npuarc_MICRO_ARCH_BUILD_AUX: 
        begin
          bcr_aux_rdata   = {8'h00,           // Reserved
                             8'h3,          // Micro-arch
                             8'h04,           // Major (Goldfish)
                             8'h00            // Patch (1st rev)
                             };
//!BCR { num: 249, val: 197378, name: "MICRO_ARCH_BUILD" }
        end


  // -------------------------------------------------------------------------
  // `MULTIPLY_BUILD_AUX
  //

        `npuarc_MULTIPLY_BUILD_AUX:
        begin
          bcr_aux_rdata   = { 8'h00,   // Reserved field is RAZ
                              8'h02,   // ARCompact V2 16x16 multiply
                              4'd3,   // DSP capabilities of the multiplier
                              2'd0,   // Number of cycles
                              2'd2,   // Serial (0), parallel (1), or Albacore (2) multiplier
                              8'd6    // ARCompact V2 32x32 multiply
                            };
//!BCR { num: 123, val: 143878, name: "MULTIPLY_BUILD" }
        end

  // -------------------------------------------------------------------------
  // `SWAP_BUILD_AUX
  //

        `npuarc_SWAP_BUILD_AUX:
        begin
          bcr_aux_rdata   = 32'd3;   // ARCompact V2 version
//!BCR { num: 124, val: 3, name: "SWAP_BUILD" }
        end

  // -------------------------------------------------------------------------
  // `NORM_BUILD_AUX
  //

        `npuarc_NORM_BUILD_AUX:
        begin
          bcr_aux_rdata   = 32'd3;   // ARCompact V2 version
        end

//!BCR { num: 125, val: 3, name: "NORM_BUILD" }
  // -------------------------------------------------------------------------
  // `MINMAX_BUILD_AUX
  //

        `npuarc_MINMAX_BUILD_AUX:
        begin
          bcr_aux_rdata   = 32'd2;   // Common V1/V2 version
//!BCR { num: 126, val: 2, name: "MINMAX_BUILD" }
        end

  // -------------------------------------------------------------------------
  // `BARREL_BUILD_AUX
  //

        `npuarc_BARREL_BUILD_AUX:
        begin
          bcr_aux_rdata   = { 22'd0,  // Reserved bits are RAZ
                              1'b`npuarc_HAS_SHIFTER,
                              1'b`npuarc_SHIFT_ASSIST,
                              8'h03
                            };
//!BCR { num: 127, val: 771, name: "BARREL_BUILD" }
        end


        `npuarc_ISA_BUILD_AUX:  // ANY_READ
        begin
          bcr_aux_rdata   = { 4'd2,
                              4'd3,
                              1'b`npuarc_LL64_OPTION,
                              1'b1,
                              1'b`npuarc_ATOMIC_OPTION,
                              1'b`npuarc_BYTE_ORDER,
                              4'd4,
                              4'd7,
                              4'd4,
                              8'd2     // ISA_CONFIG revision number
                            };
//!BCR { num: 193, val: 602174466, name: "ISA_CONFIG" }
        end
 
        
`npuarc_ISA_PROFILE_AUX:  // ANY_READ
        begin
          bcr_aux_rdata   = { 12'd0,   // Reserved 
                              4'd1,    // G3
                              4'd1,   // G2
                              4'd1,    // G1
                              8'd1     // ISA_CONFIG revision number
                            };

//!BCR { num: 248, val: 69889, name: "ISA_PROFILE" }
        end

  // -------------------------------------------------------------------------
  // `IRQ_BUILD_AUX
  //

        `npuarc_IRQ_BUILD_AUX:
        begin
          bcr_aux_rdata   = { 1'd0,                       // RAZ
                              2'd0,                  // 'N'
                              1'd0,                  // 'F'
                              4'd2,                  // 'L'
                              8'd36,               // 'EXTS'
                              8'd39,               // 'IRQS'
                              8'd2                 // VERSION
                            }
                          ;

//!BCR { num: 243, val: 35923714, name: "IRQ_BUILD" }
        end
  // -------------------------------------------------------------------------
  // STACK_REGION_BUILD_AUX
  //

        `npuarc_STACK_REGION_BUILD_AUX:  // ANY_READ
        begin
          bcr_aux_rdata   = {24'd0,
                             8'd2}; // Build Version
//!BCR { num: 197, val: 2, name: "STACK_REGION_BUILD" }
        end




 
      `npuarc_CCBIU_BUILD_AUX:
        begin
          bcr_aux_rdata = 268468481;
//!BCR { num: 231, val: 268468481, name: "BIU_BUILD" }
        end



// `define BPU_BUILD_AUX 8'hc0     // Use the 700's BPU register.

        `npuarc_BPU_BUILD_AUX:
        begin





          bcr_aux_rdata   = {  6'd0,                      // RAZ
                              26'd11079942
                            }
                          ;

//!BCR { num: 192, val: 11079942, name: "BPU_BUILD" }
        end


        `npuarc_CLUSTER_BUILD_AUX:
          bcr_aux_rdata   = { 1'd`npuarc_CC_BCR_T,             // internal SCU trace bit
                              1'd`npuarc_CC_BCR_CGATE,         // architectural clock gate
                              1'd`npuarc_CC_BCR_SM,            // Shared Memory
                              1'd`npuarc_CC_BCR_FS,            // Function Safety
                              2'd0,                     // RESERVED
                              2'd`npuarc_CC_BCR_C,             // C
                              8'd`npuarc_CC_BCR_NUM_ENTRIES,   // NUM_ENTRIES
                              1'd`npuarc_CC_BCR_SCLK,          // SCLK
                              7'd`npuarc_CC_BCR_NUM_CORES,     // NUM_CORES
                              8'd`npuarc_CC_BCR_VERSION        // VERSION
                            }
                          ;

//!BCR { num: 207, val: 1073742087, name: "CLUSTER_BUILD" }

  // -------------------------------------------------------------------------
  // -------------------------------------------------------------------------




  // -------------------------------------------------------------------------


  // -------------------------------------------------------------------------

    // CNN_BUILD_AUX is resued for the NPU (NPX) product
    // NPU_BUILD
        `npuarc_CNN_BUILD_AUX:
        begin
          bcr_aux_rdata = {
            3'd`npuarc_NPU_AM_SIZE_BCR,        // 31:29
            3'd`npuarc_NPU_VM_SIZE_BCR,        // 28:26
            3'd0,                       // 25:23
            1'b`npuarc_NPU_HAS_SFTY_BCR,       // 22
            2'd`npuarc_NPU_STU_BCR,            // 21:20
            1'b`npuarc_NPU_HAS_EVT_MGT,        // 19
            3'd`npuarc_NPU_MAC_BCR,            // 18:16
            1'b`npuarc_NPU_HAS_L1_CTRL,        // 15
            1'b`npuarc_NPU_HAS_L2_CTRL,        // 14
            1'b`npuarc_NPU_MEM_ECC,            // 13
            5'd`npuarc_NPU_SLICE_NUM,          // 12:8
            8'd`npuarc_NPU_VERSION             // 7:0
           };
//!BCR { num: 236, val: 1883040785, name: "NPU_BUILD" }
        end


  // -------------------------------------------------------------------------

// spyglass disable_block W193
// SMD: empty statement
// SJ:  simplify config code
        default: ;
// spyglass enable_block W193
    endcase
  end
end
endmodule
