// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2012 Synopsys, Inc. All rights reserved.
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
// Description:
// @p
//  The jtlb module implements the Joint-TLB for both data and instruction
//  access. The jtlb consists of two main sections the ntlb (4-way set-
//  associative TLB for only 'normal' size pages, and the stlb (fully
//  associative TLB for only 'super' size pages.
//
// @e
//
//  This .vpp source file must be pre-processed with the Verilog Pre-Processor
//  (VPP) to produce the equivalent .v file using a command such as:
//
//   vpp +q +o cpu.vpp
//
// ===========================================================================
// MMU Components in processor hierarchy
//
//  alb_cpu
//   |
//   +--alb_core
//       |
//       +--alb_mmu_jtlb
//       |   |
//       |   |
//       |   +--alb_mmu_ustlb  (wrapper with parameters and included file alb_mmu_utlb)
//       |   |
//       |   +--alb_mmu_plru8/16
//       |
//       +--alb_ifu
//       |   |
//       |   +--alb_mmu_itlb   (wrapper with parameters and included file alb_mmu_utlb_top)
//       |      |
//       |      +--alb_mmu_uitlb   (wrapper with parameters and included file alb_mmu_utlb)
//       |      |
//       |      +--alb_mmu_lru4
//       |   
//       +--alb_dmp
//       |   |
//       |   +--alb_mmu_dtlb   (wrapper with parameters and included file alb_mmu_utlb_top)
//       |      |
//       |      +--alb_mmu_udtlb   (wrapper with parameters and included file alb_mmu_utlb)
//              |
//              +--alb_mmu_plru8
//
//
// cpu_top
//   |      
//   +--alb_srams
//       |
//       +--mmu_ntlb_pd0_ram
//       |
//       +--mmu_ntlb_pd0_ram
//



// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"


//POST_PROCESS { prefix:"//D:", wire_prefix:"t_", edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 }, rst: "rst_a", edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_err", encode_reset: true, add_reset_sensitivity: 1 } }

//D: error_signal { name: "ustlb_err" }

module npuarc_jtlb (

  ////////// General input signals ///////////////////////////////////////////
  //
  input                      clk,              // Processor clock
  input                      rst_a,            // Global reset
  input                      rst_init_disable_r,
  output reg                 mmu_ready,        // Clear on reset, set when
                                               // mmu ready for operation
  input                      ecc_mmu_disable,  // ECC disable
  output reg [3:0]           ecc_mmu_sbe_count_r, // single bit error counter
  output reg [`npuarc_MMU_PD0_SYNDROME_MSB:0] fs_itlb_bank0_syndrome_r,
  output reg [`npuarc_MMU_PD0_SYNDROME_MSB:0] fs_itlb_bank1_syndrome_r,
  output reg [`npuarc_MMU_PD0_SYNDROME_MSB:0] fs_itlb_bank2_syndrome_r,
  output reg [`npuarc_MMU_PD0_SYNDROME_MSB:0] fs_itlb_bank3_syndrome_r,
  output reg [`npuarc_MMU_PD1_SYNDROME_MSB:0] fs_itlb_bank4_syndrome_r,

  output reg                   fs_itlb_bank0_ecc_sb_error_r,
  output reg                   fs_itlb_bank1_ecc_sb_error_r,
  output reg                   fs_itlb_bank2_ecc_sb_error_r,
  output reg                   fs_itlb_bank3_ecc_sb_error_r,
  output reg                   fs_itlb_bank4_ecc_sb_error_r,

  output reg                   fs_itlb_bank0_ecc_db_error_r,
  output reg                   fs_itlb_bank1_ecc_db_error_r,
  output reg                   fs_itlb_bank2_ecc_db_error_r,
  output reg                   fs_itlb_bank3_ecc_db_error_r,
  output reg                   fs_itlb_bank4_ecc_db_error_r,

  output reg [`npuarc_MMU_PD0_SYNDROME_MSB:0] fs_dtlb_bank0_syndrome_r,
  output reg [`npuarc_MMU_PD0_SYNDROME_MSB:0] fs_dtlb_bank1_syndrome_r,
  output reg [`npuarc_MMU_PD0_SYNDROME_MSB:0] fs_dtlb_bank2_syndrome_r,
  output reg [`npuarc_MMU_PD0_SYNDROME_MSB:0] fs_dtlb_bank3_syndrome_r,
  output reg [`npuarc_MMU_PD1_SYNDROME_MSB:0] fs_dtlb_bank4_syndrome_r,

  output reg                   fs_dtlb_bank0_ecc_sb_error_r,      
  output reg                   fs_dtlb_bank1_ecc_sb_error_r,      
  output reg                   fs_dtlb_bank2_ecc_sb_error_r,      
  output reg                   fs_dtlb_bank3_ecc_sb_error_r,      
  output reg                   fs_dtlb_bank4_ecc_sb_error_r,      

  output reg                   fs_dtlb_bank0_ecc_db_error_r,
  output reg                   fs_dtlb_bank1_ecc_db_error_r,
  output reg                   fs_dtlb_bank2_ecc_db_error_r,
  output reg                   fs_dtlb_bank3_ecc_db_error_r,
  output reg                   fs_dtlb_bank4_ecc_db_error_r,

  input                      mmu_ecc_sbe_clr,
  output                     mmu_en_r,         // Enable TLB lookups
  output reg                 mmu_clock_req_r,
  output reg                 mmu_cmd_active,
  input                      wa_restart_r,     // cpu pipe flush
  input                      wa_jtlb_cancel,   // flush (exc during int prol/epil)
//input                      flush_retry_r,    // cpu pipe flushed for retry
  input                      wa_jtlb_lookup_start_r, // flush/replay due to utlb miss
  output reg                 dtlb_update_pend_r,

  input                      ca_tlb_miss_excpn,
  input  [`npuarc_PD0_VPN_RANGE]    ca_tlb_miss_efa,
  input                      ca_m_chk_excpn,

  // Access type: user/kernel mode, debug op
  input                      debug_op,         // ld/st originated from debug
  input                      kernel_mode,      // has Kernel mode privileges

  // Shared lib enable, subscriptions
  output                     shared_en_r,      // Shared lib enable (PID)
  output [`npuarc_SASID_RANGE]      sasid_r,          // Current pid slib membership
  output [`npuarc_MMU_PID_ASID_RANGE] asid_rr,        // Current pid.asid (2cyc for utlbs)
  output [`npuarc_MMU_PID_ASID_RANGE] asid_r,         // Current pid.asid (1cyc for rtt)
  output                       asid_wr_en,     // pid.asid update

  ////////// MMU NTLB RAMs //////////////////////////////////////////////////
  //
  // NTLB PD0 (tag) ram interface
  output                               ntlb_pd0_clk,
  output                               ntlb_pd0_ram_ce,
  output                               ntlb_pd0_ram_we,
  output     [`npuarc_NTLB_NUM_WAYS_ECC-1:0]  ntlb_pd0_ram_wem,
  output     [`npuarc_NTLB_PD0_ADDR_MSB:0]    ntlb_pd0_ram_addr,
  output     [`npuarc_NTLB_PD0_DATA_MSB:0]    ntlb_pd0_ram_wdata,
  input      [`npuarc_NTLB_PD0_DATA_MSB:0]    ntlb_pd0_ram_rdata,

  // NTLB PD1 (data) ram interface
  output                               ntlb_pd1_clk,
  output                               ntlb_pd1_ram_ce,
  output                               ntlb_pd1_ram_we,
  output     [`npuarc_NTLB_PD1_ADDR_MSB:0]    ntlb_pd1_ram_addr,
  output     [`npuarc_NTLB_PD1_DATA_MSB:0]    ntlb_pd1_ram_wdata,
  input      [`npuarc_NTLB_PD1_DATA_MSB:0]    ntlb_pd1_ram_rdata,



  ////////// AUX interface //////////////////////////////////////////////////
  // 
  ////////// Interface for SR instructions to write aux regs ////////////////
  //         (WA stage)
  input                       aux_mmu_wen_r,    // (WA) Aux write enable
  input       [4:0]           aux_mmu_waddr_r,  // (WA) Aux write Address
  input       [`npuarc_DATA_RANGE]   aux_wdata,        // (WA) Aux write data

  ////////// Interface for aux address / perm checks and aux read ///////////
  //         (X3 stage)
  input                       aux_write,        // (X3) Aux write operation
  input                       aux_read,         // (X3) Aux read operation
  input                       aux_mmu_ren_r,    // (X3) Aux unit select
  input       [4:0]           aux_mmu_raddr_r,  // (X3) Aux address (rd/wr)

  output reg  [`npuarc_DATA_RANGE]   mmu_aux_rdata,    // (X3) LR read data
  output reg                  mmu_aux_illegal,  // (X3) SR/LR op is illegal
  output reg                  mmu_aux_k_rd,     // (X3) op needs Kernel R perm
  output reg                  mmu_aux_k_wr,     // (X3) op needs Kernel W perm
  output reg                  mmu_aux_unimpl,   // (X3) LR/SR reg is not present
  output reg                  mmu_aux_serial_sr,// (X3) SR group flush
  output reg                  mmu_aux_strict_sr,// (X3) SR single flush
  output reg                  mmu_aux_index_ecc_e,

  ////////// Interface to itlb //////////////////////////////////////////////
  //
  // itlb update request (on miss)
  input                          ifu_clk2_en,
  input                          itlb_update_req,     // late (unreg) outputs
  input       [`npuarc_PD0_VPN_RANGE]   itlb_update_req_vpn,

  // jtlb response to itlb update request
  output reg                     jrsp_itlb_update_nxt, 
  output reg                     jrsp_itlb_update, 
  output reg                     jrsp_itlb_update_hit,
  output reg                     jrsp_itlb_multi_hit,
  output reg                     jrsp_itlb_tlb_err,

  // insert / delete / Inval (aux) operations from jtlb
  output reg [`npuarc_JCMD_RANGE]       jtlb_itlb_cmd_r,   // command from jtlb (aux)
  output     [`npuarc_ITLB_INDEX_RANGE] jtlb_itlb_index_r, // Aux addr for read

  // Interface to read utlb entries
  //
  // leda NTL_CON13C off
  // leda NTL_CON37 off
  // LMD: non driving port
  // LJ:  Not all bits of bus used
  // spyglass disable_block W240
  // SMD: unused inputs
  // SJ:  inputs not always used in all configs, part of read interface
  input                          itlb_rd_val,   // rd data reg in jtlb
  input      [`npuarc_UTLB_ENTRY_RANGE] itlb_rd_data,  // LR read data (entry)
  // leda NTL_CON13C on
  // leda NTL_CON37 on
  // spyglass enable_block W240

  ////////// Interface to dtlb //////////////////////////////////////////////
  //
  // Consolidated dtlb update request (on miss(es))
  input                          dtlb_update_req,     // late (unreg) outputs
  input       [`npuarc_PD0_VPN_RANGE]   dtlb_update_req_vpn,

  // jtlb response to dtlb update request
  output reg                     jrsp_dtlb_update, 
  output reg                     jrsp_dtlb_update_hit,
  output reg                     jrsp_dtlb_multi_hit,
  output reg                     jrsp_dtlb_tlb_err,

  // insert / delete / Inval (aux) operations from jtlb
  output reg [`npuarc_JCMD_RANGE]       jtlb_dtlb_cmd_r,    // command from jtlb (aux)
  output     [`npuarc_DTLB_INDEX_RANGE] jtlb_dtlb_index_r,  // Aux addr for read

  // Interface to read utlb entries
  //
  // leda NTL_CON13C off
  // leda NTL_CON37 off
  // LMD: non driving port
  // LJ:  Not all bits of bus used
  // spyglass disable_block W240
  // SMD: unused inputs
  // SJ:  inputs not always used in all configs, part of read interface
  input                          dtlb_rd_val,   // rd data reg in jtlb
  input      [`npuarc_UTLB_ENTRY_RANGE] dtlb_rd_data,  // LR read data (entry)
  // leda NTL_CON13C on
  // leda NTL_CON37 on
  // spyglass enable_block W240

  ////////// Shared bus to uTLBs ////////////////////////////////////////////
  //
  // leda NTL_CON32 off
  // LMD: Change on net has no effect on any of the outputs
  // LJ:  Not all bits of bus used
  // Entry data for update from jtlb; also used for lookups and write by jtlb
  output reg [`npuarc_UTLB_ENTRY_RANGE] jtlb_update_data
  // leda NTL_CON32 on
             
);
  

// MMU AUX Register address definitions
//
parameter [`npuarc_AUX_REG_RANGE]  AUX_ADDR_MMU_PD0      = `npuarc_TLBPD0_AUX;
parameter [`npuarc_AUX_REG_RANGE]  AUX_ADDR_MMU_PD1      = `npuarc_TLBPD1_AUX;
parameter [`npuarc_AUX_REG_RANGE]  AUX_ADDR_MMU_PD0_HI   = `npuarc_TLBPD0_HI_AUX;
parameter [`npuarc_AUX_REG_RANGE]  AUX_ADDR_MMU_PD1_HI   = `npuarc_TLBPD1_HI_AUX;
parameter [`npuarc_AUX_REG_RANGE]  AUX_ADDR_MMU_INDEX    = `npuarc_TLB_INDEX_AUX;
parameter [`npuarc_AUX_REG_RANGE]  AUX_ADDR_MMU_CMD      = `npuarc_TLB_CMD_AUX;
parameter [`npuarc_AUX_REG_RANGE]  AUX_ADDR_MMU_PID      = `npuarc_PID_AUX;
parameter [`npuarc_AUX_REG_RANGE]  AUX_ADDR_MMU_SLS0     = `npuarc_SASID0_AUX;
parameter [`npuarc_AUX_REG_RANGE]  AUX_ADDR_MMU_SLS1     = `npuarc_SASID1_AUX;
parameter [`npuarc_AUX_REG_RANGE]  AUX_ADDR_MMU_SCRATCH0 = `npuarc_SCRATCH_DATA0_AUX;

//---------------------------------------------------------------------------
// MMU AUX commands (initiated by write to aux_mmu_cmd_r register)
//---------------------------------------------------------------------------
//parameter JTLB_CMD_NOP      = 6'h0;  // NOP
parameter JTLB_CMD_WRITE    = 6'h1;  // Write
parameter JTLB_CMD_READ     = 6'h2;  // Read
parameter JTLB_CMD_GETIX    = 6'h3;  // Get index
parameter JTLB_CMD_PROBE    = 6'h4;  // Probe
parameter JTLB_CMD_WRITENI  = 6'h5;  // Write (no invalidation of utlbs)
parameter JTLB_CMD_IVUTLB   = 6'h6;  // Invalidate utlbs
parameter JTLB_CMD_INSERT   = 6'h7;  // Insert entry (and forward to utlb)
parameter JTLB_CMD_INSERTJ  = 6'hA;  // Insert entry (jtlb only)
parameter JTLB_CMD_DELETE   = 6'h8;  // Delete entry
parameter JTLB_CMD_DELETEIS = 6'h9;  // Delete entry (ignore share bits)
parameter JTLB_CMD_RESET_LRU = 6'hB; // Reset LRU state of NTLB,STLB,ITLB,DTLB
//---------------------------------------------------------------------------
// AUX Index decode, addressing TLBs/RAMs
//---------------------------------------------------------------------------
parameter IX_NTLB_BASE     = `npuarc_MMU_INDEX_IX_WIDTH'h0;
parameter IX_NTLB_END      = IX_NTLB_BASE + `npuarc_MMU_NTLB_NUM_ENTRIES;

parameter IX_STLB_BASE     = `npuarc_MMU_INDEX_IX_WIDTH'h800;
parameter IX_STLB_END      = IX_STLB_BASE + `npuarc_MMU_STLB_NUM_ENTRIES;

parameter IX_ITLB_BASE     = `npuarc_MMU_INDEX_IX_WIDTH'h1000;
parameter IX_ITLB_END      = IX_ITLB_BASE + `npuarc_ITLB_NUM_ENTRIES;

parameter IX_DTLB_BASE     = `npuarc_MMU_INDEX_IX_WIDTH'h1100;
parameter IX_DTLB_END      = IX_DTLB_BASE + `npuarc_DTLB_NUM_ENTRIES;

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// States for the main jtlb state machine                                 //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
parameter JSM_RESET         = 5'h0;  // immed go to init or arb
parameter JSM_INIT          = 5'h1C; // Stay here till ntlb tag ram cleared
parameter JSM_ARB           = 5'h1;  // No update or aux cmd in progress
parameter JSM_CMD_TERM      = 5'h18; // (single cycle) aux cmd completed

parameter JSM_NTLB_RD1      = 5'h2;  // read ntlb
parameter JSM_NTLB_RD1B     = 5'h12; // read ntlb 2nd clk
parameter JSM_NTLB_RD2      = 5'h13; // read tlb  3nd clk (write pd0/pd1)
parameter JSM_AUX_RD1       = 5'h14; // read invalid index

parameter JSM_STLB_RD1      = 5'h3;  // read stlb
parameter JSM_ITLB_RD1      = 5'h4;  // read itlb
parameter JSM_DTLB_RD1      = 5'h6;  // read dtlb
parameter JSM_TLB_RD2       = 5'h5;  // read u/stlb 2nd clk (write pd0/pd1)

parameter JSM_NTLB_WR       = 5'h8;  // write ntlb
parameter JSM_IVUTLB        = 5'h9;  // 
parameter JSM_RESET_LRU     = 5'h19; // 

parameter JSM_UTLB_MISS1    = 5'hA;  // utlb update tag rd 1
parameter JSM_UTLB_MISS1B   = 5'hB;  // utlb update tag rd 2
parameter JSM_UTLB_MISS2    = 5'hF;  // utlb update tag rd 3
parameter JSM_UTLB_MISS3    = 5'hD;  // utlb update data rd 1
parameter JSM_UTLB_MISS4    = 5'hE;  // utlb update data rd 2
parameter JSM_LKUP_RSLT1    = 5'h10;
parameter JSM_LKUP_RSLT1B   = 5'h11;
parameter JSM_LKUP_RSLT2    = 5'h15;

// leda NTL_CON13A off
// LMD: non driving internal net Range
// LJ:  Not all bits of bus used
wire                ecc_db_error_pd0;
wire                ecc_db_error_pd1;

wire   [`npuarc_PCKD_PTE_RANGE]     pckd_data_pte; // for write/update TLB

reg pd0_rdata_en_r;
reg      ecc_db_error_pd0_r;
reg      pd1_rdata_en_r;
reg      ecc_db_error_pd1_r;

// generate clock enable for pd0 mem read data capture reg 
//

reg pd0_rdata_cg0;
reg pd1_rdata_cg0;

always @(posedge clk or posedge rst_a)
begin : pd0_rdata_cg0_PROC
  if (rst_a == 1'b1)
  begin
    pd0_rdata_cg0       <= 1'b0;
    pd1_rdata_cg0       <= 1'b0;
    ecc_db_error_pd0_r  <= 1'b0;
    pd0_rdata_en_r      <= 1'b0;
    pd1_rdata_en_r      <= 1'b0;
    ecc_db_error_pd1_r  <= 1'b0;
  end
  else 
  begin
    pd0_rdata_cg0       <= ntlb_pd0_ram_ce & !(ntlb_pd0_ram_we); // read op
    pd1_rdata_cg0       <= ntlb_pd1_ram_ce & !(ntlb_pd1_ram_we); // read op
    pd0_rdata_en_r      <= pd0_rdata_cg0;
    pd1_rdata_en_r      <= pd1_rdata_cg0;
    ecc_db_error_pd1_r  <= (pd1_rdata_en_r) ? ecc_db_error_pd1 : 1'b0;
    ecc_db_error_pd0_r  <= (pd0_rdata_en_r) ? ecc_db_error_pd0 : 1'b0;
  end
end

// ----------------------------------------------
// add memory data output register for pd0 / pd1
// ----------------------------------------------

// generate clock for pd0 mem read data capture reg
// spyglass disable_block W401
// SMD: clock signal generated and used inside module
// SJ:  no functional issue
wire pd0_rdata_clk;

npuarc_clkgate u_pd0_rdata_clkgate (
  .clk_in            (clk),
  .clock_enable      (pd0_rdata_cg0),
  .clk_out           (pd0_rdata_clk)
);
// spyglass enable_block W401
// pd0 ram read data register
//
reg [`npuarc_NTLB_PD0_DATA_MSB:0] ntlb_pd0_ram_rdata_r;

// spyglass disable_block Ar_resetcross01 STARC-2.3.4.3
// SMD: 2 sequential elements that have different resets/sets
// SJ:  Data path signals that dont require a reset, spyglass flags as different resets
// SMD: No async reset
// SJ:  Data path signals that dont require a reset
// VPOST OFF
always @(posedge pd0_rdata_clk)
begin : ntlb_pd0_ram_rdata_PROC
 ntlb_pd0_ram_rdata_r <= ntlb_pd0_ram_rdata;
end
// VPOST ON
// spyglass enable_block Ar_resetcross01 STARC-2.3.4.3
// generate clock enable for pd1 mem read data capture reg 
//
// generate clock for pd1 mem read data capture reg
// spyglass disable_block W401
// SMD: clock signal generated and used inside module
// SJ:  no functional issue
wire pd1_rdata_clk;

npuarc_clkgate u_pd1_rdata_clkgate (
  .clk_in            (clk),
  .clock_enable      (pd1_rdata_cg0),
  .clk_out           (pd1_rdata_clk)
);
// spyglass enable_block W401
// pd1 ram read data register
//
reg [`npuarc_NTLB_PD1_DATA_MSB:0] ntlb_pd1_ram_rdata_r;

// spyglass disable_block Ar_resetcross01 STARC-2.3.4.3
// SMD: 2 sequential elements that have different resets/sets
// SJ:  Data path signals that dont require a reset, spyglass flags as different resets
// SMD: No async reset
// SJ:  Data path signals that dont require a reset
// VPOST OFF
always @(posedge pd1_rdata_clk)
begin : ntlb_pd1_ram_rdata_PROC
 ntlb_pd1_ram_rdata_r <= ntlb_pd1_ram_rdata;
end
// VPOST ON
// spyglass enable_block Ar_resetcross01 STARC-2.3.4.3

// AUX register declarations
//
reg [`npuarc_DATA_RANGE]         aux_mmu_pd0_nxt;     
reg [`npuarc_DATA_RANGE]         aux_mmu_pd0_r;
reg [`npuarc_DATA_RANGE]         aux_mmu_pd1_nxt;      
reg [`npuarc_DATA_RANGE]         aux_mmu_pd1_r;
wire [`npuarc_DATA_RANGE]        aux_mmu_pd0_rr;
wire [`npuarc_DATA_RANGE]        aux_mmu_pd1_rr;

reg [`npuarc_PD1_PPN_HI_RANGE]   aux_mmu_pd1_hi_nxt;  
reg [`npuarc_PD1_PPN_HI_RANGE]   aux_mmu_pd1_hi_r;
wire [`npuarc_PD1_PPN_HI_RANGE]  aux_mmu_pd1_hi_rr;

reg [`npuarc_MMU_INDEX_IX_RANGE] aux_mmu_index_ix_nxt; 
reg [`npuarc_MMU_INDEX_IX_RANGE] aux_mmu_index_ix_r;
reg [`npuarc_MMU_INDEX_RC_RANGE] aux_mmu_index_rc_nxt;
reg [`npuarc_MMU_INDEX_RC_RANGE] aux_mmu_index_rc_r;
reg                       aux_mmu_index_e_r;

reg [`npuarc_MMU_CMD_CMD_RANGE]  aux_mmu_cmd_nxt;   
reg [`npuarc_MMU_CMD_CMD_RANGE]  aux_mmu_cmd_r;
wire [`npuarc_MMU_CMD_CMD_RANGE] aux_mmu_cmd_rr;

reg [`npuarc_MMU_PID_ASID_RANGE] aux_mmu_pid_asid_nxt;
reg [`npuarc_MMU_PID_ASID_RANGE] aux_mmu_pid_asid_r;
wire [`npuarc_MMU_PID_ASID_RANGE] aux_mmu_pid_asid_rr;

reg                       aux_mmu_pid_s_nxt;   
reg                       aux_mmu_pid_s_r;   // shared asid en
wire                      aux_mmu_pid_s_rr;

//reg                     aux_mmu_pid_ep_nxt,   aux_mmu_pid_ep_r;  // pid write en
reg                       aux_mmu_pid_t_nxt;
reg                       aux_mmu_pid_t_r;   // global tlb en
wire                      aux_mmu_pid_t_rr;

reg [`npuarc_DATA_RANGE]         aux_mmu_sls0_nxt;
reg [`npuarc_DATA_RANGE]         aux_mmu_sls0_r;
reg [`npuarc_DATA_RANGE]         aux_mmu_sls1_nxt;
reg [`npuarc_DATA_RANGE]         aux_mmu_sls1_r;
wire [`npuarc_DATA_RANGE]        aux_mmu_sls0_rr;
wire [`npuarc_DATA_RANGE]        aux_mmu_sls1_rr;
reg [`npuarc_DATA_RANGE]         aux_mmu_scratch0_nxt;
reg [`npuarc_DATA_RANGE]         aux_mmu_scratch0_r;


// aux command reg 2cyc, used after ARB state
assign aux_mmu_cmd_rr = aux_mmu_cmd_r;

// TLBIndex register 2cyc (for 2 cycle read select paths)
wire [`npuarc_MMU_INDEX_IX_RANGE] aux_mmu_index_ix_rr;
  assign aux_mmu_index_ix_rr = aux_mmu_index_ix_r;

// PID register
assign aux_mmu_pid_asid_rr = aux_mmu_pid_asid_r;

assign aux_mmu_pid_s_rr = aux_mmu_pid_s_r;

assign aux_mmu_pid_t_rr = aux_mmu_pid_t_r;


// Shared ASID (SASID) register
assign aux_mmu_sls0_rr = aux_mmu_sls0_r;

assign aux_mmu_sls1_rr = aux_mmu_sls1_r;



// when hw modifies an aux register
//
reg [`npuarc_DATA_RANGE]         hw_mmu_pd0_nxt;
reg [`npuarc_DATA_RANGE]         hw_mmu_pd1_nxt;
reg [7:0]                 hw_mmu_pd1_hi_nxt;

reg  [`npuarc_MMU_INDEX_IX_RANGE] ntlb_invlru_index;
reg  [`npuarc_MMU_INDEX_IX_RANGE] ntlb_match_index;

reg  [`npuarc_MMU_INDEX_IX_RANGE] hw_mmu_index_ix_nxt;
reg  [`npuarc_MMU_INDEX_RC_RANGE] hw_mmu_index_rc_nxt;
reg                        hw_mmu_index_e_nxt;

wire [`npuarc_MMU_CMD_CMD_RANGE]  mmu_cmd_nxt;
wire [`npuarc_MMU_CMD_CMD_RANGE]  mmu_cmd_op;

// registered command decode
//
wire   cmd_r_op_probe;
assign cmd_r_op_probe  = (aux_mmu_cmd_r == JTLB_CMD_PROBE);

wire   cmd_r_op_getix;
assign cmd_r_op_getix  = (aux_mmu_cmd_r == JTLB_CMD_GETIX);

wire   cmd_rr_op_probe;
assign cmd_rr_op_probe  = (aux_mmu_cmd_rr == JTLB_CMD_PROBE);

wire   cmd_rr_op_getix;
assign cmd_rr_op_getix  = (aux_mmu_cmd_rr == JTLB_CMD_GETIX);

reg stlb_reset_lru_nxt;
reg stlb_reset_lru_r;

reg mntlb_reset_lru_nxt;
reg mntlb_reset_lru_r;

wire   cmd_rr_op_deleteis;
assign cmd_rr_op_deleteis = (aux_mmu_cmd_rr == JTLB_CMD_DELETEIS);

wire cmd_r_op_delete;

assign cmd_r_op_delete = (aux_mmu_cmd_r == JTLB_CMD_DELETE)
                        | (aux_mmu_cmd_r == JTLB_CMD_DELETEIS)
                        ;

wire cmd_rr_op_delete;
wire cmd_rr_op_insert;

assign cmd_rr_op_delete = (aux_mmu_cmd_rr == JTLB_CMD_DELETE)
                        | (aux_mmu_cmd_rr == JTLB_CMD_DELETEIS)
                        ;

assign cmd_rr_op_insert = (aux_mmu_cmd_rr == JTLB_CMD_INSERT)
                        | (aux_mmu_cmd_rr == JTLB_CMD_INSERTJ);

// AUX register write enables
//
reg       aux_mmu_pd0_wen;
reg       aux_mmu_pd1_wen;
reg       aux_mmu_pd1_hi_wen;
reg       aux_mmu_index_wen;
reg       aux_mmu_cmd_wen;
reg       aux_mmu_pid_wen;
reg       aux_mmu_sls0_wen;
reg       aux_mmu_sls1_wen;
reg       aux_mmu_scratch0_wen;

// For RTT indicate when process ID is CHANGED
assign asid_wr_en = aux_mmu_pid_wen && (|(aux_mmu_pid_asid_nxt ^ aux_mmu_pid_asid_r));

// registers which can be written by hw (lkup,rd...) as well as aux
//
//reg       hw_mmu_pd_wen; 

reg       hw_mmu_pd0_wen;
reg       hw_mmu_pd1_wen;
// `if (`MMU_PAE_ENABLED == 1) // pd1 low,hi always written together by hw
// reg       hw_mmu_pd1_hi_wen;
// `endif

reg       hw_mmu_index_wen;

wire      mmu_pd0_wen;
wire      mmu_pd1_wen;
wire      mmu_pd1_hi_wen;
wire      mmu_index_wen;
wire      mmu_cmd_wen;

reg       cmd_reg_clr;

assign mmu_pd0_wen = aux_mmu_pd0_wen || hw_mmu_pd0_wen;
assign mmu_pd1_wen = aux_mmu_pd1_wen || hw_mmu_pd1_wen;
assign mmu_pd1_hi_wen = aux_mmu_pd1_hi_wen || hw_mmu_pd1_wen;
assign mmu_index_wen = aux_mmu_index_wen || hw_mmu_index_wen;

assign mmu_cmd_wen = aux_mmu_cmd_wen || cmd_reg_clr;
assign mmu_cmd_nxt = cmd_reg_clr ? 
                       {`npuarc_MMU_CMD_CMD_WIDTH{1'b0}} :
                       aux_mmu_cmd_nxt ;

assign mmu_cmd_op  = //aux_mmu_cmd_wen ? 
                     //aux_mmu_cmd_nxt : // new aux command
                       aux_mmu_cmd_r;    //  or pending aux command

wire       jtlb_single_match;
wire       jtlb_multiple_match;

////////////////mmu sram related nets//////////////////
reg                               ntlb_pd0_ce;
reg                               ntlb_pd0_we;
reg     [`npuarc_NTLB_NUM_WAYS-1:0]      ntlb_pd0_wem;
reg     [`npuarc_NTLB_PD0_ADDR_MSB:0]    ntlb_pd0_addr;
wire    [`npuarc_NTLB_PD0_DATA_MSB:0]    ntlb_pd0_wdata;
wire    [`npuarc_NTLB_PD0_DATA_MSB:0]    ntlb_pd0_rdata;

reg                               ntlb_pd1_ce;
reg                               ntlb_pd1_we;
reg     [`npuarc_NTLB_PD1_ADDR_MSB:0]    ntlb_pd1_addr;
wire    [`npuarc_NTLB_PD1_DATA_MSB:0]    ntlb_pd1_wdata;
wire    [`npuarc_NTLB_PD1_DATA_MSB:0]    ntlb_pd1_rdata;

///////////////////////////////////////////////////////////////////////////
//                                                                        //
// ECC error detection                                                    //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
wire                ecc_sb_error_pd0_way0; 
wire                ecc_sb_error_pd0_way1;
wire                ecc_sb_error_pd0_way2;
wire                ecc_sb_error_pd0_way3;
wire                ecc_sb_error_pd1;

wire                ecc_db_error_pd0_way0; 
wire                ecc_db_error_pd0_way1;
wire                ecc_db_error_pd0_way2;       
wire                ecc_db_error_pd0_way3;

wire                ecc_sb_error_pd0;

reg                 ecc_mmu_sbe_count_set_cg0;
wire                ecc_mmu_sbe_count_clr_cg0;
wire [3:0]          ecc_mmu_sbe_count_nxt;
//reg  [3:0]          ecc_mmu_sbe_count_r;

reg                   itlb_syndrome_set_cg0;
reg                   itlb_syndrome_set_cg1;
reg                   dtlb_syndrome_set_cg0;
reg                   dtlb_syndrome_set_cg1;

reg [`npuarc_MMU_PD0_SYNDROME_MSB:0] fs_itlb_bank0_syndrome_nxt;
reg [`npuarc_MMU_PD0_SYNDROME_MSB:0] fs_itlb_bank1_syndrome_nxt;
reg [`npuarc_MMU_PD0_SYNDROME_MSB:0] fs_itlb_bank2_syndrome_nxt;
reg [`npuarc_MMU_PD0_SYNDROME_MSB:0] fs_itlb_bank3_syndrome_nxt;
reg [`npuarc_MMU_PD1_SYNDROME_MSB:0] fs_itlb_bank4_syndrome_nxt;

reg [`npuarc_MMU_PD0_SYNDROME_MSB:0] fs_dtlb_bank0_syndrome_nxt;
reg [`npuarc_MMU_PD0_SYNDROME_MSB:0] fs_dtlb_bank1_syndrome_nxt;
reg [`npuarc_MMU_PD0_SYNDROME_MSB:0] fs_dtlb_bank2_syndrome_nxt;
reg [`npuarc_MMU_PD0_SYNDROME_MSB:0] fs_dtlb_bank3_syndrome_nxt;
reg [`npuarc_MMU_PD1_SYNDROME_MSB:0] fs_dtlb_bank4_syndrome_nxt;


assign ecc_mmu_sbe_count_nxt = ecc_mmu_sbe_count_r + 1'b1;

assign ecc_mmu_sbe_count_clr_cg0 = mmu_ecc_sbe_clr;

assign ecc_db_error_pd0 = ecc_db_error_pd0_way0
                        | ecc_db_error_pd0_way1
                        | ecc_db_error_pd0_way2
                        | ecc_db_error_pd0_way3;

assign ecc_sb_error_pd0 = ecc_sb_error_pd0_way0
                        | ecc_sb_error_pd0_way1
                        | ecc_sb_error_pd0_way2
                        | ecc_sb_error_pd0_way3;

wire [`npuarc_MMU_PD0_SYNDROME_MSB:0]        syndrome_pd0_way0;
wire [`npuarc_MMU_PD0_SYNDROME_MSB:0]        syndrome_pd0_way1;
wire [`npuarc_MMU_PD0_SYNDROME_MSB:0]        syndrome_pd0_way2;
wire [`npuarc_MMU_PD0_SYNDROME_MSB:0]        syndrome_pd0_way3;
wire [`npuarc_MMU_PD1_SYNDROME_MSB:0]        syndrome_pd1;





//---------------------------------------------------------------------
// stlb signals
//---------------------------------------------------------------------

// stlb lookup port
reg                          stlb_req_valid_nxt;
reg                          stlb_req_valid_r;
reg                          stlb_rslt_valid_nxt;
reg                          stlb_rslt_valid_r;

// lookup for insert must use promiscuous match to detect any
// overlap with existing entries

// stlb rslt outputs
wire                         stlb_rslt_match;
wire                         stlb_rslt_miss;
wire [`npuarc_STLB_INDEX_RANGE]     stlb_rslt_match_index;
wire [`npuarc_STLB_INDEX_RANGE]     stlb_lru_match_index;
wire                         stlb_rslt_match_size;
wire                         stlb_rslt_multiple_match;
reg  [`npuarc_MMU_INDEX_IX_RANGE]   stlb_invlru_index;

wire [`npuarc_PD1_PPN_RANGE]        stlb_rslt_ppn;
wire [`npuarc_PD1_UA_RANGE]         stlb_rslt_user_attr;
wire                         stlb_rslt_wr_thru;
wire [`npuarc_PD1_PERM_RANGE]       stlb_rslt_perm;
wire                         stlb_rslt_cached;

// for jcmd_insert (if no match, replace lru or invalid entry)
reg                          stlb_rslt_match_r;
reg                          stlb_rslt_multiple_match_r;

reg  [`npuarc_MMU_INDEX_IX_RANGE]   stlb_match_index;

// for jtlb inval and replace ops
//--------------------------------
wire [`npuarc_STLB_ENTRIES_RANGE]   stlb_rslt_entry_match;
reg  [`npuarc_STLB_ENTRIES_RANGE]   stlb_rslt_entry_match_r;

// one-hot with only a single bit set (bit with the lowest index)
wire [`npuarc_STLB_ENTRIES_RANGE]   stlb_rslt_entry_match_1h;
reg  [`npuarc_STLB_ENTRIES_RANGE]   stlb_rslt_entry_match_1h_r;

// stlb LRU
wire [`npuarc_STLB_ENTRIES_RANGE]   stlb_rslt_entry_matchx_1h;
wire [`npuarc_STLB_ENTRIES_RANGE]   stlb_lru_match_entry;
wire                         stlb_en_lru_advance;

reg  [`npuarc_STLB_ENTRIES_RANGE]   stlb_invalidate_entries;
wire [`npuarc_STLB_ENTRIES_RANGE]   stlb_inval_entry_1h;


// uTLB Update / LRU logic
wire                         stlb_inval_entry_avail;
wire [`npuarc_STLB_ENTRIES_RANGE]   stlb_lru_entry_1h;
reg  [`npuarc_STLB_ENTRIES_RANGE]   stlb_entry_update_1h;

//wire                         stlb_inval_utlb;  // Inval all utlb entries


// Interface to read stlb entries
//
//wire                         stlb_entry_rd_val;  // rd data reg in jtlb
wire [`npuarc_PTE_RANGE]              stlb_entry_rd_data; // LR read data (entry)



reg                            tlb_eager_match;

wire [`npuarc_PTE_RANGE]              ntlb_entry_rd_data; // LR read data (entry)
wire [`npuarc_PTE_RANGE]              itlb_entry_rd_data; // LR read data (entry)
wire [`npuarc_PTE_RANGE]              dtlb_entry_rd_data; // LR read data (entry)

reg  [`npuarc_PTE_RANGE]              tlb_entry_rd_data;  // selected read data

//---------------------------------------------------------------------
// PD0, PD1 Fields
//
//---------------------------------------------------------------------
// pd1
wire [`npuarc_PD1_PPN_RANGE]       pd1_ppn_r;
wire [`npuarc_PD1_UA_RANGE]        pd1_user_attr_r;
wire                        pd1_wr_thru_r;
wire [`npuarc_PD1_PERM_RANGE]      pd1_perm_r;
wire                        pd1_cached_r;
// pd0
wire                        pd0_shared_r;
wire [`npuarc_PD0_VPN_FRANGE]      pd0_vpn_r;
wire                        pd0_lock_r;
wire                        pd0_size_r;
wire                        pd0_valid_r;
wire                        pd0_global_r;
wire [`npuarc_PD0_ASID_RANGE]      pd0_asid_r;

// pd1
assign pd1_ppn_r       = {aux_mmu_pd1_hi_r[`npuarc_PD1_PPN_HI_RANGE],
                             aux_mmu_pd1_r[`npuarc_PD1_PPN_LO_RANGE]};
assign pd1_user_attr_r = aux_mmu_pd1_r[`npuarc_PD1_UA_RANGE];
assign pd1_wr_thru_r   = aux_mmu_pd1_r[`npuarc_PD1_WR_THRU];
assign pd1_perm_r      = aux_mmu_pd1_r[`npuarc_PD1_PERM_RANGE];
assign pd1_cached_r    = aux_mmu_pd1_r[`npuarc_PD1_CACHED];

// pd0
assign pd0_shared_r    = aux_mmu_pd0_r[`npuarc_PD0_SHARED];
assign pd0_vpn_r       = aux_mmu_pd0_r[`npuarc_PD0_VPN_RANGE];
assign pd0_lock_r      = aux_mmu_pd0_r[`npuarc_PD0_LOCK];
assign pd0_size_r      = aux_mmu_pd0_r[`npuarc_PD0_SIZE];
assign pd0_valid_r     = aux_mmu_pd0_r[`npuarc_PD0_VALID];
assign pd0_global_r    = aux_mmu_pd0_r[`npuarc_PD0_GLOBAL];
assign pd0_asid_r      = aux_mmu_pd0_r[`npuarc_PD0_ASID_RANGE];

//---------------------------------------------------------------------
// PD0, PD1 Fields (2cyc)
//
//---------------------------------------------------------------------

assign aux_mmu_pd1_hi_rr = aux_mmu_pd1_hi_r;

assign aux_mmu_pd1_rr = aux_mmu_pd1_r;

assign aux_mmu_pd0_rr = aux_mmu_pd0_r;

wire                        pd0_size_rr;
wire                        pd0_global_rr;


// pd0
assign pd0_size_rr      = aux_mmu_pd0_rr[`npuarc_PD0_SIZE];
assign pd0_global_rr    = aux_mmu_pd0_rr[`npuarc_PD0_GLOBAL];

//---------------------------------------------------------------------
// Form the packed PTE from aux regs pd0, pd1 (unpacked)
// (used by TLBs as write / update data)
//---------------------------------------------------------------------

// packed entry with {PD1,PD0} fields (exclude reserved fields)
wire   [`npuarc_PCKD_PD1_RANGE]     pckd_pte_pd1;
wire   [`npuarc_PCKD_PD0_RANGE]     pckd_pte_pd0;

// Entry data used to write (aux) stlb from pd0,1
//
assign pckd_data_pte = 
  {pckd_pte_pd1,
   pckd_pte_pd0};

assign pckd_pte_pd1 = 
  { // pd1
    pd1_ppn_r,
    pd1_user_attr_r,
    pd1_wr_thru_r,
    pd1_perm_r,
    pd1_cached_r
   };

assign pckd_pte_pd0 = 
  { // pd0
    pd0_shared_r,
    pd0_vpn_r,
    pd0_lock_r,
    pd0_size_r,
    pd0_valid_r,
    pd0_global_r,
    pd0_asid_r
   };

// version of packed entry with page number bits below super page zeroed out;
// used for update data to uTLBs during insert command
wire   [`npuarc_PCKD_PTE_RANGE]     pckd_data_pte_sz1;
wire   [`npuarc_PCKD_PD1_RANGE]     pckd_pte_pd1_sz1;
wire   [`npuarc_PCKD_PD0_RANGE]     pckd_pte_pd0_sz1;

wire   [`npuarc_PD0_VPN_RANGE]      pd0_sz1pn_mask; //const
wire   [`npuarc_PD1_PPN_RANGE]      pd1_sz1pn_mask; //const

// spyglass disable_block W486
assign pd0_sz1pn_mask = {`npuarc_PD0_VPN_WIDTH{1'b1}} << (`npuarc_MMU_PAGE_SIZE_SEL1 - `npuarc_MMU_PAGE_SIZE_SEL0);
assign pd1_sz1pn_mask = {`npuarc_PD1_PPN_WIDTH{1'b1}} << (`npuarc_MMU_PAGE_SIZE_SEL1 - `npuarc_MMU_PAGE_SIZE_SEL0);
// spyglass enable_block W486

// Entry data used to insert (aux) utlbs from pd0,1
//
assign pckd_data_pte_sz1 = 
  {pckd_pte_pd1_sz1,
   pckd_pte_pd0_sz1};

assign pckd_pte_pd1_sz1 = 
  { // pd1
    pd1_ppn_r & pd1_sz1pn_mask, // trim insignificant ppn bits for super page
    pd1_user_attr_r,
    pd1_wr_thru_r,
    pd1_perm_r,
    pd1_cached_r
   };

assign pckd_pte_pd0_sz1 = 
  { // pd0
    pd0_shared_r,
    pd0_vpn_r & pd0_sz1pn_mask, // trim insignificant vpn bits for super page
    pd0_lock_r,
    pd0_size_r,
    pd0_valid_r,
    pd0_global_r,
    pd0_asid_r
   };

// If STLB present, the utlb update data has VPN bits below size1 zeroed out for
// super pages
reg   [`npuarc_PCKD_PTE_RANGE]     pckd_mskd_data_pte;

always @*
begin : pckd_mskd_data_pte_PROC
  if (pd0_size_r == `npuarc_STLB_PAGE_SIZE)
    pckd_mskd_data_pte = pckd_data_pte_sz1;
  else
    pckd_mskd_data_pte = pckd_data_pte;
end

//---------------------------------------------------------------------
// Current processor context
//
assign mmu_en_r    = aux_mmu_pid_t_r
                   ;
assign shared_en_r = aux_mmu_pid_s_rr;
assign asid_rr     = aux_mmu_pid_asid_rr;
assign asid_r      = aux_mmu_pid_asid_r;


assign sasid_r     = {aux_mmu_sls1_rr,
                      aux_mmu_sls0_rr};

wire   pd1_exec_perm;
assign pd1_exec_perm = aux_mmu_pd1_r[`npuarc_PD1_PERM_KX]
                     | aux_mmu_pd1_r[`npuarc_PD1_PERM_UX];

//---------------------------------------------------------------------

// leda W244 off
// LMD: Shift by non-constant
// LJ:  Simple 2-4 decoder
wire [`npuarc_NTLB_NUM_WAYS-1:0]      aux_mmu_index_ix_way_1h;
assign aux_mmu_index_ix_way_1h = 4'h1 << aux_mmu_index_ix_r[1:0];
// leda W244 on




// Aux addr for read/write
wire [`npuarc_STLB_INDEX_RANGE]     stlb_aux_index_r;
wire [`npuarc_STLB_INDEX_RANGE]     stlb_aux_index_rr;
reg  [`npuarc_STLB_ENTRIES_RANGE]   stlb_aux_index_1h;

assign stlb_aux_index_r  = aux_mmu_index_ix_r[`npuarc_STLB_INDEX_RANGE];
assign stlb_aux_index_rr = aux_mmu_index_ix_rr[`npuarc_STLB_INDEX_RANGE];

// one-hot decode of jcmd index for write
always @* 
begin :  i_stlb_ix_PROC
  stlb_aux_index_1h = `npuarc_MMU_STLB_NUM_ENTRIES'b0;
  stlb_aux_index_1h[stlb_aux_index_r] = 1'b1;
end

// select lowest invalid entry or lru entry, gen index
always @* 
begin :  i_stlb_invlru_index_PROC
  stlb_invlru_index  = IX_STLB_BASE;
  stlb_invlru_index[`npuarc_STLB_INDEX_RANGE] = Enc_stlb_rslt(stlb_inval_entry_avail ? 
                                                       stlb_inval_entry_1h :
                                                       stlb_lru_entry_1h);
end

// don't advance STLB lru state for probe and delete search results
assign stlb_en_lru_advance = ~(cmd_r_op_probe | cmd_r_op_delete | cmd_r_op_getix)
                           &   stlb_rslt_valid_r;

// qualified search result for STLB lru update
assign stlb_rslt_entry_matchx_1h = stlb_rslt_entry_match_1h_r
                                 & {`npuarc_MMU_STLB_NUM_ENTRIES{stlb_en_lru_advance}};

wire                           stlb_update;
assign                         stlb_update = 1'b0; // unused in stlb

reg                            stlb_write;
reg                            stlb_write_r;
reg                            stlb_read_nxt;
reg                            stlb_read_r;
reg                            stlb_insert;

wire [`npuarc_PCKD_PTE_RANGE]         pckd_stlb_pte;



//---------------------------------------------------------------------------
// MMU state machine
//---------------------------------------------------------------------------
//
reg [4:0] jsm_state_nxt;
reg [4:0] jsm_state_r;
reg [1:0] jtlb_lkup_sel_nxt;
reg [1:0] jtlb_lkup_sel_r;

//--------------------------------------------------------------------------
reg  [`npuarc_PD0_VPN_FRANGE]      jtlb_lkup_vpn_nxt;   // 18-sz0:0
reg                         jtlb_lkup_vpn_cg0;

// leda NTL_CON13A on
reg  [`npuarc_PD0_VPN_FRANGE]      jtlb_lkup_vpn_r;     // 18-sz0:0
wire [`npuarc_PD0_VPN_FRANGE]      jtlb_lkup_vpn_rr;
wire [`npuarc_PD0_VPN_FRANGE]      jtlb_lkup_vpn_rr2;

reg  [`npuarc_PD0_ASID_RANGE]      jtlb_req_asid;
wire [`npuarc_PD0_ASID_RANGE]      jtlb_req_asid_2cyc;

reg                         ntlb_rdwr_op;

reg  [`npuarc_NTLB_NUM_WAYS-1:0]      ntlb_lru_entry_1h_r;

//---------------------------------------------------------------------------
// NTLB signals
//---------------------------------------------------------------------------
//
// NTLB clock generation
//
reg                            ntlb_pd0_clken;
reg                            ntlb_pd0_ram_ph1;
reg                            ntlb_pd0_ram_ph2;
wire                           ntlb_pd0_ram_ph3;

assign  ntlb_pd0_ram_ph3 =   (~ntlb_pd0_ram_ph1)
                          && (~ntlb_pd0_ram_ph2);

reg                            ntlb_pd1_clken;
//reg                          ntlb_pd1_ram_ph1;

reg [`npuarc_NTLB_PD0_ADDR_MSB:0]     ntlb_tram_clr_cnt;
wire                           ntlb_tram_cleared;

// NTLB PD0 (tag) ram interface
//
reg  [1:0]                     ntlb_rd_way_sel;
wire [1:0]                     ntlb_out_way_sel;
//reg [`NTLB_PD0_DATA_MSB:0]   ntlb_pd0_wem; // (don't need bit level mask)
//reg                          ntlb_rdwr_op;
reg                            ntlb_pd0_rslt_valid_nxt;

// NTLB match logic
wire [`npuarc_NTLB_VPN_TAG_RANGE]     ntlb_req_vpn_tag_rr;// 2cyc tag portion ([n:0])
// reg  [`PD0_ASID_RANGE]         ntlb_req_asid;
// wire [`PD0_ASID_RANGE]         ntlb_req_asid_2cyc;

reg                            ntlb_rslt_match;

// leda NTL_CON12A off
// LMD: undriven internal net Range
// LJ:  index bits of ntlb ram not stored (unused bits of bus)
reg  [`npuarc_NTLB_PD0_WAY0_DATA_RANGE] ntlb_pd0_way_rdata; // selected 1 way
// leda NTL_CON12A on
  
// NTLB PD1 (data) ram interface
//


reg  [`npuarc_NTLB_NUM_WAYS-1:0]      ntlb_wdata_vbit_way; // valid bits
reg  [`npuarc_NTLB_NUM_WAYS-1:0]      ntlb_wdata_lbit_way; // lock bits

reg  [`npuarc_NTLB_NUM_WAYS-1:0]      ntlb_locked_entries; // rdata
wire                           ntlb_all_entries_locked;
reg  [`npuarc_NTLB_NUM_WAYS-1:0]      ntlb_invalid_entries;
wire [`npuarc_NTLB_NUM_WAYS-1:0]      ntlb_inval_entry_1h;
wire                           ntlb_inval_entry_avail;

wire [`npuarc_NTLB_WAY_PTR_RANGE]     ntlb_invlru_way;
reg  [`npuarc_NTLB_NUM_WAYS-1:0]      ntlb_lru_entry_1h_nxt;
//reg  [`NTLB_NUM_WAYS-1:0]      ntlb_lru_entry_1h_r;
reg  [`npuarc_NTLB_NUM_WAYS-1:0]      ntlb_lruu_entry_1h;
//reg                            ntlb_lru_advance;

wire [`npuarc_NTLB_NUM_WAYS-1:0]      ntlb_invlru_way_1h;
wire [`npuarc_NTLB_NUM_WAYS-1:0]      ntlb_insert_target_1h;

// declare registers for NTLB pd0 RAM

// pd0 (pre-mux, from sram): way 0
wire                           ntlb_out_way0_shared_nxt;
wire [`npuarc_NTLB_VPN_TAG_RANGE]     ntlb_out_way0_vpn_tag_nxt;
wire                           ntlb_out_way0_lock_nxt;
wire                           ntlb_out_way0_valid_nxt;
wire                           ntlb_out_way0_global_nxt;
wire [`npuarc_PD0_ASID_RANGE]         ntlb_out_way0_asid_nxt;

// pd0 (pre-mux, from sram): way 1
wire                           ntlb_out_way1_shared_nxt;
wire [`npuarc_NTLB_VPN_TAG_RANGE]     ntlb_out_way1_vpn_tag_nxt;
wire                           ntlb_out_way1_lock_nxt;
wire                           ntlb_out_way1_valid_nxt;
wire                           ntlb_out_way1_global_nxt;
wire [`npuarc_PD0_ASID_RANGE]         ntlb_out_way1_asid_nxt;

// pd0 (pre-mux, from sram): way 2
wire                           ntlb_out_way2_shared_nxt;
wire [`npuarc_NTLB_VPN_TAG_RANGE]     ntlb_out_way2_vpn_tag_nxt;
wire                           ntlb_out_way2_lock_nxt;
wire                           ntlb_out_way2_valid_nxt;
wire                           ntlb_out_way2_global_nxt;
wire [`npuarc_PD0_ASID_RANGE]         ntlb_out_way2_asid_nxt;

// pd0 (pre-mux, from sram): way 3
wire                           ntlb_out_way3_shared_nxt;
wire [`npuarc_NTLB_VPN_TAG_RANGE]     ntlb_out_way3_vpn_tag_nxt;
wire                           ntlb_out_way3_lock_nxt;
wire                           ntlb_out_way3_valid_nxt;
wire                           ntlb_out_way3_global_nxt;
wire [`npuarc_PD0_ASID_RANGE]         ntlb_out_way3_asid_nxt;


// NTLB Match Logic
wire [`npuarc_PCKD_PTE_RANGE]      pckd_ntlb_pte;

reg [`npuarc_NTLB_NUM_WAYS-1:0]    ntlb_rslt_pid_match;
reg [`npuarc_NTLB_NUM_WAYS-1:0]    ntlb_rslt_sasid_match;
reg [`npuarc_NTLB_NUM_WAYS-1:0]    ntlb_rslt_vpn_match;
reg [`npuarc_NTLB_NUM_WAYS-1:0]    ntlb_rslt_entry_match;
reg [`npuarc_NTLB_NUM_WAYS-1:0]    ntlb_rslt_entry_match_raw_1h;
reg [`npuarc_NTLB_WAY_PTR_RANGE]   ntlb_rslt_match_way;

reg                         ntlb_rslt_multiple_match;


assign ntlb_all_entries_locked = &(ntlb_locked_entries);


// mntlb : find lru unlocked entry
//
// spyglass disable_block W398 STARC05-2.8.1.3
// SMD: Possible case covered by multiple case statments.
// SJ:  ntlb_lru_entry_1h_r is one-hot
always @*
begin : ntlb_lruu_entry_1h_PROC

  casez (ntlb_lru_entry_1h_r) // one-hot

    4'b???1: ntlb_lruu_entry_1h = (    ntlb_all_entries_locked 
                                   || ~ntlb_locked_entries[0]) ? 4'b0001 :
                                      ~ntlb_locked_entries[1]  ? 4'b0010 :
                                      ~ntlb_locked_entries[2]  ? 4'b0100 :
                                                                 4'b1000 ;
    4'b??1?: ntlb_lruu_entry_1h = (    ntlb_all_entries_locked 
                                   || ~ntlb_locked_entries[1]) ? 4'b0010 :
                                      ~ntlb_locked_entries[2]  ? 4'b0100 :
                                      ~ntlb_locked_entries[3]  ? 4'b1000 :
                                                                 4'b0001 ;
    4'b?1??: ntlb_lruu_entry_1h = (    ntlb_all_entries_locked 
                                   || ~ntlb_locked_entries[2]) ? 4'b0100 :
                                      ~ntlb_locked_entries[3]  ? 4'b1000 :
                                      ~ntlb_locked_entries[0]  ? 4'b0001 :
                                                                 4'b0010 ;
    4'b1???: ntlb_lruu_entry_1h = (    ntlb_all_entries_locked 
                                   || ~ntlb_locked_entries[3]) ? 4'b1000 :
                                      ~ntlb_locked_entries[0]  ? 4'b0001 :
                                      ~ntlb_locked_entries[1]  ? 4'b0010 :
                                                                 4'b0100 ;
    default: ntlb_lruu_entry_1h = ntlb_lru_entry_1h_r;
  endcase
end
// spyglass enable_block W398 STARC05-2.8.1.3


assign ntlb_invlru_way_1h    = ntlb_inval_entry_avail ? 
                               ntlb_inval_entry_1h :
                               ntlb_lruu_entry_1h;

assign ntlb_insert_target_1h = ntlb_rslt_match ?
                               ntlb_rslt_entry_match_raw_1h :
                               ntlb_invlru_way_1h ;

assign ntlb_invlru_way = Enc_ntlb_rslt(ntlb_invlru_way_1h);


//---------------------------------------------------------------------------
// JTLB to uTLBs cmd/update signals (*_nxt)
//---------------------------------------------------------------------------
//
reg [`npuarc_JCMD_RANGE]              jtlb_itlb_cmd_nxt;
reg                            jrsp_itlb_update_hit_nxt;
reg                            jrsp_itlb_multi_hit_nxt;
reg                            jrsp_itlb_tlb_err_nxt;

reg [`npuarc_JCMD_RANGE]              jtlb_dtlb_cmd_nxt;
reg                            jrsp_dtlb_update_nxt; 
reg                            jrsp_dtlb_update_hit_nxt;
reg                            jrsp_dtlb_multi_hit_nxt;
reg                            jrsp_dtlb_tlb_err_nxt;

reg                            jtlb_cancel_update;

reg                            utlb_update_active_nxt;
reg                            utlb_update_active_r;

reg [`npuarc_UTLB_ENTRY_RANGE]        jtlb_update_data_nxt;
reg                            jtlb_update_data_cg0;

assign jtlb_itlb_index_r = aux_mmu_index_ix_rr[`npuarc_ITLB_INDEX_RANGE];
assign jtlb_dtlb_index_r = aux_mmu_index_ix_rr[`npuarc_DTLB_INDEX_RANGE];

// jtlb match 
//

// single match in either stlb or ntlb (not both)
assign jtlb_single_match =  (stlb_rslt_match_r & (~stlb_rslt_multiple_match_r))
                          ^ (ntlb_rslt_match   & (~ntlb_rslt_multiple_match  ));

// multiple match between both stlb and ntlb
assign jtlb_multiple_match =  (stlb_rslt_match_r & ntlb_rslt_match) 
                      |   ntlb_rslt_multiple_match 
                      |   stlb_rslt_multiple_match_r;


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Auxiliary registers, next state(value), read mux and write enable logic//
//                                                                        //
////////////////////////////////////////////////////////////////////////////

//---------------------------------------------------------------------------
// X3 stage (evaluate rd/wr/permissions)
//---------------------------------------------------------------------------
//
always @*
begin : mmu_aux_rdwr_PROC

  mmu_aux_k_rd        = 1'b0;
  mmu_aux_k_wr        = 1'b0;
  mmu_aux_unimpl      = 1'b1;
  mmu_aux_illegal     = 1'b0;
  mmu_aux_serial_sr   = 1'b0;
  mmu_aux_strict_sr   = 1'b0;

  if (aux_mmu_ren_r)  // mmu aux region selected
  begin
    
    case (aux_mmu_raddr_r)

    // non-serializing registers (rd/wr)
    //-----------------------------------

    // page descriptor 0
    AUX_ADDR_MMU_PD0[4:0]: // K_RW
    begin
      mmu_aux_k_rd    = 1'b1;
      mmu_aux_k_wr    = 1'b1;
      mmu_aux_unimpl  = 1'b0;
    end

    // page descriptor 1
    AUX_ADDR_MMU_PD1[4:0]: // K_RW
    begin
      mmu_aux_k_rd    = 1'b1;
      mmu_aux_k_wr    = 1'b1;
      mmu_aux_unimpl  = 1'b0;
    end

    // page descriptor 0 high
    AUX_ADDR_MMU_PD0_HI[4:0]: // K_RW  ...always unimplemented in this version
    begin
      mmu_aux_k_rd    = 1'b1;
      mmu_aux_k_wr    = 1'b1;
    end

    // page descriptor 1 high
    AUX_ADDR_MMU_PD1_HI[4:0]: // K_RW
    begin
      mmu_aux_k_rd    = 1'b1;
      mmu_aux_k_wr    = 1'b1;
      mmu_aux_unimpl  = 1'b0;
    end

    // index for aux access
    AUX_ADDR_MMU_INDEX[4:0]: // K_RW
    begin
      mmu_aux_k_rd    = 1'b1;
      mmu_aux_k_wr    = 1'b1;
      mmu_aux_unimpl  = 1'b0;
    end

    // registers with serializing write
    //----------------------------------

    AUX_ADDR_MMU_CMD[4:0]: // K_WRITE
    begin
      mmu_aux_illegal = aux_read;
      mmu_aux_k_wr    = 1'b1;
      mmu_aux_strict_sr = aux_write; // cmd wr is serializing
      mmu_aux_unimpl  = 1'b0;
    end

    // Process ID register
    AUX_ADDR_MMU_PID[4:0]: // K_RW
    begin
      mmu_aux_k_rd    = 1'b1;
      mmu_aux_k_wr    = 1'b1;
      mmu_aux_strict_sr = aux_write; // pid wr is serializing
      mmu_aux_unimpl  = 1'b0;
    end

    // Shared lib subscriptions 0
    AUX_ADDR_MMU_SLS0[4:0]: // K_RW
    begin
      mmu_aux_k_rd    = 1'b1;
      mmu_aux_k_wr    = 1'b1;
      mmu_aux_strict_sr = aux_write; // sls0 wr is serializing
      mmu_aux_unimpl  = 1'b0;
    end

    // Shared lib subscriptions 1
    AUX_ADDR_MMU_SLS1[4:0]: // K_RW
    begin
      mmu_aux_k_rd    = 1'b1;
      mmu_aux_k_wr    = 1'b1;
      mmu_aux_strict_sr = aux_write; // sls1 wr is serializing
      mmu_aux_unimpl  = 1'b0;
    end

    // non-serializing registers (rd/wr)
    //-----------------------------------

    // scratch rd/wr register 0
    AUX_ADDR_MMU_SCRATCH0[4:0]: // K_RW
    begin
      mmu_aux_k_rd    = 1'b1;
      mmu_aux_k_wr    = 1'b1;
      mmu_aux_unimpl  = 1'b0;
    end

    default:
    begin
      // reg at address aux_mmu_raddr_r is not implemented in mmu
      mmu_aux_unimpl  = 1'b1;
    end

    endcase
  end

end

//---------------------------------------------------------------------------
// X3 stage read mux
//---------------------------------------------------------------------------
//
always @*
begin : mmu_aux_rd_mux_PROC

//mmu_aux_rdata       = `DATA_SIZE'd0;
  mmu_aux_rdata       = aux_mmu_pd0_r; // default mux input
  mmu_aux_index_ecc_e = (hw_mmu_index_e_nxt & (ecc_db_error_pd0_r | ecc_db_error_pd1_r)) & (~ecc_mmu_disable);
  case (aux_mmu_raddr_r)

  // page descriptor 0
  AUX_ADDR_MMU_PD0[4:0]: // K_RW
  begin
    mmu_aux_rdata   = aux_mmu_pd0_r 
                    ;
  end

  // page descriptor 1
  AUX_ADDR_MMU_PD1[4:0]: // K_RW
  begin
    mmu_aux_rdata   = aux_mmu_pd1_r
                    & 32'hfffff07f; // mask rsvd
  end

  AUX_ADDR_MMU_PD0_HI[4:0]: // K_RW  ...always unimplemented in this version
  begin
    mmu_aux_rdata   = 32'd0; // aux_mmu_pd0_hi_r;
  end

  AUX_ADDR_MMU_PD1_HI[4:0]: // K_RW
  begin
    mmu_aux_rdata   = {24'h0,aux_mmu_pd1_hi_r};
  end

  // index for aux access
  AUX_ADDR_MMU_INDEX[4:0]: // K_RW
  begin
    mmu_aux_rdata                      = `npuarc_DATA_SIZE'd0;
    mmu_aux_rdata[`npuarc_MMU_INDEX_ERROR]    = aux_mmu_index_e_r;
    mmu_aux_rdata[`npuarc_MMU_INDEX_RC_RANGE] = aux_mmu_index_rc_r;
    mmu_aux_rdata[`npuarc_MMU_INDEX_IX_RANGE] = aux_mmu_index_ix_r;
  end

  // cmd reg read returns 0
  AUX_ADDR_MMU_CMD[4:0]: // K_RW
  begin
    mmu_aux_rdata       = `npuarc_DATA_SIZE'd0;
  end

  // Process ID register
  AUX_ADDR_MMU_PID[4:0]: // K_RW
  begin
    mmu_aux_rdata                      = `npuarc_DATA_SIZE'd0;
    mmu_aux_rdata[`npuarc_MMU_PID_ASID_RANGE] = aux_mmu_pid_asid_r;
    mmu_aux_rdata[`npuarc_MMU_PID_S]          = aux_mmu_pid_s_r;
//  mmu_aux_rdata[`MMU_PID_EP]         = aux_mmu_pid_ep_r;
    mmu_aux_rdata[`npuarc_MMU_PID_T]          = aux_mmu_pid_t_r;
  end

  // Shared lib subscriptions 0
  AUX_ADDR_MMU_SLS0[4:0]: // K_RW
  begin
    mmu_aux_rdata[`npuarc_MMU_SLS_RANGE] = aux_mmu_sls0_r;
  end

  // Shared lib subscriptions 1
  AUX_ADDR_MMU_SLS1[4:0]: // K_RW
  begin
    mmu_aux_rdata[`npuarc_MMU_SLS_RANGE] = aux_mmu_sls1_r;
  end



  // non-serializing registers (rd/wr)
  //-----------------------------------

  // scratch rd/wr register 0
  AUX_ADDR_MMU_SCRATCH0[4:0]: // K_RW
  begin
    mmu_aux_rdata   = aux_mmu_scratch0_r;
  end

  default:
  begin
    mmu_aux_rdata   = aux_mmu_pd0_r;
  end

  endcase

end // block: mmu_aux_rd_mux_PROC


//---------------------------------------------------------------------------
// AUX write logic : WA stage (perform write)
//---------------------------------------------------------------------------
//
always @*
begin : mmu_aux_wr_PROC

  aux_mmu_pd0_wen      = 1'b0;
  aux_mmu_pd1_wen      = 1'b0;
  aux_mmu_pd1_hi_wen   = 1'b0;
  aux_mmu_index_wen    = 1'b0;
  aux_mmu_cmd_wen      = 1'b0;
  aux_mmu_pid_wen      = 1'b0;
  aux_mmu_sls0_wen     = 1'b0;
  aux_mmu_sls1_wen     = 1'b0;
  aux_mmu_scratch0_wen = 1'b0;

  aux_mmu_pd0_nxt      = 32'h0;
  aux_mmu_pd1_nxt      = 32'h0;
  aux_mmu_pd1_hi_nxt   = 8'h0;
  aux_mmu_index_rc_nxt = `npuarc_MMU_INDEX_RC_WIDTH'h0;
  aux_mmu_index_ix_nxt = `npuarc_MMU_INDEX_IX_WIDTH'h0;

  aux_mmu_cmd_nxt      = `npuarc_MMU_CMD_CMD_WIDTH'h0;

  aux_mmu_pid_asid_nxt = `npuarc_MMU_PID_ASID_WIDTH'h0;
  aux_mmu_pid_s_nxt    = 1'b0;
  aux_mmu_pid_t_nxt    = 1'b0;

  aux_mmu_sls0_nxt     = 32'h0;
  aux_mmu_sls1_nxt     = 32'h0;
  aux_mmu_scratch0_nxt = 32'h0;

  // don't allow writes in user mode unless debug host op
  //
  if (aux_mmu_wen_r && (kernel_mode | debug_op))
  begin
    
    case (aux_mmu_waddr_r)

    AUX_ADDR_MMU_PD0[4:0]: // K_RW
    begin
      aux_mmu_pd0_wen                  = 1'b1;
      
      aux_mmu_pd0_nxt                  = 32'b0;
      aux_mmu_pd0_nxt[`npuarc_PD0_SHARED]     = aux_wdata[`npuarc_PD0_SHARED];
      aux_mmu_pd0_nxt[`npuarc_PD0_VPN_RANGE]  = aux_wdata[`npuarc_PD0_VPN_RANGE];
      aux_mmu_pd0_nxt[`npuarc_PD0_SIZE]       = aux_wdata[`npuarc_PD0_SIZE];    
      aux_mmu_pd0_nxt[`npuarc_PD0_VALID]      = aux_wdata[`npuarc_PD0_VALID];
      aux_mmu_pd0_nxt[`npuarc_PD0_GLOBAL]     = aux_wdata[`npuarc_PD0_GLOBAL];
      aux_mmu_pd0_nxt[`npuarc_PD0_ASID_RANGE] = aux_wdata[`npuarc_PD0_ASID_RANGE];
    end

    AUX_ADDR_MMU_PD1[4:0]: // K_RW
    begin
      aux_mmu_pd1_wen                     = 1'b1;
      
      aux_mmu_pd1_nxt                     = 32'b0;
      aux_mmu_pd1_nxt[`npuarc_PD1_PPN_LO_RANGE]  = aux_wdata [`npuarc_PD1_PPN_LO_RANGE];
      aux_mmu_pd1_nxt[`npuarc_PD1_PERM_RANGE]    = aux_wdata [`npuarc_PD1_PERM_RANGE];
      aux_mmu_pd1_nxt[`npuarc_PD1_CACHED]        = aux_wdata [`npuarc_PD1_CACHED];
    end

    AUX_ADDR_MMU_PD1_HI[4:0]: // K_RW
    begin
      aux_mmu_pd1_hi_wen = 1'b1;
      aux_mmu_pd1_hi_nxt = aux_wdata[7:0];
    end

    AUX_ADDR_MMU_INDEX[4:0]: // K_RW
    begin
      aux_mmu_index_wen = 1'b1;
      aux_mmu_index_rc_nxt = aux_wdata[`npuarc_MMU_INDEX_RC_RANGE];
      aux_mmu_index_ix_nxt = aux_wdata[`npuarc_MMU_INDEX_IX_RANGE];
    end

    AUX_ADDR_MMU_CMD[4:0]: // K_WRITE
    begin
      aux_mmu_cmd_wen = 1'b1;
      aux_mmu_cmd_nxt = aux_wdata[`npuarc_MMU_CMD_CMD_RANGE];
    end

    // registers with serializing write
    //----------------------------------

    // Process ID register
    AUX_ADDR_MMU_PID[4:0]: // K_RW
    begin
      aux_mmu_pid_wen = 1'b1;
      aux_mmu_pid_asid_nxt = aux_wdata[`npuarc_MMU_PID_ASID_RANGE];
      aux_mmu_pid_s_nxt    = aux_wdata[`npuarc_MMU_PID_S];
      aux_mmu_pid_t_nxt    = aux_wdata[`npuarc_MMU_PID_T];
    end

    // Shared lib subscriptions 0
    AUX_ADDR_MMU_SLS0[4:0]: // K_RW
    begin
      aux_mmu_sls0_wen = 1'b1;
      aux_mmu_sls0_nxt = aux_wdata;
    end

    // Shared lib subscriptions 1
    AUX_ADDR_MMU_SLS1[4:0]: // K_RW
    begin
      aux_mmu_sls1_wen = 1'b1;
      aux_mmu_sls1_nxt = aux_wdata;
    end


    AUX_ADDR_MMU_SCRATCH0[4:0]: // K_RW
    begin
      aux_mmu_scratch0_wen = 1'b1;
      aux_mmu_scratch0_nxt = aux_wdata;
    end

    default:
    begin
      // (already in default assigns, kept for lint)
      aux_mmu_cmd_wen      = 1'b0;
    end
    endcase
  end

end // block: mmu_reg_wr_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining MMU auxiliary registers: addr, data         //
//                                                                        //
////////////////////////////////////////////////////////////////////////////


// PD0
wire   mmu_pd0_cg0;
assign mmu_pd0_cg0 = mmu_pd0_wen | ca_tlb_miss_excpn;

always @(posedge clk or posedge rst_a)
begin : mmu_aux_pd0_PROC
  if (rst_a == 1'b1)
  begin
    aux_mmu_pd0_r        <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else if (mmu_pd0_cg0)
  begin
    // pd0 may be written by aux or MMU hardware
    aux_mmu_pd0_r <= ca_tlb_miss_excpn ?
                         // capture miss address from excpn pipe
                         {1'b0, // shared
                          ca_tlb_miss_efa,
                          1'b0, // Rsvd
                          1'b0, // Size
                          1'b1, // Valid
                          1'b0, // Global
                          aux_mmu_pid_asid_r
                          } :
                         // capture (TLB index) read cmd data
                         (aux_mmu_pd0_wen ? aux_mmu_pd0_nxt : hw_mmu_pd0_nxt);
  end
end


// PD1
always @(posedge clk or posedge rst_a)
begin : mmu_aux_pd1_PROC
  if (rst_a == 1'b1)
  begin
    aux_mmu_pd1_r        <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else if (mmu_pd1_wen)
  begin
    // pd1 may be written by aux or MMU hardware
    aux_mmu_pd1_r <= aux_mmu_pd1_wen ? aux_mmu_pd1_nxt : hw_mmu_pd1_nxt;
  end
end


// PD1 HI
always @(posedge clk or posedge rst_a)
begin : aux_mmu_pd1_hi_PROC
  if (rst_a == 1'b1)
  begin
    aux_mmu_pd1_hi_r     <= {8{1'b0}};
  end
  else if (mmu_pd1_hi_wen)
  begin
    // pd1_hi may be written by aux or MMU hardware
    aux_mmu_pd1_hi_r <= aux_mmu_pd1_hi_wen ? aux_mmu_pd1_hi_nxt : hw_mmu_pd1_hi_nxt;
  end
end



// index
always @(posedge clk or posedge rst_a)
begin : aux_mmu_index_PROC
  if (rst_a == 1'b1) begin
    aux_mmu_index_e_r    <= 1'b0;
    aux_mmu_index_rc_r   <= {`npuarc_MMU_INDEX_RC_WIDTH{1'b0}};
    aux_mmu_index_ix_r   <= {`npuarc_MMU_INDEX_IX_WIDTH{1'b0}};
  end
  else if (mmu_index_wen) begin
    // index may be written by aux or MMU hardware
    aux_mmu_index_e_r  <= aux_mmu_index_wen ? aux_mmu_index_e_r    : hw_mmu_index_e_nxt;  // ignore write
    aux_mmu_index_rc_r <= aux_mmu_index_wen ? aux_mmu_index_rc_r   : hw_mmu_index_rc_nxt; // ignore write
    aux_mmu_index_ix_r <= aux_mmu_index_wen ? aux_mmu_index_ix_nxt : hw_mmu_index_ix_nxt;
  end
end


// command
always @(posedge clk or posedge rst_a)
begin : aux_mmu_cmd_PROC
  if (rst_a == 1'b1) begin
    aux_mmu_cmd_r        <= {`npuarc_MMU_CMD_CMD_WIDTH{1'b0}};
  end
  else if (mmu_cmd_wen) begin
  // cmd reg is read-only but cmd stored for mmu hw use (cleared by hw when done)
    aux_mmu_cmd_r <= mmu_cmd_nxt;
  end
end //mmu_@@@_PROC


// pid
always @(posedge clk or posedge rst_a)
begin : aux_mmu_pid_PROC
  if (rst_a == 1'b1)
  begin
    aux_mmu_pid_asid_r   <= {`npuarc_MMU_PID_ASID_WIDTH{1'b0}};
    aux_mmu_pid_s_r      <= 1'b0;
  end
  else if (aux_mmu_pid_wen) begin            // aux write of pid reg
    aux_mmu_pid_asid_r <= aux_mmu_pid_asid_nxt;
    aux_mmu_pid_s_r    <= aux_mmu_pid_s_nxt;
  end
end


// pid.t
always @(posedge clk or posedge rst_a)
begin : aux_mmu_pid_t_PROC
  if (rst_a == 1'b1)
    aux_mmu_pid_t_r      <= 1'b0;
  else if (aux_mmu_pid_wen | ca_m_chk_excpn) // aux write of pid reg
    // mchk overrides aux wr (disables mmu)
    aux_mmu_pid_t_r    <= aux_mmu_pid_t_nxt & (~ca_m_chk_excpn);
end


// sls0
always @(posedge clk or posedge rst_a)
begin : aux_mmu_sls0_PROC
  if (rst_a == 1'b1)
    aux_mmu_sls0_r   <= {`npuarc_DATA_SIZE{1'b0}};
  else if (aux_mmu_sls0_wen)               // aux write of sls0 reg
    aux_mmu_sls0_r <= aux_mmu_sls0_nxt;
end

// sls1
always @(posedge clk or posedge rst_a)
begin : aux_mmu_sls1_PROC
  if (rst_a == 1'b1)
    aux_mmu_sls1_r   <= {`npuarc_DATA_SIZE{1'b0}};
  else if (aux_mmu_sls1_wen)               // aux write of sls1 reg
    aux_mmu_sls1_r <= aux_mmu_sls1_nxt;
end



// scratch0
always @(posedge clk or posedge rst_a)
begin : aux_mmu_scratch0_PROC
  if (rst_a == 1'b1)
    aux_mmu_scratch0_r   <= {`npuarc_DATA_SIZE{1'b0}};
  else if (aux_mmu_scratch0_wen)           // aux write of scratch0 reg
    aux_mmu_scratch0_r <= aux_mmu_scratch0_nxt;
end //mmu_@@@_PROC




////////////////////////////////////////////////////////////////////////////
//                                                                        //
// AUX Index decode, addressing TLBs/RAMs                                 //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

reg  aux_ix_ntlb_sel;
reg  aux_ix_stlb_sel;
reg  aux_ix_itlb_sel;
reg  aux_ix_dtlb_sel;

always @*
begin : mmu_index_dec_PROC

  aux_ix_ntlb_sel = 1'b0;
  aux_ix_stlb_sel = 1'b0;
  aux_ix_itlb_sel = 1'b0;
  aux_ix_dtlb_sel = 1'b0;

  if (aux_mmu_index_ix_r < IX_NTLB_END)
  begin
    aux_ix_ntlb_sel = 1'b1;
  end
  else if (   (aux_mmu_index_ix_r >= IX_STLB_BASE)
            & (aux_mmu_index_ix_r <  IX_STLB_END))
  begin
    aux_ix_stlb_sel = 1'b1;
  end
  else if (  (aux_mmu_index_ix_r >= IX_ITLB_BASE)
           & (aux_mmu_index_ix_r <  IX_ITLB_END))
  begin
    aux_ix_itlb_sel = 1'b1;
  end
  else if (  (aux_mmu_index_ix_r >= IX_DTLB_BASE)
           & (aux_mmu_index_ix_r <  IX_DTLB_END))
  begin
    aux_ix_dtlb_sel = 1'b1;
  end
end


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Read/write, lookup datapaths                                           //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

// Mux to Read TLB entry (-> pd0,pd1) 
//------------------------------------
parameter RD_SEL_NTLB = 3'h0;
parameter RD_SEL_STLB = 3'h1;
parameter RD_SEL_ITLB = 3'h2;
parameter RD_SEL_DTLB = 3'h3;
parameter RD_SEL_ZERO = 3'h4;

reg  [2:0] jtlb_rd_sel_nxt;
reg  [2:0] jtlb_rd_sel_r;
wire [2:0] jtlb_rd_sel_rr;

assign jtlb_rd_sel_rr = jtlb_rd_sel_r;

always @*
begin : jtlb_rd_sel_PROC
  case (jtlb_rd_sel_rr)
    RD_SEL_NTLB: tlb_entry_rd_data = ntlb_entry_rd_data;
    RD_SEL_STLB: tlb_entry_rd_data = stlb_entry_rd_data;
    RD_SEL_ITLB: tlb_entry_rd_data = itlb_entry_rd_data;
    RD_SEL_DTLB: tlb_entry_rd_data = dtlb_entry_rd_data;
    RD_SEL_ZERO: tlb_entry_rd_data = `npuarc_PTE_WIDTH'd0;
    default:     tlb_entry_rd_data = `npuarc_PTE_WIDTH'd0;
  endcase
end


// Mux vpn/asid for lookups
//------------------------------
parameter ADDR_SEL_NONE = 2'h0;
parameter ADDR_SEL_PD   = 2'h1;
parameter ADDR_SEL_ITLB = 2'h2;
parameter ADDR_SEL_DTLB = 2'h3;

// jtlb lookup address (VPN) mux (index-1cyc, tag->2cyc)
// (used by ntlb, stlb)
always @*
begin : jtlb_lkup_vpn_sel_PROC

  case (jtlb_lkup_sel_nxt)

    ADDR_SEL_NONE,
    ADDR_SEL_PD:   
      jtlb_lkup_vpn_nxt  = pd0_vpn_r; // pd0 vpn (30:12+sz0)

    ADDR_SEL_ITLB:
      jtlb_lkup_vpn_nxt = itlb_update_req_vpn;

    ADDR_SEL_DTLB:
      jtlb_lkup_vpn_nxt = dtlb_update_req_vpn;

  endcase
end

// cancel utlb update
//
reg  wa_jtlb_cancel_r;

always @(posedge clk or posedge rst_a)
begin : wa_jtlb_cancel_PROC
  if (rst_a == 1'b1)
  begin
    wa_jtlb_cancel_r <= 1'b0;
  end
  else
  begin
    wa_jtlb_cancel_r <= wa_jtlb_cancel;
  end
end

always @*
begin : jtlb_cancel_update_PROC
  if (jtlb_lkup_sel_r == ADDR_SEL_ITLB)
    // itlb has abandoned update request due to an IFU restart
    jtlb_cancel_update = ~itlb_update_req;
  else
    // dtlb has abandoned update due to a (non-int-uop) wa_restart
    jtlb_cancel_update = wa_jtlb_cancel_r;
//  | ((jtlb_lkup_sel_r == ADDR_SEL_DTLB) & (~dtlb_update_req))
end


// ASID used in match logic in ntlb, stlb (2cyc)
//
always @*
begin : jtlb_lkup_asid_sel_PROC

  case (jtlb_lkup_sel_r)

    ADDR_SEL_NONE,
    ADDR_SEL_PD:   
    begin
      // aux cmd lookups use pd0.asid
      jtlb_req_asid   = pd0_asid_r;
// `if (`MMU_STLB_NUM_ENTRIES > 0)
//       stlb_req_asid   = pd0_asid_r;
// `endif
    end
     // lookup asid is pid.asid for utlb updates
    default:
    begin
      jtlb_req_asid   = aux_mmu_pid_asid_r;
// `if (`MMU_STLB_NUM_ENTRIES > 0)
//       stlb_req_asid   = aux_mmu_pid_asid_r;
// `endif
    end

  endcase
end

// selected req asid to match logic is 2 cycle 
//
assign jtlb_req_asid_2cyc = jtlb_req_asid;

// `if (`MMU_STLB_NUM_ENTRIES > 0)
// alb_2cyc_checker #(.WIDTH(`PD0_ASID_WIDTH)) u_alb_2cyc_checker_stlb_req_asid (
//   .data_in  (stlb_req_asid),
//   .data_out (stlb_req_asid_2cyc),
//   .clk      (clk));

// `endif

// selected req vpn to stlb lookup is 2 cycle 
//
assign jtlb_lkup_vpn_rr2 = jtlb_lkup_vpn_r;

// selected req vpn to match logic is 3 cycle 
//
assign jtlb_lkup_vpn_rr = jtlb_lkup_vpn_r;

// extract tag bits from request VPN
assign ntlb_req_vpn_tag_rr = jtlb_lkup_vpn_rr[`npuarc_PD0_VPN_FLD_MSB:      // 19-sz0
                                              `npuarc_NTLB_PD0_ADDR_WIDTH]; // 8,7,6 (trim index)

// Mux for ntlb pd0 ram address : lookup / aux / init address
//  1. Tag ram index counter for initializing ram (clear valid bits, whole word actually)
always @*
begin : ntlb_lkup_sel_PROC
  if ((jsm_state_r == JSM_RESET) || (jsm_state_r == JSM_INIT))
  begin
    ntlb_pd0_addr = ntlb_tram_clr_cnt;
  end
  else if (ntlb_rdwr_op)
  begin
    ntlb_pd0_addr = aux_mmu_index_ix_r[`npuarc_NTLB_PD0_ADDR_MSB+2:2];
  end
  else
  begin
    ntlb_pd0_addr = jtlb_lkup_vpn_nxt[`npuarc_NTLB_PD0_ADDR_MSB:0]; // index part
  end
end

// For probe and getindex commands, form the index reg field from match indexes
//------------------------------------------------------------------------------
always @*
begin : lkup_rslt_ix_PROC
  // NTLB
  ntlb_invlru_index = `npuarc_MMU_INDEX_IX_WIDTH'd0;
  ntlb_match_index = `npuarc_MMU_INDEX_IX_WIDTH'd0;

  // when not matched
  ntlb_invlru_index[`npuarc_NTLB_PD0_ADDR_WIDTH + `npuarc_NTLB_WAY_PTR_WIDTH - 1:0] =
                      {jtlb_lkup_vpn_rr[`npuarc_NTLB_PD0_ADDR_MSB:0],
                       ntlb_invlru_way};
  // when matched
  ntlb_match_index[`npuarc_NTLB_PD0_ADDR_WIDTH + `npuarc_NTLB_WAY_PTR_WIDTH - 1:0] =
                      {jtlb_lkup_vpn_rr[`npuarc_NTLB_PD0_ADDR_MSB:0],
                      ntlb_rslt_match_way}; // selected way; crit path
  // STLB
  stlb_match_index = `npuarc_MMU_INDEX_IX_WIDTH'd0;
  stlb_match_index[`npuarc_STLB_INDEX_RANGE] =  stlb_rslt_match_index;

end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Tasks of Combinational logic supporting the main jtlb FSM              //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

// Initiate write in ntlb
//-----------------------------

// Initiate read in ntlb
//-----------------------------

// Initiate lookup in ntlb (access pd0 only)
//------------------------------------------




//

// Report status/error, result code
//

// Invalidate entry(ies) in utlbs on write command
//


// Reset LRU state of ANTLB, STLB
//

// Evaluate ntlb/stlb matches and update TLBIndex aux reg
// (for probe, delete commands; on 'err', index.ix -> 0)
//

//-----------------------------------------------------------------------------
// In ARB state or any utlb-update state, begin aux command processing when
// cmd reg written or cmd pending (non-zero cmd reg)
//-----------------------------------------------------------------------------
//


// leda W427 on

//---------------------------------------------------------------------------
// Main MMU JTLB state machine comb logic
//---------------------------------------------------------------------------

always @*
begin : mmu_fsm_PROC

  // Default assignments
  //---------------------
  jsm_state_nxt         = jsm_state_r; // stay in current state
  cmd_reg_clr           = 1'b0;

  hw_mmu_index_ix_nxt   = aux_mmu_index_ix_r;
  hw_mmu_index_rc_nxt   = {`npuarc_MMU_INDEX_RC_WIDTH{1'b0}};
  hw_mmu_index_e_nxt    = 1'b0;
  hw_mmu_index_wen      = 1'b0;

  ecc_mmu_sbe_count_set_cg0 = 1'b0;
  dtlb_syndrome_set_cg0     = 1'b0;
  dtlb_syndrome_set_cg1     = 1'b0;
  fs_dtlb_bank0_syndrome_nxt= fs_dtlb_bank0_syndrome_r; 
  fs_dtlb_bank1_syndrome_nxt= fs_dtlb_bank1_syndrome_r; 
  fs_dtlb_bank2_syndrome_nxt= fs_dtlb_bank2_syndrome_r; 
  fs_dtlb_bank3_syndrome_nxt= fs_dtlb_bank3_syndrome_r; 
  fs_dtlb_bank4_syndrome_nxt= fs_dtlb_bank4_syndrome_r;
      
  itlb_syndrome_set_cg0     = 1'b0;
  itlb_syndrome_set_cg1     = 1'b0;
  fs_itlb_bank0_syndrome_nxt= fs_itlb_bank0_syndrome_r;
  fs_itlb_bank1_syndrome_nxt= fs_itlb_bank1_syndrome_r;
  fs_itlb_bank2_syndrome_nxt= fs_itlb_bank2_syndrome_r;
  fs_itlb_bank3_syndrome_nxt= fs_itlb_bank3_syndrome_r;
  fs_itlb_bank4_syndrome_nxt= fs_itlb_bank4_syndrome_r;
  // pd0,1 next value (read data)
  {hw_mmu_pd1_hi_nxt, hw_mmu_pd1_nxt, 
   hw_mmu_pd0_nxt}      = tlb_entry_rd_data;
  hw_mmu_pd0_wen        = 1'b0;
  hw_mmu_pd1_wen        = 1'b0;
  jtlb_rd_sel_nxt       = jtlb_rd_sel_r;

  // expand span of search to super page if aux pte pd0.sz=1, and 
  // global if pd0.g=1
  if (  cmd_rr_op_insert
      | cmd_rr_op_delete
     )
    tlb_eager_match    = 1'b1;
  else
    tlb_eager_match    = 1'b0;

  // stlb
  stlb_write            = 1'b0;
  stlb_insert           = 1'b0;
  stlb_read_nxt         = 1'b0;
  stlb_req_valid_nxt    = 1'b0;
  stlb_rslt_valid_nxt   = 1'b0;
  stlb_invalidate_entries = `npuarc_MMU_STLB_NUM_ENTRIES'd0;
  stlb_reset_lru_nxt  = 1'b0;

  jtlb_lkup_sel_nxt     = jtlb_lkup_sel_r;
  jtlb_lkup_vpn_cg0     = 1'b0;

  ntlb_rdwr_op          = 1'b0;

  // ntlb tag (pd0) memory
  ntlb_pd0_clken        = 1'b0;
  ntlb_pd0_ce           = 1'b0;
  ntlb_pd0_we           = 1'b0;
  ntlb_pd0_wem          = aux_mmu_index_ix_way_1h;
  ntlb_rd_way_sel       = aux_mmu_index_ix_rr[1:0];
  ntlb_wdata_vbit_way   = {`npuarc_NTLB_NUM_WAYS{1'b0}};
  ntlb_wdata_lbit_way   = {`npuarc_NTLB_NUM_WAYS{1'b0}};
//ntlb_rdwr_op          = 1'b0;
  ntlb_pd0_rslt_valid_nxt = 1'b0;
  ntlb_lru_entry_1h_nxt   = ntlb_lru_entry_1h_r;
//  ntlb_lru_advance        = 1'b0;
  mntlb_reset_lru_nxt     = 1'b0;

  // ntlb data (pd1) memory
  ntlb_pd1_clken        = 1'b0;
  ntlb_pd1_ce           = 1'b0;
  ntlb_pd1_we           = 1'b0;
  ntlb_pd1_addr         = aux_mmu_index_ix_r[`npuarc_NTLB_PD1_ADDR_MSB:0];

  // itlb
  jtlb_itlb_cmd_nxt         = `npuarc_JCMD_IDLE;
  jrsp_itlb_update_nxt      = 1'b0; 
  jrsp_itlb_update_hit_nxt  = 1'b0;
  jrsp_itlb_multi_hit_nxt   = jtlb_multiple_match;
  jrsp_itlb_tlb_err_nxt     = 1'b0;
  // dtlb
  jtlb_dtlb_cmd_nxt         = `npuarc_JCMD_IDLE;
  jrsp_dtlb_update_nxt      = 1'b0; 
  jrsp_dtlb_update_hit_nxt  = 1'b0;
  jrsp_dtlb_multi_hit_nxt   = jtlb_multiple_match;

  jrsp_dtlb_tlb_err_nxt     = 1'b0;

  utlb_update_active_nxt    = 1'b0;

  // form update data to uTLBs
  jtlb_update_data_cg0    = 1'b0;

  // default update data pd0/1
  jtlb_update_data_nxt    = pckd_mskd_data_pte;

  if (utlb_update_active_r)
  begin
    if ( 1'b0
        | (jsm_state_r == JSM_UTLB_MISS3)
        | (jsm_state_r == JSM_UTLB_MISS4)
       )
      jtlb_update_data_nxt  = pckd_ntlb_pte;
    else
      jtlb_update_data_nxt  = pckd_stlb_pte;
  end


  case (jsm_state_r) // JSM Next State <<<<<<<>>>>>>>

  //-------------------------------------------------------------------------
  JSM_RESET:  // skip init if rst_init_disable_r (aid debug)
  //-------------------------------------------------------------------------
  begin
    if (~rst_init_disable_r)
      jsm_state_nxt = JSM_INIT;
    else
      jsm_state_nxt = JSM_ARB;
  end

  //-------------------------------------------------------------------------
  JSM_INIT:  // first clear ntlb tag ram 
  //-------------------------------------------------------------------------
  begin
    ntlb_pd0_clken      = ntlb_pd0_ram_ph3; // en ntlb clk on ph3 (not ph1/2)
    ntlb_pd0_ce         = 1'b1;             // (access every third clock)
    ntlb_pd0_we         = 1'b1;
    ntlb_pd0_wem        = 4'hf;
    if (ntlb_tram_cleared)
      jsm_state_nxt = JSM_ARB;
  end

  //-------------------------------------------------------------------------
  JSM_ARB:
  //-------------------------------------------------------------------------
  begin
    // start AUX command or update operation when finished with any update
    if (  (~jrsp_itlb_update)  // if no utlb update in progress
        & (~jrsp_dtlb_update)) // (too late to early terminate)
    begin
      // start AUX command operation
      if (  (|aux_mmu_cmd_r)     // pending aux command
          && ntlb_pd0_ram_ph3
         )   // pd0 ram ready
      begin
        jtlb_lkup_sel_nxt    = ADDR_SEL_PD;
        jtlb_lkup_vpn_cg0    = 1'b1;
  
        // AUX Command start (Serializing)
        //
        //if (ifu_clk2_en)
        begin
          case (mmu_cmd_op)      // decode AUX command <<<<<<<>>>>>>>
        
          // Write or Write NI (no invalidation of utlbs)
          //---------------------------------------------
          JTLB_CMD_WRITE,
          JTLB_CMD_WRITENI:
          begin : jtlb_cmd_write_PROC
        
            hw_mmu_index_wen     = 1'b1;  // always update e,rc fields on wr (to 0 if no err)
        
            case (1'b1) // decode AUX Index <<<<<<<>>>>>>>
             
        
            // write STLB
            aux_ix_stlb_sel:
            begin
              // write stlb only if size is compatible (single cycle)
              if (   (pd0_size_r == `npuarc_STLB_PAGE_SIZE)
                 ) begin
                stlb_write    = 1'b1;    // complete write this cycle
                if (mmu_cmd_op == JTLB_CMD_WRITE) // inval utlbs
                begin
                  begin
                    jtlb_itlb_cmd_nxt = `npuarc_JCMD_INVAL_ALL;
                    jtlb_dtlb_cmd_nxt = `npuarc_JCMD_INVAL_ALL;
                  end
                  
                  jsm_state_nxt = JSM_IVUTLB; // hold jcmd for 2 clks
                end
                else
                begin
                  jsm_state_nxt = JSM_CMD_TERM;
                end
              end else begin
                // report_err_ixreg_task(`MMU_INDEX_RC_WIDTH'h2);
                hw_mmu_index_wen     = 1'b1;
                hw_mmu_index_e_nxt   = 1'b1;
                hw_mmu_index_rc_nxt  = `npuarc_MMU_INDEX_RC_WIDTH'h2;
                jsm_state_nxt = JSM_CMD_TERM;
              end
            end
        
            // write NTLB
            aux_ix_ntlb_sel:
            begin
              // advance the ntlb 'lru' victim selection on any NTLB write or writeNI
        // spyglass disable_block W486
              ntlb_lru_entry_1h_nxt = ntlb_lru_entry_1h_r[3] ? 4'h1 : // round-robin
                                      ntlb_lru_entry_1h_r   << 1'b1;
        // spyglass enable_block W486
        //      ntlb_lru_advance      = 1'b1;
        
              // present ntlb ram address/ctl (only if size is compatible)
              if (pd0_size_r == `npuarc_NTLB_PAGE_SIZE) begin
                begin
                  ntlb_pd0_ce          = 1'b1;
                  ntlb_pd0_we          = 1'b1;
                  ntlb_pd0_wem         = aux_mmu_index_ix_way_1h;
                  ntlb_rdwr_op         = 1'b1;
                  ntlb_wdata_vbit_way  = {`npuarc_NTLB_NUM_WAYS{pd0_valid_r}};
                  ntlb_wdata_lbit_way  = {`npuarc_NTLB_NUM_WAYS{pd0_lock_r}};
                  ntlb_pd1_ce          = 1'b1;
                  ntlb_pd1_we          = 1'b1;
                  ntlb_pd1_addr        = aux_mmu_index_ix_r[`npuarc_NTLB_PD1_ADDR_MSB:0];
                end
                
                ntlb_pd0_clken  = 1'b1;
                ntlb_pd1_clken  = 1'b1;
                if (mmu_cmd_op == JTLB_CMD_WRITE) // inval utlbs
                begin
                  begin
                    jtlb_itlb_cmd_nxt = `npuarc_JCMD_INVAL_ALL;
                    jtlb_dtlb_cmd_nxt = `npuarc_JCMD_INVAL_ALL;
                  end
                  
                end
                jsm_state_nxt   = JSM_NTLB_WR;
              end else begin
                // report_err_ixreg_task(`MMU_INDEX_RC_WIDTH'h2);
                hw_mmu_index_wen     = 1'b1;
                hw_mmu_index_e_nxt   = 1'b1;
                hw_mmu_index_rc_nxt  = `npuarc_MMU_INDEX_RC_WIDTH'h2;
                jsm_state_nxt   = JSM_CMD_TERM; // ignore write
              end
            end
        
        
            default: // undefined index write
            begin
              // report_err_ixreg_task(`MMU_INDEX_RC_WIDTH'h0);
              hw_mmu_index_wen     = 1'b1;
              hw_mmu_index_e_nxt   = 1'b1;
              hw_mmu_index_rc_nxt  = `npuarc_MMU_INDEX_RC_WIDTH'h0;
              hw_mmu_index_ix_nxt = `npuarc_MMU_INDEX_IX_WIDTH'd0;
              jsm_state_nxt = JSM_CMD_TERM;
            end
        
            endcase // case (1'b1)
          end
        
          // Aux Read command
          //--------------------------------------
          JTLB_CMD_READ:
          begin : jtlb_cmd_read_PROC
        
            hw_mmu_index_wen     = 1'b1;  // always update e,rc fields on rd (to 0 if no err)
                                          // (TLBIndex.ix field unchanged)
        
            case (1'b1) // decode AUX Index <<<<<<<>>>>>>>
             
            // read STLB
            aux_ix_stlb_sel:
            begin
              stlb_read_nxt   = 1'b1;    // read stlb / wr pd0,1 next cycle
              jtlb_rd_sel_nxt = RD_SEL_STLB;
              jsm_state_nxt   = JSM_STLB_RD1;
            end
        
            // read NTLB
            aux_ix_ntlb_sel:
            begin
              begin
                ntlb_pd0_ce          = 1'b1;
                ntlb_pd0_we          = 1'b0;
                ntlb_rdwr_op         = 1'b1;
                ntlb_rd_way_sel      = aux_mmu_index_ix_rr[1:0];
                ntlb_pd1_ce          = 1'b1;
                ntlb_pd1_addr        = aux_mmu_index_ix_r[`npuarc_NTLB_PD1_ADDR_MSB:0];
              end
              
              ntlb_pd0_clken    = 1'b1;
              ntlb_pd1_clken    = 1'b1;
        
              jtlb_rd_sel_nxt   = RD_SEL_NTLB;
              jsm_state_nxt     = JSM_NTLB_RD1;
            end
        
            // read ITLB
            aux_ix_itlb_sel:
            begin
              jtlb_itlb_cmd_nxt = `npuarc_JCMD_READ;
              jtlb_rd_sel_nxt   = RD_SEL_ITLB;
              jsm_state_nxt = JSM_ITLB_RD1;
            end
        
            // read DTLB
            aux_ix_dtlb_sel:
            begin
              jtlb_dtlb_cmd_nxt = `npuarc_JCMD_READ;
              jtlb_rd_sel_nxt   = RD_SEL_DTLB;
              jsm_state_nxt = JSM_DTLB_RD1;
            end
        
            default: // undefined index read
            begin
              // report_err_ixreg_task(`MMU_INDEX_RC_WIDTH'h0);
              hw_mmu_index_wen     = 1'b1;
              hw_mmu_index_e_nxt   = 1'b1;
              hw_mmu_index_rc_nxt  = `npuarc_MMU_INDEX_RC_WIDTH'h0;
              hw_mmu_index_ix_nxt = `npuarc_MMU_INDEX_IX_WIDTH'd0;
        
              jtlb_rd_sel_nxt  = RD_SEL_ZERO;
        
              jsm_state_nxt = JSM_AUX_RD1;
            end
        
            endcase // case (1'b1)
          end
        
          // Invalidate micro-TLBs
          //----------------------
          JTLB_CMD_IVUTLB:
          begin
            begin
              jtlb_itlb_cmd_nxt = `npuarc_JCMD_INVAL_ALL;
              jtlb_dtlb_cmd_nxt = `npuarc_JCMD_INVAL_ALL;
            end
            
            jsm_state_nxt = JSM_IVUTLB;
          end
        
          // Clear LRU state of all TLBs
          //----------------------------
          JTLB_CMD_RESET_LRU:
          begin
            begin
              stlb_reset_lru_nxt  = 1'b1;
              mntlb_reset_lru_nxt  = 1'b1;
            jtlb_itlb_cmd_nxt   = `npuarc_JCMD_RESET_LRU;
            jtlb_dtlb_cmd_nxt   = `npuarc_JCMD_RESET_LRU;
            end
            
            jsm_state_nxt = JSM_CMD_TERM;
          end
        
          // Commands requiring lookup in jtlb only
          //---------------------------------------
          JTLB_CMD_GETIX:
          begin : jtlb_cmd_getix_PROC
            if (pd0_size_r == `npuarc_NTLB_PAGE_SIZE)
            begin
              // Initiate size0 lookup in ntlb (for valid bits only, lru)
              begin
                ntlb_pd0_clken       = 1'b1;
                ntlb_pd0_ce          = 1'b1;
                ntlb_pd0_we          = 1'b0;
              end
              
            end
            jsm_state_nxt = JSM_LKUP_RSLT1;
          end
        
          JTLB_CMD_PROBE:
          begin : jtlb_cmd_probe_PROC
            // probe => all sizes
            stlb_req_valid_nxt   = 1'b1;
            begin
              ntlb_pd0_clken       = 1'b1;
              ntlb_pd0_ce          = 1'b1;
              ntlb_pd0_we          = 1'b0;
            end
            
            jsm_state_nxt = JSM_LKUP_RSLT1;
          end
        
          // Commands requiring global lookup
          //---------------------------------
          JTLB_CMD_INSERT,
          JTLB_CMD_INSERTJ,
          JTLB_CMD_DELETEIS,
          JTLB_CMD_DELETE:
          begin : jtlb_cmd_insertdel_PROC
        
            // if pd0.valid bit not set, ignore insert/delete (nop)
            if (~pd0_valid_r)
            begin
              hw_mmu_index_wen     = 1'b1;
              hw_mmu_index_e_nxt   = 1'b1;
              hw_mmu_index_rc_nxt  = `npuarc_MMU_INDEX_RC_WIDTH'h0;
              hw_mmu_index_ix_nxt  = `npuarc_MMU_INDEX_IX_WIDTH'h0;
              jsm_state_nxt = JSM_CMD_TERM;
            end
            // if pd0.valid bit set, proceed with insert/delete
            else
            begin
        
              // lookup both ntlb,stlb, delete all matching entries
              stlb_req_valid_nxt   = 1'b1;
              begin
                ntlb_pd0_clken       = 1'b1;
                ntlb_pd0_ce          = 1'b1;
                ntlb_pd0_we          = 1'b0;
              end
              
              jsm_state_nxt = JSM_LKUP_RSLT1;
              jtlb_update_data_cg0 = 1'b1;
          
          
              case (mmu_cmd_op)
          
              // find exact match, delete
              JTLB_CMD_DELETE,
              JTLB_CMD_INSERTJ:
              begin
                jtlb_itlb_cmd_nxt = `npuarc_JCMD_DELETE;
                jtlb_dtlb_cmd_nxt = `npuarc_JCMD_DELETE;
              end
          
              // find entry ignoring share subscr, delete
              JTLB_CMD_DELETEIS:
              begin
                jtlb_itlb_cmd_nxt = `npuarc_JCMD_DELETEIS;
                jtlb_dtlb_cmd_nxt = `npuarc_JCMD_DELETEIS;
              end
          
              JTLB_CMD_INSERT:
              begin
                if (pd1_exec_perm)  // check perms
                begin
                  jtlb_itlb_cmd_nxt = `npuarc_JCMD_INSERT;
                  jtlb_dtlb_cmd_nxt = `npuarc_JCMD_DELETE;
                end
                else
                begin
                  jtlb_dtlb_cmd_nxt = `npuarc_JCMD_INSERT;
                  jtlb_itlb_cmd_nxt = `npuarc_JCMD_DELETE;
                end
              end
        
              default:
              begin
                jtlb_itlb_cmd_nxt = `npuarc_JCMD_IDLE;
                jtlb_dtlb_cmd_nxt = `npuarc_JCMD_IDLE;
              end
          
              endcase
        
            end
          end
        
          default: // undefined command
          begin
            jsm_state_nxt = JSM_CMD_TERM;
          end
        
          endcase // case (mmu_cmd_op)
        
        end
        
  
      end
  
      // If no aux operation, handle utlb misses
      // (dtlb has priority over itlb, search both ntlb and stlb)
      else if (   dtlb_update_req && dtlb_update_pend_r 
               && ntlb_pd0_ram_ph3
              )
      begin
        utlb_update_active_nxt    = 1'b1;
        jtlb_lkup_sel_nxt = ADDR_SEL_DTLB;
        jtlb_lkup_vpn_cg0      = 1'b1;
        begin
          ntlb_pd0_clken       = 1'b1;
          ntlb_pd0_ce          = 1'b1;
          ntlb_pd0_we          = 1'b0;
        end
        
        // stlb lookup
        stlb_req_valid_nxt   = 1'b1;
        jsm_state_nxt = JSM_UTLB_MISS1;
      end
  
      // start itlb update only during ph1 of ifu clock
      else if (   itlb_update_req && (~ifu_clk2_en)
               && ntlb_pd0_ram_ph3
              )
      begin
        utlb_update_active_nxt    = 1'b1;
        jtlb_lkup_sel_nxt = ADDR_SEL_ITLB;
        jtlb_lkup_vpn_cg0      = 1'b1;
        begin
          ntlb_pd0_clken       = 1'b1;
          ntlb_pd0_ce          = 1'b1;
          ntlb_pd0_we          = 1'b0;
        end
        
        // stlb lookup
        stlb_req_valid_nxt   = 1'b1;
        jsm_state_nxt = JSM_UTLB_MISS1;
      end
    end
  end // case: JSM_ARB

  //-------------------------------------------------------------------------
  JSM_LKUP_RSLT1:
  //-------------------------------------------------------------------------
  begin
    // waiting for TLB lookups
    stlb_req_valid_nxt   = 1'b1;
    ntlb_pd0_ce      = 1'b1;
    jsm_state_nxt    = JSM_LKUP_RSLT1B;
  end

  //-------------------------------------------------------------------------
  JSM_LKUP_RSLT1B:
  //-------------------------------------------------------------------------
  begin
    // waiting for TLB lookups
    stlb_req_valid_nxt   = 1'b1;
    stlb_rslt_valid_nxt  = 1'b1;
    ntlb_pd0_ce      = 1'b1;
    jsm_state_nxt    = JSM_LKUP_RSLT2;
  end

  //-------------------------------------------------------------------------
  JSM_LKUP_RSLT2:
  //-------------------------------------------------------------------------
  begin
    // lookup results available from both an/stlb(early), ntlb(mem based-late)
    // 3 clk of ntlb mem access and 2 clk stlb registered output results valid
    // (no pd1 access needed for probe/getix)
    ntlb_pd0_rslt_valid_nxt = 1'b1;

    // HANDLE PROBE RESULTS
    //---------------------
    // check both stlb and ntlb results for match; if single match return
    // index of match in TLBIndex; if no match return error flag/code 1/00
    // if multiple match return error flag/code 1/04.
    if (aux_mmu_cmd_rr == JTLB_CMD_PROBE)
    begin : probe_rslt_COMB

      jsm_state_nxt = JSM_ARB;
      cmd_reg_clr   = 1'b1;

      begin
      
        // if NTLB pd0 ram (any way) had uncorr ecc error, report error
        // and clear index field
        //
        // counter for counting single bit error
        //
        ecc_mmu_sbe_count_set_cg0 = (ecc_mmu_sbe_count_r != 4'b1111)
                                  & (~ecc_mmu_sbe_count_clr_cg0)
                                  & ecc_sb_error_pd0;
       
        if (ecc_db_error_pd0)
        begin
          //report_err_ixreg_task(`MMU_INDEX_RC_WIDTH'h7);
          hw_mmu_index_wen     = 1'b1;
          hw_mmu_index_e_nxt   = 1'b1;
          hw_mmu_index_rc_nxt  = `npuarc_MMU_INDEX_RC_WIDTH'h7;
          hw_mmu_index_ix_nxt = `npuarc_MMU_INDEX_IX_WIDTH'd0;
        end
        else
        begin
      // leda W547 off
      // LMD: Redundant case expression
      // LJ:  Multiple match implies match
      // spyglass disable_block W398 STARC05-2.8.1.3
      // SMD: Possible case covered by multiple case statments.
      // SJ:  Multiple match implies match
          casez ({stlb_rslt_match_r,
                  ntlb_rslt_match,
                  stlb_rslt_multiple_match_r,
                  ntlb_rslt_multiple_match}
                )
          // --- lookup missed both ntlb,stlb
          4'b00??:
          begin
            // report_err_ixreg_task(`MMU_INDEX_RC_WIDTH'h0);
            hw_mmu_index_wen     = 1'b1;
            hw_mmu_index_e_nxt   = 1'b1;
            hw_mmu_index_rc_nxt  = `npuarc_MMU_INDEX_RC_WIDTH'h0;
            hw_mmu_index_ix_nxt = `npuarc_MMU_INDEX_IX_WIDTH'd0;
          end
          // --- hit NTLB ---
          4'b01?0:
          begin
            begin
              hw_mmu_index_ix_nxt   = ntlb_match_index | IX_NTLB_BASE; //sz alignd
              hw_mmu_index_rc_nxt   = {`npuarc_MMU_INDEX_RC_WIDTH{1'b0}};
              hw_mmu_index_e_nxt    = 1'b0;
              hw_mmu_index_wen      = 1'b1;
            end
            
          end
          // --- hit STLB ---
          4'b100?:
          begin
            begin
              hw_mmu_index_ix_nxt   = stlb_match_index | IX_STLB_BASE; //sz alignd
              hw_mmu_index_rc_nxt   = {`npuarc_MMU_INDEX_RC_WIDTH{1'b0}};
              hw_mmu_index_e_nxt    = 1'b0;
              hw_mmu_index_wen      = 1'b1;
            end
            
          end
          // --- Multiple hits (error, go to idle) ---
          4'b11??, // hit both STLB/NTLB
          4'b??1?, // hit multiple entries in stlb
          4'b???1: // hit multiple entries in ntlb
          begin
            // report_err_ixreg_task(`MMU_INDEX_RC_WIDTH'h4);
            hw_mmu_index_wen     = 1'b1;
            hw_mmu_index_e_nxt   = 1'b1;
            hw_mmu_index_rc_nxt  = `npuarc_MMU_INDEX_RC_WIDTH'h4;
            hw_mmu_index_ix_nxt = `npuarc_MMU_INDEX_IX_WIDTH'd0;
          end
          default: // miss
          begin
            // report_err_ixreg_task(`MMU_INDEX_RC_WIDTH'h0);
            hw_mmu_index_wen     = 1'b1;
            hw_mmu_index_e_nxt   = 1'b1;
            hw_mmu_index_rc_nxt  = `npuarc_MMU_INDEX_RC_WIDTH'h0;
            hw_mmu_index_ix_nxt = `npuarc_MMU_INDEX_IX_WIDTH'd0;
          end
          endcase      
      // leda W547 on
      // spyglass enable_block W398 STARC05-2.8.1.3
        end
      end
      

    end

    // HANDLE DELETE COMMANDS
    //------------------------
    // - Sent delete cmds to both utlbs (enh: detect multi-hits in utlbs)
    // - check both stlb and ntlb results for match, and delete all matching
    //   entries. 
    //     if no match return error flag/code 1/00
    //     if multiple match return error flag/code 1/04.
    if (  (aux_mmu_cmd_rr == JTLB_CMD_DELETE)
        | (aux_mmu_cmd_rr == JTLB_CMD_DELETEIS)
       )
    begin : lkup_rslt2_delete_cmds_COMB

      // invalidate matching ntlb entries
      if (ntlb_rslt_match)
      begin
        // clear valid bit of matching ntlb entries
        ntlb_pd0_ce         = 1'b1;
        ntlb_pd0_we         = 1'b1;
        ntlb_rdwr_op        = 1'b0; // use pd0 not ix reg
        // write only matching ways (wr data = pd0 reg)
        ntlb_pd0_wem        = ntlb_rslt_entry_match;
        ntlb_wdata_vbit_way = 4'b0;
        ntlb_wdata_lbit_way = 4'b0;

        ntlb_pd0_clken      = 1'b1; // (pd1 unchanged)
        jsm_state_nxt       = JSM_NTLB_WR;
      end
      else
      begin
        // if no matching entries to delete go idle
        cmd_reg_clr         = 1'b1;
        jsm_state_nxt       = JSM_ARB;
      end
      // invalidate matching stlb entries
      if (stlb_rslt_match_r)
      begin
        stlb_invalidate_entries = stlb_rslt_entry_match_r;
      end

      begin
      
        // if NTLB pd0 ram (any way) had uncorr ecc error, report error
        // and clear index field
        //
        // counter for counting single bit error
        //
        ecc_mmu_sbe_count_set_cg0 = (ecc_mmu_sbe_count_r != 4'b1111)
                                  & (~ecc_mmu_sbe_count_clr_cg0)
                                  & ecc_sb_error_pd0;
       
        if (ecc_db_error_pd0)
        begin
          //report_err_ixreg_task(`MMU_INDEX_RC_WIDTH'h7);
          hw_mmu_index_wen     = 1'b1;
          hw_mmu_index_e_nxt   = 1'b1;
          hw_mmu_index_rc_nxt  = `npuarc_MMU_INDEX_RC_WIDTH'h7;
          hw_mmu_index_ix_nxt = `npuarc_MMU_INDEX_IX_WIDTH'd0;
        end
        else
        begin
      // leda W547 off
      // LMD: Redundant case expression
      // LJ:  Multiple match implies match
      // spyglass disable_block W398 STARC05-2.8.1.3
      // SMD: Possible case covered by multiple case statments.
      // SJ:  Multiple match implies match
          casez ({stlb_rslt_match_r,
                  ntlb_rslt_match,
                  stlb_rslt_multiple_match_r,
                  ntlb_rslt_multiple_match}
                )
          // --- lookup missed both ntlb,stlb
          4'b00??:
          begin
            // report_err_ixreg_task(`MMU_INDEX_RC_WIDTH'h0);
            hw_mmu_index_wen     = 1'b1;
            hw_mmu_index_e_nxt   = 1'b1;
            hw_mmu_index_rc_nxt  = `npuarc_MMU_INDEX_RC_WIDTH'h0;
            hw_mmu_index_ix_nxt = `npuarc_MMU_INDEX_IX_WIDTH'd0;
          end
          // --- hit NTLB ---
          4'b01?0:
          begin
            begin
              hw_mmu_index_ix_nxt   = ntlb_match_index | IX_NTLB_BASE; //sz alignd
              hw_mmu_index_rc_nxt   = {`npuarc_MMU_INDEX_RC_WIDTH{1'b0}};
              hw_mmu_index_e_nxt    = 1'b0;
              hw_mmu_index_wen      = 1'b1;
            end
            
          end
          // --- hit STLB ---
          4'b100?:
          begin
            begin
              hw_mmu_index_ix_nxt   = stlb_match_index | IX_STLB_BASE; //sz alignd
              hw_mmu_index_rc_nxt   = {`npuarc_MMU_INDEX_RC_WIDTH{1'b0}};
              hw_mmu_index_e_nxt    = 1'b0;
              hw_mmu_index_wen      = 1'b1;
            end
            
          end
          // --- Multiple hits (error, go to idle) ---
          4'b11??, // hit both STLB/NTLB
          4'b??1?, // hit multiple entries in stlb
          4'b???1: // hit multiple entries in ntlb
          begin
            // report_err_ixreg_task(`MMU_INDEX_RC_WIDTH'h4);
            hw_mmu_index_wen     = 1'b1;
            hw_mmu_index_e_nxt   = 1'b1;
            hw_mmu_index_rc_nxt  = `npuarc_MMU_INDEX_RC_WIDTH'h4;
            hw_mmu_index_ix_nxt = `npuarc_MMU_INDEX_IX_WIDTH'd0;
          end
          default: // miss
          begin
            // report_err_ixreg_task(`MMU_INDEX_RC_WIDTH'h0);
            hw_mmu_index_wen     = 1'b1;
            hw_mmu_index_e_nxt   = 1'b1;
            hw_mmu_index_rc_nxt  = `npuarc_MMU_INDEX_RC_WIDTH'h0;
            hw_mmu_index_ix_nxt = `npuarc_MMU_INDEX_IX_WIDTH'd0;
          end
          endcase      
      // leda W547 on
      // spyglass enable_block W398 STARC05-2.8.1.3
        end
      end
      

    end


    // HANDLE INSERT
    //--------------------------------------------
    // - Sent insert cmd to both utlbs
    //   enh: detect multi-hits in utlbs
    // - check both stlb and ntlb results for match, and delete all matching
    //   entries. 
    //     if single match capture ix and return 0 in e/rc
    //     if no match return error flag/code 1/00
    //     if multiple match return error flag/code 1/04.
    if (  (aux_mmu_cmd_rr == JTLB_CMD_INSERT)
        | (aux_mmu_cmd_rr == JTLB_CMD_INSERTJ)
       )
    begin : lkup_rslt2_insert_cmds_COMB

      // For insert, always update e/rc/ix
      hw_mmu_index_wen      = 1'b1;

      // update index reg (e/rc fields)
      // ---------------------------------

      // if NTLB pd0 ram (any way) had uncorr ecc error, report error
      // and clear index field
      //
      // counter for counting single bit error
      //
      ecc_mmu_sbe_count_set_cg0 = (ecc_mmu_sbe_count_r != 4'b1111)
                                & (~ecc_mmu_sbe_count_clr_cg0)
                                & ecc_sb_error_pd0;

      if (ecc_db_error_pd0)
      begin
        // report_err_ixreg_task(`MMU_INDEX_RC_WIDTH'h7);
        hw_mmu_index_e_nxt   = 1'b1;
        hw_mmu_index_rc_nxt  = `npuarc_MMU_INDEX_RC_WIDTH'h7;
        hw_mmu_index_ix_nxt  = `npuarc_MMU_INDEX_IX_WIDTH'd0;
      end
      else
      // 
      if (jtlb_multiple_match) // multiple match
      begin
        hw_mmu_index_e_nxt    = 1'b1;
        hw_mmu_index_rc_nxt   = `npuarc_MMU_INDEX_RC_WIDTH'h4;
      end 
      else 
      if (jtlb_single_match)  // single match
      begin
        hw_mmu_index_e_nxt    = 1'b0;
        hw_mmu_index_rc_nxt   = `npuarc_MMU_INDEX_RC_WIDTH'h0;
      end
      else                    // no match in jtlb
      begin
        hw_mmu_index_e_nxt    = 1'b1;
        hw_mmu_index_rc_nxt   = `npuarc_MMU_INDEX_RC_WIDTH'h0;
      end

      // update index reg (ix field)
      // ---------------------------------
      if (pd0_size_rr == `npuarc_NTLB_PAGE_SIZE)
      begin
        // 
        if (ntlb_rslt_match)
        begin
          hw_mmu_index_ix_nxt   = ntlb_match_index | IX_NTLB_BASE; //sz alignd
        end
        else  // no ntlb match
        begin
          // invalid or lru index
          hw_mmu_index_ix_nxt   = ntlb_invlru_index | IX_NTLB_BASE; //sz alignd
        end
      end
      else  // pd0 size -> not NTLB (Super page)
      begin
        if (stlb_rslt_match_r)
        begin
          hw_mmu_index_ix_nxt   = stlb_match_index | IX_STLB_BASE; //sz alignd
        end
        else  // no stlb match
        begin
          // invalid or lru index
          hw_mmu_index_ix_nxt   = stlb_invlru_index;
        end
      end

      // advance the ntlb LRU (on insert of NORMAL PAGE)
      // ---------------------------------
      if (pd0_size_rr == `npuarc_NTLB_PAGE_SIZE)
      begin
// spyglass disable_block W486
        ntlb_lru_entry_1h_nxt = ntlb_lru_entry_1h_r[3] ? 4'h1 : // round-robin
                                ntlb_lru_entry_1h_r   << 1'b1;
// spyglass enable_block W486
//        ntlb_lru_advance      = 1'b1;
      end

      // Perform the Insert operation into appropriate TLB
      //---------------------------------------------------

      // NTLB 
      if (pd0_size_rr == `npuarc_NTLB_PAGE_SIZE)
      begin
        // clear valid bit of all matching stlb entries
        stlb_invalidate_entries = stlb_rslt_entry_match_r;
        // clear valid bit of matching ntlb entries (except insert target)
        ntlb_pd0_ce         = 1'b1;
        ntlb_pd0_we         = 1'b1;
        ntlb_rdwr_op        = 1'b0; // use pd0/match ix/way not ix reg

        // write all matching ways (wr data = pd0/1 regs)
        // if no match, target invalid/lru way
        ntlb_pd0_wem        = ntlb_rslt_match ?
                              ntlb_rslt_entry_match :
                              ntlb_invlru_way_1h;
        // set valid bit of selected way if pd0.valid set
        ntlb_wdata_vbit_way = ntlb_insert_target_1h 
                            & {`npuarc_NTLB_NUM_WAYS{pd0_valid_r}};
        // set lock bit of selected way if pd0.lock set
        ntlb_wdata_lbit_way = ntlb_insert_target_1h 
                            & {`npuarc_NTLB_NUM_WAYS{pd0_lock_r}};
        ntlb_pd1_addr       = hw_mmu_index_ix_nxt[`npuarc_NTLB_PD1_ADDR_MSB:0];
        ntlb_pd1_ce         = 1'b1;
        ntlb_pd1_we         = 1'b1;

        ntlb_pd0_clken      = 1'b1;
        ntlb_pd1_clken      = 1'b1;
        // for ntlb go finish 2 clk write of pd1
        jsm_state_nxt       = JSM_NTLB_WR;
      end
      else
      // STLB
      begin
        // write entry (pd0/pd1) to stlb
        stlb_insert         = 1'b1;
        // invalidate other matching stlb entries
        stlb_invalidate_entries =  stlb_rslt_entry_match_r
                                & (~stlb_rslt_entry_match_1h_r);

        // clear valid bit of all matching ntlb entries
        if (ntlb_rslt_match)
        begin
          ntlb_pd0_ce         = 1'b1;
          ntlb_pd0_we         = 1'b1;
          ntlb_rdwr_op        = 1'b0; // use pd0/match ix/way not ix reg
          // write all matching ways (wr data = pd0 reg)
          ntlb_pd0_wem        = ntlb_rslt_entry_match;
  
          ntlb_wdata_vbit_way = `npuarc_NTLB_NUM_WAYS'd0;
          ntlb_wdata_lbit_way = `npuarc_NTLB_NUM_WAYS'd0;
          ntlb_pd1_addr       = hw_mmu_index_ix_nxt[`npuarc_NTLB_PD1_ADDR_MSB:0];
          ntlb_pd1_ce         = 1'b1;
          ntlb_pd1_we         = 1'b1;
  
          ntlb_pd0_clken      = 1'b1;
//        ntlb_pd1_clken      = 1'b1;
          // for ntlb go finish 2 clk write of pd1
          jsm_state_nxt       = JSM_NTLB_WR;
        end
        else  // no matching entries in ntlb to invalidate
        begin
          // for stlb done after this cycle
          cmd_reg_clr         = 1'b1;
          jsm_state_nxt       = JSM_ARB;
        end
      end

    end // insert


    // HANDLE GETIX RESULTS
    //---------------------
    // if requested page size (PD0.SIZE) is:
    //    super page:   return invalid or LRU entry index in STLB
    //    normal page:  return {given index, invalid or LRU way} index in NTLB
    //
    if (aux_mmu_cmd_rr == JTLB_CMD_GETIX)
    begin : getix_rslt_COMB

      jsm_state_nxt = JSM_ARB;
      cmd_reg_clr   = 1'b1;

      hw_mmu_index_wen    = 1'b1;

      // update index e/rc
      //
      if (pd0_size_r == `npuarc_NTLB_PAGE_SIZE)
      begin
      // If ECC checking configured and getindex targeting ntlb (pd0.sz=0)
      //   if NTLB pd0 ram (any way) had uncorr ecc error, report error
      //   and return index field considering TLB entries with err as invalid
      //
      // counter for counting single bit error
      //
        ecc_mmu_sbe_count_set_cg0 = (pd0_size_rr == `npuarc_NTLB_PAGE_SIZE)
                                  & (ecc_mmu_sbe_count_r != 4'b1111)
                                  & (~ecc_mmu_sbe_count_clr_cg0)
                                  & ecc_sb_error_pd0;
    
        if (ecc_db_error_pd0)
        begin
          hw_mmu_index_e_nxt   = 1'b1;
          hw_mmu_index_rc_nxt  = `npuarc_MMU_INDEX_RC_WIDTH'h7;
        end
        else  // no ecc error (or ecc not configured)
        begin
          hw_mmu_index_e_nxt    = 1'b0;
          hw_mmu_index_rc_nxt   = `npuarc_MMU_INDEX_RC_WIDTH'h0;
        end

        if ( ntlb_all_entries_locked && (~ntlb_inval_entry_avail) )
          hw_mmu_index_e_nxt    =    1'b1;

      end  // (pd0_size_r == `NTLB_PAGE_SIZE)


      // update index.ix
      //
      if (pd0_size_rr == `npuarc_STLB_PAGE_SIZE)
      begin
        // invalid or lru index
        hw_mmu_index_ix_nxt = stlb_invlru_index;
      end
      if (pd0_size_rr == `npuarc_NTLB_PAGE_SIZE)
      begin
        // invalid or lru index
        hw_mmu_index_ix_nxt = ntlb_invlru_index | IX_NTLB_BASE; //sz alignd
      end

    end
  end // case: JSM_LKUP_RSLT2


  //-------------------------------------------------------------------------
  JSM_CMD_TERM:  // extend commands that otherwise complete in 1 cycle
  //-------------------------------------------------------------------------
  begin
    cmd_reg_clr      = 1'b1;    // clear aux cmd reg (cmd completed)
    jsm_state_nxt    = JSM_ARB;
  end

  //-------------------------------------------------------------------------
  JSM_NTLB_WR:
  //-------------------------------------------------------------------------
  // no clken, but hold these stable for one more 1x clk
  begin
    begin
      ntlb_pd0_ce          = 1'b1;
      ntlb_pd0_we          = 1'b1;
      ntlb_pd0_wem         = aux_mmu_index_ix_way_1h;
      ntlb_rdwr_op         = 1'b1;
      ntlb_wdata_vbit_way  = {`npuarc_NTLB_NUM_WAYS{pd0_valid_r}};
      ntlb_wdata_lbit_way  = {`npuarc_NTLB_NUM_WAYS{pd0_lock_r}};
      ntlb_pd1_ce          = 1'b1;
      ntlb_pd1_we          = 1'b1;
      ntlb_pd1_addr        = aux_mmu_index_ix_r[`npuarc_NTLB_PD1_ADDR_MSB:0];
    end
    
    if (aux_mmu_cmd_rr == JTLB_CMD_WRITE) // inval utlbs (hold for 2nd clock)
    begin
      begin
        jtlb_itlb_cmd_nxt = `npuarc_JCMD_INVAL_ALL;
        jtlb_dtlb_cmd_nxt = `npuarc_JCMD_INVAL_ALL;
      end
      
    end
    cmd_reg_clr      = 1'b1;    // clear aux cmd reg (cmd completed)
    jsm_state_nxt    = JSM_ARB;
  end

  //-------------------------------------------------------------------------
  JSM_NTLB_RD1:
  //-------------------------------------------------------------------------
  begin
    begin
      ntlb_pd0_ce          = 1'b1;
      ntlb_pd0_we          = 1'b0;
      ntlb_rdwr_op         = 1'b1;
      ntlb_rd_way_sel      = aux_mmu_index_ix_rr[1:0];
      ntlb_pd1_ce          = 1'b1;
      ntlb_pd1_addr        = aux_mmu_index_ix_r[`npuarc_NTLB_PD1_ADDR_MSB:0];
    end
    
    jsm_state_nxt    = JSM_NTLB_RD1B;
  end

  //-------------------------------------------------------------------------
  JSM_NTLB_RD1B:
  //-------------------------------------------------------------------------
  begin
    begin
      ntlb_pd0_ce          = 1'b1;
      ntlb_pd0_we          = 1'b0;
      ntlb_rdwr_op         = 1'b1;
      ntlb_rd_way_sel      = aux_mmu_index_ix_rr[1:0];
      ntlb_pd1_ce          = 1'b1;
      ntlb_pd1_addr        = aux_mmu_index_ix_r[`npuarc_NTLB_PD1_ADDR_MSB:0];
    end
    
    jsm_state_nxt    = JSM_NTLB_RD2;
  end

  //-------------------------------------------------------------------------
  JSM_NTLB_RD2:
  //-------------------------------------------------------------------------
  begin
    begin
      ntlb_pd0_ce          = 1'b1;
      ntlb_pd0_we          = 1'b0;
      ntlb_rdwr_op         = 1'b1;
      ntlb_rd_way_sel      = aux_mmu_index_ix_rr[1:0];
      ntlb_pd1_ce          = 1'b1;
      ntlb_pd1_addr        = aux_mmu_index_ix_r[`npuarc_NTLB_PD1_ADDR_MSB:0];
    end
    
    hw_mmu_pd0_wen   = 1'b1;
    hw_mmu_pd1_wen   = 1'b1;
    // if NTLB pd0 or pd1  ram had uncorr ecc error, report error
    //
    // counter for counting single bit error
    //
    ecc_mmu_sbe_count_set_cg0 = (ecc_mmu_sbe_count_r != 4'b1111)
                              & (~ecc_mmu_sbe_count_clr_cg0)
                              & (  ecc_sb_error_pd0
                                 | ecc_sb_error_pd1);
    if (ecc_db_error_pd0 | ecc_db_error_pd1)
    begin
      // report_err_ixreg_task(`MMU_INDEX_RC_WIDTH'h7);
      hw_mmu_index_wen     = 1'b1;   // ix field unchanged
      hw_mmu_index_e_nxt   = 1'b1;
      hw_mmu_index_rc_nxt  = `npuarc_MMU_INDEX_RC_WIDTH'h7;
    end

    cmd_reg_clr      = 1'b1;    // clear aux cmd reg (cmd completed)
    jsm_state_nxt    = JSM_ARB;
  end

  //-------------------------------------------------------------------------
  JSM_STLB_RD1:
  //-------------------------------------------------------------------------
  begin
      stlb_read_nxt   = 1'b1;         // read stlb is 2cyc
      jsm_state_nxt   = JSM_TLB_RD2;
  end

  //-------------------------------------------------------------------------
  JSM_ITLB_RD1:
  //-------------------------------------------------------------------------
  begin
      jtlb_itlb_cmd_nxt = `npuarc_JCMD_READ;
      jsm_state_nxt     = JSM_TLB_RD2; // hold cmd for 2 clks for itlb
  end

  //-------------------------------------------------------------------------
  JSM_DTLB_RD1:
  //-------------------------------------------------------------------------
  begin
      jtlb_dtlb_cmd_nxt = `npuarc_JCMD_READ;
      jsm_state_nxt     = JSM_TLB_RD2; // hold cmd for 2 clks for dtlb
  end

  //-------------------------------------------------------------------------
  JSM_AUX_RD1:
  //-------------------------------------------------------------------------
  begin
      jsm_state_nxt   = JSM_TLB_RD2;
  end

  //-------------------------------------------------------------------------
  JSM_TLB_RD2:
  //-------------------------------------------------------------------------
  begin
    ntlb_rdwr_op     = 1'b1;    // setup rd addr to antlb
    hw_mmu_pd0_wen   = 1'b1;
    hw_mmu_pd1_wen   = 1'b1;

    cmd_reg_clr      = 1'b1;    // clear aux cmd reg (cmd completed)
    jsm_state_nxt    = JSM_ARB;
  end

  //-------------------------------------------------------------------------
  JSM_IVUTLB:
  //-------------------------------------------------------------------------
  begin
    begin
      jtlb_itlb_cmd_nxt = `npuarc_JCMD_INVAL_ALL;
      jtlb_dtlb_cmd_nxt = `npuarc_JCMD_INVAL_ALL;
    end
           // hold jcmd for 2nd clock
    cmd_reg_clr   = 1'b1;    // clear aux cmd reg (cmd completed)
    jsm_state_nxt = JSM_ARB; //  and go idle
  end

  //-------------------------------------------------------------------------
  JSM_UTLB_MISS1:
  //-------------------------------------------------------------------------
  // 1st clk of ntlb mem access (ph1)
  // and stlb lookup valid (stlb_req_valid_r)
  begin
    if (jtlb_cancel_update)
    begin
      jsm_state_nxt    = JSM_ARB; // abandon update on restart
    end 
    else 
    begin
      stlb_req_valid_nxt   = 1'b1;
      utlb_update_active_nxt    = 1'b1;
      jsm_state_nxt    = JSM_UTLB_MISS1B; 
    end
  end

  //-------------------------------------------------------------------------
  JSM_UTLB_MISS1B:
  //-------------------------------------------------------------------------
  // 2nd clk of ntlb mem access (ph2)
  // and stlb lookup valid (stlb_req_valid_r)
  begin
    if (jtlb_cancel_update)
    begin
      jsm_state_nxt    = JSM_ARB; // abandon update on restart
    end 
    else 
    begin
      stlb_req_valid_nxt   = 1'b1;
      stlb_rslt_valid_nxt  = 1'b1;
      utlb_update_active_nxt    = 1'b1;
      jsm_state_nxt    = JSM_UTLB_MISS2; 
    end
  end

  //-------------------------------------------------------------------------
  JSM_UTLB_MISS2:
  //-------------------------------------------------------------------------
  // lookup results available from both stlb (early) ntlb (late):
  // 3rd clk of ntlb mem access and stlb registered output results now valid
  begin
    jtlb_update_data_cg0 = 1'b1; // in case update is from stlb
    if (jtlb_cancel_update)
    begin
      jsm_state_nxt    = JSM_ARB; // abandon update on restart
    end 
    else
    begin
      utlb_update_active_nxt    = 1'b1;

      ntlb_pd0_rslt_valid_nxt = 1'b1;
      // leda W547 off
      // LMD: Redundant case expression
      // LJ:  Multiple match implies match
      // spyglass disable_block W398 STARC05-2.8.1.3
      // SMD: Possible case covered by multiple case statments.
      // SJ:  Multiple match implies match
      casez ({stlb_rslt_match_r,
              ntlb_rslt_match,
              stlb_rslt_multiple_match_r,
              ntlb_rslt_multiple_match,
              (jtlb_lkup_sel_r == ADDR_SEL_DTLB)
             }
            )
        // --- utlb update request missed in JTLB ---
        5'b00_??_0: // itlb req 
        begin
          jrsp_itlb_update_nxt = 1'b1;  // return miss
          jsm_state_nxt = JSM_ARB;
        end
        5'b00_??_1: // dtlb req
        begin
          jrsp_dtlb_update_nxt = 1'b1;  // return miss
          jsm_state_nxt = JSM_ARB;
        end
    
        // --- hit NTLB ---
        5'b01_?0_0: // itlb req
        begin
        // setup matched way pd1 ram address / ctl
          begin
            ntlb_pd1_clken       = 1'b1;
            ntlb_pd1_ce          = 1'b1;
            ntlb_pd1_we          = 1'b0;
            ntlb_pd1_addr        = ntlb_match_index[`npuarc_NTLB_PD1_ADDR_MSB:0];
          end
          
          jsm_state_nxt = JSM_UTLB_MISS3; // wait for pd1
        end
        5'b01_?0_1: // dtlb req
        begin
        // setup matched way pd1 ram address / ctl
          begin
            ntlb_pd1_clken       = 1'b1;
            ntlb_pd1_ce          = 1'b1;
            ntlb_pd1_we          = 1'b0;
            ntlb_pd1_addr        = ntlb_match_index[`npuarc_NTLB_PD1_ADDR_MSB:0];
          end
          
          jsm_state_nxt = JSM_UTLB_MISS3; // wait for pd1
        end
    
        // --- hit STLB ---
        5'b10_0?_0: // itlb req
        begin
          jrsp_itlb_update_nxt      = 1'b1; 
          jrsp_itlb_update_hit_nxt  = 1'b1;
          jtlb_update_data_cg0      = 1'b1;
          jsm_state_nxt = JSM_ARB;
        end
        5'b10_0?_1: // dtlb req
        begin
          jrsp_dtlb_update_nxt      = 1'b1; 
          jrsp_dtlb_update_hit_nxt  = 1'b1;
          jtlb_update_data_cg0      = 1'b1;
          jsm_state_nxt = JSM_ARB;
        end
    
        // --- multiple hits (let the utlb gen the excpn) ---
        5'b11_00_0, // itlb req
        5'b??_1?_0,
        5'b??_?1_0:
        begin
          jrsp_itlb_update_nxt      = 1'b1; 
          jrsp_itlb_update_hit_nxt  = 1'b1;
          jtlb_update_data_cg0      = 1'b1;
          jsm_state_nxt = JSM_ARB;
        end
        5'b11_00_1, // dtlb req
        5'b??_1?_1,
        5'b??_?1_1:
        begin
          jrsp_dtlb_update_nxt      = 1'b1; 
          jrsp_dtlb_update_hit_nxt  = 1'b1;
          jtlb_update_data_cg0      = 1'b1;
          jsm_state_nxt = JSM_ARB;
        end
        default: jsm_state_nxt    = JSM_ARB; 
      endcase      
      // leda W547 on
      // spyglass enable_block W398 STARC05-2.8.1.3

      // if NTLB pd0 ram (any way) had ecc error, force miss and return
      // err to utlb so TLB Error exception will be generated
      //
      // counter for counting single bit error
      //
      ecc_mmu_sbe_count_set_cg0 = (ecc_mmu_sbe_count_r != 4'b1111)
                                & (~ecc_mmu_sbe_count_clr_cg0)
                                & ecc_sb_error_pd0;

      if (jtlb_lkup_sel_r == ADDR_SEL_DTLB)
      begin
        dtlb_syndrome_set_cg0 = 1'b1;

        fs_dtlb_bank0_syndrome_nxt =  syndrome_pd0_way0;
        fs_dtlb_bank1_syndrome_nxt =  syndrome_pd0_way1;
        fs_dtlb_bank2_syndrome_nxt =  syndrome_pd0_way2;
        fs_dtlb_bank3_syndrome_nxt =  syndrome_pd0_way3;
      end      
      else
      begin
        itlb_syndrome_set_cg0 = 1'b1;
 
        fs_itlb_bank0_syndrome_nxt =  syndrome_pd0_way0;
        fs_itlb_bank1_syndrome_nxt =  syndrome_pd0_way1;
        fs_itlb_bank2_syndrome_nxt =  syndrome_pd0_way2;
        fs_itlb_bank3_syndrome_nxt =  syndrome_pd0_way3;
      end      
     if (ecc_db_error_pd0)
      begin
        if (jtlb_lkup_sel_r == ADDR_SEL_DTLB)
        begin
          jrsp_dtlb_update_nxt = 1'b1;   // return miss with error
          jrsp_dtlb_tlb_err_nxt = 1'b1;  //  to dtlb
        end
        else
        begin
          jrsp_itlb_update_nxt = 1'b1;   // return miss with error
          jrsp_itlb_tlb_err_nxt = 1'b1;  //  to itlb
        end
      end

    end 
  end

  //-------------------------------------------------------------------------
  JSM_UTLB_MISS3:
  //-------------------------------------------------------------------------
  begin
    if (jtlb_cancel_update)
    begin
      jsm_state_nxt    = JSM_ARB; // abandon update on restart
    end 
    else 
    begin
      utlb_update_active_nxt    = 1'b1;
      jsm_state_nxt    = JSM_UTLB_MISS4; // second clk of pd1 ram, valid dout
      // form reply to utlb (update hit) 
    end
  end

  //-------------------------------------------------------------------------
  JSM_UTLB_MISS4:
  //-------------------------------------------------------------------------
  begin
    if (!jtlb_cancel_update)
    begin
      jtlb_update_data_cg0 = 1'b1;
      utlb_update_active_nxt    = 1'b1;

      if (jtlb_lkup_sel_r == ADDR_SEL_DTLB)
      begin
        //
        // counter for counting single bit error
        //
        ecc_mmu_sbe_count_set_cg0 = (ecc_mmu_sbe_count_r != 4'b1111)
                                  & (~ecc_mmu_sbe_count_clr_cg0)
                                  & (  ecc_sb_error_pd0
                                     | ecc_sb_error_pd1);

      dtlb_syndrome_set_cg1 = 1'b1;

      fs_dtlb_bank4_syndrome_nxt =  syndrome_pd1;
      fs_dtlb_bank0_syndrome_nxt =  syndrome_pd0_way0;
      fs_dtlb_bank1_syndrome_nxt =  syndrome_pd0_way1;
      fs_dtlb_bank2_syndrome_nxt =  syndrome_pd0_way2;
      fs_dtlb_bank3_syndrome_nxt =  syndrome_pd0_way3;

        if (ecc_db_error_pd0 | ecc_db_error_pd1)
        begin
          jrsp_dtlb_update_nxt = 1'b1;   // return miss with error
          jrsp_dtlb_tlb_err_nxt = 1'b1;  //  to dtlb
        end
        else
        begin
          jrsp_dtlb_update_nxt      = 1'b1; 
          jrsp_dtlb_update_hit_nxt  = 1'b1;
        end
      end
      else
      begin
        //
        // counter for counting single bit error
        //
        ecc_mmu_sbe_count_set_cg0 = (ecc_mmu_sbe_count_r != 4'b1111)
                                  & (~ecc_mmu_sbe_count_clr_cg0)
                                  & (  ecc_sb_error_pd0
                                     | ecc_sb_error_pd1);

        itlb_syndrome_set_cg1 = 1'b1;  

        fs_itlb_bank4_syndrome_nxt =  syndrome_pd1;
        fs_itlb_bank0_syndrome_nxt =  syndrome_pd0_way0;
        fs_itlb_bank1_syndrome_nxt =  syndrome_pd0_way1;
        fs_itlb_bank2_syndrome_nxt =  syndrome_pd0_way2;
        fs_itlb_bank3_syndrome_nxt =  syndrome_pd0_way3;
        if (ecc_db_error_pd0 | ecc_db_error_pd1)
        begin
          jrsp_itlb_update_nxt = 1'b1;   // return miss with error
          jrsp_itlb_tlb_err_nxt = 1'b1;  //  to itlb
        end
        else
        begin
          jrsp_itlb_update_nxt      = 1'b1; 
          jrsp_itlb_update_hit_nxt  = 1'b1;
        end
      end
    end
    jsm_state_nxt    = JSM_ARB;
  end

  default:
  begin
    cmd_reg_clr      = 1'b1;
    jsm_state_nxt    = JSM_ARB;
  end

  endcase // case (jsm_state_r)

end // block: mmu_fsm_PROC



//---------------------------------------------------------------------------
// Address counter for clearing NTLB tag ram on reset
//---------------------------------------------------------------------------
// leda W484 off
// LMD: Possible loss of carry/borrow in addition/subtraction
// LJ:  address addition is modulo 2^32, so carry-out should be ignored
// leda BTTF_D002 off
// LMD: Unequal length LHS and RHS in assignment LHS : x, RHS : y  
// LJ:  address addition is modulo 2^32, so carry-out should be ignored
// leda B_3200 off
// LMD: Unequal length operand in bit/arithmetic operator
// LJ:  1b addition (incr)
wire   jsm_state_init;
assign jsm_state_init = (jsm_state_r == JSM_INIT);

// VPOST OFF
always @(posedge ntlb_pd0_clk or posedge rst_a)
begin : ntlb_tram_clr_cnt_PROC
  if (rst_a == 1'b1)
  begin
    ntlb_tram_clr_cnt <= {`npuarc_NTLB_PD0_ADDR_WIDTH{1'b0}};
  end
  else if (jsm_state_init)
  begin
    ntlb_tram_clr_cnt <= ntlb_tram_clr_cnt + 1'b1;
  end
end
// VPOST ON
// leda BTTF_D002 on
// leda B_3200 on
// leda W484 on

// signal finished when in ph2 of last pd0 ram location write setup
assign ntlb_tram_cleared = (& ntlb_tram_clr_cnt) && (ntlb_pd0_ram_ph3);

wire   aux_cmd_preempt_update;
assign aux_cmd_preempt_update = (aux_mmu_cmd_wen & (jsm_state_r == JSM_UTLB_MISS1) & (!jtlb_cancel_update));

//assign mmu_ram_reset     = (jsm_state_r == JSM_RESET)
//                         | tlb_mmu_invalidate_nxt; //?

// JTLB State Machine (JSM) state
// (runs at 1x clk)
always @(posedge clk or posedge rst_a)
begin : jsm_state_PROC
  if (rst_a == 1'b1)
  begin
    ntlb_pd0_ram_ph1      <= 1'b1;
    ntlb_pd0_ram_ph2      <= 1'b0;
    mmu_ready             <= 1'b0;
    jsm_state_r           <= 5'b0;

    stlb_read_r           <= 1'b0;
    stlb_rslt_valid_r     <= 1'b0;
    stlb_req_valid_r      <= 1'b0;
    stlb_reset_lru_r      <= 1'b0;
    mntlb_reset_lru_r     <= 1'b0;
    jtlb_dtlb_cmd_r       <= 4'h0;

    utlb_update_active_r  <= 1'b0;

    jrsp_itlb_update      <= 1'b0; 
    jrsp_dtlb_update      <= 1'b0; 

    jtlb_rd_sel_r         <= 3'b0;
    jtlb_lkup_sel_r       <= 2'b0;
  end
  else
  begin
    ntlb_pd0_ram_ph1      <= ntlb_pd0_clken;
    ntlb_pd0_ram_ph2      <= ntlb_pd0_ram_ph1;
    mmu_ready             <= mmu_ready          // sticky
                          || ntlb_tram_cleared  // set
                          || rst_init_disable_r
                           ;
    jsm_state_r           <= jsm_state_nxt;
    stlb_read_r           <= stlb_read_nxt;
    stlb_rslt_valid_r     <= stlb_rslt_valid_nxt     // _r will be valid in jsm rslt2 or miss2
                          && (!aux_cmd_preempt_update); // if not cancelled utlb update (2cyc)
    stlb_req_valid_r      <= stlb_req_valid_nxt;
    stlb_reset_lru_r      <= stlb_reset_lru_nxt;

    mntlb_reset_lru_r      <= mntlb_reset_lru_nxt;

    jtlb_dtlb_cmd_r       <= jtlb_dtlb_cmd_nxt;

    utlb_update_active_r  <= utlb_update_active_nxt;

    jrsp_itlb_update      <= jrsp_itlb_update_nxt; 
    jrsp_dtlb_update      <= jrsp_dtlb_update_nxt; 

    jtlb_rd_sel_r         <= jtlb_rd_sel_nxt;
    jtlb_lkup_sel_r       <= jtlb_lkup_sel_nxt;
  end
end

// itlb update result
//
always @(posedge clk or posedge rst_a)
begin : itlb_update_PROC
  if (rst_a == 1'b1)
  begin
    jrsp_itlb_update_hit  <= 1'b0;
    jrsp_itlb_multi_hit   <= 1'b0;
    jrsp_itlb_tlb_err     <= 1'b0;
  end
  else if (jrsp_itlb_update_nxt)
  begin
    jrsp_itlb_update_hit  <= jrsp_itlb_update_hit_nxt;
    jrsp_itlb_multi_hit   <= jrsp_itlb_multi_hit_nxt;
    jrsp_itlb_tlb_err     <=  jrsp_itlb_tlb_err_nxt
                            & (~ecc_mmu_disable);
  end
end

// dtlb update result
//
always @(posedge clk or posedge rst_a)
begin : dtlb_update_PROC
  if (rst_a == 1'b1)
  begin
    jrsp_dtlb_update_hit  <= 1'b0;
    jrsp_dtlb_multi_hit   <= 1'b0;
    jrsp_dtlb_tlb_err     <= 1'b0;
  end
  else if (jrsp_dtlb_update_nxt)
  begin
    jrsp_dtlb_update_hit  <= jrsp_dtlb_update_hit_nxt;
    jrsp_dtlb_multi_hit   <= jrsp_dtlb_multi_hit_nxt;
    jrsp_dtlb_tlb_err     <=  jrsp_dtlb_tlb_err_nxt
                            & (~ecc_mmu_disable);
  end
end

always @(posedge clk or posedge rst_a)
begin : jtlb_itlb_cmd_PROC
  if (rst_a == 1'b1)
  begin
    jtlb_itlb_cmd_r       <= 4'h0;
  end
  // deassert itlb cmd (and ifu restart) at begin of clk2 period
  else
  begin
    jtlb_itlb_cmd_r       <= jtlb_itlb_cmd_nxt;
  end
end


// restart IFU on important MMU state change
//
reg mmu_aux_strict_sr_r;
reg jtlb_itlb_cmd_act_r;

always @(posedge clk or posedge rst_a)
begin : mmu_cmd_active_PROC
  if (rst_a == 1'b1)
  begin
    mmu_cmd_active      <= 1'b0;
    mmu_aux_strict_sr_r <= 1'b0;
    jtlb_itlb_cmd_act_r <= 1'b0;
  end
  else
  begin
    mmu_aux_strict_sr_r <= mmu_aux_strict_sr;
    jtlb_itlb_cmd_act_r <= (| jtlb_itlb_cmd_r);

    mmu_cmd_active <= (aux_mmu_cmd_wen & (| mmu_cmd_nxt))
                    | (aux_mmu_pid_wen)
                    | (aux_mmu_sls0_wen)
                    | (aux_mmu_sls1_wen)
                    | (| jtlb_itlb_cmd_nxt)
                    | (| jtlb_itlb_cmd_r)
                    | (  jtlb_itlb_cmd_act_r);
  end
end

// hold lookup address from utlbs, pd0
//
always @(posedge clk or posedge rst_a)
begin : jtlb_lkup_vpn_PROC
  if (rst_a == 1'b1)
  begin
    jtlb_lkup_vpn_r       <= `npuarc_PD0_VPN_WIDTH'd0;
  end
  else if (jtlb_lkup_vpn_cg0)
  begin
    jtlb_lkup_vpn_r       <= jtlb_lkup_vpn_nxt;
  end
end



// Latched lookup start for dtlb update
//
wire   dtlb_update_pend_cg0;
assign dtlb_update_pend_cg0 = wa_jtlb_lookup_start_r | jrsp_dtlb_update | (~dtlb_update_req);

always @(posedge clk or posedge rst_a)
begin : jtlb_lookup_start_PROC
  if (rst_a == 1'b1)
  begin
    dtlb_update_pend_r <= 1'b0;
  end
  else if (dtlb_update_pend_cg0)
  begin
    dtlb_update_pend_r <= wa_jtlb_lookup_start_r ? 1'b1 :                     // set
                          ( 
                            (jrsp_dtlb_update | (~dtlb_update_req) ) ? 1'b0 : // clr
                               dtlb_update_pend_r                             // hold
                          );
  end
end


// Clock request
//
wire   mmu_clock_req_cg0;
assign mmu_clock_req_cg0 = aux_mmu_ren_r | aux_mmu_wen_r | (|aux_mmu_cmd_r) | wa_restart_r;

always @(posedge clk or posedge rst_a)
begin : mmu_clock_req_PROC
  if (rst_a == 1'b1)
  begin
    mmu_clock_req_r <= 1'b0;
  end
  else if (mmu_clock_req_cg0)
  begin
    mmu_clock_req_r <= (aux_mmu_ren_r | aux_mmu_wen_r | (|aux_mmu_cmd_r)) ? 1'b1 :  // set
                       (
                         (wa_restart_r) ? 1'b0 :                                    // clr
                            mmu_clock_req_r                                         // hold
                       );
  end
end


// leda NTL_RST03 off
// leda S_1C_R off
// LMD: All registers must be asynchronously set or reset
// LJ:  Datapath
// register utlb update data
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
always @(posedge clk)
begin : jtlb_update_data_reg_PROC
  if (jtlb_update_data_cg0)
  jtlb_update_data <= jtlb_update_data_nxt;
end
// leda NTL_RST03 on
// leda S_1C_R on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// NTLB Write Data Path                                                   //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

// NTLB write data
//-----------------
// The four ways have identical write data except the valid (lsb) bit
// (note order is different from aux reg pd0 and PTE pd0; v bit is lsb)

wire [`npuarc_NTLB_PD0_WAY0_DATA_RANGE] ntlb_pd0_wdata_way0;   // each way
assign  ntlb_pd0_wdata_way0 = 
    {pd0_vpn_r[`npuarc_PD0_VPN_WIDTH-1:`npuarc_NTLB_PD0_ADDR_WIDTH], // tag part
     pd0_asid_r,
     pd0_shared_r,
     pd0_global_r,
     pd0_size_r,
     ntlb_wdata_lbit_way[0],  // hw also modifies lock bit...
     ntlb_wdata_vbit_way[0]   // hw also modifies valid bit...
     };

wire [`npuarc_NTLB_PD0_WAY0_DATA_RANGE] ntlb_pd0_wdata_way1;   // each way
assign  ntlb_pd0_wdata_way1 = 
    {pd0_vpn_r[`npuarc_PD0_VPN_WIDTH-1:`npuarc_NTLB_PD0_ADDR_WIDTH], // tag part
     pd0_asid_r,
     pd0_shared_r,
     pd0_global_r,
     pd0_size_r,
     ntlb_wdata_lbit_way[1],  // hw also modifies lock bit...
     ntlb_wdata_vbit_way[1]   // hw also modifies valid bit...
     };

wire [`npuarc_NTLB_PD0_WAY0_DATA_RANGE] ntlb_pd0_wdata_way2;   // each way
assign  ntlb_pd0_wdata_way2 = 
    {pd0_vpn_r[`npuarc_PD0_VPN_WIDTH-1:`npuarc_NTLB_PD0_ADDR_WIDTH], // tag part
     pd0_asid_r,
     pd0_shared_r,
     pd0_global_r,
     pd0_size_r,
     ntlb_wdata_lbit_way[2],  // hw also modifies lock bit...
     ntlb_wdata_vbit_way[2]   // hw also modifies valid bit...
     };

wire [`npuarc_NTLB_PD0_WAY0_DATA_RANGE] ntlb_pd0_wdata_way3;   // each way
assign  ntlb_pd0_wdata_way3 = 
    {pd0_vpn_r[`npuarc_PD0_VPN_WIDTH-1:`npuarc_NTLB_PD0_ADDR_WIDTH], // tag part
     pd0_asid_r,
     pd0_shared_r,
     pd0_global_r,
     pd0_size_r,
     ntlb_wdata_lbit_way[3],  // hw also modifies lock bit...
     ntlb_wdata_vbit_way[3]   // hw also modifies valid bit...
     };


///////////////////////////////////////////////////////////////////////////
//                                                                        //
// ECC code generation                                                    //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
wire [`npuarc_MMU_PD0_ECC_CODE_MSB:0]       pd0_wdata_way0_ecc;
wire [`npuarc_MMU_PD0_ECC_CODE_MSB:0]       pd0_wdata_way1_ecc;
wire [`npuarc_MMU_PD0_ECC_CODE_MSB:0]       pd0_wdata_way2_ecc;
wire [`npuarc_MMU_PD0_ECC_CODE_MSB:0]       pd0_wdata_way3_ecc;
wire [`npuarc_MMU_PD1_ECC_CODE_MSB:0]       pckd_pte_pd1_ecc;

npuarc_mmu_pd0_ecc_encoder u_alb_mmu_pd0_ecc_encoder_way0 (
  .data_in        (ntlb_pd0_wdata_way0),
  .ecc            (pd0_wdata_way0_ecc)
);

npuarc_mmu_pd0_ecc_encoder u_alb_mmu_pd0_ecc_encoder_way1 (
  .data_in        (ntlb_pd0_wdata_way1),
  .ecc            (pd0_wdata_way1_ecc)
);

npuarc_mmu_pd0_ecc_encoder u_alb_mmu_pd0_ecc_encoder_way2 (
  .data_in        (ntlb_pd0_wdata_way2),
  .ecc            (pd0_wdata_way2_ecc)
);

npuarc_mmu_pd0_ecc_encoder u_alb_mmu_pd0_ecc_encoder_way3 (
  .data_in        (ntlb_pd0_wdata_way3),
  .ecc            (pd0_wdata_way3_ecc)
);

npuarc_mmu_pd1_ecc_encoder u_alb_mmu_pd1_ecc_encoder (
  .data_in        (pckd_pte_pd1),
  .ecc            (pckd_pte_pd1_ecc)
);

assign  ntlb_pd0_wdata = { {pd0_wdata_way3_ecc, ntlb_pd0_wdata_way3},
                           {pd0_wdata_way2_ecc, ntlb_pd0_wdata_way2},
                           {pd0_wdata_way1_ecc, ntlb_pd0_wdata_way1},
                           {pd0_wdata_way0_ecc, ntlb_pd0_wdata_way0} };

assign  ntlb_pd1_wdata = { pckd_pte_pd1_ecc, pckd_pte_pd1 };


// leda NTL_CON13A off
// LMD: non driving internal net Range
// LJ:  Not all bits of bus used
wire [`npuarc_NTLB_PD0_WAY0_DATA_RANGE]  ecc_corrected_pd0_way0;
wire [`npuarc_NTLB_PD0_WAY0_DATA_RANGE]  ecc_corrected_pd0_way1;
wire [`npuarc_NTLB_PD0_WAY0_DATA_RANGE]  ecc_corrected_pd0_way2;
wire [`npuarc_NTLB_PD0_WAY0_DATA_RANGE]  ecc_corrected_pd0_way3;
wire [`npuarc_NTLB_PD1_WORD_RANGE]       ecc_corrected_pd1;

// leda NTL_CON13A on
///////////////////////////////////////////////////////////////////////////
//                                                                        //
// ECC error detection and correction                                                   //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
wire ecc_double_error_pd0_way0;
wire ecc_double_error_pd0_way1;
wire ecc_double_error_pd0_way2;
wire ecc_double_error_pd0_way3;
wire ecc_double_error_pd1;

wire ecc_unknown_error_pd0_way0;
wire ecc_unknown_error_pd0_way1;
wire ecc_unknown_error_pd0_way2;
wire ecc_unknown_error_pd0_way3;
wire ecc_unknown_error_pd1;


wire [`npuarc_MMU_PD0_ECC_CODE_MSB:0] corrected_ecc_pd0_way0;
wire [`npuarc_MMU_PD0_ECC_CODE_MSB:0] corrected_ecc_pd0_way1;
wire [`npuarc_MMU_PD0_ECC_CODE_MSB:0] corrected_ecc_pd0_way2;
wire [`npuarc_MMU_PD0_ECC_CODE_MSB:0] corrected_ecc_pd0_way3;
wire [`npuarc_MMU_PD1_ECC_CODE_MSB:0] corrected_ecc_pd1;


assign ecc_db_error_pd0_way0 = ecc_double_error_pd0_way0
                             | ecc_unknown_error_pd0_way0
							 ;

assign ecc_db_error_pd0_way1 = ecc_double_error_pd0_way1
                             | ecc_unknown_error_pd0_way1
							 ;

assign ecc_db_error_pd0_way2 = ecc_double_error_pd0_way2
                             | ecc_unknown_error_pd0_way2
							 ;

assign ecc_db_error_pd0_way3 = ecc_double_error_pd0_way3
                             | ecc_unknown_error_pd0_way3
							 ;

assign ecc_db_error_pd1 =      ecc_double_error_pd1
                             | ecc_unknown_error_pd1
							 ;								 

npuarc_mmu_pd0_ecc_decoder u_mmu_pd0_ecc_decoder_0 (
  .enable                     (!ecc_mmu_disable),
  .data_in                    (ntlb_pd0_rdata[`npuarc_NTLB_PD0_WAY0_DATA_RANGE]),
  .ecc_in                     (ntlb_pd0_rdata[`npuarc_NTLB_PD0_WAY0_ECC_RANGE]),

  .syndrome_out               (syndrome_pd0_way0),
  .single_err                 (ecc_sb_error_pd0_way0),
  .double_err                 (ecc_double_error_pd0_way0),
  .unknown_err                (ecc_unknown_error_pd0_way0),
  .ecc_out                    (corrected_ecc_pd0_way0),
  .data_out                   (ecc_corrected_pd0_way0)
);

npuarc_mmu_pd0_ecc_decoder u_mmu_pd0_ecc_decoder_1 (
  .enable                     (!ecc_mmu_disable),
  .data_in                    (ntlb_pd0_rdata[`npuarc_NTLB_PD0_WAY1_DATA_RANGE]),
  .ecc_in                     (ntlb_pd0_rdata[`npuarc_NTLB_PD0_WAY1_ECC_RANGE]),

  .syndrome_out               (syndrome_pd0_way1),
  .single_err                 (ecc_sb_error_pd0_way1),
  .double_err                 (ecc_double_error_pd0_way1),
  .unknown_err                (ecc_unknown_error_pd0_way1),
  .ecc_out                    (corrected_ecc_pd0_way1),
  .data_out                   (ecc_corrected_pd0_way1)
);

npuarc_mmu_pd0_ecc_decoder u_mmu_pd0_ecc_decoder_2 (
  .enable                     (!ecc_mmu_disable),
  .data_in                    (ntlb_pd0_rdata[`npuarc_NTLB_PD0_WAY2_DATA_RANGE]),
  .ecc_in                     (ntlb_pd0_rdata[`npuarc_NTLB_PD0_WAY2_ECC_RANGE]),

  .syndrome_out               (syndrome_pd0_way2),
  .single_err                 (ecc_sb_error_pd0_way2),
  .double_err                 (ecc_double_error_pd0_way2),
  .unknown_err                (ecc_unknown_error_pd0_way2),
  .ecc_out                    (corrected_ecc_pd0_way2),
  .data_out                   (ecc_corrected_pd0_way2)
);

npuarc_mmu_pd0_ecc_decoder u_mmu_pd0_ecc_decoder_3 (
  .enable                     (!ecc_mmu_disable),
  .data_in                    (ntlb_pd0_rdata[`npuarc_NTLB_PD0_WAY3_DATA_RANGE]),
  .ecc_in                     (ntlb_pd0_rdata[`npuarc_NTLB_PD0_WAY3_ECC_RANGE]),

  .syndrome_out               (syndrome_pd0_way3),
  .single_err                 (ecc_sb_error_pd0_way3),
  .double_err                 (ecc_double_error_pd0_way3),
  .unknown_err                (ecc_unknown_error_pd0_way3),
  .ecc_out                    (corrected_ecc_pd0_way3),
  .data_out                   (ecc_corrected_pd0_way3)
);

npuarc_mmu_pd1_ecc_decoder u_mmu_pd1_ecc_decoder (
  .enable                     (!ecc_mmu_disable),
  .data_in                    (ntlb_pd1_rdata[`npuarc_NTLB_PD1_WORD_RANGE]),
  .ecc_in                     (ntlb_pd1_rdata[`npuarc_NTLB_PD1_ECC_RANGE]),

  .syndrome_out               (syndrome_pd1),
  .single_err                 (ecc_sb_error_pd1),
  .double_err                 (ecc_double_error_pd1),
  .unknown_err                (ecc_unknown_error_pd1),
  .ecc_out                    (corrected_ecc_pd1),
  .data_out                   (ecc_corrected_pd1)
);

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Normal-page TLB (ntlb) RAMS                                            //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

npuarc_clkgate u_ntlb_pd0_clkgate (
  .clk_in            (clk),
  .clock_enable      (ntlb_pd0_clken),
  .clk_out           (ntlb_pd0_clk)
);

npuarc_clkgate u_ntlb_pd1_clkgate (
  .clk_in            (clk),
  .clock_enable      (ntlb_pd1_clken),
  .clk_out           (ntlb_pd1_clk)
);


// NTLB ram output mux sel is rd index or lookup match
assign ntlb_out_way_sel = ntlb_rdwr_op ? 
                          ntlb_rd_way_sel :
                          ntlb_rslt_match_way;

// NTLB read way mux
// (packed and missing index part of vpn)
always @*
begin : ntlb_out_way_sel_PROC
  case (ntlb_out_way_sel)
    2'h0: ntlb_pd0_way_rdata = ecc_corrected_pd0_way0[`npuarc_NTLB_PD0_WAY0_DATA_RANGE];
    2'h1: ntlb_pd0_way_rdata = ecc_corrected_pd0_way1[`npuarc_NTLB_PD0_WAY0_DATA_RANGE];
    2'h2: ntlb_pd0_way_rdata = ecc_corrected_pd0_way2[`npuarc_NTLB_PD0_WAY0_DATA_RANGE];
    2'h3: ntlb_pd0_way_rdata = ecc_corrected_pd0_way3[`npuarc_NTLB_PD0_WAY0_DATA_RANGE];
  endcase // case (ntlb_out_way_sel)
end


// Form the uTLB update data (packed PTE format)
// restore index part of vpn (use reg'd lkup address)
assign pckd_ntlb_pte = {ecc_corrected_pd1[`npuarc_NTLB_PD1_WORD_RANGE],
                        Insert_index_ntlb_pd0(ntlb_pd0_way_rdata[`npuarc_NTLB_PD0_WAY0_DATA_RANGE],
                                              jtlb_lkup_vpn_rr[`npuarc_NTLB_PD0_ADDR_MSB:0])
                       };

// LR read data (entry) unregistered; loads pd0,pd1 aux regs
// (first convert to Arch pd format)
assign ntlb_entry_rd_data = {Unpk_pd1(ecc_corrected_pd1[`npuarc_NTLB_PD1_WORD_RANGE]),
                             Unpk_ntlb_pd0(ntlb_pd0_way_rdata[`npuarc_NTLB_PD0_WAY0_DATA_RANGE],
                                           ntlb_pd0_addr)
                            }; 

// leda NTL_CON12A off
// LMD: undriven internal net Range
// LJ:  index bits of ntlb ram not stored (unused bits of bus)

// leda NTL_CON13A off
// LMD: non driving internal net Range
// LJ:  Not all bits of bus used
// extract fields from NTLB pd0 ram unregistered output: way 4
//
wire [`npuarc_NTLB_PD0_WAY0_DATA_RANGE] ntlb_pd0_rdata_way0;
assign ntlb_pd0_rdata_way0 = ecc_corrected_pd0_way0[`npuarc_NTLB_PD0_WAY0_DATA_RANGE];
wire [`npuarc_NTLB_PD0_WAY0_DATA_RANGE] ntlb_pd0_rdata_way1;
assign ntlb_pd0_rdata_way1 = ecc_corrected_pd0_way1[`npuarc_NTLB_PD0_WAY0_DATA_RANGE];
wire [`npuarc_NTLB_PD0_WAY0_DATA_RANGE] ntlb_pd0_rdata_way2;
assign ntlb_pd0_rdata_way2 = ecc_corrected_pd0_way2[`npuarc_NTLB_PD0_WAY0_DATA_RANGE];
wire [`npuarc_NTLB_PD0_WAY0_DATA_RANGE] ntlb_pd0_rdata_way3;
assign ntlb_pd0_rdata_way3 = ecc_corrected_pd0_way3[`npuarc_NTLB_PD0_WAY0_DATA_RANGE];

// pd0 raw outputs used in match logic
assign ntlb_out_way0_shared_nxt  = ntlb_pd0_rdata_way0[`npuarc_NTLB_PD0_SHARED];
assign ntlb_out_way0_vpn_tag_nxt = ntlb_pd0_rdata_way0[`npuarc_NTLB_PD0_TAG_MSB:
                                                             `npuarc_NTLB_PD0_TAG_LSB];
assign ntlb_out_way0_lock_nxt    = ntlb_pd0_rdata_way0[`npuarc_NTLB_PD0_LOCK];
assign ntlb_out_way0_valid_nxt   = ntlb_pd0_rdata_way0[`npuarc_NTLB_PD0_VALID];
assign ntlb_out_way0_global_nxt  = ntlb_pd0_rdata_way0[`npuarc_NTLB_PD0_GLOBAL];
assign ntlb_out_way0_asid_nxt    = ntlb_pd0_rdata_way0[`npuarc_NTLB_PD0_ASID_MSB:
                                                             `npuarc_NTLB_PD0_ASID_LSB];

// pd0 raw outputs used in match logic
assign ntlb_out_way1_shared_nxt  = ntlb_pd0_rdata_way1[`npuarc_NTLB_PD0_SHARED];
assign ntlb_out_way1_vpn_tag_nxt = ntlb_pd0_rdata_way1[`npuarc_NTLB_PD0_TAG_MSB:
                                                             `npuarc_NTLB_PD0_TAG_LSB];
assign ntlb_out_way1_lock_nxt    = ntlb_pd0_rdata_way1[`npuarc_NTLB_PD0_LOCK];
assign ntlb_out_way1_valid_nxt   = ntlb_pd0_rdata_way1[`npuarc_NTLB_PD0_VALID];
assign ntlb_out_way1_global_nxt  = ntlb_pd0_rdata_way1[`npuarc_NTLB_PD0_GLOBAL];
assign ntlb_out_way1_asid_nxt    = ntlb_pd0_rdata_way1[`npuarc_NTLB_PD0_ASID_MSB:
                                                             `npuarc_NTLB_PD0_ASID_LSB];

// pd0 raw outputs used in match logic
assign ntlb_out_way2_shared_nxt  = ntlb_pd0_rdata_way2[`npuarc_NTLB_PD0_SHARED];
assign ntlb_out_way2_vpn_tag_nxt = ntlb_pd0_rdata_way2[`npuarc_NTLB_PD0_TAG_MSB:
                                                             `npuarc_NTLB_PD0_TAG_LSB];
assign ntlb_out_way2_lock_nxt    = ntlb_pd0_rdata_way2[`npuarc_NTLB_PD0_LOCK];
assign ntlb_out_way2_valid_nxt   = ntlb_pd0_rdata_way2[`npuarc_NTLB_PD0_VALID];
assign ntlb_out_way2_global_nxt  = ntlb_pd0_rdata_way2[`npuarc_NTLB_PD0_GLOBAL];
assign ntlb_out_way2_asid_nxt    = ntlb_pd0_rdata_way2[`npuarc_NTLB_PD0_ASID_MSB:
                                                             `npuarc_NTLB_PD0_ASID_LSB];

// pd0 raw outputs used in match logic
assign ntlb_out_way3_shared_nxt  = ntlb_pd0_rdata_way3[`npuarc_NTLB_PD0_SHARED];
assign ntlb_out_way3_vpn_tag_nxt = ntlb_pd0_rdata_way3[`npuarc_NTLB_PD0_TAG_MSB:
                                                             `npuarc_NTLB_PD0_TAG_LSB];
assign ntlb_out_way3_lock_nxt    = ntlb_pd0_rdata_way3[`npuarc_NTLB_PD0_LOCK];
assign ntlb_out_way3_valid_nxt   = ntlb_pd0_rdata_way3[`npuarc_NTLB_PD0_VALID];
assign ntlb_out_way3_global_nxt  = ntlb_pd0_rdata_way3[`npuarc_NTLB_PD0_GLOBAL];
assign ntlb_out_way3_asid_nxt    = ntlb_pd0_rdata_way3[`npuarc_NTLB_PD0_ASID_MSB:
                                                             `npuarc_NTLB_PD0_ASID_LSB];

// leda NTL_CON12A on
// leda NTL_CON13A on


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// NTLB Look-up logic: checking vpn/asid/sasid against valid TLB entries  //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

//--------------------------------------------------------------------------
// NTLB Match Logic
//--------------------------------------------------------------------------

always @*
begin :  i_ntlb_match_PROC

  // compute shared-ASID match
  //
  ntlb_rslt_sasid_match[0] = (shared_en_r &
                 (
                    sasid_r[ ntlb_out_way0_asid_nxt[`npuarc_PD0_SLIX_RANGE] ]
                  | cmd_rr_op_deleteis
                 ));
  ntlb_rslt_sasid_match[1] = (shared_en_r &
                 (
                    sasid_r[ ntlb_out_way1_asid_nxt[`npuarc_PD0_SLIX_RANGE] ]
                  | cmd_rr_op_deleteis
                 ));
  ntlb_rslt_sasid_match[2] = (shared_en_r &
                 (
                    sasid_r[ ntlb_out_way2_asid_nxt[`npuarc_PD0_SLIX_RANGE] ]
                  | cmd_rr_op_deleteis
                 ));
  ntlb_rslt_sasid_match[3] = (shared_en_r &
                 (
                    sasid_r[ ntlb_out_way3_asid_nxt[`npuarc_PD0_SLIX_RANGE] ]
                  | cmd_rr_op_deleteis
                 ));
  //--------------------------------------------------------------------------
  // Compare request vpn/asid with each way of NTLB set, masking vpn bits not 
  // needed by the programmed size of each mapping.


  //--------------------------------------------
  //  Entry 0
  //--------------------------------------------
  // Compare VPN field and check entry valid bit
  ntlb_rslt_vpn_match[0] = 
      ( ~(| (ntlb_req_vpn_tag_rr ^ ntlb_out_way0_vpn_tag_nxt) ) )
    & (ntlb_out_way0_valid_nxt)
    & (~ecc_db_error_pd0_way0)
    ;

  // Check if global or shared and evaluate SASID or Compare ASID 
  ntlb_rslt_pid_match[0] = 
    // Global highest priority
    (ntlb_out_way0_global_nxt | (tlb_eager_match & pd0_global_rr) |
    // ...then shared
        ( (ntlb_out_way0_shared_nxt) ?
          // if shared entry; check appropriate sasid reg bit and global en
          ntlb_rslt_sasid_match[0] :
          // not global, or shared; check asid
          (~(|(jtlb_req_asid_2cyc ^ ntlb_out_way0_asid_nxt)) )
        )
      );
  
  //--------------------------------------------
  //  Entry 1
  //--------------------------------------------
  // Compare VPN field and check entry valid bit
  ntlb_rslt_vpn_match[1] = 
      ( ~(| (ntlb_req_vpn_tag_rr ^ ntlb_out_way1_vpn_tag_nxt) ) )
    & (ntlb_out_way1_valid_nxt)
    & (~ecc_db_error_pd0_way1)
    ;

  // Check if global or shared and evaluate SASID or Compare ASID 
  ntlb_rslt_pid_match[1] = 
    // Global highest priority
    (ntlb_out_way1_global_nxt | (tlb_eager_match & pd0_global_rr) |
    // ...then shared
        ( (ntlb_out_way1_shared_nxt) ?
          // if shared entry; check appropriate sasid reg bit and global en
          ntlb_rslt_sasid_match[1] :
          // not global, or shared; check asid
          (~(|(jtlb_req_asid_2cyc ^ ntlb_out_way1_asid_nxt)) )
        )
      );
  
  //--------------------------------------------
  //  Entry 2
  //--------------------------------------------
  // Compare VPN field and check entry valid bit
  ntlb_rslt_vpn_match[2] = 
      ( ~(| (ntlb_req_vpn_tag_rr ^ ntlb_out_way2_vpn_tag_nxt) ) )
    & (ntlb_out_way2_valid_nxt)
    & (~ecc_db_error_pd0_way2)
    ;

  // Check if global or shared and evaluate SASID or Compare ASID 
  ntlb_rslt_pid_match[2] = 
    // Global highest priority
    (ntlb_out_way2_global_nxt | (tlb_eager_match & pd0_global_rr) |
    // ...then shared
        ( (ntlb_out_way2_shared_nxt) ?
          // if shared entry; check appropriate sasid reg bit and global en
          ntlb_rslt_sasid_match[2] :
          // not global, or shared; check asid
          (~(|(jtlb_req_asid_2cyc ^ ntlb_out_way2_asid_nxt)) )
        )
      );
  
  //--------------------------------------------
  //  Entry 3
  //--------------------------------------------
  // Compare VPN field and check entry valid bit
  ntlb_rslt_vpn_match[3] = 
      ( ~(| (ntlb_req_vpn_tag_rr ^ ntlb_out_way3_vpn_tag_nxt) ) )
    & (ntlb_out_way3_valid_nxt)
    & (~ecc_db_error_pd0_way3)
    ;

  // Check if global or shared and evaluate SASID or Compare ASID 
  ntlb_rslt_pid_match[3] = 
    // Global highest priority
    (ntlb_out_way3_global_nxt | (tlb_eager_match & pd0_global_rr) |
    // ...then shared
        ( (ntlb_out_way3_shared_nxt) ?
          // if shared entry; check appropriate sasid reg bit and global en
          ntlb_rslt_sasid_match[3] :
          // not global, or shared; check asid
          (~(|(jtlb_req_asid_2cyc ^ ntlb_out_way3_asid_nxt)) )
        )
      );
  


  //  Results for lookup port `q::
  //--------------------------------------------
  
  //  Each entry's match result (result vector: 1 bit per entry)
  //  
  ntlb_rslt_entry_match = 
                      ntlb_rslt_vpn_match
                    & ntlb_rslt_pid_match;

  // final match result; valid lookup matched any entry
  //  
  ntlb_rslt_match  =  (|ntlb_rslt_entry_match)
                    & ntlb_pd0_rslt_valid_nxt;

//  ntlb_rslt_miss   = ~(|ntlb_rslt_entry_match) 
//                    & ntlb_pd0_rslt_valid_nxt;

  // Find lowest set bit (one-hot result)
  ntlb_rslt_entry_match_raw_1h = find_first_set_1h(ntlb_rslt_entry_match);


  // Find match index (of lowest set bit)
  ntlb_rslt_match_way    = find_first_set(ntlb_rslt_entry_match);


// Check for multiple hits
  ntlb_rslt_multiple_match = test_multi_set(ntlb_rslt_entry_match);

end // block: i_match_PROC
  

// collect status bits of invalid 
always @*
begin :  i_inval_status_PROC
  ntlb_invalid_entries = {
                    ~ntlb_out_way3_valid_nxt,
                    ~ntlb_out_way2_valid_nxt,
                    ~ntlb_out_way1_valid_nxt,
                    ~ntlb_out_way0_valid_nxt
                   };
end

// collect lock status bits of mntlb
always @*
begin :  i_ntlb_lock_bits_PROC
  ntlb_locked_entries = {
                    ntlb_out_way3_lock_nxt,
                    ntlb_out_way2_lock_nxt,
                    ntlb_out_way1_lock_nxt,
                    ntlb_out_way0_lock_nxt
                   };
end

// check if ntlb_invalid entry available (for update)
assign ntlb_inval_entry_avail = | ntlb_invalid_entries;
// Find lowest invalid entry (for update)
assign ntlb_inval_entry_1h = find_first_set_1h(ntlb_invalid_entries);


// NTLB 'lru' bits (1h, not per set)
always @(posedge clk or posedge rst_a)
begin : ntlb_lru_reg_PROC
  if (rst_a == 1'b1)
  begin
    ntlb_lru_entry_1h_r <= `npuarc_NTLB_NUM_WAYS'h1;
  end
  else
  begin
    ntlb_lru_entry_1h_r <= mntlb_reset_lru_r ? 4'd1 : ntlb_lru_entry_1h_nxt;
  end
end


///////////////////////////////////////////////////////////////////////////
// Generic functions used to generate lookup results
//  
// leda B_3008_A off
// LMD: Unrecommended blocking assignment (converting integer to unsigned)
// LJ:  Comb logic
// spyglass disable_block W164a
// SMD: LHS < RHS in assignment
// SJ:  using int for loop var, then in assignments (upper bits assumed 0)
// spyglass disable_block W480
// SMD: Loop index 'i' is not of type integer
// SJ:  Need specific width

// Find lowest set bit (one-hot result)
//
function automatic [`npuarc_NTLB_WAYS_RANGE] find_first_set_1h (
  input [`npuarc_NTLB_WAYS_RANGE] vec );
  reg found_one;
  integer i;
  begin
    found_one = 1'b0;
    find_first_set_1h = `npuarc_NTLB_NUM_WAYS'd0;
    for (i=0; i<`npuarc_NTLB_NUM_WAYS; i=i+1)
    begin
      if (~found_one) // stop looking after first one
      begin
        if (vec[i]) 
        begin
          found_one = 1'b1;
          find_first_set_1h[i] = 1'b1;
        end
      end
    end
  end
endfunction
        

// spyglass disable_block W416
// SMD: Return type width 'm' is less than return value width 'n'
// SJ:  Only LSB few bits of integer i are used (auto-truncated)

// Find lowest set bit (bit ptr result)
//
function automatic [`npuarc_NTLB_WAY_PTR_RANGE] find_first_set (
  input [`npuarc_NTLB_WAYS_RANGE] vec );
  reg found_one;
  integer i;
  begin
    found_one = 1'b0;
    find_first_set = `npuarc_NTLB_WAY_PTR_WIDTH'd0;
    for (i=0; i<`npuarc_NTLB_NUM_WAYS; i=i+1)
    begin
      if (~found_one) // stop looking after first one
      begin
        if (vec[i]) 
        begin
          found_one = 1'b1;
          find_first_set = i;
        end
      end
    end
  end
endfunction
// spyglass enable_block W416
        

// leda W489 off
//
function automatic test_multi_set (
  input [`npuarc_NTLB_WAYS_RANGE] vec );
  reg found_one;
  integer i;
  begin
    found_one = 1'b0;
    test_multi_set = 1'b0;
    for (i=0; i<`npuarc_NTLB_NUM_WAYS; i=i+1)
    begin
      if (vec[i]) 
      begin
        if (found_one)
          test_multi_set = 1'b1;
        found_one = 1'b1;
      end
    end
  end
endfunction
// leda W489 on
        

// Find set bit in one-hot vector (bit ptr result) 
// (simple encoder, input width for NTLB)
function automatic [`npuarc_NTLB_WAY_PTR_RANGE] Enc_ntlb_rslt;
  input [`npuarc_NTLB_WAYS_RANGE] in_1h;
  reg [`npuarc_NTLB_WAY_PTR_WIDTH:0] i;
  reg [`npuarc_NTLB_WAY_PTR_RANGE] j;
  begin
    j = `npuarc_NTLB_WAY_PTR_WIDTH'd0;
    for (i=0; i<`npuarc_NTLB_NUM_WAYS; i=i+1) 
    begin
      if (in_1h[i]) j = i;
    end
    Enc_ntlb_rslt = j;
  end
endfunction


// leda B_3008_A on
// spyglass enable_block W164a
// spyglass enable_block W480


///////////////////////////////////////////////////////////////////////////
// Generic functions used to generate lookup results
//  
// leda B_3008_A off
// LMD: Unrecommended blocking assignment (converting integer to unsigned)
// LJ:  Comb logic
// spyglass disable_block W164a
// SMD: LHS < RHS in assignment
// SJ:  using int for loop var, then in assignments (upper bits assumed 0)
// spyglass disable_block W480
// SMD: Loop index 'i' is not of type integer
// SJ:  Need specific width

// Find set bit in one-hot vector (bit ptr result) 
// (simple encoder, input width for STLB)
function automatic [`npuarc_STLB_INDEX_RANGE] Enc_stlb_rslt;
  input [`npuarc_STLB_ENTRIES_RANGE] in_1h;
  reg [`npuarc_STLB_INDEX_WIDTH:0] i;
  reg [`npuarc_STLB_INDEX_RANGE] j;
  begin
    j = `npuarc_STLB_INDEX_WIDTH'd0;
    for (i=0; i<`npuarc_MMU_STLB_NUM_ENTRIES; i=i+1) 
    begin
      if (in_1h[i]) j = i;
    end
    Enc_stlb_rslt = j;
  end
endfunction

// leda B_3008_A on
// spyglass enable_block W164a
// spyglass enable_block W480




////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Super-page TLB (stlb)                                                  //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
wire   stlb_rslt_match_cg0;
assign stlb_rslt_match_cg0 = stlb_rslt_valid_nxt && (!jtlb_cancel_update);

// Match result vector register
//
always @(posedge clk or posedge rst_a)
begin : stlb_lkup_rslt_reg_PROC
  if (rst_a == 1'b1)
  begin
    stlb_rslt_match_r          <= 1'b0;
    stlb_rslt_multiple_match_r <= 1'b0;
    stlb_rslt_entry_match_r    <= `npuarc_MMU_STLB_NUM_ENTRIES'd0;
    stlb_rslt_entry_match_1h_r <= `npuarc_MMU_STLB_NUM_ENTRIES'd0;
  end
  else if (stlb_rslt_match_cg0)
  begin
    stlb_rslt_match_r          <= stlb_rslt_match;
    stlb_rslt_multiple_match_r <= stlb_rslt_multiple_match;
    stlb_rslt_entry_match_r    <= stlb_rslt_entry_match;
    stlb_rslt_entry_match_1h_r <= stlb_rslt_entry_match_1h;
  end
end

// Match result / write op index register
//
always @(posedge clk or posedge rst_a)
begin : stlb_match_index_reg_PROC
  if (rst_a == 1'b1)
  begin
    stlb_write_r <= 1'b0;
  end
  else
  begin
    stlb_write_r               <= stlb_write;
  end
end

//---------------------------------------------------------------------------
// Form the write enables for Updating utlb entries
//---------------------------------------------------------------------------
//
//  1. For jtlb update, if no inval entry avail, update the LRU entry
//  2. for JCMD_INSERT, if miss and if no inval entry avail, update the LRU 
//     entry
//  3. For jtlb update, if inval entry avail, update the inval entry
//     with lowest index
//  4. for JCMD_INSERT, if miss and if inval entry avail, update the inval
//     entry with lowest index
//  5. for JCMD_INSERT, if hit, update hit entry with lowest index and 
//     (elsewhere) inval other hit entries (if any)
//  6. for JCMD_WRITE, update entry indexed by jtlb supplied index
//
// fyi: During invalidation only the valid bits of all entries are cleared.
//

always @* 
begin :  stlb_entry_write_PROC
  // Replace selected (lru) entry
  casez ({stlb_update, // unused
          stlb_insert, 
          stlb_rslt_match_r,  // raw port0 match ( <-jcmd )
          stlb_inval_entry_avail,
          stlb_write_r
        })
    5'b1??0?,                                                            // (1)
    5'b0100?: stlb_entry_update_1h[0] = stlb_lru_entry_1h[0];          // (2)
    5'b1??1?,                                                            // (3)
    5'b0101?: stlb_entry_update_1h[0] = stlb_inval_entry_1h[0];        // (4)
    5'b011??: stlb_entry_update_1h[0] = stlb_rslt_entry_match_1h_r[0]; // (5)
    5'b00??1: stlb_entry_update_1h[0] = stlb_aux_index_1h[0];          // (6)
    default:  stlb_entry_update_1h[0] = 1'b0;
  endcase
  // Replace selected (lru) entry
  casez ({stlb_update, // unused
          stlb_insert, 
          stlb_rslt_match_r,  // raw port0 match ( <-jcmd )
          stlb_inval_entry_avail,
          stlb_write_r
        })
    5'b1??0?,                                                            // (1)
    5'b0100?: stlb_entry_update_1h[1] = stlb_lru_entry_1h[1];          // (2)
    5'b1??1?,                                                            // (3)
    5'b0101?: stlb_entry_update_1h[1] = stlb_inval_entry_1h[1];        // (4)
    5'b011??: stlb_entry_update_1h[1] = stlb_rslt_entry_match_1h_r[1]; // (5)
    5'b00??1: stlb_entry_update_1h[1] = stlb_aux_index_1h[1];          // (6)
    default:  stlb_entry_update_1h[1] = 1'b0;
  endcase
  // Replace selected (lru) entry
  casez ({stlb_update, // unused
          stlb_insert, 
          stlb_rslt_match_r,  // raw port0 match ( <-jcmd )
          stlb_inval_entry_avail,
          stlb_write_r
        })
    5'b1??0?,                                                            // (1)
    5'b0100?: stlb_entry_update_1h[2] = stlb_lru_entry_1h[2];          // (2)
    5'b1??1?,                                                            // (3)
    5'b0101?: stlb_entry_update_1h[2] = stlb_inval_entry_1h[2];        // (4)
    5'b011??: stlb_entry_update_1h[2] = stlb_rslt_entry_match_1h_r[2]; // (5)
    5'b00??1: stlb_entry_update_1h[2] = stlb_aux_index_1h[2];          // (6)
    default:  stlb_entry_update_1h[2] = 1'b0;
  endcase
  // Replace selected (lru) entry
  casez ({stlb_update, // unused
          stlb_insert, 
          stlb_rslt_match_r,  // raw port0 match ( <-jcmd )
          stlb_inval_entry_avail,
          stlb_write_r
        })
    5'b1??0?,                                                            // (1)
    5'b0100?: stlb_entry_update_1h[3] = stlb_lru_entry_1h[3];          // (2)
    5'b1??1?,                                                            // (3)
    5'b0101?: stlb_entry_update_1h[3] = stlb_inval_entry_1h[3];        // (4)
    5'b011??: stlb_entry_update_1h[3] = stlb_rslt_entry_match_1h_r[3]; // (5)
    5'b00??1: stlb_entry_update_1h[3] = stlb_aux_index_1h[3];          // (6)
    default:  stlb_entry_update_1h[3] = 1'b0;
  endcase
  // Replace selected (lru) entry
  casez ({stlb_update, // unused
          stlb_insert, 
          stlb_rslt_match_r,  // raw port0 match ( <-jcmd )
          stlb_inval_entry_avail,
          stlb_write_r
        })
    5'b1??0?,                                                            // (1)
    5'b0100?: stlb_entry_update_1h[4] = stlb_lru_entry_1h[4];          // (2)
    5'b1??1?,                                                            // (3)
    5'b0101?: stlb_entry_update_1h[4] = stlb_inval_entry_1h[4];        // (4)
    5'b011??: stlb_entry_update_1h[4] = stlb_rslt_entry_match_1h_r[4]; // (5)
    5'b00??1: stlb_entry_update_1h[4] = stlb_aux_index_1h[4];          // (6)
    default:  stlb_entry_update_1h[4] = 1'b0;
  endcase
  // Replace selected (lru) entry
  casez ({stlb_update, // unused
          stlb_insert, 
          stlb_rslt_match_r,  // raw port0 match ( <-jcmd )
          stlb_inval_entry_avail,
          stlb_write_r
        })
    5'b1??0?,                                                            // (1)
    5'b0100?: stlb_entry_update_1h[5] = stlb_lru_entry_1h[5];          // (2)
    5'b1??1?,                                                            // (3)
    5'b0101?: stlb_entry_update_1h[5] = stlb_inval_entry_1h[5];        // (4)
    5'b011??: stlb_entry_update_1h[5] = stlb_rslt_entry_match_1h_r[5]; // (5)
    5'b00??1: stlb_entry_update_1h[5] = stlb_aux_index_1h[5];          // (6)
    default:  stlb_entry_update_1h[5] = 1'b0;
  endcase
  // Replace selected (lru) entry
  casez ({stlb_update, // unused
          stlb_insert, 
          stlb_rslt_match_r,  // raw port0 match ( <-jcmd )
          stlb_inval_entry_avail,
          stlb_write_r
        })
    5'b1??0?,                                                            // (1)
    5'b0100?: stlb_entry_update_1h[6] = stlb_lru_entry_1h[6];          // (2)
    5'b1??1?,                                                            // (3)
    5'b0101?: stlb_entry_update_1h[6] = stlb_inval_entry_1h[6];        // (4)
    5'b011??: stlb_entry_update_1h[6] = stlb_rslt_entry_match_1h_r[6]; // (5)
    5'b00??1: stlb_entry_update_1h[6] = stlb_aux_index_1h[6];          // (6)
    default:  stlb_entry_update_1h[6] = 1'b0;
  endcase
  // Replace selected (lru) entry
  casez ({stlb_update, // unused
          stlb_insert, 
          stlb_rslt_match_r,  // raw port0 match ( <-jcmd )
          stlb_inval_entry_avail,
          stlb_write_r
        })
    5'b1??0?,                                                            // (1)
    5'b0100?: stlb_entry_update_1h[7] = stlb_lru_entry_1h[7];          // (2)
    5'b1??1?,                                                            // (3)
    5'b0101?: stlb_entry_update_1h[7] = stlb_inval_entry_1h[7];        // (4)
    5'b011??: stlb_entry_update_1h[7] = stlb_rslt_entry_match_1h_r[7]; // (5)
    5'b00??1: stlb_entry_update_1h[7] = stlb_aux_index_1h[7];          // (6)
    default:  stlb_entry_update_1h[7] = 1'b0;
  endcase
  // Replace selected (lru) entry
  casez ({stlb_update, // unused
          stlb_insert, 
          stlb_rslt_match_r,  // raw port0 match ( <-jcmd )
          stlb_inval_entry_avail,
          stlb_write_r
        })
    5'b1??0?,                                                            // (1)
    5'b0100?: stlb_entry_update_1h[8] = stlb_lru_entry_1h[8];          // (2)
    5'b1??1?,                                                            // (3)
    5'b0101?: stlb_entry_update_1h[8] = stlb_inval_entry_1h[8];        // (4)
    5'b011??: stlb_entry_update_1h[8] = stlb_rslt_entry_match_1h_r[8]; // (5)
    5'b00??1: stlb_entry_update_1h[8] = stlb_aux_index_1h[8];          // (6)
    default:  stlb_entry_update_1h[8] = 1'b0;
  endcase
  // Replace selected (lru) entry
  casez ({stlb_update, // unused
          stlb_insert, 
          stlb_rslt_match_r,  // raw port0 match ( <-jcmd )
          stlb_inval_entry_avail,
          stlb_write_r
        })
    5'b1??0?,                                                            // (1)
    5'b0100?: stlb_entry_update_1h[9] = stlb_lru_entry_1h[9];          // (2)
    5'b1??1?,                                                            // (3)
    5'b0101?: stlb_entry_update_1h[9] = stlb_inval_entry_1h[9];        // (4)
    5'b011??: stlb_entry_update_1h[9] = stlb_rslt_entry_match_1h_r[9]; // (5)
    5'b00??1: stlb_entry_update_1h[9] = stlb_aux_index_1h[9];          // (6)
    default:  stlb_entry_update_1h[9] = 1'b0;
  endcase
  // Replace selected (lru) entry
  casez ({stlb_update, // unused
          stlb_insert, 
          stlb_rslt_match_r,  // raw port0 match ( <-jcmd )
          stlb_inval_entry_avail,
          stlb_write_r
        })
    5'b1??0?,                                                            // (1)
    5'b0100?: stlb_entry_update_1h[10] = stlb_lru_entry_1h[10];          // (2)
    5'b1??1?,                                                            // (3)
    5'b0101?: stlb_entry_update_1h[10] = stlb_inval_entry_1h[10];        // (4)
    5'b011??: stlb_entry_update_1h[10] = stlb_rslt_entry_match_1h_r[10]; // (5)
    5'b00??1: stlb_entry_update_1h[10] = stlb_aux_index_1h[10];          // (6)
    default:  stlb_entry_update_1h[10] = 1'b0;
  endcase
  // Replace selected (lru) entry
  casez ({stlb_update, // unused
          stlb_insert, 
          stlb_rslt_match_r,  // raw port0 match ( <-jcmd )
          stlb_inval_entry_avail,
          stlb_write_r
        })
    5'b1??0?,                                                            // (1)
    5'b0100?: stlb_entry_update_1h[11] = stlb_lru_entry_1h[11];          // (2)
    5'b1??1?,                                                            // (3)
    5'b0101?: stlb_entry_update_1h[11] = stlb_inval_entry_1h[11];        // (4)
    5'b011??: stlb_entry_update_1h[11] = stlb_rslt_entry_match_1h_r[11]; // (5)
    5'b00??1: stlb_entry_update_1h[11] = stlb_aux_index_1h[11];          // (6)
    default:  stlb_entry_update_1h[11] = 1'b0;
  endcase
  // Replace selected (lru) entry
  casez ({stlb_update, // unused
          stlb_insert, 
          stlb_rslt_match_r,  // raw port0 match ( <-jcmd )
          stlb_inval_entry_avail,
          stlb_write_r
        })
    5'b1??0?,                                                            // (1)
    5'b0100?: stlb_entry_update_1h[12] = stlb_lru_entry_1h[12];          // (2)
    5'b1??1?,                                                            // (3)
    5'b0101?: stlb_entry_update_1h[12] = stlb_inval_entry_1h[12];        // (4)
    5'b011??: stlb_entry_update_1h[12] = stlb_rslt_entry_match_1h_r[12]; // (5)
    5'b00??1: stlb_entry_update_1h[12] = stlb_aux_index_1h[12];          // (6)
    default:  stlb_entry_update_1h[12] = 1'b0;
  endcase
  // Replace selected (lru) entry
  casez ({stlb_update, // unused
          stlb_insert, 
          stlb_rslt_match_r,  // raw port0 match ( <-jcmd )
          stlb_inval_entry_avail,
          stlb_write_r
        })
    5'b1??0?,                                                            // (1)
    5'b0100?: stlb_entry_update_1h[13] = stlb_lru_entry_1h[13];          // (2)
    5'b1??1?,                                                            // (3)
    5'b0101?: stlb_entry_update_1h[13] = stlb_inval_entry_1h[13];        // (4)
    5'b011??: stlb_entry_update_1h[13] = stlb_rslt_entry_match_1h_r[13]; // (5)
    5'b00??1: stlb_entry_update_1h[13] = stlb_aux_index_1h[13];          // (6)
    default:  stlb_entry_update_1h[13] = 1'b0;
  endcase
  // Replace selected (lru) entry
  casez ({stlb_update, // unused
          stlb_insert, 
          stlb_rslt_match_r,  // raw port0 match ( <-jcmd )
          stlb_inval_entry_avail,
          stlb_write_r
        })
    5'b1??0?,                                                            // (1)
    5'b0100?: stlb_entry_update_1h[14] = stlb_lru_entry_1h[14];          // (2)
    5'b1??1?,                                                            // (3)
    5'b0101?: stlb_entry_update_1h[14] = stlb_inval_entry_1h[14];        // (4)
    5'b011??: stlb_entry_update_1h[14] = stlb_rslt_entry_match_1h_r[14]; // (5)
    5'b00??1: stlb_entry_update_1h[14] = stlb_aux_index_1h[14];          // (6)
    default:  stlb_entry_update_1h[14] = 1'b0;
  endcase
  // Replace selected (lru) entry
  casez ({stlb_update, // unused
          stlb_insert, 
          stlb_rslt_match_r,  // raw port0 match ( <-jcmd )
          stlb_inval_entry_avail,
          stlb_write_r
        })
    5'b1??0?,                                                            // (1)
    5'b0100?: stlb_entry_update_1h[15] = stlb_lru_entry_1h[15];          // (2)
    5'b1??1?,                                                            // (3)
    5'b0101?: stlb_entry_update_1h[15] = stlb_inval_entry_1h[15];        // (4)
    5'b011??: stlb_entry_update_1h[15] = stlb_rslt_entry_match_1h_r[15]; // (5)
    5'b00??1: stlb_entry_update_1h[15] = stlb_aux_index_1h[15];          // (6)
    default:  stlb_entry_update_1h[15] = 1'b0;
  endcase
end


//---------------------------------------------------------------------------
// Super-page TLB (stlb) instance                                         
//---------------------------------------------------------------------------

npuarc_ustlb   u_ustlb(  // re-use utlb module
  .clk                      (clk),                // Processor clock
  .rst                      (rst_a),              // Global reset
  .rst_init_disable_r       (rst_init_disable_r),



  .alloc_entries            (5'd`npuarc_MMU_STLB_NUM_ENTRIES), // (fixed)

  // Shared ASID
  .shared_en_r              (shared_en_r),    // Shared lib enable (PID)
  .sasid_r                  (sasid_r),        // Current pid slib membership
  .sasid_force_match        (cmd_rr_op_deleteis),

  // Request lookup
  .req0_valid_r             (stlb_req_valid_r),
  .req0_vpn_r               (jtlb_lkup_vpn_rr2),  // 2cyc
  .req0_asid_r              (jtlb_req_asid_2cyc), // asid: stlb=jtlb
  .eager_match              (tlb_eager_match),

  //  Lookup result
  .rslt0_match              (stlb_rslt_match),
  .rslt0_miss               (stlb_rslt_miss),
  .rslt0_match_index        (stlb_rslt_match_index),
  .rslt0_match_size         (stlb_rslt_match_size),
  .rslt0_multiple_match     (stlb_rslt_multiple_match),
  // for lru logic (n-hot)
  .rslt0_entry_match        (stlb_rslt_entry_match),
  .rslt0_entry_match_1h     (stlb_rslt_entry_match_1h),

  .rslt0_ppn_out            (stlb_rslt_ppn),
  .rslt0_user_attr_out      (stlb_rslt_user_attr),
  .rslt0_wr_thru_out        (stlb_rslt_wr_thru),
  .rslt0_perm_out           (stlb_rslt_perm),
  .rslt0_cached_out         (stlb_rslt_cached),

  ////////// Invalidate select sTLB entries /////////////////////////////////
  .invalidate_entries       (stlb_invalidate_entries), // Invalidate/unlock select entries
  .unlock_entries           (stlb_reset_lru_r),        // Unlock all entries

  .inval_entry_avail        (stlb_inval_entry_avail), // Current invalid entries
  .inval_entry_1h           (stlb_inval_entry_1h), // lowest index invalid entry

  ////////// Interface to read stlb entries /////////////////////////////////
  //
  .entry_rd_val             (stlb_read_r),        // read operation this cycle
  .entry_rd_addr            (stlb_aux_index_rr),  // Aux address for read
  .entry_rd_data            (pckd_stlb_pte),      // LR entry read data (pckd)

  ////////// Interface to write stlb entries ////////////////////////////////
  //
  .entry_update_1h          (stlb_entry_update_1h),
  .entry_update_data        (pckd_data_pte)       // new entry from aux cmd
);


// Unpack utlb read data (PTE -> {pd1,pd0})
//
assign   stlb_entry_rd_data = 
  {
   Unpk_pd1(pckd_stlb_pte[`npuarc_PCKD_PTE_PD1_RANGE]),
   Unpk_pd0(pckd_stlb_pte[`npuarc_PCKD_PTE_PD0_RANGE])
  }; 

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// LRU logic instance                                                     //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
assign stlb_lru_match_entry = stlb_rslt_entry_matchx_1h // stlb matches (one-hot, single match)
                             | stlb_entry_update_1h;     // keep newly inserted entry

npuarc_plru16 u_plru16 (
  .clk           (clk),
  .rst           (rst_a),
  .match_entry   (stlb_lru_match_entry),

  .lru_entry     (stlb_lru_entry_1h)     // entry selected for replacement
);







// Unpack utlb read data (PTE -> {pd1,pd0})
//
assign   itlb_entry_rd_data = 
  {
   Unpk_pd1(itlb_rd_data[`npuarc_PCKD_PTE_PD1_RANGE]),
   Unpk_pd0(itlb_rd_data[`npuarc_PCKD_PTE_PD0_RANGE])
  }; 

// Unpack utlb read data (PTE -> {pd1,pd0})
//
assign   dtlb_entry_rd_data = 
  {
   Unpk_pd1(dtlb_rd_data[`npuarc_PCKD_PTE_PD1_RANGE]),
   Unpk_pd0(dtlb_rd_data[`npuarc_PCKD_PTE_PD0_RANGE])
  }; 


//------------------------------------------------------------------------
// Unpack the read data from TLBs pckd pd0 to form the 32b PD0 register
// (and set reserved bits 0)
//------------------------------------------------------------------------
function automatic [`npuarc_DATA_RANGE] Unpk_pd0(
  input [`npuarc_PCKD_PD0_RANGE] ntlb0
  );
  begin
    Unpk_pd0                = {`npuarc_DATA_SIZE{1'b0}}; // to set reserved bits 0

    // ntlb cache tag portion of VPN
    Unpk_pd0[`npuarc_PD0_SHARED]   = ntlb0[`npuarc_PCKD_PD0_SHARED];
    Unpk_pd0[`npuarc_PD0_VPN_MSB:
             `npuarc_PD0_VPN_LSB]  = ntlb0[`npuarc_PCKD_PD0_VPN_MSB:
                                    `npuarc_PCKD_PD0_VPN_LSB];
    Unpk_pd0[`npuarc_PD0_SIZE]     = ntlb0[`npuarc_PCKD_PD0_SIZE];
    Unpk_pd0[`npuarc_PD0_LOCK]     = ntlb0[`npuarc_PCKD_PD0_LOCK];
    Unpk_pd0[`npuarc_PD0_VALID]    = ntlb0[`npuarc_PCKD_PD0_VALID];
    Unpk_pd0[`npuarc_PD0_GLOBAL]   = ntlb0[`npuarc_PCKD_PD0_GLOBAL];
    Unpk_pd0[`npuarc_PD0_ASID_MSB:
             `npuarc_PD0_ASID_LSB] = ntlb0[`npuarc_PCKD_PD0_ASID_MSB:
                                    `npuarc_PCKD_PD0_ASID_LSB];
  end
endfunction // Unpk_pd0

//------------------------------------------------------------------------
// Unpack the read data from TLBs pckd pd1 to form the 32b PD1 register
// (and set reserved bits 0)
//------------------------------------------------------------------------
function automatic [`npuarc_PTE_PD1_RANGE] Unpk_pd1(
  input [`npuarc_PCKD_PD1_RANGE] ntlb1
  );
  begin
    Unpk_pd1   = {`npuarc_PTE_PD1_WIDTH{1'b0}}; // to set reserved bits 0
    
    Unpk_pd1[`npuarc_PD1_PPN_MSB:
             `npuarc_PD1_PPN_LSB] = ntlb1[`npuarc_PCKD_PD1_PPN_MSB:
                                   `npuarc_PCKD_PD1_PPN_LSB];
    Unpk_pd1[`npuarc_PD1_UA_MSB:
             `npuarc_PD1_UA_LSB]  = ntlb1[`npuarc_PCKD_PD1_UA_MSB:
                                   `npuarc_PCKD_PD1_UA_LSB];
    Unpk_pd1[`npuarc_PD1_WR_THRU] = ntlb1[`npuarc_PCKD_PD1_WR_THRU];
    Unpk_pd1[`npuarc_PD1_PERM_KR] = ntlb1[`npuarc_PCKD_PD1_PERM_KR];
    Unpk_pd1[`npuarc_PD1_PERM_KW] = ntlb1[`npuarc_PCKD_PD1_PERM_KW];
    Unpk_pd1[`npuarc_PD1_PERM_KX] = ntlb1[`npuarc_PCKD_PD1_PERM_KX];
    Unpk_pd1[`npuarc_PD1_PERM_UR] = ntlb1[`npuarc_PCKD_PD1_PERM_UR];
    Unpk_pd1[`npuarc_PD1_PERM_UW] = ntlb1[`npuarc_PCKD_PD1_PERM_UW];
    Unpk_pd1[`npuarc_PD1_PERM_UX] = ntlb1[`npuarc_PCKD_PD1_PERM_UX];
    Unpk_pd1[`npuarc_PD1_CACHED]  = ntlb1[`npuarc_PCKD_PD1_CACHED];

  end
endfunction // Unpk_pd1

//------------------------------------------------------------------------
// Unpack the read data from <NTLB> pd0 ram to form the 32b PD0 register
// (and set reserved bits 0, and index bits of vpn to the index itself)
//------------------------------------------------------------------------
function automatic [`npuarc_DATA_RANGE] Unpk_ntlb_pd0(
  input [`npuarc_NTLB_PD0_WAY0_DATA_RANGE] ntlb0,
  input [`npuarc_NTLB_PD0_ADDR_WIDTH-1:0] index0
  );
  begin
    Unpk_ntlb_pd0                = {`npuarc_DATA_SIZE{1'b0}}; // to set reserved bits 0

    // ntlb cache tag portion of VPN
    Unpk_ntlb_pd0[`npuarc_PD0_VPN_MSB:
                  `npuarc_PD0_VPN_LSB+`npuarc_NTLB_PD0_ADDR_WIDTH] 
                                 = ntlb0[`npuarc_NTLB_PD0_TAG_MSB:
                                         `npuarc_NTLB_PD0_TAG_LSB];

    // ntlb cache index portion of VPN (not rd/wr bits, fixed to index value)
    Unpk_ntlb_pd0[`npuarc_PD0_VPN_LSB+`npuarc_NTLB_PD0_ADDR_WIDTH-1:
                  `npuarc_PD0_VPN_LSB] = index0;

    Unpk_ntlb_pd0[`npuarc_PD0_ASID_MSB:
                  `npuarc_PD0_ASID_LSB] = ntlb0[`npuarc_NTLB_PD0_ASID_MSB:
                                         `npuarc_NTLB_PD0_ASID_LSB];
    Unpk_ntlb_pd0[`npuarc_PD0_SHARED]   = ntlb0[`npuarc_NTLB_PD0_SHARED];
    Unpk_ntlb_pd0[`npuarc_PD0_LOCK]     = ntlb0[`npuarc_NTLB_PD0_LOCK];
    Unpk_ntlb_pd0[`npuarc_PD0_SIZE]     = ntlb0[`npuarc_NTLB_PD0_SIZE];
    Unpk_ntlb_pd0[`npuarc_PD0_GLOBAL]   = ntlb0[`npuarc_NTLB_PD0_GLOBAL];
    Unpk_ntlb_pd0[`npuarc_PD0_VALID]    = ntlb0[`npuarc_NTLB_PD0_VALID];
  end
endfunction // Unpk_ntlb_pd0


//------------------------------------------------------------------------
// Unpack the read data from <NTLB> pd0 ram to form packed pd0 data for
// utlb update data.
// (and set reserved bits 0, and index bits of vpn to the index itself)
//------------------------------------------------------------------------
function automatic [`npuarc_PCKD_PD0_RANGE] Insert_index_ntlb_pd0(
  input [`npuarc_NTLB_PD0_WAY0_DATA_RANGE] ntlb0,
  input [`npuarc_NTLB_PD0_ADDR_WIDTH-1:0] index0
  );
  begin
    Insert_index_ntlb_pd0                = {`npuarc_PCKD_PD0_WIDTH{1'b0}};

    // ntlb cache tag portion of VPN
    Insert_index_ntlb_pd0[`npuarc_PCKD_PD0_VPN_MSB:
                  `npuarc_PCKD_PD0_VPN_LSB+`npuarc_NTLB_PD0_ADDR_WIDTH] 
                                 = ntlb0[`npuarc_NTLB_PD0_TAG_MSB:
                                         `npuarc_NTLB_PD0_TAG_LSB];

    // ntlb cache index portion of VPN (not rd/wr bits, fixed to index value)
    Insert_index_ntlb_pd0[`npuarc_PCKD_PD0_VPN_LSB+`npuarc_NTLB_PD0_ADDR_WIDTH-1:
                  `npuarc_PCKD_PD0_VPN_LSB] = index0;

    Insert_index_ntlb_pd0[`npuarc_PCKD_PD0_ASID_MSB:
                  `npuarc_PCKD_PD0_ASID_LSB] = ntlb0[`npuarc_NTLB_PD0_ASID_MSB:
                                         `npuarc_NTLB_PD0_ASID_LSB];
    Insert_index_ntlb_pd0[`npuarc_PCKD_PD0_SHARED]   = ntlb0[`npuarc_NTLB_PD0_SHARED];
    Insert_index_ntlb_pd0[`npuarc_PCKD_PD0_LOCK]     = ntlb0[`npuarc_NTLB_PD0_LOCK];
    Insert_index_ntlb_pd0[`npuarc_PCKD_PD0_SIZE]     = ntlb0[`npuarc_NTLB_PD0_SIZE];
    Insert_index_ntlb_pd0[`npuarc_PCKD_PD0_GLOBAL]   = ntlb0[`npuarc_NTLB_PD0_GLOBAL];
    Insert_index_ntlb_pd0[`npuarc_PCKD_PD0_VALID]    = ntlb0[`npuarc_NTLB_PD0_VALID];
  end
endfunction // Unpk_ntlb_pd0_insert_index


 assign ntlb_pd0_ram_ce = ntlb_pd0_ce;
 assign ntlb_pd0_ram_we = ntlb_pd0_we;
 assign ntlb_pd0_ram_wem[7:4] = {4{~ecc_mmu_disable}};
 assign ntlb_pd0_ram_wem[3:0] = ntlb_pd0_wem;
 assign ntlb_pd0_ram_addr = ntlb_pd0_addr;
 assign ntlb_pd0_ram_wdata = ntlb_pd0_wdata;
 assign ntlb_pd0_rdata = ntlb_pd0_ram_rdata_r;
  // NTLB PD1 (data) ram interface
 assign ntlb_pd1_ram_ce = ntlb_pd1_ce;
 assign ntlb_pd1_ram_we = ntlb_pd1_we;
 assign ntlb_pd1_ram_addr = ntlb_pd1_addr;
 assign ntlb_pd1_ram_wdata = ntlb_pd1_wdata;
 assign ntlb_pd1_rdata = ntlb_pd1_ram_rdata_r;



wire ecc_mmu_sbe_count_cg0;
assign ecc_mmu_sbe_count_cg0 = ecc_mmu_sbe_count_set_cg0 | ecc_mmu_sbe_count_clr_cg0;

always @(posedge clk or posedge rst_a)
begin : ecc_mmu_sbe_count_reg_PROC
  if (rst_a == 1'b1)
  begin
    ecc_mmu_sbe_count_r   <= 4'b0000;
  end
  else
  begin
    if (ecc_mmu_sbe_count_cg0)
      ecc_mmu_sbe_count_r <= ecc_mmu_sbe_count_set_cg0 ? ecc_mmu_sbe_count_nxt :  // update
                             (
                               ecc_mmu_sbe_count_clr_cg0 ? 4'b0000 :              // clr
                                 ecc_mmu_sbe_count_r                              // hold
                              );
  end  
end


always @(posedge clk or posedge rst_a)
begin : dtlb_syndrome_reg_PROC
  if (rst_a == 1'b1)
  begin
    fs_dtlb_bank0_syndrome_r     <= {`npuarc_MMU_PD0_SYNDROME_MSB+1{1'b0}};
    fs_dtlb_bank1_syndrome_r     <= {`npuarc_MMU_PD0_SYNDROME_MSB+1{1'b0}};
    fs_dtlb_bank2_syndrome_r     <= {`npuarc_MMU_PD0_SYNDROME_MSB+1{1'b0}};
    fs_dtlb_bank3_syndrome_r     <= {`npuarc_MMU_PD0_SYNDROME_MSB+1{1'b0}};
    fs_dtlb_bank4_syndrome_r     <= {`npuarc_MMU_PD1_SYNDROME_MSB+1{1'b0}};

    fs_dtlb_bank0_ecc_sb_error_r <= 1'b0;
    fs_dtlb_bank1_ecc_sb_error_r <= 1'b0;
    fs_dtlb_bank2_ecc_sb_error_r <= 1'b0;
    fs_dtlb_bank3_ecc_sb_error_r <= 1'b0;
    fs_dtlb_bank4_ecc_sb_error_r <= 1'b0;

    fs_dtlb_bank0_ecc_db_error_r <= 1'b0;
    fs_dtlb_bank1_ecc_db_error_r <= 1'b0;
    fs_dtlb_bank2_ecc_db_error_r <= 1'b0;
    fs_dtlb_bank3_ecc_db_error_r <= 1'b0;
    fs_dtlb_bank4_ecc_db_error_r <= 1'b0;

  end
  else
  begin
    if (dtlb_syndrome_set_cg0 || dtlb_syndrome_set_cg1)
    begin
      fs_dtlb_bank0_syndrome_r    <= fs_dtlb_bank0_syndrome_nxt;
      fs_dtlb_bank1_syndrome_r    <= fs_dtlb_bank1_syndrome_nxt;
      fs_dtlb_bank2_syndrome_r    <= fs_dtlb_bank2_syndrome_nxt;
      fs_dtlb_bank3_syndrome_r    <= fs_dtlb_bank3_syndrome_nxt;

      fs_dtlb_bank0_ecc_sb_error_r<= ecc_sb_error_pd0_way0;
      fs_dtlb_bank1_ecc_sb_error_r<= ecc_sb_error_pd0_way1;
      fs_dtlb_bank2_ecc_sb_error_r<= ecc_sb_error_pd0_way2;
      fs_dtlb_bank3_ecc_sb_error_r<= ecc_sb_error_pd0_way3;

      fs_dtlb_bank0_ecc_db_error_r<= ecc_db_error_pd0_way0;
      fs_dtlb_bank1_ecc_db_error_r<= ecc_db_error_pd0_way1;
      fs_dtlb_bank2_ecc_db_error_r<= ecc_db_error_pd0_way2;
      fs_dtlb_bank3_ecc_db_error_r<= ecc_db_error_pd0_way3;

    end
    if (dtlb_syndrome_set_cg1)
    begin
      fs_dtlb_bank4_syndrome_r    <= fs_dtlb_bank4_syndrome_nxt;

      fs_dtlb_bank4_ecc_sb_error_r<= ecc_sb_error_pd1;

      fs_dtlb_bank4_ecc_db_error_r<= ecc_db_error_pd1;

    end
  end  
end

always @(posedge clk or posedge rst_a)
begin : itlb_syndrome_reg_PROC
  if (rst_a == 1'b1)
  begin
    fs_itlb_bank0_syndrome_r     <= {`npuarc_MMU_PD0_SYNDROME_MSB+1{1'b0}};
    fs_itlb_bank1_syndrome_r     <= {`npuarc_MMU_PD0_SYNDROME_MSB+1{1'b0}};
    fs_itlb_bank2_syndrome_r     <= {`npuarc_MMU_PD0_SYNDROME_MSB+1{1'b0}};
    fs_itlb_bank3_syndrome_r     <= {`npuarc_MMU_PD0_SYNDROME_MSB+1{1'b0}};
    fs_itlb_bank4_syndrome_r     <= {`npuarc_MMU_PD1_SYNDROME_MSB+1{1'b0}};

    fs_itlb_bank0_ecc_sb_error_r <= 1'b0;
    fs_itlb_bank1_ecc_sb_error_r <= 1'b0;
    fs_itlb_bank2_ecc_sb_error_r <= 1'b0;
    fs_itlb_bank3_ecc_sb_error_r <= 1'b0;
    fs_itlb_bank4_ecc_sb_error_r <= 1'b0;

    fs_itlb_bank0_ecc_db_error_r <= 1'b0;
    fs_itlb_bank1_ecc_db_error_r <= 1'b0;
    fs_itlb_bank2_ecc_db_error_r <= 1'b0;
    fs_itlb_bank3_ecc_db_error_r <= 1'b0;
    fs_itlb_bank4_ecc_db_error_r <= 1'b0;

  end
  else
  begin
    if (itlb_syndrome_set_cg0 || itlb_syndrome_set_cg1)
    begin   
      fs_itlb_bank0_syndrome_r    <= fs_itlb_bank0_syndrome_nxt;
      fs_itlb_bank1_syndrome_r    <= fs_itlb_bank1_syndrome_nxt;
      fs_itlb_bank2_syndrome_r    <= fs_itlb_bank2_syndrome_nxt;
      fs_itlb_bank3_syndrome_r    <= fs_itlb_bank3_syndrome_nxt;

      fs_itlb_bank0_ecc_sb_error_r<= ecc_sb_error_pd0_way0;
      fs_itlb_bank1_ecc_sb_error_r<= ecc_sb_error_pd0_way1;
      fs_itlb_bank2_ecc_sb_error_r<= ecc_sb_error_pd0_way2;
      fs_itlb_bank3_ecc_sb_error_r<= ecc_sb_error_pd0_way3;

      fs_itlb_bank0_ecc_db_error_r<= ecc_db_error_pd0_way0;
      fs_itlb_bank1_ecc_db_error_r<= ecc_db_error_pd0_way1;
      fs_itlb_bank2_ecc_db_error_r<= ecc_db_error_pd0_way2;
      fs_itlb_bank3_ecc_db_error_r<= ecc_db_error_pd0_way3;

    end
    if (itlb_syndrome_set_cg1)
    begin   
      fs_itlb_bank4_syndrome_r    <= fs_itlb_bank4_syndrome_nxt;

      fs_itlb_bank4_ecc_sb_error_r<= ecc_sb_error_pd1;

      fs_itlb_bank4_ecc_db_error_r<= ecc_db_error_pd1;

    end
  end  
end



endmodule
