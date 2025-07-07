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
//                     
//                     
//   ALB_DMP_STAGING                  
//                     
//                     
//                     
//
// ===========================================================================
//
// Description:
//  This module feeds the staging information for each pipeline stages.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_staging.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"


//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  rst: "rst_a", edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_dmp_staging (
// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ: some bits of inputs vectors are not used
  
  ////////// General input signals ///////////////////////////////////////////
  //
  input                          clk,            // clock
  input                          rst_a,          // reset
  input                          db_active_r,    // Debug instruction
  ////////// Interface to the X1/DC1 stage ///////////////////////////////
  //
  input                          x1_pass,              // X1  passing on ints
  input                          x1_load_r,      
  input                          x1_store_r,     
  input [1:0]                    x1_size_r, 
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input                          x1_cache_byp_r,
// spyglass enable_block W240
  input  [`npuarc_ADDR_RANGE]           x1_mem_addr0,   
  input  [`npuarc_ADDR_RANGE]           x1_mem_addr1,   
  input [`npuarc_DMP_TARGET_RANGE]      dc1_target,           // DC1 memory type  
  input [1:0]                    dc1_data_bank_sel_lo, // DC1 data bank sel
  input [1:0]                    dc1_data_bank_sel_hi, // DC1 data bank sel
  input [1:0]                    dc1_dt_bank_sel,    // tag even/odd
  input                          dc1_dt_line_cross,  // addr1 is valid
  input                          aux_cache_off,      // force uncached
  input  [3:0]                   aux_volatile_base_r,
  input  [3:0]                   aux_volatile_limit_r,
  input                          aux_volatile_strict_r,
  input                          aux_volatile_dis_r,
  input [3:0]                    aux_dmp_dcache_attr_r,     
  input                          aux_dmp_mem_attr_r,
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input [3:0]                    aux_dccm_r,         // DCCM base region
// spyglass enable_block W240
  input [7:0]          aux_memseg_r,       // MEMSEG register
  input                          ecc_dmp_disable,
  output reg [3:0]               dc1_rmw,
  ////////// Interface to the X2/DC2 stage ///////////////////////////////
  //
  input                          x2_pass,         
  input                          x2_load_r,      
  input                          x2_store_r, 
  input                          x2_exu_stall,

  input                          x2_cache_byp_r, 
  input                          x2_mpu_data_flt,      // 
  input                          x2_mpu_data_unc,     
  input                          x2_locked_r, 
  input                          x2_enable,      
  input [`npuarc_ADDR_RANGE]            x2_mem_addr0_r, 
  input [1:0]                    dc2_dtlb_efa_mux,
  input [1:0]                    dc2_dtlb_miss,
  input                          dc2_dtlb_miss_excpn,
  input                          dc2_dtlb_ovrlp_excpn,
  input                          dc2_dtlb_protv_excpn,
  input                          dc2_dtlb_ecc_error,
  input [`npuarc_PADDR_RANGE]           dtlb_rslt0_paddr,
  input [`npuarc_PADDR_RANGE]           dtlb_rslt1_paddr,
  output reg                     dtlb_lookup0_valid,
  output reg                     dtlb_lookup1_valid,
  input                          dtlb_rslt0_cached,
  output reg                     dc2_lkup1_npage_cross_r,
  input                          dc2_aux_pass,
  input [`npuarc_ADDR_RANGE]            dc2_aux_addr,
  input [7:0]                    dc2_aux_addr_hi,
  input                          dc2_aux_bank,
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
  output reg [`npuarc_ADDR_RANGE]       dc2_mem_addr1_r,        // DC2 addr plus size
// leda NTL_CON32 on
  output reg [1:0]               dc2_data_bank_sel_lo_r, 
  output reg [1:0]               dc2_data_bank_sel_hi_r, 
  output reg [`npuarc_DMP_TARGET_RANGE] dc2_target_r,           // DC2 memory type 
  output reg [3:0]               dc2_data_bank_sel_r,    // DC2 data bank
  output reg [3:0]               dc2_rmw,
  output reg                     dc2_volatile_region0,
  output reg                     dc2_volatile_region1, 
  output reg                     dc2_stuck,
  ////////// Interface to the X3/DC3 stage ///////////////////////////////
  //
  input                          x3_pass,           // X3 passing on instt
  input                          x3_load_r,      
  input                          x3_store_r,     
  input                          x3_pref_r,     
  input                          x3_pref_l2_r,     
  input                          x3_prefw_r,     
  input                          x3_pre_alloc_r,     
  input                          x3_locked_r,
  input                          x3_enable,         // X3 accepts new instruction
  output reg [`npuarc_PADDR_RANGE]      dc3_mem_addr0_r,
  output reg [`npuarc_ADDR_RANGE]       dc3_dtlb_efa,
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input      [`npuarc_ADDR_RANGE]       x3_mem_addr0_r,
// spyglass enable_block W240

  output reg                     dc3_pref,          // all sorts of pref
  output reg [`npuarc_DMP_TARGET_RANGE] dc3_target_r,      // DC3 memory type  
  output reg [2:0]               dc3_size0_r,       // DC3 size0  
  output reg [2:0]               dc3_size1_r,       // DC3 size1  
  output reg [`npuarc_PADDR_RANGE]      dc3_mem_addr1_r,   // DC3 addr plus size
  output reg [1:0]               dc3_data_bank_sel_lo_r, 
  output reg [1:0]               dc3_data_bank_sel_hi_r, 
  output reg [`npuarc_PADDR_RANGE]      dc3_mem_addr_even,
  output reg [`npuarc_PADDR_RANGE]      dc3_mem_addr_odd,
  output reg [1:0]               dc3_dt_bank_sel_r,   
  output reg                     dc3_dt_line_cross_r,    // addr1 is valid
  output reg                     dc3_enable,             // locally generated
  output reg [3:0]               dc3_rmw_r,
  output reg                     dc3_fwd_allowed_r,     // uncached st->ld fwd
  output reg                     dc3_dtlb_ecc_error_r,
  output reg [1:0]               dc3_dtlb_miss_r,
  output reg                     dc3_lkup1_page_cross_r,
  output                         dc3_dtlb_miss_excpn,
  output                         dc3_dtlb_ovrlp_excpn,
  output                         dc3_dtlb_protv_excpn,
  output                         dc3_dtlb_ecc_excpn,
  input                          dc3_mispred,
  ////////// Interface to the X4/DC4 stage ///////////////////////////////
  //
  input                          ca_load_r,
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input                          ca_store_r,
// spyglass enable_block W240
  input [1:0]                    ca_size_r,       // 00-b, 01-h, 10-w, 11-dw
  input [`npuarc_DMP_DATA_RANGE]        ca_wr_data_r,
  input                          ca_enable,       // CA acpt new isntr
  input                          ca_locked_r,     // CA locked
  input                          dc4_dt_miss_r,   // CA complete miss
  ////////// Interface to the WA stage ///////////////////////////////////
  //
  input [`npuarc_PADDR_RANGE]           wa_lpa_r,         // LPA reg 
  input                          wa_lock_flag_r,   // LF  reg value 
  input                          wa_lock_double_r, // LF  size value 

  ////////// Outputs ////////////////////////////////////////////////////
  //
  output reg                     dc4_dt_line_cross_r,    // addr1 is valid
  output reg [1:0]               dc4_dt_bank_sel_r,
  output reg                     dc4_pref_r,
  output reg                     dc4_pref_bad_r,        // Discard this pref
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
  output reg                     dc4_cache_byp_r,
// leda NTL_CON32 on
  output reg [`npuarc_DMP_TARGET_RANGE] dc4_target_r,          // DC4 memory type 
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
  output reg                     dc4_volatile_r,
// leda NTL_CON32 on  
  output reg                     dc4_strict_order_r,
  output reg [3:0]               dc4_data_mem_attr_r,
  output reg [2:0]               dc4_size0_r,    
  output reg [2:0]               dc4_size1_r,    
  output reg [`npuarc_PADDR_RANGE]      dc4_mem_addr0_r,
  output reg [`npuarc_PADDR_RANGE]      dc4_mem_addr1_r,
   output reg [3:0]              dc4_rmw_r,
  output reg                     dc4_scond_go,
  output reg                     dmp_clear_lf,
  output     [1:0]               dc4_dtlb_miss,
  output                         dc4_mispred,
  output reg [`npuarc_DMP_DATA_RANGE]   dc4_wr_data,
  input                          wa_restart_r,
  input                          wa_restart_kill_r,
  input                          wa_hlt_restart_r,

  output reg [1:0]               dc4_data_bank_sel_lo_r, 
  output reg [1:0]               dc4_data_bank_sel_hi_r

// leda NTL_CON37 on
// leda NTL_CON13C on
);


// Local Declarations

reg                     dc2_dt_line_cross_r;    // addr1 is valid

reg                     dc1_mem_pass;
reg                     dc2_mem_pass;
reg                     dc3_mem_pass;

reg  [1:0]              dc2_size_r;


reg [1:0]               dc2_dt_bank_sel_r;
reg [3:0]               dc2_rmw_prel_r;
reg                     dc2_cg0;
reg                     dc3_cg0;
reg                     dc4_cg0;

reg [`npuarc_PADDR_RANGE]      dc3_mem_addr1_nxt;
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg                     dc3_volatile_r;
// leda NTL_CON32 on
reg                     dc3_strict_order_r;

wire [2:0]              dc3_size0_nxt;
wire [2:0]              dc3_size1_nxt;
reg                     dc3_dt_bank_sel_cg0;
reg [1:0]               dc3_dt_bank_sel_nxt;
reg                     dc2_cache_byp_r;
reg                     dc3_cache_byp_r;
reg                     dc3_mpu_data_flt_r;

// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg [`npuarc_ADDR_RANGE]       dc3_dtlb_efa1_r;
reg  [1:0]              dc3_dtlb_efa_mux_r;         
// leda NTL_CON32 on
reg                     dc3_dtlb_miss_excpn_r;
reg                     dc3_dtlb_ovrlp_excpn_r;
reg                     dc3_dtlb_protv_excpn_r;
//  `if (`MMU_ECC == 1)
//reg                     dc3_dtlb_ecc_error_r;
//  `endif
reg [1:0]               dc4_dtlb_miss_r;

reg                     dc4_mispred_r;
//  `if (`DC_NEEDS_ALIAS_PRED == 0)
//reg [1:0]               dc3_dtlb_miss_r;
//  `endif


//////////////////////////////////////////////////////////////////////////////
// Asynchronous  logic defining clock gate enabled
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc1_dc2_dc3_mem_pass_PROC
  dc1_mem_pass = x1_pass & (x1_load_r | x1_store_r);
  dc2_mem_pass = x2_pass & (x2_load_r | x2_store_r);
  dc3_mem_pass = x3_pass & (x3_load_r | x3_store_r);
end

always @*
begin : dtlb_lookup_valid_PROC
  dtlb_lookup0_valid = (x2_load_r | x2_store_r);
  dtlb_lookup1_valid = (x2_load_r | x2_store_r);
end

always @*
begin : dc2_dc3_dc4_cg0_PROC
  dc2_cg0 = (dc1_mem_pass & x2_enable)     // open
          | dc2_mem_pass;                  // close
  
  dc3_cg0 = (  dc2_mem_pass 
             & x3_enable
            )                              // open
          | dc2_aux_pass
          | dc3_mem_pass                  // close
          ;                 

  dc4_cg0 = dc3_mem_pass & ca_enable;
end

////////////////////////////////////////////////////////////////////////////////
// Big Endian --> Little Endian conversion
//    Byte          HW           Word
//LE  b3 b2 b1 b0   b3 b2 b1 b0  b3 b2 b1 b0
//BE  b0 b1 b2 b3   b1 b0 b3 b2  b0 b1 b2 b3
// 
///////////////////////////////////////////////////////////////////////////////
always @*
begin : store_endian_PROC
  casez (ca_size_r)
     default: dc4_wr_data = ca_wr_data_r;
  endcase // case(ca_size_r)
end
   

reg                           dc1_partial;
//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Asynchronous block defining ECC dc1 logic for RMW (partial writes)
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc1_rmw_PROC
  dc1_partial   =  (x1_size_r   == 2'b00)
                 | (x1_size_r   == 2'b01)
                 | ((x1_size_r  == 2'b10) & (x1_mem_addr0[1:0] != 2'b00))
                 | ((x1_size_r  == 2'b11) & (x1_mem_addr0[1:0] != 2'b00))
                 ;
  
  dc1_rmw[0]     =    x1_store_r 
                  &   dc1_partial
                  &   (~ecc_dmp_disable);
                  
  dc1_rmw[1]     =    x1_store_r 
                  &   dc1_partial
                  &   (~ecc_dmp_disable);
                  
  dc1_rmw[2]     =    x1_store_r 
                  &   dc1_partial
                  &   (~ecc_dmp_disable); 
                  
  dc1_rmw[3]     =    x1_store_r 
                  &   dc1_partial
                  &   (~ecc_dmp_disable); 
                  
end

///////////////////////////////////////////////////////////////////////////////
// detect normal-page cross
//
//////////////////////////////////////////////////////////////////////////////
reg               dc1_lkup1_npage_cross;
always @*
begin : lkup1_npage_cross_PROC
  // Byte   -> never crosses
  // Half   -> crosses when [(11111)]
  // Word   -> crosses when [(111, > 00)]
  // Double -> crosses when [(11,  > 000)]
  //
  case (x1_size_r)
  2'b01:
    // Half-Word
    //
    dc1_lkup1_npage_cross = (& x1_mem_addr0[11:0]);
  2'b10:
    // Word
    //
    dc1_lkup1_npage_cross = (  (& x1_mem_addr0[11:2])
                       & (| x1_mem_addr0[1:0]));
  2'b11:
    // Double Word
    //
    dc1_lkup1_npage_cross = (  (& x1_mem_addr0[11:3])
                       & (| x1_mem_addr0[2:0]));
  default:
    // Byte
    //
    dc1_lkup1_npage_cross = 1'b0;
  endcase
end

//////////////////////////////////////////////////////////////////////////////
// Bank selection 
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc2_data_bank_PROC
  dc2_data_bank_sel_r =  {dc2_data_bank_sel_hi_r[1], dc2_data_bank_sel_lo_r[1],
                          dc2_data_bank_sel_hi_r[0], dc2_data_bank_sel_lo_r[0]};
end

//////////////////////////////////////////////////////////////////////////////
// Read Modify write
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc2_rmw_PROC
  dc2_rmw =   dc2_rmw_prel_r
            & {dc2_data_bank_sel_hi_r[1], dc2_data_bank_sel_lo_r[1],
               dc2_data_bank_sel_hi_r[0], dc2_data_bank_sel_lo_r[0]}
            & {4{x2_store_r}}
            & ( ({4{dc2_target_r == `npuarc_DMP_TARGET_DCCM}})
               |({4{dc2_target_r == `npuarc_DMP_TARGET_DC}}) );    
end          


//////////////////////////////////////////////////////////////////////////////
// Adjust dc2 target if necessary
//
//////////////////////////////////////////////////////////////////////////////
reg [`npuarc_DMP_TARGET_RANGE] dc2_target_nxt;

always @*
begin : dc2_target_nxt_PROC
  dc2_target_nxt = dc1_target;
  
  if (  (dc1_target == `npuarc_DMP_TARGET_DC)
      & aux_cache_off )
  begin
    dc2_target_nxt = `npuarc_DMP_TARGET_MEM;
  end
end


reg  dc2_dc_volatile_region0;
reg  dc2_dc_volatile_region1;
//////////////////////////////////////////////////////////////////////////////
//@ Check for accesess in the volatile region
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin: dc2_volatile_PROC 
  // Figure out what is the top volatile region
  //
  if (  (aux_volatile_limit_r == 4'b0000)
      | (aux_volatile_limit_r <= aux_volatile_base_r))
  begin
    dc2_volatile_region0 = (x2_mem_addr0_r[31:28] >= aux_volatile_base_r);
    dc2_volatile_region1 = (dc2_mem_addr1_r[31:28] >= aux_volatile_base_r);
  end
  else
  begin
    dc2_volatile_region0 =  (x2_mem_addr0_r[31:28] >= aux_volatile_base_r)
                          & (x2_mem_addr0_r[31:28] < aux_volatile_limit_r); 
    dc2_volatile_region1 =  (dc2_mem_addr1_r[31:28] >= aux_volatile_base_r)
                          & (dc2_mem_addr1_r[31:28] < aux_volatile_limit_r); 
  end
  
  
  // Is this dc access in a volatile (uncached) region?
  //
  dc2_dc_volatile_region0     =  (dc2_target_r == `npuarc_DMP_TARGET_DC)
                                  & dc2_volatile_region0  
                                  & (~aux_volatile_dis_r)
                             ;
  
  dc2_dc_volatile_region1     = (dc2_target_r == `npuarc_DMP_TARGET_DC)
                                  & dc2_volatile_region1  
                                  & (~aux_volatile_dis_r)
                             ;
end

wire dc2_data_unc;
//////////////////////////////////////////////////////////////////////////////
//
//////////////////////////////////////////////////////////////////////////////
assign dc2_data_unc = 1'b0
                     | (x2_mpu_data_unc & (dc2_target_r == `npuarc_DMP_TARGET_DC))
                     ;
                     


//////////////////////////////////////////////////////////////////////////////
//@ Figure out if the EXU is holding up a X2 instruction
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc2_stuck_PROC
  // A DC2 instruction is either hold up by a downstream stall (2) or it is
  // being held up by the EXU (1)
  //
  dc2_stuck = x2_exu_stall
            | (~dc3_enable)
            ;
end


reg [`npuarc_DMP_TARGET_RANGE] dc3_target_nxt;
reg                     dc3_volatile_nxt;
reg                     dc3_strict_order_nxt;
reg                     dc3_fwd_allowed_nxt;

wire                    dc2_gt_climit_qual;
wire                    dc2_per_region_qual;
wire                    dc2_per2_region_qual;
wire                    dc2_mem_region_qual;

//////////////////////////////////////////////////////////////////////////////
// Region adjustment
//
//////////////////////////////////////////////////////////////////////////////
assign dc2_gt_climit_qual =  1'b0
                           | dc2_dc_volatile_region0 
                           ;

assign dc2_per_region_qual = 1'b0
                           ;

assign dc2_per2_region_qual = 1'b0
                            ;

assign dc2_mem_region_qual  =  dc2_gt_climit_qual
   // When FC bit is set to 0 and the dc2_target is the DCACHE set the
   // target to MEM
                             | (   (~dtlb_rslt0_cached)
                                &  (dc2_target_r == `npuarc_DMP_TARGET_DC))
                            ;

assign dc3_dtlb_miss_excpn  =   dc3_dtlb_miss_excpn_r 
                              & (x3_load_r | x3_store_r)
                              ;
assign dc3_dtlb_ovrlp_excpn =   dc3_dtlb_ovrlp_excpn_r
                              & (x3_load_r | x3_store_r)
                              & (~dc3_pref)
                              ;
assign dc3_dtlb_protv_excpn =   dc3_dtlb_protv_excpn_r
                              & (x3_load_r | x3_store_r)
                              & (~dc3_pref)
                              ;
assign dc3_dtlb_ecc_excpn   =   dc3_dtlb_ecc_error_r
                              & (x3_load_r | x3_store_r)
                              & (~dc3_pref)
                              ;

//////////////////////////////////////////////////////////////////////////////
// Check region credentials: volatile, st-ld fwd allowed
//
//////////////////////////////////////////////////////////////////////////////
reg dc2_addr_non_volatile;
reg dc2_ex_or_scond;
reg dc2_di;
reg dc2_fwd_ok;
reg dc2_volatile;
reg dc2_strict_order;
reg dc2_addr_strict;

always @*
begin : dc3_checks_nxt_PROC
  // Check for address that are "cached" or "non-volatile"
  // 
  dc2_addr_non_volatile = 1'b0 
                         | (~dc2_volatile_region0)
                         | aux_volatile_dis_r
                         ;

  // Check for ".di" instructions 
  //
  dc2_di              = x2_cache_byp_r;
  
  dc2_ex_or_scond     =  x2_store_r
                       | x2_locked_r
                       ;
  
  // Could this store forward data a subsequent load?
  //
  dc2_fwd_ok           =   dc2_addr_non_volatile
                         & (~dc2_di) 
                         & (~dc2_ex_or_scond)
                         & (dtlb_rslt0_cached)
                         ; 
 
  // Is this a volatile ld/st?
  //
  dc2_volatile         =   (~dc2_addr_non_volatile)
                         | dc2_di
                         | (~dtlb_rslt0_cached)
                         ;

  // stage strict requirement 
  // 
  dc2_addr_strict      = aux_volatile_strict_r
                       ;
  
  // Strict or relaxing order?
  //
  dc2_strict_order     =  (dc2_addr_strict & (~dc2_addr_non_volatile))
                         | dc2_di
                         | (~dtlb_rslt0_cached)
                         ;
end    

//////////////////////////////////////////////////////////////////////////////
// PAE-40
//
//////////////////////////////////////////////////////////////////////////////
reg [`npuarc_DMP_TARGET_RANGE] dc2_target_qual;
always @*
begin : dc2_target_qual_PROC
  // The debugger inserted load store bypass the MMU translation and use the
  // aux_memseg register instead
  //
  
  dc2_target_qual = dc2_target_r;
  
  if (  
        1'b0
      | (  db_active_r 
         & (| aux_memseg_r)
         & (   (dc2_target_r == `npuarc_DMP_TARGET_ICCM)
            || (dc2_target_r == `npuarc_DMP_TARGET_DCCM)))
     )
  begin
    dc2_target_qual = `npuarc_DMP_TARGET_MEM;
  end         
end

always @*
begin : dc3_target_nxt_PROC
  
  if (dc2_per_region_qual)
  begin
    dc3_target_nxt       = `npuarc_DMP_TARGET_PER;
    dc3_fwd_allowed_nxt  = dc2_fwd_ok;
    dc3_volatile_nxt     = dc2_volatile;
    dc3_strict_order_nxt = dc2_strict_order;
  end
  else if (dc2_per2_region_qual)
  begin
    dc3_target_nxt       = `npuarc_DMP_TARGET_PER2;
    dc3_fwd_allowed_nxt  = dc2_fwd_ok;
    dc3_volatile_nxt     = dc2_volatile;
    dc3_strict_order_nxt = dc2_strict_order;
  end
  else if (dc2_mem_region_qual)
  begin
    dc3_target_nxt       = `npuarc_DMP_TARGET_MEM;
    dc3_fwd_allowed_nxt  = dc2_fwd_ok;
    dc3_volatile_nxt     = dc2_volatile;
    dc3_strict_order_nxt = dc2_strict_order;
  end
  else if (dc2_data_unc)
  begin
    dc3_target_nxt       = `npuarc_DMP_TARGET_MEM;
    dc3_fwd_allowed_nxt  = dc2_fwd_ok;
    dc3_volatile_nxt     = dc2_volatile;
    dc3_strict_order_nxt = dc2_addr_non_volatile;
  end
  else
  begin
    // DCache/DCCM is always non-volatile
    //
    dc3_target_nxt      = dc2_target_qual;
    dc3_fwd_allowed_nxt =  (dc2_target_r == `npuarc_DMP_TARGET_DC)
                         | (dc2_target_r == `npuarc_DMP_TARGET_DCCM)
                         | (dc2_fwd_ok);
    dc3_volatile_nxt    =  dc2_volatile
                         & (dc2_target_r != `npuarc_DMP_TARGET_DC)
                         & (dc2_target_r != `npuarc_DMP_TARGET_DCCM);                         
    dc3_strict_order_nxt = dc2_strict_order
                         & (dc2_target_r != `npuarc_DMP_TARGET_DC)
                         & (dc2_target_r != `npuarc_DMP_TARGET_DCCM);  
  end
end

//////////////////////////////////////////////////////////////////////////////
// 
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc3_dtlb_efa_PROC
  //
  //
  dc3_dtlb_efa  =    dc3_dtlb_efa_mux_r[0]
                  ?  x3_mem_addr0_r
                  :  {dc3_dtlb_efa1_r[`npuarc_ADDR_MSB:3], 3'b000}
                  ; 
end

//////////////////////////////////////////////////////////////////////////////
//@ Figure out if the EXU is holding up a X2 instruction
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin
  dc3_enable = x3_enable;
end

//////////////////////////////////////////////////////////////////////////////
// Addr for tag match 
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc3_mem_addr_PROC
  if (dc3_mem_addr0_r[`npuarc_DC_TAG_BANK_ID] == 1'b0)
  begin
    dc3_mem_addr_even = dc3_mem_addr0_r;
    dc3_mem_addr_odd  = dc3_mem_addr1_r;
  end
  else
  begin
    dc3_mem_addr_even  = dc3_mem_addr1_r;
    dc3_mem_addr_odd   = dc3_mem_addr0_r;
  end
end

//////////////////////////////////////////////////////////////////////////////
// Pref 
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc3_pref_PROC
  dc3_pref = x3_pref_r | x3_pref_l2_r | x3_prefw_r | x3_pre_alloc_r;
end
//////////////////////////////////////////////////////////////////////////////
//
// Compute the address for load1
// 
//////////////////////////////////////////////////////////////////////////////
// leda BTTF_D002 off
// leda B_3200 off
// leda W484 off
// LMD: Unequal length LHS and RHS in assignment LHS
// LJ:  One bit incrementor
always @*
begin : dc3_mem_addr1_nxt_PROC
  dc3_mem_addr1_nxt[`npuarc_PADDR_MSB:3]= dtlb_rslt1_paddr[`npuarc_PADDR_MSB:3];
  dc3_mem_addr1_nxt[2:0]         = 3'b000;
end

// leda W484 on
// leda B_3200 on
// leda BTTF_D002 on

//////////////////////////////////////////////////////////////////////////////
//
//@
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc3_dt_bank_sel_PROC
  dc3_dt_bank_sel_cg0  =   dc2_aux_pass | dc3_cg0;
  dc3_dt_bank_sel_nxt  =   dc2_aux_pass
                         ? {dc2_aux_bank, ~dc2_aux_bank}
                         : dc2_dt_bank_sel_r;

end


reg [`npuarc_DMP_TARGET_RANGE] dc4_target_nxt;
reg [3:0]               dc4_data_mem_attr_nxt;

//////////////////////////////////////////////////////////////////////////////
//
// Potential adjustment of the dc4 target
// 
//////////////////////////////////////////////////////////////////////////////


always @*
begin : dc4_target_nxt_PROC
  dc4_target_nxt = dc3_target_r;
end

//////////////////////////////////////////////////////////////////////////////
//
// Computation of dc4_data_mem_attr_nxt 
//  
// This is the (IBP) cmd_cache attribute that will eventually go out on the
// the bus
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc4_data_mem_attr_nxt_PROC
  case (dc3_target_r)
  `npuarc_DMP_TARGET_MEM:  dc4_data_mem_attr_nxt = {3'b000, aux_dmp_mem_attr_r};
  `npuarc_DMP_TARGET_DC:   dc4_data_mem_attr_nxt = aux_dmp_dcache_attr_r;
  default:          dc4_data_mem_attr_nxt = 4'b0000;
  endcase
end

assign dc4_dtlb_miss =  dc4_dtlb_miss_r
                      & {2{(ca_load_r | ca_store_r)}}
                      ;

assign dc4_mispred   =  dc4_mispred_r
                      & (ca_load_r | ca_store_r)
                      ;
reg       dc4_scond_lpa_match_cg0;
reg       dc4_scond_lpa_match_r;
reg       dc4_scond_lpa_match_nxt;
reg       dc4_store_clear_cg0;
reg       dc4_store_clear_lf_r;
reg       dc4_store_clear_lf_nxt;
reg       dc4_store_nxt;

reg [3:0] dc3_bank0;
reg [3:0] dc3_bank1;
reg       dc3_odd_to_even_cross;
reg [3:0] lpa_bank;
reg       lpa_addr_match_prel0;
reg       lpa_addr_match_prel1;
reg       lpa_match0;
reg       lpa_match1;
reg       lpa_match;

//////////////////////////////////////////////////////////////////////////////
//                                                                           
// LPA address comparison      
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : lpa_addr_match_PROC
  // LPA bank mask
  //
  lpa_bank = 4'b0000;
  
  casez ({wa_lpa_r[3:2], wa_lock_double_r})
  3'b00_0: 
  begin
    lpa_bank[0] = 1'b1;
  end  
  
  3'b00_1: 
  begin
    lpa_bank[0] = 1'b1;
    lpa_bank[1] = 1'b1;
  end  
  
  3'b01_?:
  begin
    // llockd is 8-byte aligned
    //
    lpa_bank[1] = 1'b1;
  end
  
  3'b10_0:
  begin
    lpa_bank[2] = 1'b1;
  end
  
  3'b10_1:
  begin
    lpa_bank[2] = 1'b1;
    lpa_bank[3] = 1'b1;
  end
  
  default: // 3'b11_?
  begin
    lpa_bank[3] = 1'b1;
  end
  endcase
  
  // DC3 bank mask
  //
  dc3_odd_to_even_cross  =   dc3_data_bank_sel_hi_r[1] 
                           & dc3_data_bank_sel_lo_r[0];
                            
  
  if (dc3_odd_to_even_cross)
  begin
    // Adjust the bank mask
    //
    dc3_bank0[3:0]        = {dc3_data_bank_sel_hi_r[1],
                             dc3_data_bank_sel_lo_r[1],
                             1'b0,
                             1'b0};
    
    dc3_bank1[3:0]        = {1'b0,
                             1'b0,
                             dc3_data_bank_sel_hi_r[0],
                             dc3_data_bank_sel_lo_r[0]};
    
  end
  else
  begin
    dc3_bank0[3:0]        = {dc3_data_bank_sel_hi_r[1],
                             dc3_data_bank_sel_lo_r[1],
                             dc3_data_bank_sel_hi_r[0],
                             dc3_data_bank_sel_lo_r[0]};

    dc3_bank1[3:0]        = {1'b0,
                             1'b0,
                             dc3_data_bank_sel_hi_r[0],
                             dc3_data_bank_sel_lo_r[0]};
  end
  
  // Address Comparator
  //
  lpa_addr_match_prel0   = (wa_lpa_r[`npuarc_PADDR_MSB:4] == dc3_mem_addr0_r[`npuarc_PADDR_MSB:4]);
  lpa_addr_match_prel1   = (wa_lpa_r[`npuarc_PADDR_MSB:4] == dc3_mem_addr1_r[`npuarc_PADDR_MSB:4]);


  // Putting it all together
  //
  lpa_match0 =    lpa_addr_match_prel0 
               & (|(lpa_bank & dc3_bank0)); 

  lpa_match1 = lpa_addr_match_prel1 
               & (|(lpa_bank & dc3_bank1)); 
               
   
  // Check for a match against lpa, taking into account unaligned stores.
  //
  if (dc3_odd_to_even_cross)
  begin
    // Bank 3-0 crossing
    //
    lpa_match = lpa_match0 | lpa_match1;
  end
  else
  begin
    lpa_match = lpa_match0;
  end              
end

always @*
begin : dc3_lpa_match_PROC
  // Clock gate
  //
  dc4_scond_lpa_match_cg0 = x3_store_r & x3_pass & x3_locked_r;
  
  
  // We have a match when the SCOND memory address matches LPA
  //
  dc4_scond_lpa_match_nxt =   x3_store_r
                            & x3_locked_r
                            & lpa_match0;

  // Clear the lock flag if storing to the locked address
  //
  dc4_store_nxt           = x3_store_r & (~x3_locked_r);
    
  dc4_store_clear_lf_nxt  =  dc4_store_nxt 
                           & wa_lock_flag_r 
                           & lpa_match 
                           & (~(wa_restart_r | wa_restart_kill_r | wa_hlt_restart_r))
                           ;
  
  // Enable the clock gate when the store instruciton moves to CA. 
  //
  dc4_store_clear_cg0     =   (x3_store_r & x3_pass & ca_enable)
                            | dc4_store_clear_lf_r;
end

  
//////////////////////////////////////////////////////////////////////////////
// SCOND 
// 
////////////////////////////////////////////////////////////////////////////
always @*
begin : dc4_scond_go_PROC
  // dc4_scond_go is asserted when an SCOND is in CA, the lock flag is set
  // and the scond address matches LPA
  //
  dc4_scond_go =  dc4_scond_lpa_match_r
                & wa_lock_flag_r
                & ca_store_r
                & ca_locked_r
                & (~(   (dc4_target_r == `npuarc_DMP_TARGET_DC)
                     & dc4_dt_miss_r))
                ;
end

//////////////////////////////////////////////////////////////////////////////
// 
////////////////////////////////////////////////////////////////////////////
always @*
begin : dmp_clear_lf_PROC
  // We clear the lock flag when
  // there is a store to the locked address (1)
  
  dmp_clear_lf =  dc4_store_clear_lf_r   // (1)
                ;
end

//////////////////////////////////////////////////////////////////////////////
// Module instantiation:
// The pre size alignment of size1
// 
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_dmp_pre_size_aligner u_alb_dmp_pre_size_aligner_0 (
  .addr_2_to_0                  (x2_mem_addr0_r[2:0]),
  .size                         (dc2_size_r         ),
  .bank_sel                     ({dc2_data_bank_sel_hi_r[1],
                                  dc2_data_bank_sel_lo_r[1],
                                  dc2_data_bank_sel_hi_r[0],
                                  dc2_data_bank_sel_lo_r[0]}),

  .aln_size0                    (dc3_size0_nxt      ),
  .aln_size1                    (dc3_size1_nxt      )
);




//////////////////////////////////////////////////////////////////////////////
// Synchronous process 
//
//////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin : dc2_size_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc2_size_r              <= 2'b00;
    dc2_mem_addr1_r         <= 32'd0;
    dc2_target_r            <= `npuarc_DMP_TARGET_DCCM;
    dc2_data_bank_sel_lo_r  <= 2'b00;
    dc2_data_bank_sel_hi_r  <= 2'b00;
    dc2_dt_line_cross_r     <= 1'b0; 
    dc2_dt_bank_sel_r       <= 2'b00;
    dc2_cache_byp_r         <= 1'b0;
    dc2_rmw_prel_r          <= 4'b0000;
    dc2_lkup1_npage_cross_r <= 1'b0;
  end
  else if (dc2_cg0)
  begin
// spyglass disable_block Clock_info03a
// SMD: Clock-net unconstrained
// SJ:  is constrained 
    dc2_size_r              <= x1_size_r;
    dc2_mem_addr1_r         <= x1_mem_addr1;
    dc2_target_r            <= dc2_target_nxt & {3{(x1_load_r | x1_store_r)}};
    dc2_data_bank_sel_lo_r  <= dc1_data_bank_sel_lo & {2{(x1_load_r | x1_store_r)}};
    dc2_data_bank_sel_hi_r  <= dc1_data_bank_sel_hi & {2{(x1_load_r | x1_store_r)}};
    dc2_dt_line_cross_r     <= dc1_dt_line_cross & (x1_load_r | x1_store_r);  
    dc2_dt_bank_sel_r       <= dc1_dt_bank_sel & {2{(x1_load_r | x1_store_r)}};
    dc2_cache_byp_r         <= x1_cache_byp_r | aux_cache_off;
    dc2_rmw_prel_r          <= dc1_rmw;
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
    dc2_lkup1_npage_cross_r <= dc1_lkup1_npage_cross;
// leda NTL_CON32 on
  end
end
// spyglass enable_block Clock_info03a
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
always @(posedge clk or posedge rst_a)
begin : dc3_target_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc3_target_r              <= `npuarc_DMP_TARGET_DCCM;
    dc3_volatile_r            <= 1'b0;
    dc3_strict_order_r        <= 1'b0;
    dc3_fwd_allowed_r         <= 1'b0;
    dc3_data_bank_sel_lo_r    <= 2'b00;
    dc3_data_bank_sel_hi_r    <= 2'b00;
    dc3_size0_r               <= 3'b000;
    dc3_size1_r               <= 3'b000;
    dc3_mem_addr0_r           <= {`npuarc_PADDR_SIZE{1'b0}};
    dc3_mem_addr1_r           <= {`npuarc_PADDR_SIZE{1'b0}};
    dc3_dtlb_efa1_r           <= {`npuarc_ADDR_SIZE{1'b0}};
    dc3_lkup1_page_cross_r    <= 1'b0;
    dc3_dt_line_cross_r       <= 1'b0;  
    dc3_cache_byp_r           <= 1'b0;
    dc3_rmw_r                 <= 4'b0000;
  end
  else if (dc3_cg0)
  begin
    dc3_target_r            <= dc3_target_nxt;
    dc3_volatile_r          <= dc3_volatile_nxt;
    dc3_strict_order_r      <= dc3_strict_order_nxt;
    dc3_fwd_allowed_r       <= dc3_fwd_allowed_nxt;
    dc3_data_bank_sel_lo_r  <= dc2_data_bank_sel_lo_r & {2{(x2_load_r | x2_store_r)}};
    dc3_data_bank_sel_hi_r  <= dc2_data_bank_sel_hi_r & {2{(x2_load_r | x2_store_r)}};
    dc3_size0_r             <= dc3_size0_nxt;
    dc3_size1_r             <= dc3_size1_nxt;
    dc3_mem_addr0_r         <=  dc2_aux_pass
                              ? {dc2_aux_addr_hi, dc2_aux_addr} 
                              : dtlb_rslt0_paddr;
        
    dc3_mem_addr1_r         <= dc3_mem_addr1_nxt;
    dc3_dtlb_efa1_r         <= dc2_mem_addr1_r;
    dc3_lkup1_page_cross_r  <= dc2_lkup1_npage_cross_r;
    dc3_dt_line_cross_r     <= dc2_dt_line_cross_r;  
    dc3_cache_byp_r         <= dc2_cache_byp_r;
    dc3_rmw_r               <=  dc2_rmw;
  end
end
//leda NTL_CON32 on
always @(posedge clk or posedge rst_a)
begin : dc3_mpu_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc3_mpu_data_flt_r <= 1'b0;
  end
  else if (dc3_cg0)
  begin
    dc3_mpu_data_flt_r <= x2_mpu_data_flt;
  end 
end // block :  dc3_mpu_reg_PROC

always @(posedge clk or posedge rst_a)
begin : dc3_dtlb_miss_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc3_dtlb_efa_mux_r      <= 2'b00;
    dc3_dtlb_miss_r         <= 2'b00;
    dc3_dtlb_miss_excpn_r   <= 1'b0;
    dc3_dtlb_ovrlp_excpn_r  <= 1'b0;
    dc3_dtlb_protv_excpn_r  <= 1'b0;
    dc3_dtlb_ecc_error_r    <= 1'b0;
  end
  else if (dc3_cg0)
  begin
    dc3_dtlb_efa_mux_r      <= dc2_dtlb_efa_mux;
    dc3_dtlb_miss_r         <= dc2_dtlb_miss        & ({2{~db_active_r}});
    dc3_dtlb_miss_excpn_r   <= dc2_dtlb_miss_excpn  & (~db_active_r);
    dc3_dtlb_ovrlp_excpn_r  <= dc2_dtlb_ovrlp_excpn & (~db_active_r);
    dc3_dtlb_protv_excpn_r  <= dc2_dtlb_protv_excpn & (~db_active_r);
    dc3_dtlb_ecc_error_r    <= dc2_dtlb_ecc_error;
  end 
end

always @(posedge clk or posedge rst_a)
begin : dc3_dt_bank_sel_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc3_dt_bank_sel_r         <= 2'b00;
  end
  else if (dc3_dt_bank_sel_cg0)
  begin
    dc3_dt_bank_sel_r       <= dc3_dt_bank_sel_nxt;
  end
end  
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
always @(posedge clk or posedge rst_a)
begin : dc4_target_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_target_r              <= `npuarc_DMP_TARGET_DCCM;
    dc4_volatile_r            <= 1'b0;
    dc4_strict_order_r        <= 1'b0;
    dc4_data_mem_attr_r       <= 4'b0000;
    dc4_data_bank_sel_lo_r    <= 2'b00;
    dc4_data_bank_sel_hi_r    <= 2'b00;
    dc4_mem_addr1_r           <= {`npuarc_PADDR_SIZE{1'b0}};
    dc4_size0_r               <= 3'b000;
    dc4_size1_r               <= 3'b000;
    dc4_pref_r                <= 1'b0;
    dc4_pref_bad_r            <= 1'b0;
    dc4_cache_byp_r           <= 1'b0;
    dc4_dt_line_cross_r       <= 1'b0; 
    dc4_dt_bank_sel_r         <= 2'b00;
    dc4_rmw_r                 <= 4'b0000;
  end
  else if (dc4_cg0)
  begin
    dc4_target_r            <= dc4_target_nxt;
    dc4_volatile_r          <= dc3_volatile_r;
    dc4_strict_order_r      <= dc3_strict_order_r;
    dc4_data_mem_attr_r     <= dc4_data_mem_attr_nxt;
    dc4_data_bank_sel_lo_r  <= dc3_data_bank_sel_lo_r;
    dc4_data_bank_sel_hi_r  <= dc3_data_bank_sel_hi_r;
    dc4_mem_addr1_r         <= dc3_mem_addr1_r;
    dc4_size0_r             <= dc3_size0_r;
    dc4_size1_r             <= dc3_size1_r;
    dc4_pref_r              <= dc3_pref;
    dc4_pref_bad_r          <=    dc3_pref 
                             & ( 1'b0
                                  | (| dc3_dtlb_miss_r)
                                  | dc3_dtlb_ovrlp_excpn_r
                                  | dc3_dtlb_protv_excpn_r
                                  | dc3_dtlb_protv_excpn_r
                                  | dc3_mpu_data_flt_r
                               );
    dc4_cache_byp_r         <= dc3_cache_byp_r;
    dc4_dt_line_cross_r     <= dc3_dt_line_cross_r;  
    dc4_dt_bank_sel_r       <= dc3_dt_bank_sel_r
                               & {2{(dc3_target_r == `npuarc_DMP_TARGET_DC)}}; 
    dc4_rmw_r               <= dc3_rmw_r;
  end
end
// leda NTL_CON32 on
always @(posedge clk or posedge rst_a)
begin : dc4_dtlb_miss_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_mem_addr0_r         <= {`npuarc_PADDR_SIZE{1'b0}};
    dc4_dtlb_miss_r         <= 2'b00;
    dc4_mispred_r           <= 1'b0;
  end
  else if (dc4_cg0)
  begin
    dc4_mem_addr0_r         <= dc3_mem_addr0_r;  
    dc4_dtlb_miss_r         <=   dc3_dtlb_miss_r 
                               & {(~dc3_pref), (~dc3_pref)}
                               & {2{~(   dc3_dtlb_miss_excpn_r 
                                       | dc3_dtlb_ovrlp_excpn_r
                                       | dc3_dtlb_protv_excpn_r
                                       | dc3_dtlb_ecc_error_r
                                     )
                                 } };
   dc4_mispred_r            <= dc3_mispred;
  end
end

always @(posedge clk or posedge rst_a)
begin : dc4_lpa_match_PROC
  if (rst_a == 1'b1)
  begin
    dc4_scond_lpa_match_r <= 1'b0;
  end
  else if (dc4_scond_lpa_match_cg0)
  begin
    dc4_scond_lpa_match_r <= dc4_scond_lpa_match_nxt;
  end
end

always @(posedge clk or posedge rst_a)
begin : dc4_store_clear_lf_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_store_clear_lf_r <= 1'b0;
  end
  else if (dc4_store_clear_cg0 == 1'b1)
  begin
    dc4_store_clear_lf_r <= dc4_store_clear_lf_nxt;
  end
end

endmodule // alb_dmp_staging

