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
//     DMP_SKID_BUFFER
//
// ===========================================================================
//
// Description:
//
//  The dmp_load_aligner module implements the a skid buffer for the D$/DCCM
//  memories of the Data memory pipeline (DMP).
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_skid_buffer.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"


//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  rst: "rst_a", edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_dmp_skid_buffer (
  ////////// General input signals ///////////////////////////////////////////
  //
  input                               clk,
  input                               rst_a,
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input                               ecc_dmp_disable,
// spyglass enable_block W240
  ////////// Inputs from X3 //////////////////////////////////////////////////
  //
//`if ( (`DC_ECC == 1) || (`DC_PARITY == 1) || (`DCCM_ECC == 1) || (`DCCM_PARITY == 1))
  input [3:0]                         dc3_bank_sel_r,
//`endif  
  input                               x3_load_r,
  input                               x3_store_r,
  input                               x3_pass,
  input[`npuarc_DMP_TARGET_RANGE]            dc3_target_r,
  input                               dc3_stall_r,
  input [3:0]                         dc3_rmw_r,
  output reg [3:0]                    dc3_skid_ecc_valid,
  input                               dc3_pref,
  input [1:0]                         dc3_dt_bank_sel_r,
  input                               ca_enable,

  ////////// Inputs from Dcache memory banks ////////////////////////////////
  //
  input [`npuarc_DC_DRAM_RANGE]              dc_data_even_dout_lo, // Dout from memories
  input [`npuarc_DC_DRAM_RANGE]              dc_data_even_dout_hi,
  input [`npuarc_DC_DRAM_RANGE]              dc_data_odd_dout_lo,
  input [`npuarc_DC_DRAM_RANGE]              dc_data_odd_dout_hi,
  input [`npuarc_DC_TRAM_RANGE]              dc_tag_even_dout_w0,
  input [`npuarc_DC_TRAM_RANGE]              dc_tag_even_dout_w1,
  input [`npuarc_DC_TRAM_RANGE]              dc_tag_odd_dout_w0,
  input [`npuarc_DC_TRAM_RANGE]              dc_tag_odd_dout_w1,
  ////////// Inputs from DCCM memory banks ////////////////////////////////
  //
  input [`npuarc_DBL_DCCM_RANGE]             bank0_dout,
  input [`npuarc_DBL_DCCM_RANGE]             bank1_dout,

  input                               dc3_even_way0_hit,   // even hit information
  input                               dc3_odd_way0_hit,    // odd  hit information
  
  input                               dmu_evict_rd,        // DMU doing eviction
  input                               dc3_dc_poisoned,     // dc3 poisoned information 
  input [`npuarc_DC_WAY_RANGE]               dc3_dt_even_hit_way_hot_prel,
  input [`npuarc_DC_WAY_RANGE]               dc3_dt_odd_hit_way_hot_prel,

  input [3:0]                         dc3_ecc_data_bank_sel, 

  input                               wa_restart_r,        // WA restart

  ////////// Inputs from WQ ////////////////////////////////
  //
  input [3:0]                         wq_fwd_bank,         // WQ fwd
  input                               wq_fwd_replay,       // WQ fwd replay
  input [15:0]                        wq_ctrl_mask,        // WQ retire mask
  input [`npuarc_DATA_RANGE]                 wq_dc_data_even_lo,  // WQ retire data
  input [`npuarc_DATA_RANGE]                 wq_dc_data_even_hi,  // WQ retire data
  input [`npuarc_DATA_RANGE]                 wq_dc_data_odd_lo,   // WQ retire data
  input [`npuarc_DATA_RANGE]                 wq_dc_data_odd_hi,   // WQ retire data
  
  ////////// Outputs ////////////////////////////////////////////////////////
  //
  output                              ecc0_even_sel,
  output                              ecc0_odd_sel,
  output reg [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_ecc0_even_lo ,
  output reg [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_ecc0_even_hi ,
  output reg [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_ecc0_odd_lo  ,
  output reg [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_ecc0_odd_hi  ,
  output reg [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_ecc1_even_lo ,
  output reg [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_ecc1_even_hi ,
  output reg [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_ecc1_odd_lo  ,
  output reg [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_ecc1_odd_hi  ,
  output reg [`npuarc_DC_WAY_RANGE]          dc3_dt_even_hit_way_hot,
  output reg [`npuarc_DC_WAY_RANGE]          dc3_dt_odd_hit_way_hot,
  output reg [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_even_lo,           
  output reg [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_even_hi,           
  output reg [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_odd_lo,           
  output reg [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_odd_hi,
  output reg [`npuarc_DC_TRAM_RANGE]         dc3_dt_even_w0,
  output reg [`npuarc_DC_TRAM_RANGE]         dc3_dt_even_w1,
  output reg [`npuarc_DC_TRAM_RANGE]         dc3_dt_odd_w0,
  output reg [`npuarc_DC_TRAM_RANGE]         dc3_dt_odd_w1,
  output reg [`npuarc_DCCM_DATA_ECC_RANGE]   dc3_dccm_data_even_lo,
  output reg [`npuarc_DCCM_DATA_ECC_RANGE]   dc3_dccm_data_even_hi,
  output reg [`npuarc_DCCM_DATA_ECC_RANGE]   dc3_dccm_data_odd_lo,
  output reg [`npuarc_DCCM_DATA_ECC_RANGE]   dc3_dccm_data_odd_hi,

  output reg                          dc4_wq_skid_replay_r,
  output reg [3:0]                    dc4_dccm_ecc_skid_sb_error_r,
  output reg [3:0]                    dc4_dccm_ecc_skid_db_error_r,
  output reg [`npuarc_SYNDROME_MSB:0]        dc_skid_bank0_syndrome_r,
  output reg [`npuarc_SYNDROME_MSB:0]        dc_skid_bank1_syndrome_r,
  output reg [`npuarc_SYNDROME_MSB:0]        dc_skid_bank2_syndrome_r,
  output reg [`npuarc_SYNDROME_MSB:0]        dc_skid_bank3_syndrome_r,
  output reg [3:0]                    dc4_dc_ecc_skid_sb_error_r,
  output reg [3:0]                    dc4_dc_ecc_skid_db_error_r,

  output                              dc_skid_active
);

// Local Declarations
//
reg [3:0]                             dc4_dccm_ecc_skid_sb_error_nxt;
reg [3:0]                             dc4_dccm_ecc_skid_db_error_nxt;
reg [3:0]                             dc4_dc_ecc_skid_sb_error_nxt;
reg [3:0]                             dc4_dc_ecc_skid_db_error_nxt;

reg                                   dc3_stuck;
reg                                   dc4_wq_skid_replay_nxt;

reg [3:0]                             dc3_skid_data_cg0;

reg [`npuarc_DC_DCCM_DATA_ECC_RANGE]         dc3_skid_data_even_lo_r;
reg [`npuarc_DC_DCCM_DATA_ECC_RANGE]         dc3_skid_data_even_hi_r;
reg [`npuarc_DC_DCCM_DATA_ECC_RANGE]         dc3_skid_data_odd_lo_r;
reg [`npuarc_DC_DCCM_DATA_ECC_RANGE]         dc3_skid_data_odd_hi_r;

reg [`npuarc_DC_DCCM_DATA_ECC_RANGE]         dc3_skid_data_even_lo_nxt;
reg [`npuarc_DC_DCCM_DATA_ECC_RANGE]         dc3_skid_data_even_hi_nxt;
reg [`npuarc_DC_DCCM_DATA_ECC_RANGE]         dc3_skid_data_odd_lo_nxt;
reg [`npuarc_DC_DCCM_DATA_ECC_RANGE]         dc3_skid_data_odd_hi_nxt;

reg [`npuarc_DC_TRAM_RANGE]                  dc3_skid_tag_even_w0_r; 
reg [`npuarc_DC_TRAM_RANGE]                  dc3_skid_tag_even_w1_r; 
reg [`npuarc_DC_TRAM_RANGE]                  dc3_skid_tag_odd_w0_r; 
reg [`npuarc_DC_TRAM_RANGE]                  dc3_skid_tag_odd_w1_r; 
reg [`npuarc_DC_WAY_RANGE]                   dc3_skid_even_hit_way_hot_r;
reg [`npuarc_DC_WAY_RANGE]                   dc3_skid_odd_hit_way_hot_r;

reg                                   dc3_skid_wq_replay_r;
reg                                   dc3_set_fwd_replay;
reg                                   dc3_reset_fwd_replay;
reg                                   dc3_skid_replay;
reg                                   dc3_skid_cg0;
reg                                   dc3_skid_select;
reg                                   dc3_dc_skid_select;
reg                                   dc3_dc_skid_data_select;
reg                                   dc3_dccm_skid_select;
reg                                   dc3_skid_state_r;
reg                                   dc3_skid_state_nxt;
reg                                   dc3_target_dc;

reg                                   dc3_target_dccm;

reg [3:0]                             dc3_skid_ecc_valid_r; 



//////////////////////////////////////////////////////////////////////////////////////
//
// Data Skid select - D$
//
/////////////////////////////////////////////////////////////////////////////////////
always @*
begin : dc3_dc_skid_select_PROC
  if (dc3_dc_skid_select)
  begin
    // Select the Tag information from the skid buffer
    //
    dc3_dt_even_hit_way_hot      = dc3_skid_even_hit_way_hot_r;
    dc3_dt_odd_hit_way_hot       = dc3_skid_odd_hit_way_hot_r;
  end
  else
  begin
    // Select information directly from the tag comparator
    //
    dc3_dt_even_hit_way_hot      = dc3_dt_even_hit_way_hot_prel;
    dc3_dt_odd_hit_way_hot       = dc3_dt_odd_hit_way_hot_prel;
    end
end

assign ecc0_even_sel = dc3_dc_skid_data_select | dc3_even_way0_hit;
assign ecc0_odd_sel  = dc3_dc_skid_data_select | dc3_odd_way0_hit;
always @*
begin : dc3_ecc0_calc_data_PROC
  if (dc3_dc_skid_data_select)
  begin    
    // Select the Data information from the sid buffer
    //
    dc3_dd_data_ecc0_even_lo          =  dc3_skid_data_even_lo_r[`npuarc_DC_WAY_DATA_ECC_RANGE];
    dc3_dd_data_ecc0_even_hi          =  dc3_skid_data_even_hi_r[`npuarc_DC_WAY_DATA_ECC_RANGE];
    dc3_dd_data_ecc0_odd_lo           =  dc3_skid_data_odd_lo_r[`npuarc_DC_WAY_DATA_ECC_RANGE];
    dc3_dd_data_ecc0_odd_hi           =  dc3_skid_data_odd_hi_r[`npuarc_DC_WAY_DATA_ECC_RANGE];
  end
  else
  begin
    // Select information directly from the Data memories
    //
    dc3_dd_data_ecc0_even_lo    =   dc_data_even_dout_lo[`npuarc_DC_WAY0_DATA_ECC_RANGE]   // way 0
                             ;

    dc3_dd_data_ecc0_even_hi    = dc_data_even_dout_hi[`npuarc_DC_WAY0_DATA_ECC_RANGE]   // way 0    
                             ;   
    dc3_dd_data_ecc0_odd_lo     =  dc_data_odd_dout_lo[`npuarc_DC_WAY0_DATA_ECC_RANGE]    // way 0
                             ;
    dc3_dd_data_ecc0_odd_hi     = dc_data_odd_dout_hi[`npuarc_DC_WAY0_DATA_ECC_RANGE]    // way 0    
                             ;
   end
end

always @*
begin : dc3_ecc1_calc_data_PROC
    // Select information directly from the Data memories
    //
    dc3_dd_data_ecc1_even_lo    =   dc_data_even_dout_lo[`npuarc_DC_WAY1_DATA_ECC_RANGE]   // way 1
                             ;

    dc3_dd_data_ecc1_even_hi    = dc_data_even_dout_hi[`npuarc_DC_WAY1_DATA_ECC_RANGE]   // way 1
                             ;   
    dc3_dd_data_ecc1_odd_lo     = dc_data_odd_dout_lo[`npuarc_DC_WAY1_DATA_ECC_RANGE]    // way 1    
                             ;
    dc3_dd_data_ecc1_odd_hi     = dc_data_odd_dout_hi[`npuarc_DC_WAY1_DATA_ECC_RANGE]    // way 1
                             ;
end

always @*
begin : dc3_dc_skid_data_select_PROC
  if (dc3_dc_skid_data_select)
  begin    

    // Select the Data information from the sid buffer
    //
    dc3_dd_data_even_lo          =  dc3_skid_data_even_lo_r[`npuarc_DC_WAY_DATA_ECC_RANGE];
    dc3_dd_data_even_hi          =  dc3_skid_data_even_hi_r[`npuarc_DC_WAY_DATA_ECC_RANGE];
    dc3_dd_data_odd_lo           =  dc3_skid_data_odd_lo_r[`npuarc_DC_WAY_DATA_ECC_RANGE];
    dc3_dd_data_odd_hi           =  dc3_skid_data_odd_hi_r[`npuarc_DC_WAY_DATA_ECC_RANGE];
    dc3_dt_even_w0               = dc3_skid_tag_even_w0_r;
    dc3_dt_even_w1               = dc3_skid_tag_even_w1_r;
    dc3_dt_odd_w0                = dc3_skid_tag_odd_w0_r;
    dc3_dt_odd_w1                = dc3_skid_tag_odd_w1_r;
  end
  else
  begin
     
    // Select information directly from the Data memories
    //
    dc3_dd_data_even_lo    =   (dc3_even_way0_hit)
                             ? dc_data_even_dout_lo[`npuarc_DC_WAY0_DATA_ECC_RANGE]   // way 0
                             : dc_data_even_dout_lo[`npuarc_DC_WAY1_DATA_ECC_RANGE]   // way 1
                             ;

    dc3_dd_data_even_hi    = (!dc3_even_way0_hit)
                             ? dc_data_even_dout_hi[`npuarc_DC_WAY1_DATA_ECC_RANGE]   // way 1
                             : dc_data_even_dout_hi[`npuarc_DC_WAY0_DATA_ECC_RANGE]   // way 0    
                             ;   
    dc3_dd_data_odd_lo     =   (dc3_odd_way0_hit)
                             ? dc_data_odd_dout_lo[`npuarc_DC_WAY0_DATA_ECC_RANGE]    // way 0
                             : dc_data_odd_dout_lo[`npuarc_DC_WAY1_DATA_ECC_RANGE]    // way 1    
                             ;
    dc3_dd_data_odd_hi     =   (!dc3_odd_way0_hit)
                             ? dc_data_odd_dout_hi[`npuarc_DC_WAY1_DATA_ECC_RANGE]    // way 1
                             : dc_data_odd_dout_hi[`npuarc_DC_WAY0_DATA_ECC_RANGE]    // way 0    
                             ;
    dc3_dt_even_w0         = dc_tag_even_dout_w0;     
    dc3_dt_even_w1         = dc_tag_even_dout_w1;     
    dc3_dt_odd_w0          = dc_tag_odd_dout_w0;     
    dc3_dt_odd_w1          = dc_tag_odd_dout_w1;     
   end
end

always @*
begin : dc3_skid_ecc_valid_PROC
  //
  //
  if ( 1'b0
      | dc3_dccm_skid_select
      | dc3_dc_skid_data_select
     )
  begin
    dc3_skid_ecc_valid = dc3_skid_ecc_valid_r;
  end
  else
  begin
    dc3_skid_ecc_valid = dc3_bank_sel_r 
                       &  (~wq_fwd_bank)
                       & {4{~dc3_dc_poisoned}};
  end  
end


//////////////////////////////////////////////////////////////////////////////////////
//
// Data Skid select - DCCM
//
/////////////////////////////////////////////////////////////////////////////////////
always @*
begin : dc3_dccm_data_PROC
  if (dc3_dccm_skid_select)
  begin
    // Select data from skid buffer
    //
    dc3_dccm_data_even_lo  = dc3_skid_data_even_lo_r[`npuarc_DCCM_DATA_ECC_RANGE];
    dc3_dccm_data_even_hi  = dc3_skid_data_even_hi_r[`npuarc_DCCM_DATA_ECC_RANGE];
    dc3_dccm_data_odd_lo   = dc3_skid_data_odd_lo_r[`npuarc_DCCM_DATA_ECC_RANGE];
    dc3_dccm_data_odd_hi   = dc3_skid_data_odd_hi_r[`npuarc_DCCM_DATA_ECC_RANGE];
    
  end
  else
  begin
    // Select data from dc3
    //
    dc3_dccm_data_even_lo  = bank0_dout[`npuarc_DBL_DCCM_LO_RANGE];   
    dc3_dccm_data_even_hi  = bank0_dout[`npuarc_DBL_DCCM_HI_RANGE];   
    dc3_dccm_data_odd_lo   = bank1_dout[`npuarc_DBL_DCCM_LO_RANGE];   
    dc3_dccm_data_odd_hi   = bank1_dout[`npuarc_DBL_DCCM_HI_RANGE];   
  end
end

//////////////////////////////////////////////////////////////////////////////////////
//
// Common for both D$ and DCCM
//
/////////////////////////////////////////////////////////////////////////////////////
always @*
begin : dc3_dd_data_PROC
  if (dc3_skid_select)
  begin
    // Select the Data information from the skid buffer
    //   
    dc3_skid_replay      =  dc3_skid_wq_replay_r;
  end
  else
  begin
    // Select information directly from the Data memories
    //   
   dc3_skid_replay      = wq_fwd_replay & (~dc3_stall_r);
  end
end

///////////////////////////////////////////////////////////////////////////////////////
//
// WQ FWD replay condition
//
///////////////////////////////////////////////////////////////////////////////////////
always @*
begin : dc3_set_fwd_replay_PROC
  dc3_set_fwd_replay     =   dc3_skid_replay 
                           & x3_pass 
                           & ca_enable;

  dc3_reset_fwd_replay   = dc4_wq_skid_replay_r;
end

//////////////////////////////////////////////////////////////////////////////
// Skid buffer FSM to avoid tag squashing
//  
//////////////////////////////////////////////////////////////////////////////
parameter DC3_SKID_DEFAULT = 1'b0;
parameter DC3_SKID_SELECT  = 1'b1;

always @*
begin : dc3_skid_fsm_PROC

  dc3_skid_cg0            = 1'b0;
  dc3_skid_data_cg0       = 4'd0;
  dc3_dc_skid_select      = 1'b0;
  dc3_dc_skid_data_select = 1'b0;
  dc3_dccm_skid_select = 1'b0;
  dc3_skid_select      = 1'b0;

  dc3_skid_state_nxt   = dc3_skid_state_r;
 

  dc3_target_dccm      =   (x3_load_r | x3_store_r)
                         & (dc3_target_r == `npuarc_DMP_TARGET_DCCM)
                         ;

  dc3_target_dc        =   (x3_load_r | x3_store_r)
                         & (dc3_target_r == `npuarc_DMP_TARGET_DC)
                         ;
 
  dc3_stuck            =   (x3_load_r | x3_store_r) 
                         & (dc3_target_dccm | dc3_target_dc)
                         & (~(x3_pass & ca_enable))
                         & (~dc3_dc_poisoned)
                       ;
  
  case (dc3_skid_state_r)
  DC3_SKID_DEFAULT:
  begin
    if (  dc3_stuck
        & (~wa_restart_r)
       )
    begin
      dc3_skid_cg0        = 1'b1;
      dc3_skid_data_cg0   =  dc3_bank_sel_r
                          & (  4'b0000
                             | {4{(~dc3_pref & dc3_target_dc & (x3_load_r | (~ecc_dmp_disable & x3_store_r & (|dc3_rmw_r))))}}
                             | {4{(dc3_target_dccm & (x3_load_r | (~ecc_dmp_disable & x3_store_r & (|dc3_rmw_r))))}}
                            );

      dc3_skid_state_nxt  = DC3_SKID_SELECT;
    end
  end

  default: // DC3_SKID_SELECT
  begin
    //
    // activate the dc3_skid_data_cg0 in case of retirement of stores
    // 
    dc3_skid_data_cg0[0]         = | wq_ctrl_mask[3:0];
    dc3_skid_data_cg0[1]         = | wq_ctrl_mask[7:4];
    dc3_skid_data_cg0[2]         = | wq_ctrl_mask[11:8];
    dc3_skid_data_cg0[3]         = | wq_ctrl_mask[15:12];
    
    // Select the skid buffer for the dc3 stuck dc3 instruction
    //
    dc3_dc_skid_select        = dc3_target_dc;
    dc3_dc_skid_data_select   = dc3_target_dc & (~dmu_evict_rd);
    dc3_dccm_skid_select = dc3_target_dccm;
    dc3_skid_select      =   1'b1
                           & (~dmu_evict_rd)
                           ;
    if (  x3_pass
        | (~(x3_load_r | x3_store_r))
        | dc3_dc_poisoned
        | wa_restart_r
       )
    begin
      // The stalled/holdup instruction in X3 is moving forward or got killed
      //
      dc3_skid_state_nxt  = DC3_SKID_DEFAULT;
    end
  end
  endcase
end

assign dc_skid_active = dc3_skid_select;

////////////////////////////////////////////////////////////////////////////////////////
//
// Asynchronous process to compute the _nxt values of the skid data buffer
//
///////////////////////////////////////////////////////////////////////////////////////

reg [`npuarc_DC_DCCM_DATA_ECC_RANGE] dc_bank_even_lo_data; 
reg [`npuarc_DC_DCCM_DATA_ECC_RANGE] dc_bank_even_hi_data;
reg [`npuarc_DC_DCCM_DATA_ECC_RANGE] dc_bank_odd_lo_data;  
reg [`npuarc_DC_DCCM_DATA_ECC_RANGE] dc_bank_odd_hi_data;  


always @*
begin : dc_bank_data_PROC
  // Data coming from memory banks
  //
  case (dc3_target_dccm)
  1'b1:
  begin
    // DCCM
    //
    dc_bank_even_lo_data = bank0_dout[`npuarc_DBL_DCCM_LO_RANGE];
    dc_bank_even_hi_data = bank0_dout[`npuarc_DBL_DCCM_HI_RANGE];
    dc_bank_odd_lo_data  = bank1_dout[`npuarc_DBL_DCCM_LO_RANGE];
    dc_bank_odd_hi_data  = bank1_dout[`npuarc_DBL_DCCM_HI_RANGE];
  end
  default:
  begin
    dc_bank_even_lo_data = dc3_even_way0_hit
                         ? dc_data_even_dout_lo[`npuarc_DC_WAY0_DATA_ECC_RANGE]   // way 0
                         : dc_data_even_dout_lo[`npuarc_DC_WAY1_DATA_ECC_RANGE]   // way 1
                         ;

    dc_bank_even_hi_data = !dc3_even_way0_hit
                         ? dc_data_even_dout_hi[`npuarc_DC_WAY1_DATA_ECC_RANGE]   // way 1
                         : dc_data_even_dout_hi[`npuarc_DC_WAY0_DATA_ECC_RANGE]   // way 0    
                         ;
 
    dc_bank_odd_lo_data  = dc3_odd_way0_hit
                         ? dc_data_odd_dout_lo[`npuarc_DC_WAY0_DATA_ECC_RANGE]    // way 0
                         : dc_data_odd_dout_lo[`npuarc_DC_WAY1_DATA_ECC_RANGE]    // way 1    
                         ;
 
    dc_bank_odd_hi_data  = !dc3_odd_way0_hit
                         ? dc_data_odd_dout_hi[`npuarc_DC_WAY1_DATA_ECC_RANGE]    // way 1
                         : dc_data_odd_dout_hi[`npuarc_DC_WAY0_DATA_ECC_RANGE]    // way 0    
                         ;

  end
  endcase 
end



always @*
begin : dc3_skid_data_nxt_PROC
  // These are the nxt values to be captured in the skid buffer
  //
  
  // Default values: keep what is in the skid buffer already
  //
  
  dc3_skid_data_even_lo_nxt = dc3_skid_data_even_lo_r;
  dc3_skid_data_even_hi_nxt = dc3_skid_data_even_hi_r;
  dc3_skid_data_odd_lo_nxt  = dc3_skid_data_odd_lo_r; 
  dc3_skid_data_odd_hi_nxt  = dc3_skid_data_odd_hi_r;

  // Update the skid buffer with the memory contents
  //
  if (dc3_skid_cg0)
  begin
    dc3_skid_data_even_lo_nxt = dc_bank_even_lo_data;
    dc3_skid_data_even_hi_nxt = dc_bank_even_hi_data;
    dc3_skid_data_odd_lo_nxt  = dc_bank_odd_lo_data;
    dc3_skid_data_odd_hi_nxt  = dc_bank_odd_hi_data;
  end
  
  // Update the skid buffer on a per byte basis on a WQ conflict 
  //
  // Byte0 to Byte3 (bank0). 
  //
  if (wq_ctrl_mask[0])
    dc3_skid_data_even_lo_nxt[`npuarc_BYTE0_RANGE] = wq_dc_data_even_lo[`npuarc_BYTE0_RANGE];
  
  if (wq_ctrl_mask[1])
    dc3_skid_data_even_lo_nxt[`npuarc_BYTE1_RANGE] = wq_dc_data_even_lo[`npuarc_BYTE1_RANGE];
  
  if (wq_ctrl_mask[2])
    dc3_skid_data_even_lo_nxt[`npuarc_BYTE2_RANGE] = wq_dc_data_even_lo[`npuarc_BYTE2_RANGE];
  
  if (wq_ctrl_mask[3])
    dc3_skid_data_even_lo_nxt[`npuarc_BYTE3_RANGE] = wq_dc_data_even_lo[`npuarc_BYTE3_RANGE];
    
  
  // Byte4 to Byte7 (bank1)
  //
  if (wq_ctrl_mask[4])
    dc3_skid_data_even_hi_nxt[`npuarc_BYTE0_RANGE] = wq_dc_data_even_hi[`npuarc_BYTE0_RANGE];
  
  if (wq_ctrl_mask[5])
    dc3_skid_data_even_hi_nxt[`npuarc_BYTE1_RANGE] = wq_dc_data_even_hi[`npuarc_BYTE1_RANGE];
  
  if (wq_ctrl_mask[6])
    dc3_skid_data_even_hi_nxt[`npuarc_BYTE2_RANGE] = wq_dc_data_even_hi[`npuarc_BYTE2_RANGE];
  
  if (wq_ctrl_mask[7])
    dc3_skid_data_even_hi_nxt[`npuarc_BYTE3_RANGE] = wq_dc_data_even_hi[`npuarc_BYTE3_RANGE];
    
  
  // Byte8 to Byte11 (bank2)
  //
  if (wq_ctrl_mask[8])
    dc3_skid_data_odd_lo_nxt[`npuarc_BYTE0_RANGE] = wq_dc_data_odd_lo[`npuarc_BYTE0_RANGE];
  
  if (wq_ctrl_mask[9])
    dc3_skid_data_odd_lo_nxt[`npuarc_BYTE1_RANGE] = wq_dc_data_odd_lo[`npuarc_BYTE1_RANGE];
  
  if (wq_ctrl_mask[10])
    dc3_skid_data_odd_lo_nxt[`npuarc_BYTE2_RANGE] = wq_dc_data_odd_lo[`npuarc_BYTE2_RANGE];
  
  if (wq_ctrl_mask[11])
    dc3_skid_data_odd_lo_nxt[`npuarc_BYTE3_RANGE] = wq_dc_data_odd_lo[`npuarc_BYTE3_RANGE];
    
  
  // Byte12 to Byte16 (bank3)
  //
  if (wq_ctrl_mask[12])
    dc3_skid_data_odd_hi_nxt[`npuarc_BYTE0_RANGE] = wq_dc_data_odd_hi[`npuarc_BYTE0_RANGE];
  
  if (wq_ctrl_mask[13])
    dc3_skid_data_odd_hi_nxt[`npuarc_BYTE1_RANGE] = wq_dc_data_odd_hi[`npuarc_BYTE1_RANGE];
  
  if (wq_ctrl_mask[14])
    dc3_skid_data_odd_hi_nxt[`npuarc_BYTE2_RANGE] = wq_dc_data_odd_hi[`npuarc_BYTE2_RANGE];
  
  if (wq_ctrl_mask[15])
    dc3_skid_data_odd_hi_nxt[`npuarc_BYTE3_RANGE] = wq_dc_data_odd_hi[`npuarc_BYTE3_RANGE];
end






reg dc3_stuck_r;
reg dc3_stuck_rr;

reg dc4_ecc_skid_set_cg0;
reg dc4_ecc_skid_clr_cg0;

always @*
begin : dc4_ecc_skid_set_cg0_PROC
  //
  //
  //  Set it when the instruction in X3 is still stuck
  //  and there is a wq_ctrl_mask_update
  //
  dc4_ecc_skid_set_cg0 = dc3_stuck_r
                       & (~dc3_stuck_rr)   
                       & (|wq_ctrl_mask)
                       & (~dc3_pref)
                       & (
                             ( (  (dc3_dt_bank_sel_r[0] & (|dc3_dt_even_hit_way_hot))
                                | (dc3_dt_bank_sel_r[1] & (|dc3_dt_odd_hit_way_hot )))
                               & dc3_target_dc)
                          | dc3_target_dccm)       
                       & (~x3_pass)
                       & (~(|dc4_dccm_ecc_skid_sb_error_r))
                       & (~(|dc4_dc_ecc_skid_sb_error_r))
                       ;

  dc4_ecc_skid_clr_cg0 = wa_restart_r;
end









wire ecc_sb_error_even_lo;
wire ecc_sb_error_even_hi;
wire ecc_sb_error_odd_lo;
wire ecc_sb_error_odd_hi;

wire ecc_db_error_even_lo;
wire ecc_db_error_even_hi;
wire ecc_db_error_odd_lo;
wire ecc_db_error_odd_hi;

wire [`npuarc_DATA_RANGE] ecc_corrected_even_lo;
wire [`npuarc_DATA_RANGE] ecc_corrected_even_hi;
wire [`npuarc_DATA_RANGE] ecc_corrected_odd_lo;
wire [`npuarc_DATA_RANGE] ecc_corrected_odd_hi;

wire [`npuarc_SYNDROME_MSB:0] syndrome_even_lo;
wire [`npuarc_SYNDROME_MSB:0] syndrome_even_hi;
wire [`npuarc_SYNDROME_MSB:0] syndrome_odd_lo;
wire [`npuarc_SYNDROME_MSB:0] syndrome_odd_hi;


npuarc_alb_ecc_combined u_alb_dmp_ecc_combined_0 (
  .data_in                        (dc3_skid_data_even_lo_r[31:0] ),  // Data bits
  .ecc_code_in                    (dc3_skid_data_even_lo_r[38:32]),  // ECC  bits 
  .ecc_dmp_disable                (ecc_dmp_disable        ),  // ECC Disabled
  .syndrome                       (syndrome_even_lo       ),
  .sb_error                       (ecc_sb_error_even_lo   ),  // SB error
  .db_error                       (ecc_db_error_even_lo   ),  // DB error
// spyglass disable_block UnloadedOutTerm-ML
// SMD: Outputs connected to floating net
// SJ: corrected data not used in this design
  .data_out                       (ecc_corrected_even_lo  )   
// spyglass enable_block UnloadedOutTerm-ML
);

npuarc_alb_ecc_combined u_alb_dmp_ecc_combined_1 (
  .data_in                        (dc3_skid_data_even_hi_r[31:0] ),  // Data bits
  .ecc_code_in                    (dc3_skid_data_even_hi_r[38:32]),  // ECC  bits
  .ecc_dmp_disable                (ecc_dmp_disable        ),  // ECC Disabled
  .syndrome                       (syndrome_even_hi       ),
  .sb_error                       (ecc_sb_error_even_hi   ),  // SB error
  .db_error                       (ecc_db_error_even_hi   ),  // DB error
// spyglass disable_block UnloadedOutTerm-ML
// SMD: Outputs connected to floating net
// SJ: corrected data not used in this design
  .data_out                       (ecc_corrected_even_hi  )   
// spyglass enable_block UnloadedOutTerm-ML
);

npuarc_alb_ecc_combined u_alb_dmp_ecc_combined_2 (
  .data_in                        (dc3_skid_data_odd_lo_r[31:0] ),  // Data bits
  .ecc_code_in                    (dc3_skid_data_odd_lo_r[38:32]),  // ECC  bits
  .ecc_dmp_disable                (ecc_dmp_disable       ),  // ECC Disabled
  .syndrome                       (syndrome_odd_lo       ),
  .sb_error                       (ecc_sb_error_odd_lo   ),  // SB error
  .db_error                       (ecc_db_error_odd_lo   ),  // DB error
// spyglass disable_block UnloadedOutTerm-ML
// SMD: Outputs connected to floating net
// SJ: corrected data not used in this design
  .data_out                       (ecc_corrected_odd_lo  ) 
// spyglass enable_block UnloadedOutTerm-ML
);

npuarc_alb_ecc_combined u_alb_dmp_ecc_combined_3 (
  .data_in                        (dc3_skid_data_odd_hi_r[31:0] ),  // Data bits
  .ecc_code_in                    (dc3_skid_data_odd_hi_r[38:32]),  // ECC  bits
  .ecc_dmp_disable                (ecc_dmp_disable       ),  // ECC Disabled
  .syndrome                       (syndrome_odd_hi       ),
  .sb_error                       (ecc_sb_error_odd_hi   ),  // SB error
  .db_error                       (ecc_db_error_odd_hi   ),  // DB error
// spyglass disable_block UnloadedOutTerm-ML
// SMD: Outputs connected to floating net
// SJ: corrected data not used in this design
  .data_out                       (ecc_corrected_odd_hi  )   
// spyglass enable_block UnloadedOutTerm-ML
);


wire [3:0] dc3_ecc_valid;
assign dc3_ecc_valid = dc3_target_dc
                     ? dc3_ecc_data_bank_sel 
                     : {4{dc3_target_dccm}}
                     ;      

reg [3:0]  dc3_skid_ecc_valid_nxt;      
reg [3:0]  dc3_skid_ecc_valid_cg0;      
always @*
begin : dc3_skid_data_even_lo_nxt_PROC
  //
  //

  dc3_skid_ecc_valid_cg0[0]  = dc3_stuck & (~dc3_stuck_r)
                             | (|wq_ctrl_mask[3:0]   & dc3_bank_sel_r[0]);

  dc3_skid_ecc_valid_cg0[1]  = dc3_stuck & (~dc3_stuck_r)
                             | (|wq_ctrl_mask[7:4]   & dc3_bank_sel_r[1]);
                          
  dc3_skid_ecc_valid_cg0[2]  = dc3_stuck & (~dc3_stuck_r)
                             | (|wq_ctrl_mask[11:8]   & dc3_bank_sel_r[2]);  

  dc3_skid_ecc_valid_cg0[3]  = dc3_stuck & (~dc3_stuck_r)
                             | (|wq_ctrl_mask[15:12]   & dc3_bank_sel_r[3]);  


  dc3_skid_ecc_valid_nxt = dc3_skid_ecc_valid_r;

  if (dc3_skid_ecc_valid_cg0[0])
  begin
    dc3_skid_ecc_valid_nxt[0]  = dc3_stuck & (~dc3_stuck_r) 
                               ? (~(|wq_ctrl_mask[3:0]   & dc3_bank_sel_r[0]))
                               : dc3_skid_ecc_valid_r[0] & (~(|wq_ctrl_mask[3:0]   & dc3_bank_sel_r[0])); 
  end

  if (dc3_skid_ecc_valid_cg0[1])
  begin 
    dc3_skid_ecc_valid_nxt[1]  = dc3_stuck & (~dc3_stuck_r)
                               ? (~(|wq_ctrl_mask[7:4]   & dc3_bank_sel_r[1]))
                               : dc3_skid_ecc_valid_r[1] & (~(|wq_ctrl_mask[7:4]   & dc3_bank_sel_r[1]));
  end

  if (dc3_skid_ecc_valid_cg0[2])
  begin
    dc3_skid_ecc_valid_nxt[2]  = dc3_stuck & (~dc3_stuck_r)
                               ? (~(|wq_ctrl_mask[11:8]  & dc3_bank_sel_r[2]))
                               : dc3_skid_ecc_valid_r[2] & (~(|wq_ctrl_mask[11:8]  & dc3_bank_sel_r[2]));
  end

  if (dc3_skid_ecc_valid_cg0[3])
  begin
    dc3_skid_ecc_valid_nxt[3]  = dc3_stuck & (~dc3_stuck_r)
                               ? (~(|wq_ctrl_mask[15:12] & dc3_bank_sel_r[3]))
                               : dc3_skid_ecc_valid_r[3] & (~(|wq_ctrl_mask[15:12] & dc3_bank_sel_r[3]));
  end  
end  

reg [`npuarc_SYNDROME_MSB:0] dc_skid_bank0_syndrome_nxt;
reg [`npuarc_SYNDROME_MSB:0] dc_skid_bank1_syndrome_nxt;
reg [`npuarc_SYNDROME_MSB:0] dc_skid_bank2_syndrome_nxt;
reg [`npuarc_SYNDROME_MSB:0] dc_skid_bank3_syndrome_nxt;
always@*
begin : dc_skid_syndrome_nxt_PROC
  //
  //  Capturing the correct Syndrome for the double bit error
  
  dc_skid_bank0_syndrome_nxt = syndrome_even_lo;
  dc_skid_bank1_syndrome_nxt = syndrome_even_hi;
  dc_skid_bank2_syndrome_nxt = syndrome_odd_lo;
  dc_skid_bank3_syndrome_nxt = syndrome_odd_hi;
end


always @*
begin : dc4_wq_skid_replay_nxt_PROC
  //
  // Default Value

  dc4_wq_skid_replay_nxt = dc4_wq_skid_replay_r;

  if (dc3_set_fwd_replay)
  begin
    dc4_wq_skid_replay_nxt   = 1'b1;
  end
  else if (dc3_reset_fwd_replay)
  begin
    dc4_wq_skid_replay_nxt   = 1'b0;
  end
end




// spyglass disable_block STARC05-2.2.3.3
// SMD: Flipflop value assigned more than once over same signal in always construct
// SJ:  Conflit covered by assertions

always @*
begin : dc4_dccm_ecc_skid_sb_error_nxt_PROC
  //
  // Default Value
  
  dc4_dccm_ecc_skid_sb_error_nxt = dc4_dccm_ecc_skid_sb_error_r;
  dc4_dccm_ecc_skid_db_error_nxt = dc4_dccm_ecc_skid_db_error_r;
  
    if (dc4_ecc_skid_set_cg0)
    begin
      dc4_dccm_ecc_skid_sb_error_nxt = { ecc_sb_error_odd_hi,  ecc_sb_error_odd_lo,
                                        ecc_sb_error_even_hi, ecc_sb_error_even_lo}
                                    & dc3_skid_ecc_valid_nxt
                                    & dc3_ecc_valid 
                                    & {4{dc3_target_dccm}}
                                    & dc3_bank_sel_r;  

      dc4_dccm_ecc_skid_db_error_nxt = { ecc_db_error_odd_hi,  ecc_db_error_odd_lo,
                                        ecc_db_error_even_hi, ecc_db_error_even_lo}
                                    & dc3_skid_ecc_valid_nxt
                                    & dc3_skid_ecc_valid_r   
                                    & dc3_ecc_valid 
                                    & {4{dc3_target_dccm}}
                                    & dc3_bank_sel_r;  
    end
    
    if (dc4_ecc_skid_clr_cg0)
    begin
      dc4_dccm_ecc_skid_sb_error_nxt = 4'b0000;
      dc4_dccm_ecc_skid_db_error_nxt = 4'b0000;
    end
end
// spyglass enable_block STARC05-2.2.3.3


// spyglass disable_block STARC05-2.2.3.3
// SMD: Flipflop value assigned more than once over same signal in always construct
// SJ:  Conflit covered by assertions

always @*
begin : dc4_dc_ecc_skid_sb_error_nxt_PROC
  //
  // Default Value

  dc4_dc_ecc_skid_sb_error_nxt = dc4_dc_ecc_skid_sb_error_r;
  dc4_dc_ecc_skid_db_error_nxt = dc4_dc_ecc_skid_db_error_r;

  if (dc4_ecc_skid_set_cg0)
  begin
    dc4_dc_ecc_skid_sb_error_nxt = { ecc_sb_error_odd_hi,  ecc_sb_error_odd_lo,
                                     ecc_sb_error_even_hi, ecc_sb_error_even_lo}
                                 & dc3_skid_ecc_valid_nxt
                                 & dc3_ecc_valid 
                                 & {4{dc3_target_dc}}
                                 & dc3_bank_sel_r;  

    dc4_dc_ecc_skid_db_error_nxt = { ecc_db_error_odd_hi,  ecc_db_error_odd_lo,
                                     ecc_db_error_even_hi, ecc_db_error_even_lo}
                                 & dc3_skid_ecc_valid_nxt
                                 & dc3_skid_ecc_valid_r   
                                 & dc3_ecc_valid 
                                 & {4{dc3_target_dc}}
                                 & dc3_bank_sel_r;   

  end
  
  if (dc4_ecc_skid_clr_cg0)
  begin
    dc4_dc_ecc_skid_sb_error_nxt = 4'b0000;
    dc4_dc_ecc_skid_db_error_nxt = 4'b0000;
  end
end
// spyglass enable_block STARC05-2.2.3.3

////////////////////////////////////////////////////////////////////////////////////////
//
// Synchronous Process
//
///////////////////////////////////////////////////////////////////////////////////////
// leda TEST_975 off
// LMD: Latch enabled by a clock affects data input of flipflops clocked by the trailing edge of the same clock
// LJ:

always @ (posedge clk or posedge rst_a)
begin : dc3_skid_wq_replay_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc3_skid_wq_replay_r      <= 1'b0;
  end
  else if (dc3_skid_cg0 == 1'b1)
  begin
    dc3_skid_wq_replay_r    <=  (wq_fwd_replay & (~dc3_stall_r))
                              | dc3_dc_poisoned
                              ;
  end
end

always @ (posedge clk or posedge rst_a)
begin : dc3_skid_tag_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc3_skid_tag_even_w0_r    <= {`npuarc_DC_TRAM_BITS{1'b0}};
    dc3_skid_tag_even_w1_r    <= {`npuarc_DC_TRAM_BITS{1'b0}};
    dc3_skid_tag_odd_w0_r     <= {`npuarc_DC_TRAM_BITS{1'b0}};
    dc3_skid_tag_odd_w1_r     <= {`npuarc_DC_TRAM_BITS{1'b0}};
  end
  else if (dc3_skid_cg0 == 1'b1)
  begin
    dc3_skid_tag_even_w0_r    <= dc_tag_even_dout_w0;
    dc3_skid_tag_even_w1_r    <= dc_tag_even_dout_w1;
    dc3_skid_tag_odd_w0_r     <= dc_tag_odd_dout_w0; 
    dc3_skid_tag_odd_w1_r     <= dc_tag_odd_dout_w1; 
  end
end


always @ (posedge clk or posedge rst_a)
begin : dc3_skid_data_even_lo_reg_PROC
  if (rst_a == 1'b1)
  begin 
    dc3_skid_data_even_lo_r   <= {`npuarc_DC_DCCM_DATA_ECC_SIZE{1'b0}};
  end
  else if (dc3_skid_data_cg0[0] == 1'b1)
  begin
    dc3_skid_data_even_lo_r <= dc3_skid_data_even_lo_nxt;
  end
end

always @ (posedge clk or posedge rst_a)
begin : dc3_skid_data_even_hi_reg_PROC
  if (rst_a == 1'b1)
  begin 
    dc3_skid_data_even_hi_r   <= {`npuarc_DC_DCCM_DATA_ECC_SIZE{1'b0}};
  end
  else if (dc3_skid_data_cg0[1] == 1'b1)
  begin
    dc3_skid_data_even_hi_r <= dc3_skid_data_even_hi_nxt;
  end
end

always @ (posedge clk or posedge rst_a)
begin : dc3_skid_data_odd_lo_reg_PROC
  if (rst_a == 1'b1)
  begin 
    dc3_skid_data_odd_lo_r   <= {`npuarc_DC_DCCM_DATA_ECC_SIZE{1'b0}};
  end
  else if (dc3_skid_data_cg0[2] == 1'b1)
  begin
    dc3_skid_data_odd_lo_r <= dc3_skid_data_odd_lo_nxt;
  end
end

always @ (posedge clk or posedge rst_a)
begin : dc3_skid_data_odd_hi_reg_PROC
  if (rst_a == 1'b1)
  begin 
    dc3_skid_data_odd_hi_r   <= {`npuarc_DC_DCCM_DATA_ECC_SIZE{1'b0}};
  end
  else if (dc3_skid_data_cg0[3] == 1'b1)
  begin
    dc3_skid_data_odd_hi_r <= dc3_skid_data_odd_hi_nxt;
  end
end


always @ (posedge clk or posedge rst_a)
begin : dc3_stuck_reg_PROC
  if (rst_a == 1'b1)
  begin 
    dc3_stuck_r  <= 1'b0;
    dc3_stuck_rr <= 1'b0;
  end
  else
  begin
    dc3_stuck_r  <= dc3_stuck
                  & (~wa_restart_r);
    dc3_stuck_rr <= dc3_stuck_r;
  end
end  



// leda TEST_975 on
always @ (posedge clk or posedge rst_a)
begin : dc4_wq_skid_replay_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_wq_skid_replay_r     <= 1'b0;
  end
  else
  begin
    dc4_wq_skid_replay_r     <= dc4_wq_skid_replay_nxt;
  end  
end

// leda TEST_975 off
// LMD: Latch enabled by a clock affects data input of flipflops clocked by the trailing edge of the same clock
// LJ: 
always @ (posedge clk or posedge rst_a)
begin : dc3_skid_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc3_skid_even_hit_way_hot_r          <= 2'b00;
    dc3_skid_odd_hit_way_hot_r           <= 2'b00;
  end
  else if (dc3_skid_cg0)
  begin
    dc3_skid_even_hit_way_hot_r        <= dc3_dt_even_hit_way_hot_prel;
    dc3_skid_odd_hit_way_hot_r         <= dc3_dt_odd_hit_way_hot_prel;
  end
end
// leda TEST_975 on



always @ (posedge clk or posedge rst_a)
begin : dc_skid_bank0_syndrome_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc_skid_bank0_syndrome_r     <= {`npuarc_SYNDROME_MSB+1{1'b0}};
    dc_skid_bank1_syndrome_r     <= {`npuarc_SYNDROME_MSB+1{1'b0}};
    dc_skid_bank2_syndrome_r     <= {`npuarc_SYNDROME_MSB+1{1'b0}};
    dc_skid_bank3_syndrome_r     <= {`npuarc_SYNDROME_MSB+1{1'b0}};
  end
  else
  begin
    dc_skid_bank0_syndrome_r     <= dc_skid_bank0_syndrome_nxt;        
    dc_skid_bank1_syndrome_r     <= dc_skid_bank1_syndrome_nxt;        
    dc_skid_bank2_syndrome_r     <= dc_skid_bank2_syndrome_nxt;        
    dc_skid_bank3_syndrome_r     <= dc_skid_bank3_syndrome_nxt;        
  end
end


// spyglass disable_block STARC05-2.2.3.3
// SMD: Flipflop value assigned more than once over same signal in always construct
// SJ:  Conflit covered by assertions

always @ (posedge clk or posedge rst_a)
begin : dc4_dccm_ecc_skid_sb_error_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_dccm_ecc_skid_sb_error_r   <= 4'b0000;
    dc4_dccm_ecc_skid_db_error_r   <= 4'b0000;
  end
  else
  begin
    dc4_dccm_ecc_skid_sb_error_r <= dc4_dccm_ecc_skid_sb_error_nxt;
    dc4_dccm_ecc_skid_db_error_r <= dc4_dccm_ecc_skid_db_error_nxt;
  end
end
// spyglass enable_block STARC05-2.2.3.3

// spyglass disable_block STARC05-2.2.3.3
// SMD: Flipflop value assigned more than once over same signal in always construct
// SJ:  Conflit covered by assertions

always @ (posedge clk or posedge rst_a)
begin : dc4_dc_ecc_skid_sb_error_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_dc_ecc_skid_sb_error_r   <= 4'b0000;
    dc4_dc_ecc_skid_db_error_r   <= 4'b0000;
  end
  else
  begin
    dc4_dc_ecc_skid_sb_error_r   <= dc4_dc_ecc_skid_sb_error_nxt;
    dc4_dc_ecc_skid_db_error_r   <= dc4_dc_ecc_skid_db_error_nxt;
  end
end
// spyglass enable_block STARC05-2.2.3.3






always @ (posedge clk or posedge rst_a)
begin : dc3_skid_ecc_valid_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc3_skid_ecc_valid_r  <= 4'd0;
  end
  else
  begin
    dc3_skid_ecc_valid_r  <= dc3_skid_ecc_valid_nxt;
  end
end

always @ (posedge clk or posedge rst_a)
begin : dc3_skid_state_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc3_skid_state_r <= 1'b0;
  end
  else
  begin
    dc3_skid_state_r <= dc3_skid_state_nxt;
  end
end

endmodule // alb_dmp_skid_buffer

