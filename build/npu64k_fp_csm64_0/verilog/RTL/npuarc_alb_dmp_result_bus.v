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
//                   
//  ALB_DMP_RESULT_BUS                 
//                   
//                   
//
// ===========================================================================
//
// Description:
// This module is respoosible for delievering the DMP load results. Results 
// can come from different DMP sub-modules: DCCM, Load Queue, etc.
// Each DMP unit requests the result bus with the req signal. The request signal
// shoud be sent to the result bus the cycle before the actual load result 
// (data) is valid. Note that multiple DMP units may request the result bus 
// at the same time.  The result bus performs an arbitration and ack the 
// sub-unit with the highest priority. 
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_result_bus.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"


//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 }, rst: "rst_a", edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_dmp_result_bus (
// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ: some bits of inputs vectors are not used
  ////////// General input signals ///////////////////////////////////////////
  //
  input                        clk,            // clock
  input                        rst_a,          // reset

  ////////// Interface to DC3 stage //////////////////////////////////////
  //
  input                        x3_pass,
  input                        x3_load_r,
  input                        x3_store_r,
  input [1:0]                  x3_size_r,       // 00-b, 01-h, 10-w, 11-dw
  input                        x3_sex_r,        // DC3 load sign extension
  input [3:0]                  x3_addr_3_to_0_r,
  input [1:0]                  dc3_data_bank_sel_lo_r,
  input [1:0]                  dc3_data_bank_sel_hi_r,
  input [`npuarc_DMP_TARGET_RANGE]    dc3_target_r,
  input                        dc3_dt_miss,   
  input [3:0]                  dc3_rmw_r,
  input                        dc3_fwd_req,        // uncached store to ld fwd
  
  input [3:0]                  wq_fwd_bank,
  input [`npuarc_DATA_RANGE]          wq_fwd_data_bank0_lo,
  input [`npuarc_DATA_RANGE]          wq_fwd_data_bank0_hi,
  input [`npuarc_DATA_RANGE]          wq_fwd_data_bank1_lo,
  input [`npuarc_DATA_RANGE]          wq_fwd_data_bank1_hi,
  
  ////////// Interface to CA stage //////////////////////////////////////
  // 
  input                        ca_enable,
  input                        ca_valid_r,
  input                        ca_load_r,
  input                        ca_sex_r,       // DC3 load sign extension
  input [1:0]                  ca_size_r,      // 00-b, 01-h, 10-w, 11-dw
  input [3:0]                  ca_addr_3_to_0_r,
  input [`npuarc_DMP_TARGET_RANGE]    dc4_target_r,
  output reg [3:0]             wq_fwd_bank_r,
  output reg [`npuarc_DATA_RANGE]     rb_fwd_data_bank0_lo_r,  
  output reg [`npuarc_DATA_RANGE]     rb_fwd_data_bank0_hi_r,
  output reg [`npuarc_DATA_RANGE]     rb_fwd_data_bank1_lo_r,
  output reg [`npuarc_DATA_RANGE]     rb_fwd_data_bank1_hi_r,
  ////////// Interface to DCCM (dc3 info) /////////////////////////////////////
  //
  input                        dccm_rb_req,      // DCCM delivering res nxt cyc
  input [`npuarc_DBL_DCCM_LO_RANGE]   dccm_rb_bank0_lo_r,
  input [`npuarc_DBL_DCCM_LO_RANGE]   dccm_rb_bank0_hi_r,
  input [`npuarc_DBL_DCCM_LO_RANGE]   dccm_rb_bank1_lo_r,
  input [`npuarc_DBL_DCCM_LO_RANGE]   dccm_rb_bank1_hi_r,

  ////////// Interface to DCACHE (dc3 info) ////////////////////////////////////
  //
  input                          dc_rb_req,       // DC delivering res nxt cyc
  input                          dc_dt_hit,       // Hit in the tag memories 
  input [`npuarc_DC_WAY_DATA_ECC_RANGE] dc_rb_bank0_lo_r,
  input [`npuarc_DC_WAY_DATA_ECC_RANGE] dc_rb_bank0_hi_r,
  input [`npuarc_DC_WAY_DATA_ECC_RANGE] dc_rb_bank1_lo_r,
  input [`npuarc_DC_WAY_DATA_ECC_RANGE] dc_rb_bank1_hi_r,
   
  ////////// Interface to the post-commit stage (load queue) ////////////////
  //
  input                        lq_rb_req,            // load queue req
  input                        lq_rb_err,            // load queue req with error
  input [`npuarc_GRAD_TAG_RANGE]      lq_rb_tag,            // load queue tag
  input                        lq_rb_sex,            // sex
  input [1:0]                  lq_rb_size,           // b, w, hw , dw
  input [`npuarc_PADDR_RANGE]         lq_rb_addr,    //
  
  output reg                   lq_rb_ack,            // load queue ack
  
  input [`npuarc_DOUBLE_RANGE]        lq_rb_data_even_r,                 
  input [`npuarc_DOUBLE_RANGE]        lq_rb_data_odd_r,                 

  ////////// Interface to the post-commit stage (dc miss queue) ///////////////
  //
  input                        mq_rb_req,       // miss queue req          
  input                        mq_rb_err,       // miss queue req with error          
  input [`npuarc_GRAD_TAG_RANGE]      mq_rb_tag,                                  
  input [`npuarc_PADDR_RANGE]         mq_rb_addr,      // Address of load data    
  input [3:0]                  mq_bank_sel,                                
  input                        mq_sex,          // Load sign extension     
  input [1:0]                  mq_size,         // 00-b, 01-h, 10-w, 11-dw 
  output reg                   mq_rb_ack,       // miss queue ack          
  
  input [`npuarc_DC_DATA_RANGE]       mq_rb_data,                 
  output wire [`npuarc_DC_DATA_RANGE] rb_aln_data,                 
  
  ////////// Interface to the result bus ////////////////////////////////////
  //
  input                        wq_scond_rb_req,  // Request retirement
  input  [`npuarc_GRAD_TAG_RANGE]     wq_scond_rb_tag,  // Retiremnt tag
  input                        wq_scond_rb_flag, // Retirement data  (z flag)
  output reg                   wq_scond_rb_ack,  // Retirement ack
  
  ////////// SCOND status /////////////////////////////////////////////////
  //
  input                        dc4_scond_go,     // SCOND status at CA
  ////////// Retirement interface //////////////////////////////////////////
  //
  output reg                   rb_retire_req_r,               
  output reg                   rb_retire_err_r,               
  output reg [`npuarc_GRAD_TAG_RANGE] rb_retire_tag_r,               
                 
  ////////// Status //////////////////////////////////////////////////////
  //
  output reg                   rb_empty,
  
  ////////// Commit load results  ////////////////////////////////////////
  //
  output reg                   dc3_fast_byp,        // DC3 fast byp
  output reg                   dc4_fast_byp_r,      // DC4 fast byp validation
  output reg                   dc4_fast_byp_miss_r, // DC4 fast byp (MDR)
  output reg [`npuarc_DATA_RANGE]     rb_fast_data,        // fast 32-bit load
  output reg                   rb_scond_zflag,      // SCOND success/failure
  output reg                   rb_stall_r,          // result bus stall
  output [`npuarc_DMP_DATA_RANGE]     rb_rf_wdata          // load data aligned and sex   
// leda NTL_CON37 on  
// leda NTL_CON13C on  
);

// Local Declaration
reg [`npuarc_DMP_DATA_RANGE]   rb_retire_data_nxt;
reg                     lq_rb_ack_r;
reg                     dc_rb_ack;
reg                     mq_rb_ack_r;
reg                     dc_rb_ack_r;
reg                     dc_mq_rb_ack_r;
reg                     dccm_rb_ack;
reg                     dccm_rb_ack_r;
   
reg                     dc3_rb_req;     
reg                     dc4_rb_req_r;     

reg                     dc4_load_cg0;

reg                     rb_ctl_cg0; 


reg [1:0]               rb_aln_size_nxt;
reg                     rb_aln_sex_nxt;
reg [3:0]               rb_aln_addr_3_to_0_nxt;

reg                     rb_aln_data_cg0;
reg                     rb_tag_cg0;

reg [`npuarc_DOUBLE_RANGE]     rb_aln_data0;
reg [`npuarc_DOUBLE_RANGE]     rb_aln_data1;

reg [1:0]               rb_aln_size_r;
reg                     rb_aln_sex_r;
reg [3:0]               rb_aln_addr_3_to_0_r;

// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg [7:0]               rb_fast_bank_sel_hot_r;
reg [7:0]               rb_fast_bank_sel_hot_nxt;
// leda NTL_CON32 on

reg                     rb_retire_err_nxt;              
reg                     rb_retire_req_nxt;              
reg [`npuarc_GRAD_TAG_RANGE]   rb_retire_tag_nxt;               

reg                     rb_retire_zflag_valid_r;
reg                     rb_retire_zflag_valid_nxt;

reg                     rb_retire_zflag_r;
reg                     rb_retire_zflag_nxt;

reg                     rb_fwd_data_bank0_lo_cg0;  
reg                     rb_fwd_data_bank0_hi_cg0;  
reg                     rb_fwd_data_bank1_lo_cg0;  
reg                     rb_fwd_data_bank1_hi_cg0; 

reg [`npuarc_DATA_RANGE]       rb_fwd_data_bank0_lo_nxt;
reg [`npuarc_DATA_RANGE]       rb_fwd_data_bank0_hi_nxt;
reg [`npuarc_DATA_RANGE]       rb_fwd_data_bank1_lo_nxt;
reg [`npuarc_DATA_RANGE]       rb_fwd_data_bank1_hi_nxt;
reg                     rb_fwd_enb_bank0_lo_r;
reg                     rb_fwd_enb_bank0_hi_r;
reg                     rb_fwd_enb_bank1_lo_r;
reg                     rb_fwd_enb_bank1_hi_r;

reg                     rb_fwd_enb_bank0_lo_nxt;
reg                     rb_fwd_enb_bank0_hi_nxt;
reg                     rb_fwd_enb_bank1_lo_nxt;
reg                     rb_fwd_enb_bank1_hi_nxt;
reg                     dc3_aligned_load;
reg                     dc3_target_dccm;
reg                     dc3_target_dc;
reg                     dc4_fast_byp_cg0;
reg                     dc4_fast_byp_nxt;     
reg                     dc4_fast_byp_miss_nxt;


reg [3:0]               mq_fwd_bank_sel_r;
reg [3:0]               mq_req_bank_sel_r;
wire [3:0]              dc4_mq_bank_sel;

wire [`npuarc_DATA_RANGE]      dccm_rb_data0_lo;
wire [`npuarc_DATA_RANGE]      dccm_rb_data0_hi;
wire [`npuarc_DATA_RANGE]      dccm_rb_data1_lo;
wire [`npuarc_DATA_RANGE]      dccm_rb_data1_hi;

wire [`npuarc_DATA_RANGE]      dc_rb_data0_lo; 
wire [`npuarc_DATA_RANGE]      dc_rb_data0_hi; 
wire [`npuarc_DATA_RANGE]      dc_rb_data1_lo; 
wire [`npuarc_DATA_RANGE]      dc_rb_data1_hi; 

reg                     rb_stall_nxt;
   
   assign dccm_rb_data1_hi = dccm_rb_bank1_hi_r[`npuarc_DATA_RANGE]; 
   assign dccm_rb_data1_lo = dccm_rb_bank1_lo_r[`npuarc_DATA_RANGE];
   assign dccm_rb_data0_hi = dccm_rb_bank0_hi_r[`npuarc_DATA_RANGE];
   assign dccm_rb_data0_lo = dccm_rb_bank0_lo_r[`npuarc_DATA_RANGE];
   assign dc_rb_data1_hi = dc_rb_bank1_hi_r[`npuarc_DATA_RANGE]; 
   assign dc_rb_data1_lo = dc_rb_bank1_lo_r[`npuarc_DATA_RANGE];
   assign dc_rb_data0_hi = dc_rb_bank0_hi_r[`npuarc_DATA_RANGE];
   assign dc_rb_data0_lo = dc_rb_bank0_lo_r[`npuarc_DATA_RANGE];
   
   
//////////////////////////////////////////////////////////////////////////////
//                                                                          
// DC3 signals
//                                                                           
//////////////////////////////////////////////////////////////////////////////

always @*
begin : dc3_rb_req_PROC
  // A dc3 request to the result bus happen when:
  // - DC3 load accessing Dcache
  // - DC3 load accessing DCCM
  // - DC3 uncached load getting its result from WQ
  // The DCCM and the DCache request the result bus mutually exclusively in the
  // DC3 stage. 
  //
   dc3_rb_req       = (dc3_fwd_req & x3_pass)
                   | dccm_rb_req
                   | dc_rb_req
                   ;
  dc3_target_dccm  = (dc3_target_r == `npuarc_DMP_TARGET_DCCM);
  dc3_target_dc    = (dc3_target_r == `npuarc_DMP_TARGET_DC);
end

always @*
begin : dc4_load_cg0_PROC
  //
  //
  dc4_load_cg0 = (x3_load_r & x3_pass)  // Set
               | (~ca_load_r)           // Clear 
               ; 
end
//////////////////////////////////////////////////////////////////////////////
//                                                                          
// FWD mux (before the flop)
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : rb_fwd_data_PROC
  // Forward source (default to WQ)
  //
  if (wq_fwd_bank[0])
    rb_fwd_data_bank0_lo_nxt = wq_fwd_data_bank0_lo;
  else
    rb_fwd_data_bank0_lo_nxt = lq_rb_data_even_r[`npuarc_DBL_LO_RANGE];
   
  if (wq_fwd_bank[1])
    rb_fwd_data_bank0_hi_nxt = wq_fwd_data_bank0_hi;
  else
    rb_fwd_data_bank0_hi_nxt = lq_rb_data_even_r[`npuarc_DBL_HI_RANGE];

  if (wq_fwd_bank[2])
    rb_fwd_data_bank1_lo_nxt = wq_fwd_data_bank1_lo;
  else
    rb_fwd_data_bank1_lo_nxt = lq_rb_data_odd_r[`npuarc_DBL_LO_RANGE];

  if (wq_fwd_bank[3])
    rb_fwd_data_bank1_hi_nxt = wq_fwd_data_bank1_hi;
  else
    rb_fwd_data_bank1_hi_nxt = lq_rb_data_odd_r[`npuarc_DBL_HI_RANGE];
  
end
//////////////////////////////////////////////////////////////////////////////
// Arbitration logic: 
// The various DMP units need to request the result bus one cycle before
// provding the results, e.g:  in-order loads request the result bus in
// DC3, providing the data in DC4.
// The same applies for the post commit ld queue (lq) and for the dcache miss
// queue(mq).
// Note that all control information (size, sex, etc.) are provided together
// with the request. It is just the data that comes one cycle later.
//////////////////////////////////////////////////////////////////////////////

always @*
begin : rb_mux_PROC
  // DMP result bus outputs
  //
  rb_retire_req_nxt        = 1'b0;
  rb_retire_tag_nxt        = {`npuarc_GRAD_TAG_BITS{1'b0}};
  
  // DMP LQ bus errors
  //
  rb_retire_err_nxt        = 1'b0;
 
  rb_stall_nxt             = 1'b0;
  // Aligner inputs
  //
  rb_aln_size_nxt          = rb_aln_size_r;       
  rb_aln_sex_nxt           = rb_aln_sex_r;        
  rb_aln_addr_3_to_0_nxt   = rb_aln_addr_3_to_0_r;
  
  // clock gate enable
  //
  rb_aln_data_cg0          = 1'b0;             
  rb_tag_cg0               = 1'b0;             
  
  rb_ctl_cg0               =   lq_rb_ack_r
                             | mq_rb_ack_r
                             | dc_rb_ack_r
                             | dccm_rb_ack_r
                             | rb_retire_req_r;
  

  rb_retire_zflag_valid_nxt = 1'b0;
  rb_retire_zflag_nxt       = rb_retire_zflag_r;
  // Fast bank sel
  //
  rb_fast_bank_sel_hot_nxt = rb_fast_bank_sel_hot_r;
  dc_rb_ack                = 1'b0;
  dccm_rb_ack              = 1'b0;
  lq_rb_ack                = 1'b0;
  mq_rb_ack                = 1'b0;
  wq_scond_rb_ack          = 1'b0;
  
  if (dc3_rb_req)
  begin
    // Data is coming from the pipe (DC3 stage).
    //
    dc_rb_ack                = dc_rb_req;
    
    dccm_rb_ack              = dccm_rb_req;
    // Aligner inputs
    //
    rb_aln_size_nxt          = x3_size_r;    
    rb_aln_sex_nxt           = x3_sex_r;
    rb_aln_addr_3_to_0_nxt   = x3_addr_3_to_0_r;
    
    // Fast bank sel
    //
    rb_fast_bank_sel_hot_nxt      = {4'b0000, 4'b0000}; // DCache, DCCM
    rb_fast_bank_sel_hot_nxt[3:0] = 
                              {((x3_addr_3_to_0_r[3:2] == 2'b11) & dccm_rb_req),
                               ((x3_addr_3_to_0_r[3:2] == 2'b10) & dccm_rb_req),
                               ((x3_addr_3_to_0_r[3:2] == 2'b01) & dccm_rb_req),
                               ((x3_addr_3_to_0_r[3:2] == 2'b00) & dccm_rb_req)};
    rb_fast_bank_sel_hot_nxt[7:4] = 
                              {((x3_addr_3_to_0_r[3:2] == 2'b11) & dc_rb_req),
                               ((x3_addr_3_to_0_r[3:2] == 2'b10) & dc_rb_req),
                               ((x3_addr_3_to_0_r[3:2] == 2'b01) & dc_rb_req),
                               ((x3_addr_3_to_0_r[3:2] == 2'b00) & dc_rb_req)};
    
    // Turn on the clock
    //
    rb_ctl_cg0               = 1'b1;
    rb_aln_data_cg0          = 1'b1;


  end
  else if (wq_scond_rb_req)
  begin
    // SCOND retirement
    //
    wq_scond_rb_ack           = 1'b1;
    
    rb_tag_cg0                = 1'b1; 

    rb_retire_zflag_valid_nxt = 1'b1;
    rb_retire_zflag_nxt       = wq_scond_rb_flag;
    
    // DMP result bus outputs
    //
    rb_retire_req_nxt         = 1'b1;     
    rb_retire_tag_nxt         = wq_scond_rb_tag;
    
    // Turn on the clock
    //
    rb_ctl_cg0                = 1'b1;
  end
  else if (mq_rb_req)
  begin
    // Data is coming from Data Cache miss queue.
    //
    mq_rb_ack              = 1'b1;
 
    // Generate a one cycle stall when a load instruction is stalled in CA
    // and there is a retirement request   
    //    
    rb_stall_nxt           = ca_load_r  
                           & dc4_rb_req_r
                           & (~ca_enable);
    
    // Aligner inputs
    //
    rb_aln_size_nxt        = mq_size;
    rb_aln_sex_nxt         = mq_sex;
    rb_aln_addr_3_to_0_nxt = mq_rb_addr[3:0];

    rb_aln_data_cg0        = 1'b1;
    rb_tag_cg0             = 1'b1;
    
    // DMP result bus outputs
    //
    rb_retire_req_nxt      = 1'b1;     
    rb_retire_tag_nxt      = mq_rb_tag;
   
    rb_retire_err_nxt      = mq_rb_err;

    // Turn on the clock
    //
    rb_ctl_cg0             = 1'b1;
  end
  else if (lq_rb_req)
  begin
    // Data is coming from load queue.
    //
    lq_rb_ack              = 1'b1;
   
    // Generate a one cycle stall when a load instruction is stalled in CA
    // and there is a retirement request 
    //   
    rb_stall_nxt           = ca_load_r 
                           & dc4_rb_req_r
                           & (~ca_enable);
    
    rb_aln_size_nxt        = lq_rb_size;
    rb_aln_sex_nxt         = lq_rb_sex;
    rb_aln_addr_3_to_0_nxt = lq_rb_addr[3:0];

    rb_aln_data_cg0        = 1'b1; 
    rb_tag_cg0             = 1'b1; 
    
    // DMP result bus outputs
    //
    rb_retire_req_nxt      = 1'b1;     
    rb_retire_tag_nxt      = lq_rb_tag;
    
    rb_retire_err_nxt      = lq_rb_err;
    
    // Turn on the clock
    //
    rb_ctl_cg0             = 1'b1;
    
  end
  else if (ca_valid_r & ca_load_r)
  begin
    // Valid data pending in CA pipe (DC4 stage).
    //
    dc_rb_ack              = dc4_target_r == `npuarc_DMP_TARGET_DC;
    dccm_rb_ack            = dc4_target_r == `npuarc_DMP_TARGET_DCCM;
    // Aligner inputs
    //
    rb_aln_size_nxt        = ca_size_r;    
    rb_aln_sex_nxt         = ca_sex_r;
    rb_aln_addr_3_to_0_nxt = ca_addr_3_to_0_r;
    
    // Turn on the clock
    //
    rb_ctl_cg0             = 1'b1; 
    rb_aln_data_cg0        = 1'b1; 
  end
end



//////////////////////////////////////////////////////////////////////////////
//
// Asynchronous logic defining the fast bypass validation
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc4_fast_byp_nxt_PROC
  // Validate the speculative DC3 byp
  //
  dc4_fast_byp_cg0         =   x3_load_r 
                             | dc4_fast_byp_r
                             | dc4_fast_byp_miss_r
                             ;
  
  dc4_fast_byp_nxt         =    (    dc3_fast_byp

                                  &  dc3_target_dccm
                                  & (~(| wq_fwd_bank))
                                )
                             
                             |  (    dc3_fast_byp
                                  & (~(| wq_fwd_bank))   
                                  & dc3_target_dc
                                  & dc_dt_hit                         
                                )
                                ;
                               
  dc4_fast_byp_miss_nxt    =   dc3_fast_byp
                             & dc3_target_dc
                             & dc3_dt_miss
                             ;
end

//////////////////////////////////////////////////////////////////////////////
//
//  WQ Fwd bank and data clock gate
//
//////////////////////////////////////////////////////////////////////////////
reg  dc3_partial_st_dccm;
reg  dc3_partial_st_dc;
always @*
begin : rb_fwd_enb_PROC
  dc3_partial_st_dccm      =   x3_store_r
                            & (|dc3_rmw_r)
                            & x3_pass
                            & (dc3_target_r == `npuarc_DMP_TARGET_DCCM);

  dc3_partial_st_dc        =   x3_store_r
                            & (|dc3_rmw_r)
                            & x3_pass
                            & (dc3_target_r == `npuarc_DMP_TARGET_DC);

  // When there is dc3_rb_req or 
  // when there is a partial store in x3 
  //
  if (  dc3_rb_req
      | dc3_partial_st_dccm
      | dc3_partial_st_dc
     )
  begin
    rb_fwd_enb_bank0_lo_nxt  = wq_fwd_bank[0];
    rb_fwd_enb_bank0_hi_nxt  = wq_fwd_bank[1];
    rb_fwd_enb_bank1_lo_nxt  = wq_fwd_bank[2];
    rb_fwd_enb_bank1_hi_nxt  = wq_fwd_bank[3];
    rb_fwd_data_bank0_lo_cg0 = dc3_data_bank_sel_lo_r[0];
    rb_fwd_data_bank0_hi_cg0 = dc3_data_bank_sel_hi_r[0];
    rb_fwd_data_bank1_lo_cg0 = dc3_data_bank_sel_lo_r[1];
    rb_fwd_data_bank1_hi_cg0 = dc3_data_bank_sel_hi_r[1];
  end
  else
  begin
    rb_fwd_enb_bank0_lo_nxt  = 1'b0;
    rb_fwd_enb_bank0_hi_nxt  = 1'b0;
    rb_fwd_enb_bank1_lo_nxt  = 1'b0;
    rb_fwd_enb_bank1_hi_nxt  = 1'b0;
    rb_fwd_data_bank0_lo_cg0 = 1'b0;  
    rb_fwd_data_bank0_hi_cg0 = 1'b0;  
    rb_fwd_data_bank1_lo_cg0 = 1'b0;  
    rb_fwd_data_bank1_hi_cg0 = 1'b0;  
  end
end

//////////////////////////////////////////////////////////////////////////////
//
// Forwarding the bank information from WQ
//
/////////////////////////////////////////////////////////////////////////////
always @*
begin : wq_fwd_bank_PROC
  wq_fwd_bank_r = { rb_fwd_enb_bank1_hi_r, rb_fwd_enb_bank1_lo_r,
                    rb_fwd_enb_bank0_hi_r, rb_fwd_enb_bank0_lo_r };
end
//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Combinational logic selecting the data input to the aligner
//                                                                           
//////////////////////////////////////////////////////////////////////////////
assign dc4_mq_bank_sel = mq_rb_ack_r ?
                         mq_req_bank_sel_r : mq_fwd_bank_sel_r;
// route this bus to DMU for cross-line forwarding which can come from
// any sources: DC, line buffer, WQ
//
assign rb_aln_data     = {rb_aln_data1, rb_aln_data0};  

always @*
begin : rb_aln_data_PROC
  case (1'b1)
  lq_rb_ack_r:
  begin
    rb_aln_data0 = lq_rb_data_even_r;
    rb_aln_data1 = lq_rb_data_odd_r;
  end
  dc_mq_rb_ack_r:
  begin
    // This is the case the dmu (or miss queue) is retiring a load from the
    // line buffer. The entire data is in the line buffer. 
    //
    rb_aln_data0[`npuarc_DBL_LO_RANGE] = (dc4_mq_bank_sel[0] ?
                                   mq_rb_data[`npuarc_WORD0_RANGE] :
                                   (rb_fwd_enb_bank0_lo_r ?
                                    rb_fwd_data_bank0_lo_r : 
                                    dc_rb_data0_lo[`npuarc_DATA_RANGE]));
    rb_aln_data0[`npuarc_DBL_HI_RANGE] = (dc4_mq_bank_sel[1] ?
                                   mq_rb_data[`npuarc_WORD1_RANGE] :
                                   (rb_fwd_enb_bank0_hi_r ?
                                    rb_fwd_data_bank0_hi_r : 
                                    dc_rb_data0_hi[`npuarc_DATA_RANGE]));
    rb_aln_data1[`npuarc_DBL_LO_RANGE] = (dc4_mq_bank_sel[2] ?
                                   mq_rb_data[`npuarc_WORD2_RANGE] :
                                   (rb_fwd_enb_bank1_lo_r ?
                                    rb_fwd_data_bank1_lo_r : 
                                    dc_rb_data1_lo[`npuarc_DATA_RANGE]));
    rb_aln_data1[`npuarc_DBL_HI_RANGE] = (dc4_mq_bank_sel[3] ?
                                   mq_rb_data[`npuarc_WORD3_RANGE] :
                                   (rb_fwd_enb_bank1_hi_r ?
                                    rb_fwd_data_bank1_hi_r : 
                                    dc_rb_data1_hi[`npuarc_DATA_RANGE]));
  end
  
  default:
  begin
    rb_aln_data0[`npuarc_DBL_LO_RANGE] =   rb_fwd_enb_bank0_lo_r
                                  ? rb_fwd_data_bank0_lo_r
                                  : dccm_rb_data0_lo[`npuarc_DATA_RANGE];
    rb_aln_data0[`npuarc_DBL_HI_RANGE] =   rb_fwd_enb_bank0_hi_r
                                  ? rb_fwd_data_bank0_hi_r
                                  : dccm_rb_data0_hi[`npuarc_DATA_RANGE];
    rb_aln_data1[`npuarc_DBL_LO_RANGE] =   rb_fwd_enb_bank1_lo_r
                                  ? rb_fwd_data_bank1_lo_r
                                  : dccm_rb_data1_lo[`npuarc_DATA_RANGE];
    rb_aln_data1[`npuarc_DBL_HI_RANGE] =   rb_fwd_enb_bank1_hi_r
                                  ? rb_fwd_data_bank1_hi_r
                                  : dccm_rb_data1_hi[`npuarc_DATA_RANGE];
  
  end
  endcase  
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Module instantiation: load aligner
//                                                                           
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_dmp_load_aligner u_alb_dmp_load_aligner (
  .dmp_aln_data0        (rb_aln_data0        ),
  .dmp_aln_data1        (rb_aln_data1        ),
  .dmp_aln_size         (rb_aln_size_r       ),
  .dmp_aln_sex          (rb_aln_sex_r        ),
  .dmp_aln_addr_3_to_0  (rb_aln_addr_3_to_0_r),

  .aln_data             (rb_rf_wdata         )
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Fast bypass (DC3)
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc3_fast_byp_PROC
  // This is a speculative fast bypass 
  //
  
  dc3_aligned_load =    x3_load_r              
                     & (x3_size_r == 2'b10)
                     & (x3_addr_3_to_0_r[1:0] == 2'b00);
  
  
  // Early fast bypass
  //
  dc3_fast_byp     =   dc3_aligned_load 
                     & (dc3_target_dccm | dc3_target_dc);
  
  
end
//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Fast data
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : rb_fast_data_PROC
  // The fast bypass data comes either from the DCCM or from the DCache
  // It doesn't go through the aligner
  //
  
  rb_fast_data = 
            ({32{rb_fast_bank_sel_hot_r[0]}} & dccm_rb_bank0_lo_r[`npuarc_DATA_RANGE])
          | ({32{rb_fast_bank_sel_hot_r[1]}} & dccm_rb_bank0_hi_r[`npuarc_DATA_RANGE])
          | ({32{rb_fast_bank_sel_hot_r[2]}} & dccm_rb_bank1_lo_r[`npuarc_DATA_RANGE])
          | ({32{rb_fast_bank_sel_hot_r[3]}} & dccm_rb_bank1_hi_r[`npuarc_DATA_RANGE])
          | ({32{rb_fast_bank_sel_hot_r[4]}} & dc_rb_bank0_lo_r[`npuarc_DATA_RANGE])
          | ({32{rb_fast_bank_sel_hot_r[5]}} & dc_rb_bank0_hi_r[`npuarc_DATA_RANGE])
          | ({32{rb_fast_bank_sel_hot_r[6]}} & dc_rb_bank1_lo_r[`npuarc_DATA_RANGE])
          | ({32{rb_fast_bank_sel_hot_r[7]}} & dc_rb_bank1_hi_r[`npuarc_DATA_RANGE])
      ;  
end

//////////////////////////////////////////////////////////////////////////////
// SCOND result
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : rb_zflag_PROC
  if (rb_retire_zflag_valid_r)
  begin
    // We have a SCOND retiring. Pick the zflag from the retirement i/f
    //
    rb_scond_zflag = rb_retire_zflag_r;
  end
  else
  begin
    // Set the zflag for SOCND that commit with no graduation
    //
    // Condition for success:
    // (1) Matching LPA
    // (2) Lock flag still set
    //
    rb_scond_zflag = dc4_scond_go;
  end
end

//////////////////////////////////////////////////////////////////////////////
// Status
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : rb_empty_PROC
  // The restul bus is idle when no unit is requesting retirement and 
  // any pending retirement has been acknowledged.
  //
  rb_empty = ~(rb_retire_req_r | rb_retire_req_nxt);
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Synchronous process: ctl flops
//                                                                           
//////////////////////////////////////////////////////////////////////////////
// VPOST OFF

always @(posedge clk or posedge rst_a)
begin : rb_retire_req_reg_PROC
  if (rst_a == 1'b1)
  begin
    rb_retire_req_r          <= 1'b0;
    rb_retire_err_r          <= 1'b0;
  end
  else if (rb_ctl_cg0)
  begin
    rb_retire_req_r        <= rb_retire_req_nxt;
    rb_retire_err_r        <= rb_retire_err_nxt;
  end
end

always @(posedge clk or posedge rst_a)
begin : dc_rb_ack_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc_rb_ack_r     <= 1'b0;
    mq_rb_ack_r     <= 1'b0;
    dc_mq_rb_ack_r  <= 1'b0;
    dccm_rb_ack_r   <= 1'b0;
    lq_rb_ack_r     <= 1'b0;
  end
  else if (rb_ctl_cg0)
  begin
    dc_rb_ack_r    <= dc_rb_ack;
    mq_rb_ack_r    <= mq_rb_ack;
    dc_mq_rb_ack_r <= dc_rb_ack | mq_rb_ack;
    dccm_rb_ack_r  <= dccm_rb_ack;
    lq_rb_ack_r    <= lq_rb_ack;
  end
end

always @(posedge clk or posedge rst_a)
begin : rb_fwd_enb_bank0_lo_reg_PROC
  if (rst_a == 1'b1)
  begin
    rb_fwd_enb_bank0_lo_r   <= 1'b0;
    rb_fwd_enb_bank0_hi_r   <= 1'b0;
    rb_fwd_enb_bank1_lo_r   <= 1'b0;
    rb_fwd_enb_bank1_hi_r   <= 1'b0;  
  end
  else if (  dc3_rb_req
        | dc3_partial_st_dccm
        | dc3_partial_st_dc
       )
  begin
    rb_fwd_enb_bank0_lo_r <= rb_fwd_enb_bank0_lo_nxt;
    rb_fwd_enb_bank0_hi_r <= rb_fwd_enb_bank0_hi_nxt;
    rb_fwd_enb_bank1_lo_r <= rb_fwd_enb_bank1_lo_nxt;
    rb_fwd_enb_bank1_hi_r <= rb_fwd_enb_bank1_hi_nxt;
  end
end
// VPOST ON
always @(posedge clk or posedge rst_a)
begin : mq_fwd_bank_sel_reg_PROC
  if (rst_a == 1'b1)
  begin
    mq_fwd_bank_sel_r <= 4'b0000;
  end
  else if (dc3_rb_req)
  begin
    mq_fwd_bank_sel_r <= mq_bank_sel;
  end
end

always @(posedge clk or posedge rst_a)
begin : mq_req_bank_sel_reg_PROC
  if (rst_a == 1'b1)
  begin
    mq_req_bank_sel_r <= 4'b0000;
  end
  else if (mq_rb_req)
  begin
    mq_req_bank_sel_r <= mq_bank_sel;
  end
end

// VPOST OFF

always @(posedge clk or posedge rst_a)
begin : rb_retire_zflag_reg_PROC
  if (rst_a == 1'b1)
  begin
    rb_retire_zflag_valid_r <= 1'b0;
    rb_retire_zflag_r       <= 1'b0;
  end
  else if (rb_ctl_cg0)
  begin
    rb_retire_zflag_valid_r <= rb_retire_zflag_valid_nxt;
    rb_retire_zflag_r       <= rb_retire_zflag_nxt;   
  end
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Synchronous process: data flops
//                                                                           
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : rb_aln_size_reg_PROC
  if (rst_a == 1'b1)
  begin
    rb_aln_size_r           <= 2'b00;
    rb_aln_sex_r            <= 1'b0;
    rb_aln_addr_3_to_0_r    <= 4'b0000; 
  end
  else if (rb_aln_data_cg0)
  begin
    rb_aln_size_r         <= rb_aln_size_nxt;       
    rb_aln_sex_r          <= rb_aln_sex_nxt;        
    rb_aln_addr_3_to_0_r  <= rb_aln_addr_3_to_0_nxt;
  end
end

always @(posedge clk or posedge rst_a)
begin : rb_retire_tag_reg_PROC
  if (rst_a == 1'b1)
  begin
    rb_retire_tag_r    <= {`npuarc_GRAD_TAG_BITS{1'b0}};
  end
  else if (rb_tag_cg0)
  begin
    rb_retire_tag_r    <= rb_retire_tag_nxt;       
  end
end
// VPOST ON

always @(posedge clk or posedge rst_a)
begin : rb_fast_bank_sel_hot_reg_PROC
  if (rst_a == 1'b1)
  begin
    rb_fast_bank_sel_hot_r <= {4'b0000, 4'b0000};
  end
  else if (dc3_rb_req)
  begin
    rb_fast_bank_sel_hot_r <= rb_fast_bank_sel_hot_nxt; 
  end
end

// VPOST OFF
always @(posedge clk or posedge rst_a)
begin : dc4_rb_req_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_rb_req_r <= 1'b0;
  end
  else if (dc4_load_cg0)
  begin
    dc4_rb_req_r <= dc3_rb_req;
  end
end



// leda TEST_975 off
// LMD: Latch enabled by a clock affects data input of flipflops clocked by the trailing edge of the same clock
// LJ:
//
always @(posedge clk or posedge rst_a)
begin : dc4_fast_byp_PROC
  if (rst_a == 1'b1)
  begin
    dc4_fast_byp_r      <= 1'b0;
    dc4_fast_byp_miss_r <= 1'b0;
  end
  else if (dc4_fast_byp_cg0)
  begin
    dc4_fast_byp_r      <= dc4_fast_byp_nxt       & x3_pass & ca_enable;    
    dc4_fast_byp_miss_r <= dc4_fast_byp_miss_nxt  & x3_pass & ca_enable;
  end
end
// leda TEST_975 on
// VPOST ON

// leda NTL_RST03 off
// LMD: A flipflop without reset
// LJ:  Data path signals that dont require a reset
// leda S_1C_R off
// LMD: A flipflop without reset
// LJ:  Data path signals that dont require a reset
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
// KS: Conditional reset datapath when safety enabled
always @(posedge clk)
begin : rb_fwd_data_bank0_lo_reg_PROC
  if (rb_fwd_data_bank0_lo_cg0 == 1'b1)
  begin
    rb_fwd_data_bank0_lo_r <= rb_fwd_data_bank0_lo_nxt;
  end
end

always @(posedge clk)
begin : rb_fwd_data_bank0_hi_reg_PROC
  if (rb_fwd_data_bank0_hi_cg0 == 1'b1)
  begin
    rb_fwd_data_bank0_hi_r <= rb_fwd_data_bank0_hi_nxt;
  end
end

always @(posedge clk)
begin : rb_fwd_data_bank1_lo_reg_PROC
  if (rb_fwd_data_bank1_lo_cg0 == 1'b1)
  begin
    rb_fwd_data_bank1_lo_r <= rb_fwd_data_bank1_lo_nxt;
  end
end

always @(posedge clk)
begin : rb_fwd_data_bank1_hi_reg_PROC
  if (rb_fwd_data_bank1_hi_cg0 == 1'b1)
  begin
    rb_fwd_data_bank1_hi_r <= rb_fwd_data_bank1_hi_nxt;
  end
end


// leda NTL_RST03 on
// leda S_1C_R on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01
// VPOST OFF

always @(posedge clk or posedge rst_a)
begin : rb_stall_reg_PROC
  if (rst_a == 1'b1)
  begin
    rb_stall_r  <= 1'b0;
  end
  else
  begin
    rb_stall_r  <= rb_stall_nxt;
  end
end  
// VPOST ON


endmodule // alb_dmp_result_bus
