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
//   ALB_DMP_RF                 
//                     
//                     
//                     
//
// ===========================================================================
//
// Description:
//  This module implements the Refill Unit for the Data Cache.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_rf.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"


 

//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  rst: "rst_a", edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_dmp_rf (
// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ: some bits of inputs vectors are not used
  ////////// General input signals ///////////////////////////////////////////
  //
  input                       clk,              // clock
  input                       rst_a,            // reset

  input                       dc4_mq_addr_match,
  input                       dc3_mq_addr_match,

  ////////// Read command channel  /////////////////////////////////////////
  //
  output reg                  rf_cmd_valid, 
  output reg                  rf_cmd_excl, 
  input                       rf_cmd_accept,
  output reg                  rf_cmd_read,  
  output reg [`npuarc_PADDR_RANGE]   rf_cmd_addr,  
  output reg                  rf_cmd_prot,  
  output reg                  rf_cmd_wrap,  
  output reg [3:0]            rf_cmd_burst_size,
  ////////// Entry to be sent out on the cmd channel  /////////////////////
  //
  input                       mq_cmd_valid,       
  input                       mq_cmd_pre_alloc,
  input                       mq_cmd_cache_rf,  
  input                       mq_cmd_cache_op, 
  input                       mq_cmd_userm,       
  input [`npuarc_PADDR_RANGE]        mq_cmd_addr,  
  output reg [`npuarc_MQ_PTR_RANGE]  rf_cmd_rptr_r,     

  ////////// Entry to be retired ///////////////////////////////////////////
  //
  input                       mq_valid,
  input [`npuarc_PADDR_RANGE]        mq_addr,
  input                       mq_cache_lock,
  input                       mq_pre_alloc,
  input                       mq_pref,
  input                       mq_scond,
  input                       mq_dirty,
  input                       mq_cb_complete,
  input                       mq_replacement_way,
  input                       mq_replacement_valid,
  input                       mq_bus_err_r,
  
  ////////// DMU interface //////////////////////////////////////////////
  //
  input                       rf_ack_ok,
  output reg                  rf_dc_start,        // Request access
  output reg                  rf_dc_ready,        // Ready to dump line buffer
  output reg                  rf_dc_done,         // All done
  
  ////////// Status of the eviction buffer //////////////////////////////////
  //
  input                       cb_buf_busy_r,
  input                       cb_full,
  
  ////////// Status of the WQ  ////////////////////////////////////////////
  //
  input                       wq_scond_entry,
  
  ////////// Line buffer interface ////////////////////////////////////////
  //
  input                       lb_ready_to_dc, // line buffer ready
  input                       lb_err_r,       // line buffer error
  
  output reg                  lbuf_initial,  // set critical word first
  output reg                  lbuf_rd_valid, // Lbuf --> DC 
  output reg                  lbuf_rd_last,  // Lbuf --> DC
  
  output reg                  rf_lbuf_rd_last_r,
   
  ////////// LSMQ interface ///////////////////////////////////////////////
  //
  input                       lsmq_done,     // done all ld/st to this line
  
  ////////// RF delayed bus error interface /////////////////////////////////
  //
  output reg                  rf_err_req,
  output reg [`npuarc_DC_LBUF_RANGE] rf_err_addr,
  
  ////////// Interface to the  Data Cache Arrays /////////////////////////
  //
  input                       dd_busy_nxt,    // One of the Data banks busy

  output reg                  rf_req_dt_even, // Request even tag array
  output reg                  rf_req_dt_odd,  // Request odd tag array
  output reg                  rf_dt_odd_sel,  // Request odd tag array
  output reg [`npuarc_DC_WAY_RANGE]  rf_dt_way_hot,  // Selected way to write
  output reg                  rf_dt_we,       // Write enable, 0=read
  output reg [2:0]            rf_dt_wem,      // Mask=write enable
  output reg [`npuarc_DC_IDX_RANGE]  rf_dt_addr,     // Address from MQ
  output reg                  rf_dt_valid,    // Valid bit
  output reg [`npuarc_DC_TAG_RANGE]  rf_dt_tag,      // Data tag
  
  output reg                  rf_req_dd,       // DC1 Request to data array
  input                       rf_ack_dd,       // Request acknowledged    
  output reg [`npuarc_DC_WAY_RANGE]  rf_dd_way_hot,   // Selected way to write
  output reg                  rf_dd_we,        // Write enable, 0=read
  output reg [`npuarc_DC_ADR_RANGE]  rf_dd_addr,      // DC2 Address from MQ
  
  // Status (dirty, lock, lru)
  //
  output reg                  rf_req_ds,       // request status flops
  output reg                  rf_ds_odd_sel,   // even, odd set
  output reg                  rf_ds_we,        // write enable
  output reg [2:0]            rf_ds_wem,       // lock, dirty, lru
  output reg [`npuarc_DC_WAY_RANGE]  rf_ds_way_hot,   // selected way to write
  output reg [`npuarc_DC_IDX_RANGE]  rf_ds_addr,
  output reg                  rf_ds_lock,
  output reg                  rf_ds_dirty,
  output reg                  rf_ds_lru        // new lru
// leda NTL_CON37 on  
// leda NTL_CON13C on  
);


// Local declarations
//
// RF->DC FSM
//
reg [2:0]            rf_dc_state_r;
reg [2:0]            rf_dc_state_nxt;
reg [2-1:0]         rf_dc_counter_r;
reg [2-1:0]         rf_dc_counter_nxt;
wire [2-1:0]        rf_dc_counter_incr;
reg                  rf_dc_counter_done_r;
wire                 rf_dc_counter_done_nxt;
wire                 rf_dc_counter_zero;

wire[2:0]            rf_dc_state_next;
wire[2-1:0]	      rf_dc_counter_next ;
wire 		            rf_dc_counter_done_next;

reg                  rf_ack_ok_r;  
// RF->BIU
//  
wire                 rf_biu_state_next;
wire [`npuarc_MQ_PTR_RANGE] rf_cmd_rptr_next;
wire [1:0]           rf_cmd_cnt_next;
 
reg                  rf_biu_state_r;
reg                  rf_biu_state_nxt;
reg                  rf_biu_push;

reg                  rf_lbuf_pop;
reg                  rf_lbuf_pop_r;
  
reg [`npuarc_MQ_PTR_RANGE]  rf_cmd_rptr_nxt;
wire [`npuarc_MQ_PTR_RANGE] rf_cmd_rptr_incr;

reg  [1:0]           rf_cmd_cnt_r;
reg  [1:0]           rf_cmd_cnt_nxt;
wire [1:0]           rf_cmd_cnt_incr;
wire [1:0]           rf_cmd_cnt_decr;
wire                 rf_cmd_cnt_max;
wire                 rf_cb_is_available;


reg                  rf_mq_scond_cg0;
reg                  rf_mq_scond_r;
reg                  rf_mq_scond_nxt;

//////////////////////////////////////////////////////////////////////////
//                                                                        
// Handy variables     
//                                                                        
//////////////////////////////////////////////////////////////////////////
// leda BTTF_D002 off
// leda B_3200 off
// LMD: Unequal length LHS and RHS in assignment LHS
// LJ:  One bit incrementor. Never overflows

// leda W484 off
// LMD: Possible loss of carry/borrow in addition/subtraction LHS
// LJ: Pointer arithmetic: incremented value will not overflow
//
// rf_dc_counter_done always comes form the flop, we compute the rf_dc_counter_done_nxt
// one cycle early and use the registered version
//
assign rf_dc_counter_done_nxt = rf_dc_counter_nxt == {2{1'b1}};

assign rf_dc_counter_zero = rf_dc_counter_r == {2{1'b0}};
assign rf_dc_counter_incr = rf_dc_counter_r + 1'b1;
// leda W484 on
// leda BTTF_D002 on
// leda B_3200 on


//////////////////////////////////////////////////////////////////////////
//                                                                        
// RF FSM       
//                                                                        
//////////////////////////////////////////////////////////////////////////

parameter RF_IDLE           = 3'b000;
parameter RF_PREPARE        = 3'b001;
parameter RF_WAIT_BANK_BUSY = 3'b010;
parameter RF_WRITE_DATA0    = 3'b011;
parameter RF_WRITE_DATA1    = 3'b100;
parameter RF_ALL_LOCKED     = 3'b101;
parameter RF_WAIT_SCOND     = 3'b110;

always @*
begin : rf_dc_fsm_PROC

  // Data tag
  //
  rf_req_dt_even            = 1'b0;
  rf_req_dt_odd             = 1'b0; 
  rf_dt_odd_sel             = mq_addr[`npuarc_DC_TAG_BANK_ID];
  rf_dt_way_hot             = {mq_replacement_way, ~mq_replacement_way};
  rf_dt_wem                 = 3'b011;   // 2: Exclusive, 1: Valid, 0: tag;  
  rf_dt_we                  = 1'b1;      
  rf_dt_addr                = mq_addr[`npuarc_DC_IDX_RANGE]; 
  rf_dt_valid               = 1'b1;
  rf_dt_tag                 = mq_addr[`npuarc_DC_TAG_RANGE];       
  
  // Status (dirty, lock, lru)
  //
  rf_req_ds                 = 1'b0; 
  rf_ds_odd_sel             = mq_addr[`npuarc_DC_TAG_BANK_ID]; 
  rf_ds_we                  = 1'b0; 
  rf_ds_wem                 = 3'b000; 
  rf_ds_way_hot             = {mq_replacement_way, ~mq_replacement_way};
  rf_ds_addr                = mq_addr[`npuarc_DC_IDX_RANGE];    
  rf_ds_lock                = 1'b0;
  rf_ds_dirty               = 1'b0;
  rf_ds_lru                 = ~mq_replacement_way; 
  
  
  // Data Data
  //
  rf_req_dd                 = 1'b0;
  rf_dd_way_hot             = {mq_replacement_way, ~mq_replacement_way}; 
  rf_dd_we                  = (~lb_err_r);
  rf_dd_addr                = {mq_addr[`npuarc_DC_DADR_RANGE], rf_dc_counter_r}; 

  // Control signals of MQ and Lbuf for reading Line buf into DC
  //
  lbuf_rd_valid             = 1'b0;
  lbuf_rd_last              = 1'b0;
  rf_lbuf_pop               = 1'b0;
  
  
  rf_dc_counter_nxt         = rf_dc_counter_r;
  rf_dc_start               = 1'b0;
  rf_dc_ready               = 1'b0;
  rf_dc_done                = 1'b0;
  


  rf_mq_scond_cg0           = 1'b0;
  rf_mq_scond_nxt           = rf_mq_scond_r;

  rf_err_req                = 1'b0;
  rf_err_addr               = mq_addr[`npuarc_DC_LBUF_RANGE];
  
  rf_dc_state_nxt           = rf_dc_state_r;
  
  case (rf_dc_state_r)
  RF_IDLE:
  begin
    // We start requesting ownership a bit early.Otherwise it would be possible 
    // that a DC2 instruction that conflicts with the line buffer doesn't see
    // the line buffer hit. This signal needs to be available early as it 
    // is used to generate the dc2_stall. 
    // 
    rf_dc_start =  mq_cb_complete 
                 & lb_ready_to_dc
                 //& (~dc_pipe_busy)
                 ;
    
    if (   mq_valid
         & mq_cb_complete
         & (~dc3_mq_addr_match)
         & (~dc4_mq_addr_match)
         & lb_ready_to_dc
         & lsmq_done
         //& (~dc_pipe_busy)
        )
    begin
      // Line buffer is ready to be written into the cache.
      //
      // Are we processing a scond transaction?
      //
      rf_mq_scond_cg0          = 1'b1;
      rf_mq_scond_nxt          = mq_scond; 
      
      rf_dc_ready       = 1'b1;
      rf_dc_counter_nxt = {2{1'b0}};
      rf_dc_state_nxt   = mq_replacement_valid ? RF_PREPARE : RF_ALL_LOCKED;
    end
  end
  
  RF_PREPARE:
  begin
    // The refill unit should always be able to access the cache 
    //
    rf_dc_start       = ~rf_ack_ok_r; 
    rf_dc_ready       = 1'b1; 
    
    if (dd_busy_nxt)
    begin
      // The DD banks are not available next cycle. Either a dc1 instruction
      // or the WQ accessed it this cycle
      //
      rf_dc_state_nxt   = RF_WAIT_BANK_BUSY;
    end
    else if (rf_ack_ok_r)
    begin
      rf_dc_state_nxt   = RF_WRITE_DATA0;
    end
  end
  
  RF_WAIT_BANK_BUSY:
  begin
    rf_dc_start       = ~rf_ack_ok_r; 
    rf_dc_ready       = 1'b1; 
    
    if (rf_ack_ok_r)
    begin
      rf_dc_state_nxt = RF_WRITE_DATA0;
    end  
  end
  
  RF_ALL_LOCKED:
  begin
    rf_dc_start       = ~rf_ack_ok_r;   
    rf_dc_ready       = 1'b1; 
    
    if (rf_ack_ok_r)
    begin
      // Gracefully finish the process of aquiring and releasing the cache
      //
      lbuf_rd_last       = 1'b1;
      rf_lbuf_pop        = 1'b1;
      rf_dc_done         = 1'b1;
      rf_dc_state_nxt    = RF_IDLE;
    end  
  end
  
  RF_WRITE_DATA0:
  begin
    // DD memory write
    //
    rf_req_dd                 =  1'b1
                               ;
   
    // DT memory (write new tag, valid and exclusive bit)
    //
    rf_req_dt_even            =    rf_dc_counter_zero 
                                & (~mq_addr[`npuarc_DC_TAG_BANK_ID]);
    rf_req_dt_odd             =    rf_dc_counter_zero 
                                &  mq_addr[`npuarc_DC_TAG_BANK_ID];

    rf_dt_we                  =   (~lb_err_r)
                                ;
    
    rf_dt_wem                 = 3'b011;    // e,v,t
    
    rf_dt_valid               = 1'b1;
    
    // Write dirty bit if the line is dirty. Promote the replacement way
    // to  MRU. Lock the cache line when performing a lock cache instruction
    //
    rf_req_ds                 = rf_dc_counter_zero; 
    rf_ds_we                  =   (~lb_err_r)
                                ; 
                                
    rf_ds_wem                 = {mq_cache_lock,  // lock
                                 1'b1,           // dirty
                                 1'b1};          // lru
    rf_ds_dirty               = (  mq_dirty
                                 | mq_pre_alloc 
                                );
    rf_ds_lock                = mq_cache_lock;
    rf_ds_lru                 = ~mq_replacement_way;
    
    // Generated a delayed bus error if the line buffer contains an error resp.
    // and there has been no bus error reported for that line yet 
    //
    rf_err_req                =  lb_err_r 
                               & (~mq_pref)
                               & (~mq_bus_err_r)
                               & rf_dc_counter_zero;

    if (   rf_ack_dd
        )
    begin
      // LBUF->DC
      //
      lbuf_rd_valid   = 1'b1;
    
      rf_dc_state_nxt = RF_WRITE_DATA1;
    end
  end
  
  RF_WRITE_DATA1:
  begin
    // No access to DD this cycle
    //
    if (  rf_dc_counter_done_r
        )
    begin
      lbuf_rd_last       = 1'b1;
      rf_lbuf_pop        = 1'b1;      
      rf_dc_done         = 1'b1;
      rf_mq_scond_cg0    = 1'b1;
      
      if (  rf_mq_scond_r 
          & wq_scond_entry)
      begin
        // Wait for the scond to evaluate before providing a rd_ack to the SCU
        //
        rf_lbuf_pop      = 1'b0;
        rf_dc_state_nxt  = RF_WAIT_SCOND;
      end
      else
      begin
        rf_mq_scond_nxt  = 1'b0;
        rf_dc_state_nxt  = RF_IDLE;
      end
    end
    else
    begin
      // Lets go write again
      //
      rf_dc_counter_nxt  = rf_dc_counter_incr;
      rf_dc_state_nxt    = RF_WRITE_DATA0;  
    end
  end

  RF_WAIT_SCOND:
  begin
    rf_mq_scond_cg0 = 1'b1;

    if (wq_scond_entry == 1'b0)
    begin
      rf_lbuf_pop     = 1'b1;
      rf_mq_scond_nxt = 1'b0;
      rf_dc_state_nxt = RF_IDLE;
    end
  end
 
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept 
  default:
    ;
  endcase
end

//////////////////////////////////////////////////////////////////////////////
// BIU interface: Sending out read commands
// 
//////////////////////////////////////////////////////////////////////////////

// leda BTTF_D002 off
// leda B_3200 off
// LMD: Unequal length LHS and RHS in assignment LHS
// LJ:  One bit incrementor. Never overflows

// leda W484 off
// LMD: Possible loss of carry/borrow in addition/subtraction LHS
// LJ: Pointer arithmetic: incremented value will not overflow
assign rf_cmd_rptr_incr = rf_cmd_rptr_r + 1'b1;
// leda W484 on
// leda BTTF_D002 on
// leda B_3200 on

assign rf_cb_is_available = (~cb_buf_busy_r) & (~cb_full); 

parameter RF_BIU_IDLE           = 1'b0;
parameter RF_BIU_WAIT_ACCEPT    = 1'b1;

always @*
begin : rf_biu_fsm_PROC
  // Default values
  //
  rf_cmd_valid         = 1'b0; 
  rf_cmd_excl          = 1'b0;
  rf_cmd_read          = 1'b1;
  rf_cmd_addr          = mq_cmd_addr;
  rf_cmd_prot          = ~mq_cmd_userm;
  rf_cmd_wrap          = 1'b1;
  rf_cmd_burst_size    = 4'b0011;
  
  rf_biu_push           = 1'b0;
  rf_cmd_rptr_nxt       = rf_cmd_rptr_r;
  
  rf_biu_state_nxt      = rf_biu_state_r;
  
  case (rf_biu_state_r)
  RF_BIU_IDLE:
  begin
    // Send out a refill command if the top of the mq is valid and we haven't
    // reached the maximum number of outstanding refills and when the eviction
    // buffer is available.
    // The copy back unit is available when the eviction buffer is not
    // busy *and* the copy back have not reached the max number of 
    // oustanding bus transactions
    //
    if (   mq_cmd_valid 
        & (~rf_cmd_cnt_max)
        & (rf_cb_is_available | mq_cmd_cache_op))
    begin
      case (1'b1)
      mq_cmd_cache_op:
      begin
        // Only need to send a refill for a lock refill
        //
        rf_cmd_valid    = mq_cmd_cache_rf;
        rf_cmd_rptr_nxt = mq_cmd_cache_rf ? rf_cmd_rptr_r : rf_cmd_rptr_incr;
      end
      
      mq_cmd_pre_alloc:
      begin
        // No need to send out a RF transaction
        //
        rf_biu_push        = 1'b1;
        rf_cmd_rptr_nxt    = rf_cmd_rptr_incr;
      end
      
      default:
      begin
        rf_cmd_valid    =  1'b1;
      end
      endcase
      
      if (rf_cmd_valid)
      begin
        if (rf_cmd_accept)
        begin
          // Register that we sent out a read command and increment the cmd
          // read pointer
          //
          rf_biu_push     = 1'b1;
          rf_cmd_rptr_nxt = rf_cmd_rptr_incr;
        end
        else
        begin
          // Go wait until the command is accepted
          //
          rf_biu_state_nxt = RF_BIU_WAIT_ACCEPT;
        end
      end
    end
  end
  
  RF_BIU_WAIT_ACCEPT:
  begin
    rf_cmd_valid = 1'b1;
    
    if (rf_cmd_accept)
    begin
      rf_biu_push     = 1'b1;
      rf_cmd_rptr_nxt = rf_cmd_rptr_incr;
      rf_biu_state_nxt = RF_BIU_IDLE;
    end
  end
  
  default:
    ;
  endcase
end

// spyglass enable_block W193
//////////////////////////////////////////////////////////////////////////////
// Asynchronous logic: Initialization of the line buffer pointer
// 
//////////////////////////////////////////////////////////////////////////////
always @*
begin : lbuf_initial_PROC
  // We initialize the line buffer to point to the crtical word when:
  //
  // (1)  The very first refill command is sent out
  // (2)  We have outstanding refills and the the line buffer becomes available
  //
  lbuf_initial  =   ((rf_cmd_cnt_r == 2'b00) & rf_biu_push )       // (1)
                  | ((rf_cmd_cnt_r != 2'b00) & rf_lbuf_rd_last_r); // (2)
                  
end

//////////////////////////////////////////////////////////////////////////////
// Asynchronous logic: Counting the number of outstanding read commands 
// 
//////////////////////////////////////////////////////////////////////////////

// leda BTTF_D002 off
// leda B_3200 off
// LMD: Unequal length LHS and RHS in assignment LHS
// LJ:  One bit incrementor. Never overflows

// leda W484 off
// LMD: Possible loss of carry/borrow in addition/subtraction LHS
// LJ: Pointer arithmetic: incremented value will not overflow
assign rf_cmd_cnt_incr = rf_cmd_cnt_r + 1'b1;
assign rf_cmd_cnt_decr = rf_cmd_cnt_r - 1'b1;
assign rf_cmd_cnt_max  = rf_cmd_cnt_r == 2'b10;
// leda W484 on
// leda BTTF_D002 on
// leda B_3200 on


assign rf_biu_pop      = rf_lbuf_pop_r; 

always @*
begin : rf_cmd_cnt_nxt_PROC

  case ({rf_biu_push, rf_biu_pop})
  2'b10:  
  begin
    // Only push
    //
    rf_cmd_cnt_nxt = rf_cmd_cnt_incr;
  end
  
  2'b01:
  begin
    // Only pop
    //
    rf_cmd_cnt_nxt = rf_cmd_cnt_decr;
  end
  
  default:
  begin
    // No push, no pop. Or push and pop. In either case,  rf_cmd_cnt_r
    // remains the same
    //
// spyglass disable_block Ac_conv01
// SMD: Multiple synchronizers converging on mux
// SJ:  Signals are independent 
    rf_cmd_cnt_nxt = rf_cmd_cnt_r;
// spyglass enable_block Ac_conv01
  end
  endcase
end

//////////////////////////////////////////////////////////////////////////
//                                                                        
// Synchronous processes   
//                                                                        
//////////////////////////////////////////////////////////////////////////
assign rf_dc_state_next   = 
			rf_dc_state_nxt;
assign rf_dc_counter_next  =
			rf_dc_counter_nxt;
assign rf_dc_counter_done_next  =
			rf_dc_counter_done_nxt;
  
always @(posedge clk or posedge rst_a)
begin: rf_dc_state_sync_PROC
  if (rst_a == 1'b1)
  begin
    rf_dc_state_r        <= RF_IDLE;
    rf_dc_counter_r      <= {2{1'b0}};
    rf_dc_counter_done_r <= 1'b0;
  end
  else
  begin
    rf_dc_state_r        <= rf_dc_state_next;
    rf_dc_counter_r      <= rf_dc_counter_next;
    rf_dc_counter_done_r <= rf_dc_counter_done_next;
  end
end
assign  rf_biu_state_next  = 
			rf_biu_state_nxt;
assign    rf_cmd_rptr_next   = 
			 rf_cmd_rptr_nxt;
assign    rf_cmd_cnt_next    = 
			rf_cmd_cnt_nxt;
always @(posedge clk or posedge rst_a)
begin: rf_biu_state_sync_PROC
  if (rst_a == 1'b1)
  begin
    rf_biu_state_r <= RF_BIU_IDLE;
    rf_cmd_rptr_r  <= {`npuarc_MQ_PTR_DEPTH{1'b0}};
    rf_cmd_cnt_r   <= 2'b00;
  end
  else
  begin
    rf_biu_state_r <= rf_biu_state_next;
    rf_cmd_rptr_r  <= rf_cmd_rptr_next;
    rf_cmd_cnt_r   <= rf_cmd_cnt_next;
  end
end

always @(posedge clk or posedge rst_a)
begin: rf_lbuf_sync_PROC
  if (rst_a == 1'b1)
  begin
    rf_lbuf_pop_r     <= 1'b0;
    rf_lbuf_rd_last_r <= 1'b0;
  end
  else
  begin
    rf_lbuf_pop_r     <= rf_lbuf_pop;
    rf_lbuf_rd_last_r <= lbuf_rd_last;
  end
end



always @(posedge clk or posedge rst_a)
begin : rf_ack_ok_sync_PROC
  if (rst_a == 1'b1)
  begin
    rf_ack_ok_r <= 1'b0;
  end
  else
  begin
    rf_ack_ok_r <= rf_ack_ok;
  end
end


always @(posedge clk or posedge rst_a)
begin : rf_mq_scond_reg_PROC
  if (rst_a == 1'b1)
  begin
    rf_mq_scond_r <= 1'b0;
  end
  else if (rf_mq_scond_cg0)
  begin
    rf_mq_scond_r <= rf_mq_scond_nxt;
  end
end


endmodule // alb_dmp_rf

