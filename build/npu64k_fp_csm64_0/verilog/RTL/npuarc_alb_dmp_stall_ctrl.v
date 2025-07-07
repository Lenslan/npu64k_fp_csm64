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
//  ALB_DMP_STALL_CTRL               
//                   
//                   
//
// ===========================================================================
//
// Description:
//  This module implements the stalling and replay information that are generated 
//  during X1, X2 and CA stages of the pipeline respectively.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_stall_ctrl.vpp
//
// ===========================================================================
// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"



//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  rst: "rst_a", edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_dmp_stall_ctrl (
// leda NTL_CON13C off
// LMD: non driving port
// LJ: some bits of inputs vectors are not used
// spyglass disable_block W193
// SMD: empty statements
// SJ:  empty default statements kept and empty statements cause no problems
  ////////// General input signals ///////////////////////////////////////////
  //
  input                          clk,            // clock
  input                          rst_a,          // reset

  ////////// Interface to the X1/DC1 stage ///////////////////////////////
  //
  input                          x1_load_r,     
  input                          x1_store_r,     
  input                          dc1_dccm_stall,
  input                          dc1_dc_stall,
  input                          dtlb_update_pend_r,   // dtlb update pend
  
  ////////// Interface to the X2/DC2 stage ///////////////////////////////
  //
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input                          x2_store_r,    
// spyglass enable_block W240
  input                          x2_uop_inst_r,
  input [1:0]                    x2_mem_addr0_r,
  input                          x2_locked_r,
  input                          dc2_dccm_stall_r,
  input                          dc2_cft_stall_r,
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input [`npuarc_DMP_TARGET_RANGE]      dc2_target_r,
// spyglass enable_block W240
  output reg                     dc2_dc_uop_stall,
  
  ////////// Interface to the X3/DC3 stage ///////////////////////////////
  //
  input                          x3_pass,           // X3 passing on instt
  input                          x3_load_r,
  input                          x3_pref_r,
  input                          x3_store_r,     
  input                          x3_locked_r,
  input                          x3_uop_inst_r,     
  input [3:0]                    dc3_rmw_r,      
  input [`npuarc_DMP_TARGET_RANGE]      dc3_target_r,      // DC3 memory type  
  input [3:0]                    dc3_bank_sel_r,
  input                          dc3_dc_poisoned, 
  
  ////////// Interface to the CA stage ///////////////////////////////
  //
  input                          ca_load_r,
  input                          ca_store_r,
  input                          ca_locked_r,
  input                          ca_uop_inst_r,
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input                          ca_pass,                // CA pass
// spyglass enable_block W240
  input [3:0]                    dc4_rmw_r,      
  input [3:0]                    dc4_bank_sel_r,   
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input [`npuarc_DMP_TARGET_RANGE]      dc4_target_r,           // DC4 memory type 
// spyglass enable_block W240
  input [1:0]                    dc4_dt_bank_sel_r,      //

   
  ////////// Interface to the WA stage ///////////////////////////////
  //
  input                          wa_restart_r,
  input                          dc4_dccm_ecc_replay,
  input                          dc4_dc_ecc_replay_r,
  input                          dc4_wq_ovf_replay_r,
  input                          dc4_wq_order_replay_r,
  input                          wq_dc4_fwd_replay_r,
  input                          dc4_wq_skid_replay_r,
  input      [1:0]               dc4_dtlb_miss_r,
  input                          dc4_mispred,

  output reg                     wa_replay_r,
  
  ////////// Structural hazard (LQ) ///////////////////////////////////////////
  //
  input                          lq_empty_r,
  input                          lq_full_nxt,
  
  ////////// Structural hazard (WQ) ///////////////////////////////////////////
  //
  input                          dc4_wq_full,
  input                          dc4_wq_one_empty,
  input                          wq_dc_entry,
  input                          wq_scond_entry,
  input                          wq_non_dc_entry,
  input                          wq_retire,
  input                          wq_empty,
  input                          wq_more_than_one_empty,
  
  input                          dc3_dt_hit,
  input                          dc3_dt_miss,
  input                          dc4_dt_hit_r,
  input                          dc4_dt_miss_r,
  input                          dmu_empty,
  input                          mq_one_or_less_entry,
  input                          dmu_mq_full,
  input                          dmu_lsmq_full,
  input                          lsmq_two_empty,
  input                          dc4_lsmq_nomatch_replay,
  output reg                     dc4_mq_replay_r,
  output reg                     dc4_lsmq_replay_r,
  input                          rb_stall_r,  
  
  ////////// Outputs to the EXU ///////////////////////////////////////////
  //
  output                         dc1_stall,
  output                         dc2_stall,
  output                         dc4_stall,
  output                         dc4_replay          
// leda NTL_CON13C on
);


// Local Declarations

reg       dc1_atomic_stall;

reg       dc3_load_adv; 
reg       dc3_store_adv;
reg       dc3_ex_adv;
reg       dc3_mem_adv;
reg       dc3_store_dc_adv;
reg       dc3_store_dc_hit_adv;
reg       dc3_store_dccm_adv;


reg [2:0] dc4_state_nxt;
reg [2:0] dc4_state_r;
reg       dc4_state_cg0;

reg       dc4_dc_wq_stall_nxt;
reg       dc4_dc_wq_stall_r;

reg       dc4_stall_nxt;
reg       dc4_stall_r;

reg       dc4_replay_nxt;
reg       dc4_replay_r;

reg       dc4_ld_stall_replay;
reg       dc4_mq_replay_nxt;
reg       dc4_lsmq_replay_nxt;
reg       dc4_lsmq_stall_nxt;
reg       dc4_mq_stall_r;
reg       dc4_lsmq_stall_r;
reg       dc4_poisoned_replay_nxt;
reg       dc4_dc_miss;


reg       dc2_scond;
reg       dc3_scond;
reg       dc4_scond;
//////////////////////////////////////////////////////////////////////////////
// Asynchronous  logic for stalling loads in DC2 when there is a non-resolved
// scond in DC3/DC4/WQ
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc1_atomic_stall_PROC
  // Asserted when we have a SCOND in DC2
  //
  dc2_scond        = x2_store_r & x2_locked_r;

  // Asserted when we have a SCOND in DC3
  //
  dc3_scond        = x3_store_r & x3_locked_r;
  
  // Asserted when we have a SCOND in CA
  //
  dc4_scond        = ca_store_r & ca_locked_r;
  
  // Stall loads/stores in DC1 when there is a pending SCOND
  //
  dc1_atomic_stall =  (x1_load_r | x1_store_r)
                    & (  dc2_scond
                       | dc3_scond
                       | dc4_scond
                       | wq_scond_entry);
end

reg dc2_uop_target_dc;
//////////////////////////////////////////////////////////////////////////////
// Asynchronous  logic for dc2 uop stall
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc2_dc_uop_stall_PROC
  // Stall a uop store in DC2 when:
  // - WQ contains non cache entries
  //
  dc2_uop_target_dc =   x2_store_r
                      & x2_uop_inst_r
                      & (x2_mem_addr0_r[1:0] == 2'b00)  // Make sure that uop is 32 bit aligned
                      & (dc2_target_r == `npuarc_DMP_TARGET_DC);
  
  dc2_dc_uop_stall =   dc2_uop_target_dc
                    &  wq_non_dc_entry;
end

//////////////////////////////////////////////////////////////////////////////
// Asynchronous  logic for dc3 information
//
//////////////////////////////////////////////////////////////////////////////

reg dc3_bank_any_cross;
reg dc3_bank30_cross;
reg dc3_dc_wr_two;
reg dc3_dccm_wr_two;
reg dc3_wr_one;
reg dc3_wr_two;
//////////////////////////////////////////////////////////////////////////////
// Asynchronous  logic for dc3 information
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc3_wr_PROC
  // Unaligned write crosses
  //
  dc3_bank30_cross   = dc3_bank_sel_r[3] & dc3_bank_sel_r[0]; 
  
  // Unaligned write crosses
  //
  dc3_bank_any_cross =  (dc3_bank_sel_r[1] & dc3_bank_sel_r[0])
                      | (dc3_bank_sel_r[2] & dc3_bank_sel_r[1])
                      | (dc3_bank_sel_r[3] & dc3_bank_sel_r[2]);

  
  // 
  //
  dc3_dc_wr_two      =   (dc3_target_r == `npuarc_DMP_TARGET_DC)
                       & (| dc3_rmw_r)
                       & (dc3_bank_any_cross);

  //
  //
  dc3_dccm_wr_two    =   (dc3_target_r == `npuarc_DMP_TARGET_DCCM)
                       & (| dc3_rmw_r)
                       & (dc3_bank_any_cross);
  
  //
  //  
  dc3_wr_one = x3_store_r;

  dc3_wr_two =   x3_store_r 
               & (  dc3_bank30_cross
                  | dc3_dc_wr_two
                  | dc3_dccm_wr_two
                 )
                 ; 
end

always @*
begin : dc3_ld_st_ex_advances_PROC

  dc3_load_adv         = x3_load_r  & (~x3_store_r)  & x3_pass;
  dc3_store_adv        = x3_store_r & (~x3_load_r)   & x3_pass;
  dc3_ex_adv           = x3_load_r  & x3_store_r     & x3_pass;
  dc3_mem_adv          = (x3_load_r | x3_store_r)    & x3_pass;
end
  
always @*
begin : dc3_store_dc_hit_adv_PROC
  // Store advancing
  //
  dc3_store_dc_adv      =    x3_store_r  
                           & (~x3_load_r)  
                           & x3_pass;
  // Store hit or uop
  //
  dc3_store_dc_hit_adv =   dc3_store_dc_adv
                         & (    (~dc3_dt_miss)
                         
                              & (~dc4_dc_miss)
                              & dmu_empty
                            | (x3_uop_inst_r));
end

always @*
begin : dc3_store_dccm_adv_PROC
  // Store to DCCM 
  //
  dc3_store_dccm_adv =     x3_store_r  
                         & (~x3_load_r)  
                         & x3_pass 
                         & (~dc4_dc_miss)
                         & dmu_empty
                         ;
end

reg dc4_bank_any_cross;
reg dc4_bank30_cross;
reg dc4_dc_wr_two;
reg dc4_dccm_wr_two;
reg dc4_wr_two;

//////////////////////////////////////////////////////////////////////////////
// Asynchronous  logic for dc4 information
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc4_wr_PROC
  // Unaligned write crosses
  //
  dc4_bank30_cross   = dc4_bank_sel_r[3] & dc4_bank_sel_r[0]; 
  
  // Unaligned write crosses
  //
  dc4_bank_any_cross =  (dc4_bank_sel_r[1] & dc4_bank_sel_r[0])
                      | (dc4_bank_sel_r[2] & dc4_bank_sel_r[1])
                      | (dc4_bank_sel_r[3] & dc4_bank_sel_r[2]);

  
  // 
  //
  dc4_dc_wr_two      =   (dc4_target_r == `npuarc_DMP_TARGET_DC)
                       & (| dc4_rmw_r)
                       & (dc4_bank_any_cross);

  //
  //
  dc4_dccm_wr_two    =   (dc4_target_r == `npuarc_DMP_TARGET_DCCM)
                       & (| dc4_rmw_r)
                       & (dc4_bank_any_cross);
  
  //
  //
  dc4_wr_two =   ca_store_r 
               & (  dc4_bank30_cross
                  | dc4_dc_wr_two
                  | dc4_dccm_wr_two
                 )
                 ; 
end


//////////////////////////////////////////////////////////////////////////////
// @
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc4_dc_miss_PROC
  //
  //
  dc4_dc_miss  =  (ca_load_r | ca_store_r) 
                & (dc4_target_r == `npuarc_DMP_TARGET_DC)
                & dc4_dt_miss_r;
end

//////////////////////////////////////////////////////////////////////////////
// Asynchronous  logic for dc4 information
//
//////////////////////////////////////////////////////////////////////////////
reg dc4_ldst_stuck;
reg mq_more_than_one_replay;
reg dc4_dt_hit_replay;
reg dc4_dt_line_cross_replay;
reg dc4_dt_miss_replay;

always @*
begin : dc4_ld_stall_replay_PROC
  //
  //  
  dc4_ldst_stuck    = (ca_load_r | ca_store_r)
                    & (dc4_target_r == `npuarc_DMP_TARGET_DC)
                    & (~ca_pass)
                    & (~dc4_dc_wq_stall_r)
                    & (~wa_restart_r);
 
  
  // (1) Initiate a replay when dmu is having more than one entry and the stall is due to EXU
  // 
  mq_more_than_one_replay = ((~dc4_stall_r) & (~mq_one_or_less_entry)); 
 
 
  // (2) The LSMQ is full, the top of the MQ is matching with the DC4 instruction,
  //     there is no pending entries in the LSMQ, then replay the instruction in CA

     
  // (4) In case of a load hit stalled in CA due to WAW and there is a pending LQ or MQ entry then we replay the load
  //
  dc4_dt_hit_replay =  dc4_dt_hit_r 
                    & (  ca_load_r 
                       | (|dc4_rmw_r)
                      ) 
                    & (~dc4_stall_r) 
                    & (~lq_empty_r | ~dmu_empty);

  // (5) In case of DC4 instruction that crosses cache lines and LSMQ is full
  // 
  dc4_dt_line_cross_replay = dmu_lsmq_full                                       
                           & dc4_dt_hit_r 
                           & dc4_dt_miss_r;

  // (6) In case of ld/st miss in CA and wq/LQ having ext entries
  // 
  dc4_dt_miss_replay   = dc4_dt_miss_r
                       & wq_non_dc_entry
                       & (~lq_empty_r);

  // putting it all together;
  //
  dc4_ld_stall_replay  =  dc4_ldst_stuck
                       & (  mq_more_than_one_replay               // (1) 
                          | dc4_lsmq_nomatch_replay               // (2)
                          | dc4_dt_hit_replay                     // (4)
                          | dc4_dt_line_cross_replay              // (5)
                          | dc4_dt_miss_replay                    // (6)
                         );
end


//////////////////////////////////////////////////////////////////////////////
// Asynchronous  logic 
//
//////////////////////////////////////////////////////////////////////////////
reg wr_one_stall;
reg wr_two_stall;
always @*
begin: wr_stall_PROC
  // Deciding when to stall next cycle (DC4) because of WQ being full
  // This depends on how many entries we are writing, how many entries are
  // available
  //
  wr_one_stall =  dc4_wq_full & (~wq_retire);
  
  wr_two_stall =  dc4_wq_full
                | (dc4_wq_one_empty & (~wq_retire));
  
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          
///////////////////////////////////////////////////////////////////////////////
reg dc3_non_uop_store;
reg dc4_non_uop_store;

always @*
begin : non_uop_store_PROC
  dc3_non_uop_store = x3_store_r & (~x3_uop_inst_r);
  dc4_non_uop_store = ca_store_r & (~ca_uop_inst_r);
end 



//////////////////////////////////////////////////////////////////////////////
//  
//
//////////////////////////////////////////////////////////////////////////////
reg wq_dc_cu_entry;
always @*
begin : wq_entry_PROC
  wq_dc_cu_entry = wq_dc_entry
                 ;
end

//////////////////////////////////////////////////////////////////////////////
//  DC4 stall FSM
//
//////////////////////////////////////////////////////////////////////////////
parameter  DC4_DEFAULT                   = 3'b000;
parameter  DC4_WQ_FULL                   = 3'b001;
parameter  DC4_LQ_FULL                   = 3'b010;
parameter  DC4_LQ_FULL_AND_RAW_HAZARD    = 3'b011;
parameter  DC4_LSMQ_FULL                 = 3'b101;
always @*
begin : dc4_stall_replay_fsm_PROC

  // A load is replayed when it conflicts with more than one entry in the  
  // write queue
  //
  dc4_replay_nxt          = 1'b0;
  
  
  dc4_dc_wq_stall_nxt     = dc4_dc_wq_stall_r;
  dc4_stall_nxt           = dc4_stall_r;
  dc4_state_nxt           = dc4_state_r;
  dc4_state_cg0           = 1'b1; 
  
  dc4_mq_replay_nxt       = 1'b0;
  dc4_lsmq_replay_nxt     = 1'b0;
  dc4_lsmq_stall_nxt      = 1'b0;
  dc4_poisoned_replay_nxt = 1'b0;


  case (dc4_state_r)
  DC4_DEFAULT:
  begin
    dc4_state_cg0      = (x3_load_r | x3_store_r); 
    dc4_replay_nxt     = (dc3_mem_adv & dc3_dc_poisoned);


    case (dc3_target_r)
    `npuarc_DMP_TARGET_MEM,
    `npuarc_DMP_TARGET_ICCM:
    begin 
      case (1'b1)
      dc3_load_adv:
      begin

        if (lq_full_nxt)
        begin
          // When there is a non DC/DCCM loads in DC3, it can stall in CA
          // In case of DC: Tag squashing of dc1 and dc2 is  prevented
          // by skid buffers
          //
          dc4_stall_nxt  = 1'b1;
          
          // Note: can only stall the CA stage if the WQ doesn't have 
          // any entries targeting the internal memories. Otherwise a 
          // replay is necessary (next cycle)
          //
          dc4_state_nxt  = DC4_LQ_FULL;
        end
      end
      
      dc3_store_adv:
      begin
        // Stall next cycle when:
        // - The wq is full and we need two entries
        // - The wq is full and we need one entry and we are not retiring 
        //

        if (  (dc3_wr_two    & wr_two_stall)
            | ((~dc3_wr_two) & wr_one_stall)) 
        begin
          dc4_stall_nxt  = 1'b1;

          dc4_state_nxt  = DC4_WQ_FULL; 
        end
      end
      
      dc3_ex_adv:
      begin

        if (   (ca_load_r & ca_store_r)       // EX in CA
            | (~(wq_empty  & (~ca_store_r)))  // WQ not empty       
            | (~(lq_empty_r & (~ca_load_r)))  // LQ not empty  
           )
        begin
          // An EX instruction can not proceed
          //
          dc4_stall_nxt  = 1'b1;

          dc4_state_nxt  = DC4_LQ_FULL_AND_RAW_HAZARD;
        end
      end
    
      default:
        ;
      endcase  
    end
    

    `npuarc_DMP_TARGET_DC:
    begin
      // Replay conditions
      //
      dc4_mq_replay_nxt   =   dc3_mem_adv
                            & (~dc3_dc_poisoned)
                            & (~x3_pref_r) 
                            & dmu_mq_full
                            & (  dc3_dt_miss
                              ); 

      dc4_lsmq_replay_nxt =   dc3_mem_adv
                            & (~dc3_dc_poisoned)
                            & (~x3_pref_r) 
                            & (~dmu_mq_full)
                            & dmu_lsmq_full
                            & (  (dc3_dt_miss & dc3_dt_hit) // line crossing
                               | (x3_load_r   & x3_store_r) // EX
                              );

      dc4_lsmq_stall_nxt =   dc3_mem_adv
                            & (~dc3_dc_poisoned)
                            & (~x3_pref_r) 
                            & (~dmu_mq_full)
                            & dmu_lsmq_full
                            & (  dc3_dt_miss
                              )    
                            ; 
      
     

     dc4_poisoned_replay_nxt =   dc3_mem_adv 
                               & dc3_dc_poisoned;
      
     // Combining 
     //
     dc4_replay_nxt          =  dc4_mq_replay_nxt
                             | dc4_lsmq_replay_nxt
                             | dc4_poisoned_replay_nxt
                             ;

     dc4_stall_nxt           =  dc4_replay_nxt ? 1'b0 : dc4_lsmq_stall_nxt;


     dc4_state_nxt           = (dc4_stall_nxt & (~dc4_replay_nxt)) 
                             ? DC4_LSMQ_FULL
                             : dc4_state_r;

      // Check for a potential full WQ
      //
      if (  (dc3_store_dc_hit_adv  & dc3_wr_two    & wr_two_stall)
          | (dc3_store_dc_hit_adv  & (~dc3_wr_two) & wr_one_stall))
      begin
        // Stall next cycle when:
        // - The wq is full and we need two entries
        // - The wq is full and we need one entry and we are not retiring 
        //
        dc4_stall_nxt       = 1'b1;
        dc4_dc_wq_stall_nxt = 1'b1;
        dc4_state_nxt       = DC4_WQ_FULL; 
      end
      
    end

    `npuarc_DMP_TARGET_DCCM:
    begin
      // Check there is nothing in CA targeting DC and the DMU is empty
      //
      if (  (dc3_store_dccm_adv  & dc3_wr_two    & wr_two_stall)
          | (dc3_store_dccm_adv  & (~dc3_wr_two) & wr_one_stall))
      begin
        // Stall next cycle when:
        // - The wq is full and we need two entries
        // - The wq is full and we need one entry and we are not retiring 
        //
        dc4_stall_nxt       = 1'b1;
        dc4_dc_wq_stall_nxt = 1'b1;
        dc4_state_nxt       = DC4_WQ_FULL; 
      end
    end
    
    default:
      ;
    endcase  
  end

  DC4_WQ_FULL:
  begin
    // When there is a wa_restart, don't replay
    // 
    dc4_replay_nxt      =  (  (wq_dc_cu_entry & (~dc4_dc_wq_stall_r)) 
                            )
                          & (~wa_restart_r);  
    
    if (   (wq_retire & (~dc4_wr_two))
         | wq_more_than_one_empty
         | wa_restart_r
         | ((ca_load_r == 1'b0) & (ca_store_r == 1'b0))
        )
    begin
      dc4_dc_wq_stall_nxt = 1'b0;
      dc4_stall_nxt       = 1'b0;
      dc4_state_nxt       = DC4_DEFAULT;
    end
  end
 
  DC4_LQ_FULL:
  begin
    if (   !lq_full_nxt
         | wa_restart_r
         | ((ca_load_r == 1'b0) & (ca_store_r == 1'b0))
       )
    begin
      dc4_stall_nxt   = 1'b0;
      dc4_state_nxt   = DC4_DEFAULT;
    end
  end
  
  DC4_LQ_FULL_AND_RAW_HAZARD:
  begin
    // When there is a wa_restart, don't replay    
    //  
    dc4_replay_nxt  =   wq_dc_cu_entry
                     & (~wa_restart_r);
    
    if (  (  (wq_empty & (~ca_store_r) & (~lq_full_nxt))
           | (wq_empty & ca_store_r    & lq_empty_r))
           | wa_restart_r)
    begin
      dc4_stall_nxt   = 1'b0;
      dc4_state_nxt   = DC4_DEFAULT;
    end
  end

  DC4_LSMQ_FULL:
  begin
    //
    // Wait until the LSMQ is not full
    //
    if (  ((!dmu_lsmq_full) & (^dc4_dt_bank_sel_r))
        | (lsmq_two_empty & (&dc4_dt_bank_sel_r))    
        | wa_restart_r)    
    begin
      dc4_stall_nxt       = 1'b0;
      dc4_state_nxt       = DC4_DEFAULT;
    end
  end


  default:
    ;
  endcase  
end


// RB stall is a one cycle stall coming form result bus
//
assign dc4_stall = dc4_stall_r | rb_stall_r;

//////////////////////////////////////////////////////////////////////////////
// Synchronous process 
//
//////////////////////////////////////////////////////////////////////////////

// leda TEST_975 off
// LMD: Latch enabled by a clock affects data input of flipflops clocked by the trailing edge of the same clock
// LJ:
always @(posedge clk or posedge rst_a)
begin : dc4_stall_replay_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_stall_r           <= 1'b0;
    dc4_dc_wq_stall_r     <= 1'b0;
    dc4_replay_r          <= 1'b0;
    dc4_mq_replay_r       <= 1'b0;
    dc4_lsmq_replay_r     <= 1'b0;
    dc4_mq_stall_r        <= 1'b0;
    dc4_lsmq_stall_r      <= 1'b0;
  end
  else
  begin
    dc4_stall_r           <= dc4_stall_nxt;
    dc4_dc_wq_stall_r     <= dc4_dc_wq_stall_nxt;
    dc4_replay_r          <=  dc4_replay_nxt
                           | dc4_ld_stall_replay
                           ;
    dc4_mq_replay_r       <= dc4_mq_replay_nxt;
    dc4_lsmq_replay_r     <= dc4_lsmq_replay_nxt;
    dc4_mq_stall_r        <= 1'b0;
    dc4_lsmq_stall_r      <= dc4_lsmq_stall_nxt;
  end
end

always @(posedge clk or posedge rst_a)
begin : dc4_state_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_state_r       <= DC4_DEFAULT;
  end
  else if (dc4_state_cg0 == 1'b1)
  begin
    dc4_state_r      <= dc4_state_nxt;
  end  
end


// leda TEST_975 on

always @(posedge clk or posedge rst_a)
begin : wa_replay_reg_PROC
  if (rst_a == 1'b1)
  begin
    wa_replay_r <= 1'b0;
  end
  else
  begin
    wa_replay_r <= dc4_replay
                 & (ca_load_r | ca_store_r);   
  end
end

//////////////////////////////////////////////////////////////////////////////
// Output drivers 
//
//////////////////////////////////////////////////////////////////////////////

assign dc1_stall   = 1'b0
                  | dc1_dccm_stall
                  | dc1_dc_stall
                  | dtlb_update_pend_r
                  | dc1_atomic_stall
                  ;                   

assign dc2_stall =  1'b0 
                  | dc2_dccm_stall_r
                  | dc2_cft_stall_r
                  | dc2_dc_uop_stall
                  ;

assign dc4_replay =  dc4_replay_r
                   | dc4_dccm_ecc_replay
                   | dc4_dc_ecc_replay_r
                   | (dc4_wq_ovf_replay_r & (~dc4_dc_wq_stall_r))
                   | dc4_wq_skid_replay_r   
                   | dc4_wq_order_replay_r
                   | wq_dc4_fwd_replay_r      // unable to forward  
                   | (|dc4_dtlb_miss_r)
                   | dc4_mispred
                   ;
// spyglass enable_block W193

endmodule // alb_dmp_stall_ctrl

