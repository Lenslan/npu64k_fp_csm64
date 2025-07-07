// Library ARCv2HS-3.5.999999999
//------------------------------------------------------------------------------
//
// Copyright (C) 2010-2013 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary
// work of Synopsys, Inc., and is fully protected under copyright and
// trade secret laws. You may not view, use, disclose, copy, or distribute
// this file or any information contained herein except pursuant to a
// valid written license from Synopsys, Inc.
//
// Certain materials incorporated herein are copyright (C) 2010 - 2013, The
// University Court of the University of Edinburgh. All Rights Reserved.
//
// The entire notice above must be reproduced on all authorized copies.
//
// =============================================================================
//
// Description:
//
//  The fetch module implements the Fetch stage of the AlbaCore pipeline. This
//  is the first stage, responsible for issuing instruction fetch requests to
//  I-cache or ICCM, aligning the resulting instructions and pre-decoding
//  them before passing them on to the Execute stage.
//
//  The ICCM also allows accesses as data memory from the DMP
//
//
//  In general this design is a two cycle sram design although it allows
//  configuration of single clock sram.
//  The interfaces, however, are always single cycle clock driven.
// =============================================================================





//POST_PROCESS { prefix:"//D:", wire_prefix:"t_", edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }

//D: error_signal { name: "alb_bpu_edc_err" }
//D: error_signal { name: "alb_bpu_aux_edc_err" }
//D: error_signal { name: "alb_icache_edc_err" }
//D: error_signal { name: "alb_ifu_tosq_edc_err" }
//D: error_signal { name: "alb_ifu_fetch_if_edc_err" }
//D: error_signal { name: "alb_ifu_addr_dec_edc_err" }
//D: error_signal { name: "alb_ifu_data_mux_edc_err" }
//D: error_signal { name: "alb_fetch_buf_edc_err" }
//D: error_signal { name: "mrl_ifu_align_edc_err" }
//D: error_signal { name: "alb_ifu_brinfo_buf_edc_err" }
//D: error_signal { name: "itlb_err" }

module npuarc_alb_ifu (
  ////////// General input signals //////////////////////////////////////////////
  //
  input                        clk,    //core clock
// spyglass disable_block W240
// SMD: Signal declared but not used
// SJ:  not used in all configs
  input                        l1_clock_active,
// spyglass enable_block W240
  input                        rst_a,  //async. reset. can directly drive flops

//  output                       imem_clk,

  input                        dbg_cache_rst_disable_r,


  input   [36:0]     ic_tag_dout0,
  output  [36:0]     ic_tag_din0,
  output [36:0] ic_tag_wem0,    
  output  [12:6]      ic_tag_addr0,
  output                       ic_tag_cen0,
  output                       ic_tag_wen0,
  output                       ic_tag_way0_clk,
  input   [36:0]     ic_tag_dout1,
  output  [36:0]     ic_tag_din1,
  output [36:0] ic_tag_wem1,    
  output  [12:6]      ic_tag_addr1,
  output                       ic_tag_cen1,
  output                       ic_tag_wen1,
  output                       ic_tag_way1_clk,
  input   [36:0]     ic_tag_dout2,
  output  [36:0]     ic_tag_din2,
  output [36:0] ic_tag_wem2,    
  output  [12:6]      ic_tag_addr2,
  output                       ic_tag_cen2,
  output                       ic_tag_wen2,
  output                       ic_tag_way2_clk,
  input   [36:0]     ic_tag_dout3,
  output  [36:0]     ic_tag_din3,
  output [36:0] ic_tag_wem3,    
  output  [12:6]      ic_tag_addr3,
  output                       ic_tag_cen3,
  output                       ic_tag_wen3,
  output                       ic_tag_way3_clk,

  input   [78-1:0]     ic_data_dout0,
  output  [10:0]          ic_data_addr0,
  output  [78-1:0]     ic_data_din0,
  output                           ic_data_cen0,
  output                           ic_data_wen0,
  output  [10-1:0] ic_data_wem0,
  output                           ic_data_bank0_clk,
  input   [78-1:0]     ic_data_dout1,
  output  [10:0]          ic_data_addr1,
  output  [78-1:0]     ic_data_din1,
  output                           ic_data_cen1,
  output                           ic_data_wen1,
  output  [10-1:0] ic_data_wem1,
  output                           ic_data_bank1_clk,


  ///////////// MPU interface //////////////////////////////////////////
  //
  output [31:5]       ifetch_addr_mpu,
  input                        ifetch_viol,
// spyglass disable_block W240
// SMD: Signal declared but not used
// SJ:  not used in all configs
  input                        ifetch_unc,
// spyglass enable_block W240

// leda NTL_CON37 off
// LMD: Signal/Net must read from the input port 
// LJ: Signals are defined as part of the internal bus protocol, readibility
  ////////// Interface to BIU  //////////////////////////////////////////
  output                       ifu_ibus_cmd_valid,
  output                       ifu_ibus_cmd_prot,
  input                        ifu_ibus_cmd_accept,
  output  [39:0]       ifu_ibus_cmd_addr,
  output                       ifu_ibus_cmd_wrap,
  output                       ifu_ibus_cmd_cache,
  output  [3:0]                ifu_ibus_cmd_burst_size,
  input                        ifu_ibus_rd_valid,
  output                       ifu_ibus_rd_accept,
  input  [63:0]       ifu_ibus_rd_data,
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  not used in all config

// spyglass disable_block W240
// SMD: Signal declared but not used
// SJ:  not used in all configs
  input                        ifu_ibus_rd_last,
// leda NTL_CON13C on
// spyglass enable_block W240
  input                        ifu_ibus_err_rd,
// leda NTL_CON37 on


  // leda NTL_CON37 off
  // LMD: non driving port range
  // LJ:  DMI interface

  // leda NTL_CON37 on

// ECC fault status signals
  // leda NTL_CON37 off
  // LMD: Signal/Net must read from the input port in module 
  // LJ:  Ecc status signals
// spyglass disable_block W240
// SMD: Signal declared but not used
// SJ:  Ecc status signals
  input                       ecc_ifu_disable,
  input                       ecc_ifu_expn_disable,
// spyglass enable_block W240

  // leda NTL_CON37 on
  output                      ic_tag_ecc_err,
  output                      al_icache_ecc_err,
  input                       ic_tag_ecc_sbe_clr,
  output reg [3:0]            ic_tag_ecc_sbe_cnt,

  input                       ic_data_ecc_sbe_clr,
  output reg [3:0]            ic_data_ecc_sbe_cnt,

//   `if (0 == 1) // { 4
  output                      fs_ic_tag_bank0_ecc_sb_error_r,
  output                      fs_ic_tag_bank0_ecc_db_error_r,
  output [5:0]    fs_ic_tag_bank0_syndrome_r,
  output                      fs_ic_tag_bank1_ecc_sb_error_r,
  output                      fs_ic_tag_bank1_ecc_db_error_r,
  output [5:0]    fs_ic_tag_bank1_syndrome_r,
  output                      fs_ic_tag_bank2_ecc_sb_error_r,
  output                      fs_ic_tag_bank2_ecc_db_error_r,
  output [5:0]    fs_ic_tag_bank2_syndrome_r,
  output                      fs_ic_tag_bank3_ecc_sb_error_r,
  output                      fs_ic_tag_bank3_ecc_db_error_r,
  output [5:0]    fs_ic_tag_bank3_syndrome_r,
  output                      fs_ic_data_bank00_ecc_sb_error_r,
  output                      fs_ic_data_bank00_ecc_db_error_r,
  output [5:0]    fs_ic_data_bank00_syndrome_r,
  output                      fs_ic_data_bank01_ecc_sb_error_r,
  output                      fs_ic_data_bank01_ecc_db_error_r,
  output [5:0]    fs_ic_data_bank01_syndrome_r,
  output                      fs_ic_data_bank10_ecc_sb_error_r,
  output                      fs_ic_data_bank10_ecc_db_error_r,
  output [5:0]    fs_ic_data_bank10_syndrome_r,
  output                      fs_ic_data_bank11_ecc_sb_error_r,
  output                      fs_ic_data_bank11_ecc_db_error_r,
  output [5:0]    fs_ic_data_bank11_syndrome_r,
//   `endif // } 4


  output                      ifu_ivic,
  output                      ifu_ivil,


///////////////////////////
//AUX REGISTER INTERFACE //
///////////////////////////
//
///////////Common signals////////
input                    aux_write,
input                    aux_read,
input [31:0]      aux_wdata,
  // leda NTL_CON13C off
  // leda NTL_CON37 off
  // LMD: non driving port range
  // LJ:  aux interface
/////////Icache AUX register interface//////// 

input                    aux_ic_ren_r,       //  (X3) Aux Reg Enable
// spyglass disable_block W240
// SMD: Signal declared but not read
// SJ:  Signal is unused in some configs
input                    aux_ic_wen_r,       //  (WA) Aux Reg Enable
// spyglass enable_block W240
input     [3:0]          aux_ic_raddr_r,
// spyglass disable_block W240
// SMD: Signal declared but not read
// SJ:  Signal is unused in some configs
input     [3:0]          aux_ic_waddr_r,
// spyglass enable_block W240
output    [31:0]  ic_aux_rdata,       //  (X3) LR read data
output                   ic_aux_illegal,     //  (X3) SR/LR illegal
output                   ic_aux_k_rd,        //  (X3) need Kernel Read
output                   ic_aux_k_wr,        //  (X3) needs Kernel W perm
output                   ic_aux_unimpl,      //  (X3) Invalid Reg
output                   ic_aux_serial_sr,   //  (X3) SR group flush pipe
output                   ic_aux_strict_sr,   //  (X3) SR flush pipe

  // leda NTL_CON13C on
  // leda NTL_CON37 on
/////////BPU AUX register interface//////// 
input                    aux_bpu_ren_r,       //  (X3) Aux Reg Enable
input                    aux_bpu_wen_r,       //  (WA) Aux Reg Enable
input     [3:0]          aux_bpu_raddr_r,
input     [3:0]          aux_bpu_waddr_r,
output    [31:0]  bpu_aux_rdata,       //  (X3) LR read data
output                   bpu_aux_illegal,     //  (X3) SR/LR illegal
output                   bpu_aux_k_rd,        //  (X3) need Kernel Read
output                   bpu_aux_k_wr,        //  (X3) needs Kernel W perm
output                   bpu_aux_unimpl,      //  (X3) Invalid Reg
output                   bpu_aux_serial_sr,   //  (X3) SR group flush pipe
output                   bpu_aux_strict_sr,   //  (X3) SR flush pipe
///////////////////////////////////
// END OF AUX REGISTER INTERFACE //
///////////////////////////////////


  // Fetch Restart Interface/////////////////////////////////////////////////
  //
  // leda NTL_CON13C off
  // leda NTL_CON37 off
  // LMD: non driving port range
  // LJ:   Fetch Restart Interface
  input                       fch_restart,       // Global pipeline restart signal
  input                       fch_iprot_replay,  // replay iprot violation 
  input                       fch_restart_vec,
  input   [31:1]         fch_target,    // Tgt of Comt-stage pip restart
  input   [6:3]   fch_target_successor,  
// spyglass disable_block W240
// SMD: Signal declared but not used
// SJ:  not used in all configs
  input                       ar_user_mode_r,   // fetch in user mode
// spyglass enable_block W240
  // leda NTL_CON13C on
  // leda NTL_CON37 on
  // Instruction Issue Interface /////////////////////////////////////
  //

  output                      al_pass,         // Fetch pass valid insn to dec
  output     [31:0]    al_inst,         // the next instruction word
  output     [31:0]    al_limm,         // the aligned 32-bit immediate

  input                       da_holdup,        // stall  from Dec stage


  output                      al_exception,     //  indicates current instruction raised exception
  output [2:0]   al_excpn_type,    //  type of exception
  output [6:0]   al_excpn_info,    //  execute perms for current instruction 
  output                      al_ifu_err_nxtpg,
  output                      al_iprot_viol,    // spec. ifetch prot violation (replay)



  output                      al_is_predicted,  // 1 -> current instruction is a predicted
                                                // branch, which may predicted taken or not-taken
                                                // 0 -> current instruction has no assosiated prediction
  output                      al_prediction,      // 1 -> Predicts the branch is taken
                                                 // 0 -> No branch or predicts branch no taken

  output [31:1]          al_predicted_bta,  // The predicted BTA of the current current instruction

  output [2:0]     al_prediction_type, // Type of prediction

  output                      al_error_branch,   // 1 -> stale branch was detected and current instrn is invalid
                                                 //      Requires misprediction from current PC and a commit
                                                 //      error response
  output [5:0]     al_branch_info,    // Tag of info needed on mispredition or branch-commit to
                                                 // update the predictor state

  output                      al_with_dslot,     // 1 -> delay slot


  /////////////////////////////////////////////////////////////////////////////
  // Mispredict Interface
  //
  input                       mpd_mispred,       // 1 -> indicates a speculative mispredication has
                                                  //        been detected
  input                       mpd_direction,     // Was the branch taken or not taken
                                                  // 1-> taken, 0-> not taken
  input                       mpd_error_branch,  // Error predicton, need to delete this predition from branch
                                                  // cache; also deletes fragged instructions
  input                       mpd_is_predicted,  // Was a prediction made for this branch when it was
                                                  // issued?
  input                       mpd_mispred_outcome,  // Was the branch outcome incorrectly predicted

  input                       mpd_mispred_bta,   // Was the bta mispredicted

  input [5:0]      mpd_branch_info,   // Tag of branch info, used to update the preditor state
                                                  // during mispredict actions

  input [2:0]      mpd_type,              
  // type of the mispredicted branch, same meaning as wa_type, but supplied with mispredict        
      
  input [31:1]           mpd_seq_next_pc,       
  // PC of the instruction sequentially following the branch 
  // and potential delay slot
  // same meaning as wa_seq_next_pc, but supplied with mispredict

  input                       mpd_dslot,  
  // Does the mispredicted branch have a delay slot?
  // leda NTL_CON37 off
  // LMD: non driving port range
  // LJ:  Not all bits of addr used
  input [31:1]           mpd_pc,            // Similar to wa_pc: PC of the branch instruction
  // leda NTL_CON37 on
  input                       mpd_tail_pc_3,      // Similar to wa_tail_pc_3:
                                                  // Bit 3 of PC-2 of the instruction following branch
                                                  // or delay slot, indicating the fetch block where the
                                                  // tail of the instruction is located

  input [1:0]        mpd_commit_size,    // Similar to wa_commit_size: Size of branch

  input                       mpd_secondary,
       // Similar to wa_secondary: Indicates if this instruction can be a secondary branch

  input                       mpd_early,  
      // indicates if a mispredict is early (in the X2 stage) or late (in the WB stage).
      // 0: mispredict is late
      // 1: mispredict is early

  ///////////////////////////////////////////////////////////////////////////////////////
  // Branch Commit info from execution unit
  //

  input                       wa_pass,           // Request to commit a branch to IFU

  input [2:0]      wa_type,           // Type of committing branch

  input                       wa_secondary,
  // Indicates if this instruction can be a secondary branch

  input [31:1]           wa_pc,             // PC of the branch that is committing

  input                       wa_tail_pc_3,      // Bit 3 of PC-2 of the instruction following branch
                                                  // or delay slot, indicating the fetch block where the
                                                  // tail of the instruction is located
  input                       wa_dslot,          // Does the committed branch instrution have a delay slot

  input [31:1]           wa_target,         // BTA of a branch/jump that is commiting

  input [1:0]        wa_commit_size,    // Size of committing branch (1,2,3 or 4)

  input [5:0]      wa_branch_info,    // Tag of branch for updating preditor state

  input                       wa_direction,      // Was the branch taken? 1-> taken, 0-> not-taken

  input                       wa_error_branch,   // Prediction error: used to delete the prediction 
                                                  // from branch cache
  input                       wa_is_predicted,   // Was a prediction made for this branch

  input                       wa_mispred_outcome, // Was the outcome mispredicted

  input                       wa_commit_mispred_bta, // Was the BTA mispredicted

  // interface to branch cache RAMs
  output [67:0] bc_din0,
  output [11:4]  bc_addr0,
  output                     bc_me0,
  output                     bc_we0,
  output [67:0] bc_wem0,
  input  [67:0] bc_dout0,

  // interface to prediction table RAMs
  output [7:0] gs_din0,
  output [13:4]      gs_addr0,
  output                     gs_me0,
  output                     gs_we0,
  output [7:0] gs_wem0,
  input  [7:0] gs_dout0,
  output                     bc_ram0_clk,
  output                     pt_ram0_clk,
  output                     bc_ram0_clk_en,
  output                     pt_ram0_clk_en,

  output [67:0] bc_din1,
  output [11:4]  bc_addr1,
  output                     bc_me1,
  output                     bc_we1,
  output [67:0] bc_wem1,
  input  [67:0] bc_dout1,

  output [7:0] gs_din1,
  output [13:4]      gs_addr1,
  output                     gs_me1,
  output                     gs_we1,
  output [7:0] gs_wem1,
  input  [7:0] gs_dout1,
  output                     bc_ram1_clk,
  output                     pt_ram1_clk,
  output                     bc_ram1_clk_en,
  output                     pt_ram1_clk_en,


  /////////////////////////////////////////////////////////////////////////////
  // Performance monitor signals
  output                  ifu_icache_miss_r,
  output                  ifu_icache_hit_r,
  output                  ifu_icache_disabled,
  output                  ifu_way_pred_miss_r,
  output                  ifu_issue_stall_r,
  
  output                  ifu_bit_error_r,


  // Access type: user/kernel mode, pid shared bit (common to all req ports)
  input                         mmu_en_r,       // Enable TLB lookups
  input                         mpu_en_r,
  input                         mmu_ready,      // MMU initialized
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  not used in all config
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs 
  input                         mmu_clock_req_r,// MMU clock request
// spyglass enable_block W240
// leda NTL_CON13C on  
  input                         mmu_cmd_active,
  input                         shared_en_r,    // Shared lib enable (PID)
  input  [63:0]         sasid_r,        // Current pid slib membership
  input  [7:0]  asid_r,         // Current pid.asid
                
  input                         db_active_r,

  ///////////////////////////////////////////////////////////////////////////
  ///// Lookup Interface (to itlb) //////////////////////////////////////////
// itlb update request (on miss)
  output                        ifu_clk2_en,
  output                        itlb_update_req,
  output [30:12]       itlb_update_req_vpn,

// jtlb response to itlb update request
  input                         jrsp_itlb_update_nxt, 
  input                         jrsp_itlb_update, 
  input                         jrsp_itlb_update_hit,
  input                         jrsp_itlb_multi_hit,
  input                         jrsp_itlb_tlb_err,

// insert / delete / Inval (aux) operations from jtlb
  input  [3:0]          jtlb_itlb_cmd_r,   // command from jtlb (aux)
  input  [1:0]    jtlb_itlb_index_r, // Aux addr for read/write
  
// Interface to read utlb entries
//
  output                        itlb_rd_val,   // rd data reg in jtlb
  output [69:0]    itlb_rd_data,  // LR read data (entry)

  ////////// Shared bus to uTLBs ////////////////////////////////////////////
  //
  // Entry data for update from jtlb; also used for lookups and write by jtlb
  input  [69:0]    jtlb_update_data,



  /////////////////////////////////////////////////////////////////////////////
  // Halt interface
  input                   fch_stop_r,    // halt request (effective with fch_start=1)
  output                  ifu_idle_r     // IFU acknowleding that it is idle

);



reg fch_restart_int;
reg fch_restart_int_vec;
reg [31:1] fch_target_int;
reg [6:3] fch_target_int_successor;  


wire cycle2_r;

  wire va_in_transl_range;

wire mmu_restart;
wire ifu_active;
assign mmu_restart = mmu_cmd_active & ifu_active;

//reg                   fch_restart_r;
reg                   fch_restart_vec_r;
reg [31:1]       fch_target_r;
  // leda NTL_CON32 off
  // LMD: Change on net has no effect on any of the outputs
  // LJ:  Not all bits of bus used
reg [6:3] fch_target_successor_r;  
  // leda NTL_CON32 on


always @(posedge clk or posedge rst_a) 
begin: mmu_restart_PROC
  if (rst_a == 1'b1) 
  begin
    fch_restart_vec_r <= 1'b0;
    fch_target_r <= {31{1'b0}};
    fch_target_successor_r <= 4'd0;
  end
  else if (fch_restart)
  begin
    fch_restart_vec_r <= fch_restart_vec;
    fch_target_r <= fch_target;
    fch_target_successor_r <= fch_target_successor;
  end
end // block: mmu_restart_PROC

//reg extend_restart;
always @*
begin: extend_restart_PROC
  if (mmu_restart & (~fch_restart))
  begin
    fch_restart_int = 1'b1;
    fch_restart_int_vec = fch_restart_vec_r;
    fch_target_int = fch_target_r;
    fch_target_int_successor = fch_target_successor_r;  
  end
  else
  begin
    fch_restart_int = fch_restart;
    fch_restart_int_vec = fch_restart_vec;
    fch_target_int = fch_target;
    fch_target_int_successor = fch_target_successor;  
  end
end // always @ *

wire fetch_icache_way_sec;
wire fetch_icache_is_restart;
wire icache_tag_par_mode_r;
wire al_is_predicted_int;

// BTA Miss handling
wire bta_miss;
//wire [2:0] bta_offset;
wire [2:0] bta_offset;
wire [31:1] bta_miss_disp;
wire bta_miss_disp_vld;

//restart qualification
wire exu_fetch_restart;
assign exu_fetch_restart = (fch_restart_int && (!fch_stop_r)) //single pulse restart from exu
                         ;
wire exu_hlt_restart;
assign exu_hlt_restart  = (fch_restart_int && fch_stop_r)     //single pulse stop from exu
                        ;
wire bpu_fetch_restart_org; //original restart from bpu
wire bpu_fetch_restart;     //qualified by non-stop state
wire restart_state;         //a period from exu restart to bpu restart
wire restart_state_r;       //the period before bpu restart arrives


`ifndef TTVTOC // { 1
`endif       // } 1

//internal clock
wire clk2; //two cycle clock
wire clk2_en; //identify which phase is the second half of clk2, sync with clk
wire clk2_en_r; //from clk_ctrl

//halt/run signals
wire hlt_stall;
wire ifu_hlt_rdy;
wire fetch_mem_busy;


wire ic_hlt_ready;
wire ic_mem_busy;
wire ic_aux_busy;
 
wire itlb_active;

assign ifu_hlt_rdy = 
  ic_hlt_ready &
  (~itlb_active) &
  1'b1;

assign fetch_mem_busy = 
  ic_mem_busy |
  1'b0;


//prediction unit
////
// signals to direct the fetch request to either ICCM0, ICCM1, Icache or IFQUEUE
  wire fetch_iccm0;
  assign fetch_iccm0 = 1'b0;

  wire fetch_iccm1;
  assign fetch_iccm1 = 1'b0;

   wire fetch_icache;

wire fetch_req;
wire fetch_rdy;
wire [31:1] fetch_addr0;
wire [5:4] fetch_addr1_offset;
wire [2:0] fetch_bank_ctl;
wire fetch_way_force;
wire [2-1:0] fetch_way_ptr;
wire fetch_seq;
wire fetch_way_sec;
wire fetch_way_req;

//sigals to BPU for way prediction
wire [2-1:0] way_for_pred;
wire way_for_pred_vld;
wire way_sec_for_pred;
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  some bits of pc are unused
wire [31:1] way_for_pred_pc;
// leda NTL_CON13A on
wire wr_way;                 // Write control for way prediction
wire [1:0] way_in; // Predicted way of the fetch
wire way_in_sec; // is the way for a secondary branch?
wire [11:4] way_index; // Branch cache index for the way
wire                    way_bank; // Bank for the way

wire [1:0] way_pred; // Predicted way of the fetch
//wire [1:0] way_pred_out; // Predicted way of the fetch; fast version
//wire way_valid;            // way prediction is valid             
wire way_valid_out;        // way prediction is valid; fast version             
wire way_valid_detect;     // way prediction is valid for mpd case            
wire way_sec;              // is the way pred for a secondary branch?

wire way_seq;            // sequential way; turn off tag check            
wire way_req;            // request to provide way prediction when way_valid=0

  assign                wr_way = way_for_pred_vld;
  assign                way_in = way_for_pred;
  assign                way_in_sec = way_sec_for_pred;
  assign                way_index = way_for_pred_pc[11:4];
  assign                way_bank = way_for_pred_pc[3];


wire brinfo_vld;
wire brinfo_is_br;
wire brinfo_is_br_last;
wire [31:1] brinfo_bta;
wire [4-1:1] brinfo_br_offset;
wire [42:0] brinfo_pkt;

//after fetch_pd_if isolation
wire fetch_iccm0_int;
wire fetch_iccm1_int;
wire [2-1:0] fetch_iccm0_bank_int;
wire [2-1:0] fetch_iccm1_bank_int;
wire fetch_icache_int;
wire [31:1] fetch_addr0_int;
wire [5:4] fetch_addr1_offset_int;
wire [2+1:0] fetch_bank_ctl_int;
wire fetch_is_restart_int;
wire fetch_rdy_int;
wire refetch_int;
wire fetch_vec_int;
wire fetch_way_force_int;
wire [2-1:0] fetch_way_ptr_int;
wire fetch_seq_int;
wire fetch_way_sec_int;
wire fetch_way_req_int;
wire fetch_way_bank_id_int;
wire fetch_way_tail_int;

wire brinfo_is_br_int;
wire brinfo_is_restart_int;
wire brinfo_kill_2nd_int;
wire brinfo_is_br_last_int;
wire [31:1] brinfo_bta_int;
wire [4-1:1] brinfo_br_offset_int;
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  not used signal range
wire [42:0] brinfo_pkt_int;
// leda NTL_CON13A on
wire [2+1:0] brinfo_bank_ctl_int;
wire brinfo_bta_miss_int;
//wire [2:0] brinfo_bta_miss_offset_int;
wire [2:0] brinfo_bta_miss_offset_int;

//brinfo output from fetch address decoder
wire brinfo_id_vld;
wire brinfo_id_is_restart;
wire brinfo_id_kill_2nd;
wire brinfo_id_is_br;
wire brinfo_id_is_br_last;
wire [31:1] brinfo_id_bta;
wire [2+1:0] brinfo_id_bank_ctl;
wire [4-1:1] brinfo_id_br_offset;
wire [42:0] brinfo_id_pkt;
wire brinfo_id_bta_miss;
//wire [2:0] brinfo_id_bta_miss_offset;
wire [2:0] brinfo_id_bta_miss_offset;
wire fetch_data_mux_out_take; //ready signal to ID fifo

//fetch address decoder to icache
wire [31:1] fetch_icache_addr0;
wire [31:1] fetch_icache_addr1;
wire fetch_icache_req;
wire fetch_icache_vec;
wire fetch_icache_way_force;
wire [2-1:0] fetch_icache_way_ptr;

wire fetch_icache_seq;
wire fetch_icache_way_req;
wire fetch_icache_way_bank_id;
wire fetch_icache_way_tail;
wire  fetch_icache_ecc_enable;

//wire  ic_tag_ecc_err_int;
wire  fetch_data2buf_ecc_enable;
wire  buf_data_out_ecc_enable0;
wire  buf_data_out_ecc_enable1;
wire fetch_icache_ack;
wire [156-1:0] fetch_icache_data;
wire [2-1:0] fetch_icache_data_vld;
wire fetch_icache_data_err;
wire [2-1:0] fetch_icache_data_way;
wire fetch_icache_data_rdy;


//fetch decoder to iccm0
wire [2-1:0] fetch_iccm0_kill;
assign fetch_iccm0_kill = 2'b0;

//fetch decoder to iccm1
wire [2-1:0] fetch_iccm1_kill;
assign fetch_iccm1_kill = {2{1'b0}};

//fetch decoder output to buffer
wire [156-1:0] fetch_data2buf;
wire [2-1:0] fetch_data2buf_vld;
//
wire [2-1:0] fetch_data2buf_vld_qual;
assign fetch_data2buf_vld_qual = fetch_data2buf_vld & {2{!hlt_stall}};
wire [4:0] fetch_data2buf_err; //bit1-iccm addr error, bit0-Icache bus error 
wire [2:0] fetch_data2buf_experm; //
wire fetch_data2buf_rdy;
wire [2-1:0] fetch_data2buf_way;

//
wire fetch_data2buf_rdy_qual;
assign fetch_data2buf_rdy_qual = fetch_data2buf_rdy | hlt_stall | restart_state;
wire brinfo_data2buf_restart;
//wire buf_data_out_restart0;
//wire buf_data_out_restart1;
wire [2-1:0] brinfo_data2buf_br;
wire [2-1:0] brinfo_data2buf_first_word;
wire [4-1:1] brinfo_data2buf_br_offset;
wire [42:0] brinfo_data2buf_pkt;
wire brinfo_data2buf_br_last;
wire [2-1:0] brinfo_data2buf_bank_ctl;
wire [1:0] brinfo_data2buf_bank_cnt;

wire [2-1:0] bta2buf_vld;
wire [1:0] bta2buf_bank_cnt;
wire [31:1] bta2buf_bta;
wire bta_tail_stall;
wire bta2buf_rdy;

//buffer outputs
wire [156/2-1:0] buf_data_out_w0;
wire buf_data_out_vld0;
wire [4:0] buf_data_out_err0;
wire [2:0]                 buf_data_out_experm0;
wire [2-1:0] buf_data_out_way0;
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  unused signal range
wire [4-2:1] buf_data_out_br_offset0;
// leda NTL_CON13A on
wire [42:0] buf_data_out_pkt0;
wire [31:1] buf_data_out_bta0;
wire buf_data_out_first_word0;
wire [2-1:0] buf_data_out_bank_ctl0;
wire [156/2-1:0] buf_data_out_w1;
wire buf_data_out_vld1;
wire [4:0] buf_data_out_err1;
wire [2:0]                 buf_data_out_experm1;
wire [2-1:0] buf_data_out_way1;
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  unused signal range
wire [4-2:1] buf_data_out_br_offset1;
// leda NTL_CON13A on
wire [42:0] buf_data_out_pkt1;
wire [31:1] buf_data_out_bta1;
wire buf_data_out_first_word1;
wire [2-1:0] buf_data_out_bank_ctl1;

//alignment output
wire buf_taken;
wire buf_taken_single;
wire [1:0] buf_taken_count_nxt;

///////////////////////////////////////////////////////////////////////////////
// Fetch Protection
//
wire [31:5]   ifetch_chk_addr;

wire   ic_mpu_viol;                       // @ ic output

assign ifetch_addr_mpu = ifetch_chk_addr; // to mpu
wire   ifetch_mpu_viol;
assign ifetch_mpu_viol = ifetch_viol;     // @ ic req_addr_r (from mpu)



wire            ifetch_iprot_viol;  // @ ic req_addr_r
wire            ic_iprot_viol;      // @ ic output
wire            dmux_iprot_viol;    // @ data mux output
wire            dbuf_iprot_viol0;   // @ data buf output
wire            dbuf_iprot_viol1;   // @ data buf output

// Lookup port
wire                           itlb_lkup0_valid;
// leda NTL_CON13A off
// LMD: non driving internal net Range
// LJ:  Itlb interface
wire   [31:0]     itlb_lkup0_vaddr;
// leda NTL_CON13A on

wire                           itlb_lkup0_stall_nxt;

reg                            jrsp_itlb_update2_r;

// stall for one clk2 cycle after new entry written (2cyc path)
always @(posedge clk or posedge rst_a) 
begin: jrsp_itlb_update2_PROC
  if (rst_a == 1'b1) begin
    jrsp_itlb_update2_r  <= 1'b0;
  end
  else 
  begin
    jrsp_itlb_update2_r  <= jrsp_itlb_update_nxt || jrsp_itlb_update;
  end
end

wire                           itlb_rslt0_valid;
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  unused signal range
wire                           itlb_rslt0_valid2; // extended to clk2
wire       [11:10]     itlb_rslt0_user_attr;
wire                           itlb_rslt0_wr_thru;
wire       [6:1]   itlb_rslt0_perm;
wire                           itlb_rslt0_cached;
   
// leda NTL_CON13A on

wire                           itlb_rslt0_match;
wire                           itlb_rslt0_multiple_match;
wire                           itlb_rslt0_ecc_err;

wire       [39:0]      itlb_rslt0_paddr;
wire       [39:0]      itlb_rslt0_paddr_r;

wire                           itlb_ovrlp_excpn;
wire                           itlb_miss_excpn;
wire                           itlb_ecc_err_excpn;
wire [2:0]   itlb_exec_perm;

reg                            itlb_ovrlp_excpn_nxt;
reg                            itlb_miss_excpn_nxt;
reg                            itlb_ecc_err_excpn_nxt;
reg [2:0]    itlb_exec_perm_nxt; 

wire                           itlb_fail_nxt;

reg                            itlb_ovrlp_excpn_r;
reg                            itlb_miss_excpn_r;
reg                            itlb_ecc_err_excpn_r;
reg [2:0]    itlb_exec_perm_r;
reg                            itlb_fail_r; // unsuccessful translation

wire                           itlb_ovrlp_excpn_r_r;
wire                           itlb_miss_excpn_r_r;
wire                           itlb_ecc_err_excpn_r_r;
wire [2:0]   itlb_exec_perm_r_r;


always @(*)
begin: itlb_excpns_nxt_PROC
  begin
    if (restart_state) begin
      itlb_miss_excpn_nxt  = 1'b0;
      itlb_ecc_err_excpn_nxt = 1'b0;
      itlb_ovrlp_excpn_nxt = 1'b0;
      itlb_exec_perm_nxt   = 3'b011;
    end
    else if (itlb_rslt0_valid) begin
      itlb_miss_excpn_nxt  = ~itlb_rslt0_match;
      itlb_ecc_err_excpn_nxt = itlb_rslt0_ecc_err;
      itlb_ovrlp_excpn_nxt = itlb_rslt0_match & itlb_rslt0_multiple_match;

      itlb_exec_perm_nxt   = {va_in_transl_range,
                             ({2{(~itlb_rslt0_match)}})
                           | ({itlb_rslt0_perm[4]
                             , itlb_rslt0_perm[1]})
                             }
                           ;
    end
    else begin
      itlb_miss_excpn_nxt  = itlb_miss_excpn_r;
      itlb_ecc_err_excpn_nxt = itlb_ecc_err_excpn_r;
      itlb_ovrlp_excpn_nxt = itlb_ovrlp_excpn_r;
      itlb_exec_perm_nxt   = itlb_exec_perm_r;
    end
  end
end

assign itlb_fail_nxt = (!(|itlb_exec_perm_nxt[1:0])) // both x perm low
                        | itlb_miss_excpn_nxt 
                        | itlb_ovrlp_excpn_nxt
                        | itlb_ecc_err_excpn_nxt;


// hold itlb results for clk2 based sampling by ifq/icache/iccm
//
always @(posedge clk or posedge rst_a) 
begin: itlb_excpns_PROC
  if (rst_a == 1'b1) begin
    itlb_miss_excpn_r    <= 1'b0;
    itlb_ecc_err_excpn_r <= 1'b0;
    itlb_ovrlp_excpn_r   <= 1'b0;
    itlb_exec_perm_r     <= 3'b0;
    itlb_fail_r          <= 1'b0;
  end
  else 
  begin
    itlb_miss_excpn_r    <= itlb_miss_excpn_nxt;
    itlb_ecc_err_excpn_r <= itlb_ecc_err_excpn_nxt;
    itlb_ovrlp_excpn_r   <= itlb_ovrlp_excpn_nxt;
    itlb_exec_perm_r     <= itlb_exec_perm_nxt;
    itlb_fail_r          <= itlb_rslt0_valid ? itlb_fail_nxt : itlb_fail_r;
  end
end

// alb_2cyc_checker #(.WIDTH(1)) xx_2cyc_checker 
//    (.data_in  ( xx_2cyc ),
//     .data_out ( xx ),
//     .clk (clk));

// alb_2cyc_checker #(.WIDTH(1)) itlb_miss_excpn_2cyc_checker 
//    (.data_in  ( itlb_miss_excpn_2cyc ),
//     .data_out ( itlb_miss_excpn ),
//     .clk (clk));

//  `if (1 == 1)
assign ifu_clk2_en = clk2_en;

// itlb exceptions associated with icache inst data presented to 
// ifu_data_mux/fetch_data_buffer
assign itlb_miss_excpn    = icache_tag_par_mode_r ? itlb_miss_excpn_r    : itlb_miss_excpn_r_r;
assign itlb_ecc_err_excpn = icache_tag_par_mode_r ? itlb_ecc_err_excpn_r : itlb_ecc_err_excpn_r_r;
assign itlb_ovrlp_excpn   = icache_tag_par_mode_r ? itlb_ovrlp_excpn_r   : itlb_ovrlp_excpn_r_r;
assign itlb_exec_perm     = icache_tag_par_mode_r ? itlb_exec_perm_r     : itlb_exec_perm_r_r;






// For ICCM's hold itlb lookup result until output data accepted
//
wire   rslt0_accept;

assign rslt0_accept     = restart_state  
                        | (clk2_en 
                        );



//====================================================================
//==================== pipe stage  : prediction unit
//==================== upper stage : none but get feedback from other stages
//==================== lower stage : request FIFO 
//====================================================================

// connections for basic BPU functionality
wire [21:0] mpd_branch_info_full;
wire [21:0] wa_branch_info_full_pre;
wire [21:0] wa_branch_info_full;
wire [52:0] mpd_branch_info_full_new;
wire [52:0] wa_branch_info_full_new;
wire mem_req;
wire mem_busy;
wire unaligned;
wire kill_2nd;
wire fetch0;
wire fetch1;
wire [31:1] fa0;
wire [6-1:4] fa1_diff;
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  unused signal range
wire [70:0] branch_info_fb;
// leda NTL_CON13A on
wire [31:1]         top_of_stack;
wire                     write_tosq_r;

wire taken;
//wire [2:0] offset;
wire [2:0] offset;
wire [31:1] bta_pred; // the BTA of the predicted taken branch
wire                    bta_valid;
wire fetch_tail;

// BPU aux registers

wire start_prediction;
wire [2:0] bpu_ctrl;       // Control dynamic BPU, single cycle timing path
wire [2:0] bpu_ctrl_2cyc;  // Control dynamic BPU, 2-cycle timing path
wire   bpu_flush; // flush and initialize branch predictor
wire   bpu_flush_ack; //to connect to bpu
wire   bpu_init_r; // BPU is busy with init or flush

wire [31:1] mpd_tos;
wire [31:1] wa_tos;

//
reg exu_restart_state_r;
reg exu_restart_state_next;
always @(posedge clk or posedge rst_a) 
begin: restart_reg_PROC
  if (rst_a == 1'b1) begin
    exu_restart_state_r <= 1'b0;
  end
  else begin
    exu_restart_state_r <= exu_restart_state_next;
  end
end

always@ (*)
begin: restart_logic_PROC
  exu_restart_state_next = exu_restart_state_r;
  if (bpu_fetch_restart || exu_hlt_restart) 
  begin
    exu_restart_state_next = 1'b0;
  end
  else if (exu_fetch_restart) 
  begin
    exu_restart_state_next = 1'b1;
  end
end

assign restart_state = 
                     exu_fetch_restart | exu_restart_state_r;
assign restart_state_r = exu_restart_state_r;


assign fetch_req = mem_req;
assign mem_busy = ~(fetch_rdy||restart_state) || (~clk2_en) 
                || ic_aux_busy
                 ;
assign fetch_addr0 = fa0;
// no offset when its 32 block size and the ifu width is 128
assign fetch_addr1_offset = fa1_diff[5:4];

assign fetch_bank_ctl = {unaligned, fetch1, fetch0};
assign fetch_way_force = way_valid_out;
assign fetch_way_ptr = way_pred;
assign fetch_seq = way_seq;
assign fetch_way_sec = way_sec;
assign fetch_way_req = way_req;

assign brinfo_br_offset = offset;
assign brinfo_is_br = taken; 
assign brinfo_is_br_last = ~fetch_tail; 
assign brinfo_bta[31:1] = bta_pred;

assign brinfo_pkt[42:0] = {{3{1'b0}},branch_info_fb[70-31:0]};
wire                           brinfo_bta_miss;
assign brinfo_bta_miss = bta_miss;
//wire  [2:0]                    brinfo_bta_miss_offset;
wire  [2:0]                    brinfo_bta_miss_offset;
assign brinfo_bta_miss_offset = bta_offset;

npuarc_alb_bpu ualb_bpu(


// Fetch-restart interface

  .fch_restart          (exu_fetch_restart    ),  // Global pipeline restart signal; 1 => start execution at fch_target
  .fch_restart_vec      (fch_restart_int_vec      ),  // Global pipeline restart signal; 1 => start execution at fch_target
  .fch_target           (fch_target_int           ),  // absolute target of br, jmp from execution unit
  .fch_target_successor (fch_target_int_successor ),  // carry plus address of the next 64-bit instruction fetch block: 

  // Control BPU Prediction
  .start_prediction     (start_prediction     ),
  .bpu_ctrl             (bpu_ctrl             ),
  .bpu_ctrl_2cyc        (bpu_ctrl_2cyc        ),

  // Mispredict interface
  // mispredict info from the Execution Unit

  .mpd_mispred          (mpd_mispred         ),   // 1 => triggers a mispredict and start of instruction fetch at target
  .mpd_direction        (mpd_direction       ),   // was the branch taken or not taken? 1: taken, 0: not taken
  .mpd_error_branch     (mpd_error_branch    ),   // error prediction, need to delete this prediction from branch cache; also deletes fragged instructions
  .mpd_is_predicted     (mpd_is_predicted    ),   // was a prediction made for this branch?
  .mpd_mispred_outcome  (mpd_mispred_outcome ),   // was the direction (taken/not taken) mispredicted?
  .mpd_mispred_bta      (mpd_mispred_bta     ),   // was the BTA mispredicted?
  .mpd_type             (mpd_type            ),
  .mpd_seq_next_pc      (mpd_seq_next_pc     ),
  .mpd_pc               (mpd_pc              ),        
  .mpd_tail_pc_3        (mpd_tail_pc_3       ),
  .mpd_dslot            (mpd_dslot           ),
  .mpd_commit_size      (mpd_commit_size     ),
  .mpd_secondary        (mpd_secondary       ),
  .mpd_early            (mpd_early           ),

  // commit info from the Execution Unit about committed branches
  .wa_pass                (wa_pass               ),    // Request to commit a branch to IFU
  .wa_type                (wa_type               ),    // prediction type, like al_prediction_type               
  .wa_secondary           (wa_secondary          ),    // indicates if this instruction can be a secondary branch
  .wa_pc                  (wa_pc                 ),    // pc of the branch that is committed
  .wa_tail_pc_3           (wa_tail_pc_3          ),    // bit 3 of PC-2 of the instruction following branch or delay slot instruction
  .wa_dslot               (wa_dslot              ),    // does this branch instruction have a delay slot?
  .wa_target              (wa_target             ),    // branch target address of the branch/jump that is committed
  .wa_commit_size         (wa_commit_size        ),    // size of the branch instruction plus optional delay slot instruction
  .wa_direction           (wa_direction          ),    // was the branch taken or not taken? 1: taken, 0: not taken
  .wa_error_branch        (wa_error_branch       ),    // error prediction, need to delete this prediction from branch cache; 
  .wa_is_predicted        (wa_is_predicted       ),    // was a prediction made for this branch?
  .wa_mispred_outcome     (wa_mispred_outcome    ),    // was the direction (taken/not taken) mispredicted?
  .wa_commit_mispred_bta  (wa_commit_mispred_bta ),    // was the BTA mispredicted?

  .al_pass                (al_pass               ),

  // AUX registers

  // The following are interfaces to the BPU AUX registers from the IFU AUX register module
  .bpu_flush          (bpu_flush              ), // flush and initialize branch predictor; 
  .bpu_flush_ack      (bpu_flush_ack          ), // handshake signal
  .bpu_init_r         (bpu_init_r             ),
                 


  // performance counters
  .cycle2_r             (cycle2_r             ),

  ///////// Interface to Branch predictor RAM banks
  // Branch predictor RAMs have individual bit write enables, wem (write enable mask).

  .bc_din0     (bc_din0    ),
  .bc_addr0    (bc_addr0   ),
  .bc_me0      (bc_me0     ),
  .bc_we0      (bc_we0     ),
  .bc_wem0     (bc_wem0    ),
  .bc_dout0    (bc_dout0   ),

  .bc_din1     (bc_din1    ),
  .bc_addr1    (bc_addr1   ),
  .bc_me1      (bc_me1     ),
  .bc_we1      (bc_we1     ),
  .bc_wem1     (bc_wem1    ),
  .bc_dout1    (bc_dout1   ),

  .gs_din0     (gs_din0    ),
  .gs_addr0    (gs_addr0   ),
  .gs_me0      (gs_me0     ),
  .gs_we0      (gs_we0     ),
  .gs_wem0     (gs_wem0    ),
  .gs_dout0    (gs_dout0   ),

  .gs_din1     (gs_din1    ),
  .gs_addr1    (gs_addr1   ),
  .gs_me1      (gs_me1     ),
  .gs_we1      (gs_we1     ),
  .gs_wem1     (gs_wem1    ),
  .gs_dout1    (gs_dout1   ),

  .bc_ram0_clk (bc_ram0_clk),
  .bc_ram1_clk (bc_ram1_clk),
  .pt_ram0_clk (pt_ram0_clk),
  .pt_ram1_clk (pt_ram1_clk),
  .bc_ram0_clk_en (bc_ram0_clk_en),
  .bc_ram1_clk_en (bc_ram1_clk_en),
  .pt_ram0_clk_en (pt_ram0_clk_en),
  .pt_ram1_clk_en (pt_ram1_clk_en),


  /////////////////////////////////////////////////////////////////////////////
  // interface with instruction memory, icache or ICCM

  // handshake
  .mem_req        (mem_req        ), // start a memory access
  .mem_busy       (mem_busy       ), // indicator from the Icache/ICCM that it cannot accept an access now.

  // fetch control signals
  .restart        (bpu_fetch_restart_org), // a restart occurred, so flush the pipeline
  .unaligned_out  (unaligned      ), // 1: the 128-bit fetch block starts in bank 1; 0: the 128-bit fetch block starts in bank 0
  .kill_2nd       (kill_2nd       ), // skip the 2nd fetch block that is being fetched in the current fetch cycle.

  // the signals fetch0 and fetch1 determine if 1 or 2 banks are used and which
  .fetch0         (fetch0         ), // 1: enable a fetch from bank0 at address fa0; 0: disable fetch from bank0
  .fetch1         (fetch1         ), // 1: enable a fetch from bank1 at address fa1; 0: disable fetch from bank1

   // addresses
  .fa0_out        (fa0            ),  // Full fetch address for bank 0, including BTA offset 
  .fa1_out_diff   (fa1_diff       ), // fetch address for bank 1, only the bits that are different from fa0



   .fetch_icache  (fetch_icache  ),

   // way prediction
  .way_pred_gated       (way_pred      ), // Predicted way of the fetch
//  .way_pred_out   (way_pred_out  ), // Predicted way of the fetch
//  .way_valid      (way_valid     ),            // way prediction is valid
  .way_valid_out  (way_valid_out ),            // way prediction is valid
  .way_valid_detect  (way_valid_detect), // way prediction is valid; for mpd case
  .way_sec        (way_sec       ), // is the way pred for a secondary branch?
  .way_seq        (way_seq       ), // sequential way; tags off
  .way_req        (way_req       ), // request to provide way prediction when way_valid=0
  // Branch cache input port for icache to set way prediction
  .wr_way         (wr_way        ), // Write control for way prediction
  .way_in         (way_in        ), // Predicted way of the fetch
  .way_in_sec     (way_in_sec    ), // is the way for a secondary branch?
  .way_index      (way_index     ), // Branch cache index for the way
  .way_bank       (way_bank      ), // Branch cache bank for the way

  // BTA miss handling
  .bta_miss        (bta_miss          ),
  .bta_offset_out      (bta_offset        ),
  .bta_displ       (bta_miss_disp     ),
  .bta_displ_valid (bta_miss_disp_vld ),
                 
  // info attached to fetch blocks
  .branch_info_fb_out (branch_info_fb ), 
  .top_of_stack   (top_of_stack   ),
  .write_tosq_r   (write_tosq_r   ),
  .taken_out          (taken          ),
  .offset_out         (offset         ), // the offset of the branch instruction in the fetch block; can be 128 bits
  .bta_pred_out       (bta_pred       ), // the BTA of the predicted taken branch
  .bta_valid      (bta_valid      ), // indicates if bta_pred is valid; will be delayed in case of BTA miss
  .fetch_tail     (fetch_tail     ), // indicates that the next fetch is the tail of the current branch instruction 

  .mispredict_branch_info (mpd_branch_info_full_new ), 
  .commit_branch_info     (wa_branch_info_full_new  ),


// global signals
  .clk                 (clk       ),
  .rst_a               (rst_a     )
   );


assign bpu_fetch_restart =  bpu_fetch_restart_org && (!exu_hlt_restart);
    
  wire ifu_idle_r_int;
  assign ifu_idle_r = ( ifu_idle_r_int 
                      )
                    & (~bpu_flush) 
                    & (~bpu_init_r)
                    ;
     
//====================================================================
//==================== pipe stage  : request FIFO from prediction unit
//==================== upper stage : prediction unit 
//==================== lower stage : fetch decoder 
//====================================================================
wire restart_way_vld;
assign restart_way_vld = way_valid_detect;
wire [2-1:0] restart_way;
assign restart_way = mpd_branch_info_full[21-1:21-2];


npuarc_alb_ifu_fetch_if alb_ifu_fetch_if_u(
        .clk             (clk               ),
        .clk2_en         (clk2_en           ),
        .rst_a           (rst_a             ),


        .ifu_hlt_rdy     (ifu_hlt_rdy       ),
        .hlt_restart     (exu_hlt_restart   ),
        .fetch_restart   (exu_fetch_restart ),
        .mmu_restart     (mmu_restart),
        .ifu_active      (ifu_active),
        .ifu_idle_r      (ifu_idle_r_int    ),
        .hlt_stall       (hlt_stall         ),


        .fch_target             (fch_target_int             ),
        .fch_target_successor   (fch_target_int_successor   ),
        .restart_way_vld        (restart_way_vld        ),
        .restart_way            (restart_way            ),

        .restart                (restart_state          ),
        .restart_r              (restart_state_r        ),
        .bpu_restart            (bpu_fetch_restart      ),
        .restart_vec            (fch_restart_int_vec        ),
        .fetch_req              (fetch_req              ),
        .fetch_iccm0            (fetch_iccm0            ),
        .fetch_iccm1            (fetch_iccm1            ),
        .fetch_icache           (fetch_icache           ),
        .fetch_bank_ctl         (fetch_bank_ctl         ),
        .fetch_way_force        (fetch_way_force        ),
        .fetch_way_ptr          (fetch_way_ptr          ),
        .fetch_seq              (fetch_seq              ),
        .fetch_way_sec          (fetch_way_sec          ),
        .fetch_way_req          (fetch_way_req          ),
        .fetch_addr0            (fetch_addr0            ),
        .fetch_addr1_offset     (fetch_addr1_offset     ),
        .brinfo_kill_2nd        (kill_2nd               ),
        .brinfo_is_br           (brinfo_is_br           ),
        .brinfo_is_br_last      (brinfo_is_br_last      ),
        .brinfo_bta             (brinfo_bta             ),
        .brinfo_br_offset       (brinfo_br_offset       ),
        .brinfo_bta_miss        (brinfo_bta_miss        ),
        .brinfo_bta_miss_offset (brinfo_bta_miss_offset ),
        .brinfo_pkt             (brinfo_pkt             ),
        .fetch_rdy              (fetch_rdy              ),

        .fetch_iccm0_kill       (fetch_iccm0_kill       ),
        .fetch_iccm1_kill       (fetch_iccm1_kill       ),
        .fetch_iccm0_out        (fetch_iccm0_int        ),
        .fetch_iccm1_out        (fetch_iccm1_int        ),
        .fetch_iccm0_bank_out   (fetch_iccm0_bank_int   ),
        .fetch_iccm1_bank_out   (fetch_iccm1_bank_int   ),
        .fetch_icache_out       (fetch_icache_int       ),
        .fetch_bank_ctl_out     (fetch_bank_ctl_int     ),
        .fetch_is_restart_out   (fetch_is_restart_int   ),
        .fetch_vec_out          (fetch_vec_int          ),
        .fetch_way_force_out    (fetch_way_force_int    ),
        .fetch_way_ptr_out      (fetch_way_ptr_int      ),
        .fetch_seq_out          (fetch_seq_int          ),
        .fetch_way_sec_out      (fetch_way_sec_int      ),
        .fetch_way_req_out      (fetch_way_req_int      ),
        .fetch_way_bank_id_out  (fetch_way_bank_id_int  ),
        .fetch_way_tail_out     (fetch_way_tail_int     ),
        .fetch_addr0_out        (fetch_addr0_int        ),
        .fetch_addr1_offset_out (fetch_addr1_offset_int ),
        .refetch                (refetch_int            ),
        .brinfo_vld             (brinfo_vld             ),
        .brinfo_is_restart_out  (brinfo_is_restart_int  ),
        .brinfo_kill_2nd_out    (brinfo_kill_2nd_int    ),
        .brinfo_is_br_out       (brinfo_is_br_int       ),
        .brinfo_is_br_last_out  (brinfo_is_br_last_int  ),
        .brinfo_bta_out         (brinfo_bta_int         ),
        .brinfo_br_offset_out   (brinfo_br_offset_int   ),
        .brinfo_bta_miss_out    (brinfo_bta_miss_int    ),
        .brinfo_bta_miss_offset_out(brinfo_bta_miss_offset_int),
        .brinfo_pkt_out         (brinfo_pkt_int         ),
        .brinfo_bank_ctl_out    (brinfo_bank_ctl_int    ),
        .fetch_out_rdy          (fetch_rdy_int          )
);
        

////////////////////////////////////////////////////////////////////////////////
// Decode the parameters from the branch info queue and insert the TOS from
// the tos_queue
//
// leda NTL_CON12A off
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  unused signals
wire                wa_alt_way_valid_unused;
wire [1:0] wa_alt_way_unused;
wire                wa_way_secondary_unused;
wire [1:0] wa_brinfo_tosp_unused;
wire [1:0]          wa_num_nt_unused;
wire [13:4] wa_ghr_unused;
wire                wa_brinfo_strength_unused;
wire [1:0] wa_brinfo_offset_unused; // offset of the primary branch
wire                wa_brinfo_valid_unused;  // is the primary branch valid?

wire                mp_alt_way_valid_unused;
wire [1:0] mp_alt_way_unused;
wire                mp_way_secondary_unused;
wire [1:0] mp_brinfo_tosp_unused;
wire [1:0]          mp_num_nt_unused;
wire [13:4] mp_ghr_unused;
wire                mp_brinfo_strength_unused;
wire [1:0]          mp_brinfo_offset_unused; // offset of the primary branch
wire                mp_brinfo_valid_unused;  // is the primary branch valid?
// leda NTL_CON13A on
// leda NTL_CON12A on
////////////////////////////////////////////////////////////////////////////////
// extract the parameters from wa_branch_info_full
// 
assign {
        wa_alt_way_valid_unused    , 
        wa_alt_way_unused[1:0],
        wa_way_secondary_unused,
        wa_brinfo_offset_unused, // offset of the primary branch
        wa_brinfo_valid_unused,       // is the primary branch valid?
        wa_brinfo_tosp_unused [1:0],
        wa_num_nt_unused[1:0]       ,
        wa_ghr_unused[13:4] ,
        wa_brinfo_strength_unused       // indicates if the primary branch is predicted (taken or not taken)
        } = wa_branch_info_full;

////////////////////////////////////////////////////////////////////////////////
// extract the parameters from mpd_branch_info_full
// 
assign {
        mp_alt_way_valid_unused  , 
        mp_alt_way_unused[1:0],
        mp_way_secondary_unused,
        mp_brinfo_offset_unused, // offset of the primary branch
        mp_brinfo_valid_unused,       // is the primary branch valid?
        mp_brinfo_tosp_unused [1:0],
        mp_num_nt_unused[1:0]       ,
        mp_ghr_unused[13:4] ,
        mp_brinfo_strength_unused       // indicates if the primary branch is predicted (taken or not taken)
        } = mpd_branch_info_full;

////////////////////////////////////////////////////////////////////////////////
// pack the parameters for wa_branch_info_full
//
assign wa_branch_info_full_new =
       {
        wa_alt_way_valid_unused     , 
        wa_alt_way_unused[1:0],
        wa_way_secondary_unused     ,
        wa_tos [31:1]          ,  // Return Stack Top of Stack value
        wa_brinfo_offset_unused, // offset of the primary branch
        wa_brinfo_valid_unused      , // is the primary branch valid?
        wa_brinfo_tosp_unused [1:0],
        wa_num_nt_unused[1:0]       ,
        wa_ghr_unused[13:4] ,
        wa_brinfo_strength_unused       // indicates if the primary branch is predicted (taken or not taken)
        };

////////////////////////////////////////////////////////////////////////////////
// pack the parameters for mpd_branch_info_full
//
assign mpd_branch_info_full_new = 
        {
        mp_alt_way_valid_unused     , 
        mp_alt_way_unused[1:0],
        mp_way_secondary_unused     ,
        mpd_tos[31:1]          , // Return Stack Top of Stack value
        mp_brinfo_offset_unused, // offset of the primary branch
        mp_brinfo_valid_unused      , // is the primary branch valid?
        mp_brinfo_tosp_unused [1:0],
        mp_num_nt_unused[1:0]       ,
        mp_ghr_unused[13:4] ,
        mp_brinfo_strength_unused     // indicates if the primary branch is predicted (taken or not taken)
        };

wire [2:0] tos_index;
wire [2:0] mpd_branch_tosq_indx;
wire [2:0] wa_branch_tosq_indx;
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  unused signal
wire                  tosq_holdup_unused;
// leda NTL_CON13A on
////////////////////////////////////////////////////////////////////////////////
// TOS QUEUE       
// TOS Information  from BPU is stored in this buffer. Retrieved based on the
// mispredict and commit information from the EXU
////////////////////////////////////////////////////////////////////////////////
npuarc_alb_ifu_tos_queue ualb_ifu_tos_queue
  (
  .clk              (clk               ), // clock input 
  .rst_a            (rst_a             ), // async reset in

// Fetch Restart
  .fch_restart      (fch_restart_int   ), // Restart from EXU, including lpb_restart

// branch info from the BPU 
  .br_info_valid    (write_tosq_r      ), // branch info is valid
  .br_info          (top_of_stack      ), // branch info 

// TOS Queue full holdup
  .tosq_holdup      (tosq_holdup_unused), // stall signal from tosq

// holdup from next stage
//  .holdup_in        (1'b1             ), // holdup from Fetch buffer

// TOS index to next  stage
  .tos_indx         (tos_index         ), // index of the the TOSQ

// Interface from mispredict of the Execute Unit
  .mpd_mispredict   (mpd_mispred      ), // indicates a mispredict 
  .mpd_tos_indx     (mpd_branch_tosq_indx  ), // index of the mipredict branch from mpd
//  .mpd_dslot        (mpd_dslot        ), // indicates a mispredict 
//  .mpd_error_branch (mpd_error_branch ), // indicates error branch 
  .mpd_tos          (mpd_tos          ), // branch info for the mispredict from mpd

// Interface from commit of the Execute Unit
  .wa_pass          (wa_pass          ),  // indicates a brach commit 
  .wa_tos_indx      (wa_branch_tosq_indx ),  // index of the mispredict branch from commit 
  .wa_tos           (wa_tos           )   // branch info for the mispredict from commit
   );



  
//====================================================================
//===================== pipe stage : fetch decoder 
//===================== upper stage : prediction unit
//===================== lower stage : iccm/icache controller
//====================================================================
// -- fetch request is from prediction unit
//  1. iccm0
//  2. iccm1
//  3. icache
// -- fetch output goes to fetech buffer
//
npuarc_alb_ifu_addr_dec alb_ifu_addr_dec_u (
  .clk                  (clk2              ),
  .rst_a                (rst_a             ),
  .restart              (restart_state     ),
  .bpu_restart          (bpu_fetch_restart ),


  //from prediction unit
  .fetch_iccm0          (fetch_iccm0_int      ),
  .fetch_iccm1          (fetch_iccm1_int      ),
  .fetch_iccm0_bank     (fetch_iccm0_bank_int ),
  .fetch_iccm1_bank     (fetch_iccm1_bank_int ),
  .fetch_icache         (fetch_icache_int     ),
  .fetch_bank_ctl       (fetch_bank_ctl_int   ),
  .fetch_is_restart     (fetch_is_restart_int ),
  .fetch_vec            (fetch_vec_int        ),
  .fetch_way_force      (fetch_way_force_int  ),
  .fetch_way_ptr        (fetch_way_ptr_int    ),
  .fetch_seq            (fetch_seq_int        ),
  .fetch_way_sec        (fetch_way_sec_int    ),
  .fetch_way_req        (fetch_way_req_int    ),
  .fetch_way_bank_id    (fetch_way_bank_id_int),
  .fetch_way_tail       (fetch_way_tail_int   ),
  .fetch_addr0          (fetch_addr0_int        ),
  .fetch_addr1_offset   (fetch_addr1_offset_int ),
  .refetch              (refetch_int            ),
  .brinfo_vld           (brinfo_vld             ),
  .brinfo_is_restart    (brinfo_is_restart_int  ),
  .brinfo_kill_2nd      (brinfo_kill_2nd_int    ),
  .brinfo_is_br         (brinfo_is_br_int       ),
  .brinfo_is_br_last    (brinfo_is_br_last_int  ),
  .brinfo_bta           (brinfo_bta_int         ),
  .brinfo_bank_ctl      (brinfo_bank_ctl_int    ),
  .brinfo_br_offset     (brinfo_br_offset_int   ),
  .brinfo_bta_miss      (brinfo_bta_miss_int    ),
  .brinfo_bta_miss_offset(brinfo_bta_miss_offset_int),
  .brinfo_pkt     ({tos_index,brinfo_pkt_int[42-3:0]}),
  .fetch_rdy            (fetch_rdy_int          ),

  //to targets


  .fetch_icache_addr0  (fetch_icache_addr0   ),
  .fetch_icache_addr1  (fetch_icache_addr1   ),
  .fetch_icache_req     (fetch_icache_req      ),
  .fetch_icache_ack     (fetch_icache_ack      ),
  .fetch_icache_vec     (fetch_icache_vec      ),

  .fetch_icache_way_force(fetch_icache_way_force),
  .fetch_icache_way_ptr     (fetch_icache_way_ptr     ),
  .fetch_icache_seq         (fetch_icache_seq         ),
  .fetch_icache_way_sec     (fetch_icache_way_sec     ),
  .fetch_icache_way_req     (fetch_icache_way_req     ),
  .fetch_icache_way_bank_id (fetch_icache_way_bank_id ),
  .fetch_icache_way_tail    (fetch_icache_way_tail    ),
  .fetch_icache_is_restart  (fetch_icache_is_restart  ),

  .fetch_data_take      (fetch_data_mux_out_take ),
  .brinfo_id_vld        (brinfo_id_vld           ),
  .brinfo_id_is_restart (brinfo_id_is_restart    ),
  .brinfo_id_kill_2nd   (brinfo_id_kill_2nd      ),
  .brinfo_id_is_br      (brinfo_id_is_br         ),
  .brinfo_id_is_br_last (brinfo_id_is_br_last    ),
  .brinfo_id_bta        (brinfo_id_bta           ),
  .brinfo_id_bank_ctl   (brinfo_id_bank_ctl      ),
  .brinfo_id_br_offset  (brinfo_id_br_offset     ),
  .brinfo_id_pkt        (brinfo_id_pkt           ),
  .brinfo_id_bta_miss   (brinfo_id_bta_miss      ),
  .brinfo_id_bta_miss_offset(brinfo_id_bta_miss_offset)
);

 


wire           ic_aux_data_ecc_err;
wire           al_icache_ecc_err_int;
assign al_icache_ecc_err = al_icache_ecc_err_int | ic_aux_data_ecc_err;


wire          al_icache_ecc_sb_err;
wire          ic_aux_data_ecc_sb_err;
wire          ic_tag_ecc_sb_err;
reg [3:0]     ic_data_ecc_sbe_cnt_next;
reg [3:0]     ic_tag_ecc_sbe_cnt_next;

always @(posedge clk or posedge rst_a) 
begin: ic_ecc_sbe_cnt_reg_PROC
  if (rst_a == 1'b1) begin
    ic_data_ecc_sbe_cnt <= 4'h0;
    ic_tag_ecc_sbe_cnt  <= 4'h0;
  end
  else begin
    ic_data_ecc_sbe_cnt <= ic_data_ecc_sbe_cnt_next;
    ic_tag_ecc_sbe_cnt  <= ic_tag_ecc_sbe_cnt_next;
  end
end

// IC Data ECC Single bit erorr counter
always @(*) 
begin: ic_data_ecc_sbe_cnt_logic_PROC
  ic_data_ecc_sbe_cnt_next = ic_data_ecc_sbe_cnt;

  if (ic_data_ecc_sbe_clr) begin
    ic_data_ecc_sbe_cnt_next = 4'h0;
  end
  else if (al_icache_ecc_sb_err | ic_aux_data_ecc_sb_err) begin
    if(ic_data_ecc_sbe_cnt < 4'hf) begin
      ic_data_ecc_sbe_cnt_next = ic_data_ecc_sbe_cnt + 1;
    end
  end
end

// IC Tag ECC Single bit erorr counter
always @(*) 
begin: ic_tag_ecc_sbe_cnt_logic_PROC
  ic_tag_ecc_sbe_cnt_next = ic_tag_ecc_sbe_cnt;

  if (ic_tag_ecc_sbe_clr) begin
    ic_tag_ecc_sbe_cnt_next = 4'h0;
  end
  else if (ic_tag_ecc_sb_err) begin
    if(ic_tag_ecc_sbe_cnt < 4'hf) begin
      ic_tag_ecc_sbe_cnt_next = ic_tag_ecc_sbe_cnt + 1;
    end
  end
end







//====================================================================
//===================== pipe stage : iccm 
//===================== up stage   : fetch decoder request
//===================== down stage : fetch data 
//====================================================================
//ICCM arbitor


reg  itlb_stall_r;
wire itlb_stall;

assign itlb_stall = (itlb_stall_r | jrsp_itlb_update2_r);

always @(posedge clk or posedge rst_a) 
begin: itlb_stall_r_PROC
  if (rst_a == 1'b1) begin
    itlb_stall_r <= 1'b0;
  end
  else
  begin
    itlb_stall_r <= itlb_lkup0_stall_nxt;
  end
end


reg  exu_hlt_restart_r;
wire exu_hlt_restart2;

always @(posedge clk or posedge rst_a) 
begin: exu_hlt_restart_PROC
  if (rst_a == 1'b1) begin
    exu_hlt_restart_r <= 1'b0;
  end
  else
  begin
    exu_hlt_restart_r <= exu_hlt_restart;
  end
end

// stretch for use in clk2 domain (icache)
assign exu_hlt_restart2 = exu_hlt_restart | exu_hlt_restart_r;


//====================================================================
//===================== pipe stage : icache control (cucurrent with iccm)
//===================== up stage   : fetch decoder request
//===================== down stage : fetch data 
//====================================================================
//icache
npuarc_alb_icache u_icache (
  .clk                  (clk2              ),
  .clk_en               (clk2_en           ),
  .clk2_en_r            (clk2_en_r         ),
  .clk_ibus             (clk               ),
  .rst_a                (rst_a             ),

  .dbg_cache_rst_disable_r (dbg_cache_rst_disable_r),

  .restart              (restart_state     ),
  .exu_hlt_restart      (exu_hlt_restart2  ),
  .bpu_restart          (bpu_fetch_restart ),
  .hlt_ready            (ic_hlt_ready      ),
  .mpd_pc_load          (exu_fetch_restart ), //to load mispredicted PC
  .mpd_pc               (mpd_pc            ), //mispredicted PC, for way prediction at restart
  .mpd_direction        (mpd_direction     ),
  .mpd_mispred          (mpd_mispred       ),
  .mem_busy             (ic_mem_busy       ),
  .aux_busy             (ic_aux_busy       ),
  .ar_user_mode_r       (ar_user_mode_r    ),
  .ifu_icache_miss_r    (ifu_icache_miss_r ),
  .ifu_way_pred_miss_r  (ifu_way_pred_miss_r),
  .ifu_icache_hit_r     (ifu_icache_hit_r  ),
  .ifu_icache_disabled  (ifu_icache_disabled),
  .cycle2_r             (cycle2_r          ),


  .ic_data_din0        (ic_data_din0    ),
  .ic_data_dout0       (ic_data_dout0   ),
  .ic_data_addr0       (ic_data_addr0   ), 
  .ic_data_cen0        (ic_data_cen0    ),
  .ic_data_wen0        (ic_data_wen0    ),
  .ic_data_wem0        (ic_data_wem0    ),
  .ic_data_din1        (ic_data_din1    ),
  .ic_data_dout1       (ic_data_dout1   ),
  .ic_data_addr1       (ic_data_addr1   ), 
  .ic_data_cen1        (ic_data_cen1    ),
  .ic_data_wen1        (ic_data_wen1    ),
  .ic_data_wem1        (ic_data_wem1    ),

  .ic_tag_din0         (ic_tag_din0     ),
  .ic_tag_dout0        (ic_tag_dout0    ),
  .ic_tag_wem0         (ic_tag_wem0     ),    
  .ic_tag_addr0        (ic_tag_addr0    ),
  .ic_tag_cen0         (ic_tag_cen0     ),
  .ic_tag_wen0         (ic_tag_wen0     ),
  .ic_tag_din1         (ic_tag_din1     ),
  .ic_tag_dout1        (ic_tag_dout1    ),
  .ic_tag_wem1         (ic_tag_wem1     ),    
  .ic_tag_addr1        (ic_tag_addr1    ),
  .ic_tag_cen1         (ic_tag_cen1     ),
  .ic_tag_wen1         (ic_tag_wen1     ),
  .ic_tag_din2         (ic_tag_din2     ),
  .ic_tag_dout2        (ic_tag_dout2    ),
  .ic_tag_wem2         (ic_tag_wem2     ),    
  .ic_tag_addr2        (ic_tag_addr2    ),
  .ic_tag_cen2         (ic_tag_cen2     ),
  .ic_tag_wen2         (ic_tag_wen2     ),
  .ic_tag_din3         (ic_tag_din3     ),
  .ic_tag_dout3        (ic_tag_dout3    ),
  .ic_tag_wem3         (ic_tag_wem3     ),    
  .ic_tag_addr3        (ic_tag_addr3    ),
  .ic_tag_cen3         (ic_tag_cen3     ),
  .ic_tag_wen3         (ic_tag_wen3     ),

  // MPU / IPROT interface
  .ifetch_chk_addr      (ifetch_chk_addr  ),
  .ifetch_mpu_viol      (ifetch_mpu_viol),
  .ic_mpu_viol          (ic_mpu_viol),
  .ifetch_unc           (ifetch_unc),
  .ifetch_iprot_viol    (ifetch_iprot_viol),
  .ic_iprot_viol        (ic_iprot_viol),

  .itlb_lkup_valid      (itlb_lkup0_valid),
  .itlb_stall           (itlb_stall),
  .jrsp_itlb_update     (jrsp_itlb_update2_r),
  .req_vaddr_r          (itlb_lkup0_vaddr),
  .req_paddr            (itlb_rslt0_paddr_r),

  .itlb_fail_r          (itlb_fail_r),
  .itlb_miss_excpn_nxt  (itlb_miss_excpn_nxt),
  .itlb_miss_excpn_r_r  (itlb_miss_excpn_r_r),

  .itlb_ecc_err_excpn_nxt  (itlb_ecc_err_excpn_nxt),
  .itlb_ecc_err_excpn_r_r  (itlb_ecc_err_excpn_r_r),

  .itlb_ovrlp_excpn_nxt  (itlb_ovrlp_excpn_nxt),
  .itlb_ovrlp_excpn_r_r  (itlb_ovrlp_excpn_r_r),

  .itlb_exec_perm_nxt    (itlb_exec_perm_nxt),
  .itlb_exec_perm_r_r    (itlb_exec_perm_r_r),

  .icache_tag_par_mode_r (icache_tag_par_mode_r),

  .fa_pc_nxt0          (fetch_icache_addr0 ),
  .fa_pc_nxt1          (fetch_icache_addr1 ),
  .fa_fetch             (fetch_icache_req         ),
  .fa_bank_ctl          (fetch_bank_ctl_int[2:0]),
  .fa_way_bank_id       (fetch_icache_way_bank_id ),
  .fa_way_tail          (fetch_icache_way_tail    ),
  .fa_is_restart        (fetch_icache_is_restart  ),
  .fa_way_force         (fetch_icache_way_force   ),
  .fa_way_ptr           (fetch_icache_way_ptr     ),
  .fa_vec               (fetch_icache_vec         ),
  .fa_seq               (fetch_icache_seq         ),
  .fa_way_sec           (fetch_icache_way_sec     ),
  .fa_way_req           (fetch_icache_way_req     ),
  .fa_rdy               (fetch_icache_ack         ),

  .fa_data              (fetch_icache_data        ),
  .fa_data_vld          (fetch_icache_data_vld    ),
  .fa_data_err          (fetch_icache_data_err    ),
  .fa_data_way          (fetch_icache_data_way    ),
  .fa_data_rdy          (fetch_icache_data_rdy    ),
  .ecc_enable           (fetch_icache_ecc_enable  ),
  .ic_tag_ecc_err       (ic_tag_ecc_err           ),
  .ic_aux_data_ecc_err  (ic_aux_data_ecc_err      ),
  .ecc_ifu_disable      (ecc_ifu_disable          ),
  .ic_tag_ecc_sb_err   (ic_tag_ecc_sb_err         ),
  .ic_aux_data_ecc_sb_err (ic_aux_data_ecc_sb_err  ),
//   `if (0 == 1) // { 3
  .fs_ic_tag_bank0_syndrome_r   (fs_ic_tag_bank0_syndrome_r),
  .fs_ic_tag_bank0_ecc_sb_error_r (fs_ic_tag_bank0_ecc_sb_error_r),
  .fs_ic_tag_bank0_ecc_db_error_r (fs_ic_tag_bank0_ecc_db_error_r),
  .fs_ic_tag_bank1_syndrome_r   (fs_ic_tag_bank1_syndrome_r),
  .fs_ic_tag_bank1_ecc_sb_error_r (fs_ic_tag_bank1_ecc_sb_error_r),
  .fs_ic_tag_bank1_ecc_db_error_r (fs_ic_tag_bank1_ecc_db_error_r),
  .fs_ic_tag_bank2_syndrome_r   (fs_ic_tag_bank2_syndrome_r),
  .fs_ic_tag_bank2_ecc_sb_error_r (fs_ic_tag_bank2_ecc_sb_error_r),
  .fs_ic_tag_bank2_ecc_db_error_r (fs_ic_tag_bank2_ecc_db_error_r),
  .fs_ic_tag_bank3_syndrome_r   (fs_ic_tag_bank3_syndrome_r),
  .fs_ic_tag_bank3_ecc_sb_error_r (fs_ic_tag_bank3_ecc_sb_error_r),
  .fs_ic_tag_bank3_ecc_db_error_r (fs_ic_tag_bank3_ecc_db_error_r),
//   `endif               // } 3

  .ifu_ivic             (ifu_ivic            ),
  .ifu_ivil             (ifu_ivil            ),
  .aux_read             (aux_read            ),
  .aux_write            (aux_write           ),
  .aux_wdata            (aux_wdata           ),
  .aux_ic_ren_r         (aux_ic_ren_r        ),
  .aux_ic_wen_r         (aux_ic_wen_r        ),
  .aux_ic_raddr_r       (aux_ic_raddr_r      ),
  .aux_ic_waddr_r       (aux_ic_waddr_r      ),
  .ic_aux_rdata         (ic_aux_rdata        ),
  .ic_aux_illegal       (ic_aux_illegal      ),
  .ic_aux_k_rd          (ic_aux_k_rd         ),
  .ic_aux_k_wr          (ic_aux_k_wr         ),
  .ic_aux_unimpl        (ic_aux_unimpl       ),
  .ic_aux_serial_sr     (ic_aux_serial_sr    ),
  .ic_aux_strict_sr     (ic_aux_strict_sr    ),

  .way_for_pred         (way_for_pred        ),
  .way_sec_for_pred     (way_sec_for_pred    ),
  .way_for_pred_vld     (way_for_pred_vld    ),
  .way_for_pred_pc      (way_for_pred_pc     ),


  .ifu_ibus_cmd_valid      (ifu_ibus_cmd_valid  ),
  .ifu_ibus_cmd_prot       (ifu_ibus_cmd_prot   ),
  .ifu_ibus_cmd_accept     (ifu_ibus_cmd_accept ),
  .ifu_ibus_cmd_addr       (ifu_ibus_cmd_addr   ),
  .ifu_ibus_cmd_burst_size (ifu_ibus_cmd_burst_size),
  .ifu_ibus_cmd_wrap       (ifu_ibus_cmd_wrap   ), 
  .ifu_ibus_cmd_cache      (ifu_ibus_cmd_cache  ), 
  .ifu_ibus_rd_valid       (ifu_ibus_rd_valid   ), 
  .ifu_ibus_rd_accept      (ifu_ibus_rd_accept  ), 
  .ifu_ibus_rd_data        (ifu_ibus_rd_data    ), 
  .ifu_ibus_err_rd         (ifu_ibus_err_rd     )  
);


//====================================================================
//==================== pipe stage  : fetch memory data 
//==================== upper stage : iccm/icache memory
//==================== lower stage : fetch buffer 
//====================================================================

npuarc_alb_ifu_data_mux alb_ifu_data_mux_u (
  .clk                  (clk2            ),
  .core_clk             (clk             ),
  .rst_a                (rst_a           ),
  .restart              (restart_state   ),

  //from targets
  .fetch_icache_data      (fetch_icache_data     ),
  .fetch_icache_data_vld  (fetch_icache_data_vld ),
  .fetch_icache_data_err  (fetch_icache_data_err ),
  .fetch_icache_data_rdy  (fetch_icache_data_rdy ),
  .ic_mpu_viol          (ic_mpu_viol),
  .ic_iprot_viol        (ic_iprot_viol         ),

  .fetch_icache_data_way(fetch_icache_data_way),
  .fetch_icache_ecc_enable (fetch_icache_ecc_enable ),



  .itlb_ovrlp_excpn     (itlb_ovrlp_excpn      ),
  .itlb_miss_excpn      (itlb_miss_excpn       ),
  .itlb_ecc_err_excpn   (itlb_ecc_err_excpn    ),
  .itlb_exec_perm       (itlb_exec_perm        ),
  .fetch_data_mux_out_take (fetch_data_mux_out_take),

  .brinfo_id_vld        (brinfo_id_vld         ),
  .brinfo_id_is_restart (brinfo_id_is_restart  ),
  .brinfo_id_kill_2nd   (brinfo_id_kill_2nd    ),
  .brinfo_id_is_br      (brinfo_id_is_br       ),
  .brinfo_id_is_br_last (brinfo_id_is_br_last  ),
  .brinfo_id_bta        (brinfo_id_bta         ),
  .brinfo_id_bank_ctl   (brinfo_id_bank_ctl    ),
  .brinfo_id_br_offset  (brinfo_id_br_offset   ),
  .brinfo_id_pkt        (brinfo_id_pkt         ),
  .brinfo_id_bta_miss   (brinfo_id_bta_miss    ),
  .brinfo_id_bta_miss_offset(brinfo_id_bta_miss_offset),
  .bta_miss_update      (bta_valid             ),

  .bta_miss_disp_vld    (bta_miss_disp_vld     ),
  .bta_miss_disp        (bta_miss_disp         ),

 //to buffer
  .fetch_data_out       (fetch_data2buf        ),
  .fetch_data_vld_out   (fetch_data2buf_vld    ),
  .fetch_data_err_out   (fetch_data2buf_err    ),
  .dmux_iprot_viol      (dmux_iprot_viol       ),
  .fetch_data_exec_perm (fetch_data2buf_experm ),
  .fetch_data_way_out   (fetch_data2buf_way    ),
  .fetch_ecc_enable     (fetch_data2buf_ecc_enable  ),
  .fetch_data_rdy       (fetch_data2buf_rdy_qual    ),
  .brinfo_restart_out   (brinfo_data2buf_restart    ),
  .brinfo_br_out        (brinfo_data2buf_br         ),
  .brinfo_first_word_out(brinfo_data2buf_first_word ),
  .brinfo_br_last_out   (brinfo_data2buf_br_last    ),
  .brinfo_bank_ctl_out  (brinfo_data2buf_bank_ctl   ),
  .brinfo_bank_cnt_out  (brinfo_data2buf_bank_cnt   ),
  .brinfo_br_offset_out (brinfo_data2buf_br_offset  ),
  .brinfo_pkt_out       (brinfo_data2buf_pkt        ),

  .bta_vld_out          (bta2buf_vld                ),
  .bta_bank_cnt_out     (bta2buf_bank_cnt           ),
  .bta_info_bta_out     (bta2buf_bta                ),
  .bta_tail_stall       (bta_tail_stall             ),
  .bta_rdy              (bta2buf_rdy                )
);

//====================================================================
//===================== pipe stage : fetch buffer
//===================== up stage   : fetch data
//===================== down stage : align&predecoder
//====================================================================
//fetch buffer
npuarc_alb_fetch_buf alb_fetch_buf_u(
  .clk                      (clk                    ),
  .clk2_en                  (clk2_en                ),
  .rst_a                    (rst_a                  ),
  .restart                  (restart_state          ),


  .buf_data_in              (fetch_data2buf          ),
  .buf_data_in_vld          (fetch_data2buf_vld_qual ),
  .buf_data_in_err          (fetch_data2buf_err      ),
  .buf_data_in_iprot_viol   (dmux_iprot_viol         ),
  .buf_data_in_experm       (fetch_data2buf_experm   ),
  .buf_data_in_way          (fetch_data2buf_way      ),
  .buf_in_ecc_enable        (fetch_data2buf_ecc_enable ),
  .buf_data_in_rdy          (fetch_data2buf_rdy        ),
  .buf_data_restart_in      (brinfo_data2buf_restart   ),
  .buf_data_br_in           (brinfo_data2buf_br        ),
  .buf_data_first_word_in   (brinfo_data2buf_first_word),
  .buf_data_br_last_in      (brinfo_data2buf_br_last   ),
  .buf_data_bta_in          (bta2buf_bta               ),
  .buf_data_bank_ctl_in     (brinfo_data2buf_bank_ctl  ),
  .buf_data_bank_cnt_in     (brinfo_data2buf_bank_cnt  ),
  .buf_data_br_offset_in    (brinfo_data2buf_br_offset ),
  .buf_data_pkt_in          (brinfo_data2buf_pkt       ),

  .buf_bta_in_vld           (bta2buf_vld               ),
  .buf_bta_in_bank_cnt      (bta2buf_bank_cnt          ),
  .bta_tail_stall           (bta_tail_stall            ),
  .buf_bta_in_rdy           (bta2buf_rdy               ),

  .buf_data_out_w0          (buf_data_out_w0         ),
  .buf_data_out_vld0        (buf_data_out_vld0       ),
  .buf_data_out_err0        (buf_data_out_err0       ),
  .buf_data_out_experm0    (buf_data_out_experm0   ),
  .buf_data_out_iprot_viol0 (dbuf_iprot_viol0        ),
  .buf_data_out_way0        (buf_data_out_way0       ),
  .buf_out_ecc_enable0      (buf_data_out_ecc_enable0 ),
  .buf_data_out_bta0        (buf_data_out_bta0        ),
  .buf_data_out_first_word0 (buf_data_out_first_word0 ),
  .buf_data_out_bank_ctl0   (buf_data_out_bank_ctl0   ),
  .buf_data_out_br_offset0  (buf_data_out_br_offset0  ),
  .buf_data_out_pkt0        (buf_data_out_pkt0        ),
  .buf_data_out_w1          (buf_data_out_w1         ),
  .buf_data_out_vld1        (buf_data_out_vld1       ),
  .buf_data_out_err1        (buf_data_out_err1       ),
  .buf_data_out_experm1    (buf_data_out_experm1   ),
  .buf_data_out_iprot_viol1 (dbuf_iprot_viol1        ),
  .buf_data_out_way1        (buf_data_out_way1       ),
  .buf_out_ecc_enable1      (buf_data_out_ecc_enable1 ),
  .buf_data_out_bta1        (buf_data_out_bta1        ),
  .buf_data_out_first_word1 (buf_data_out_first_word1 ),
  .buf_data_out_bank_ctl1   (buf_data_out_bank_ctl1   ),
  .buf_data_out_br_offset1  (buf_data_out_br_offset1  ),
  .buf_data_out_pkt1        (buf_data_out_pkt1        ),

  .buf_taken            (buf_taken            ),
  .buf_taken_single     (buf_taken_single     ),
  .buf_taken_count_nxt  (buf_taken_count_nxt  )

);


wire [23:0] branch_info_fb0;
wire [23:0] branch_info_fb1;

assign branch_info_fb0[23:0] = buf_data_out_first_word0 ? 
     {buf_data_out_pkt0[42:38], buf_data_out_pkt0[18:0]}
      :
     {buf_data_out_pkt0[42:38], buf_data_out_pkt0[37:19]}
;
assign branch_info_fb1[23:0] = buf_data_out_first_word1 ? 
   {buf_data_out_pkt1[42:38], buf_data_out_pkt1[18:0]}
  :
   {buf_data_out_pkt1[42:38], buf_data_out_pkt1[37:19]}
;

assign al_is_predicted = al_is_predicted_int;
wire [21:0] al_brinfo_full;

wire [2:0]     al_tosq_indx;
wire                      brq_holdup;

////////////////////////////////////////////////////////////////////////////////
//Instruction Alignment Module
//
////////////////////////////////////////////////////////////////////////////////

npuarc_alb_ifu_align alb_ifu_align_u(
  .clk                (clk                    ),
  .rst_a              (rst_a                  ),
  .restart            (bpu_fetch_restart      ), //restart from bpu, single pulse
  .flush              (fch_restart_int            ), //restart from exu, single pulse, for both fetch and stop 
  .restart_pc               (fch_target_int             ),

  //fetch buffer interface
    .inst0             (buf_data_out_w0[128/2-1:0] ),    

  .ecc_code0         (buf_data_out_w0[78-1:64] ),
  .vld0              (buf_data_out_vld0     ),
  .err0              (buf_data_out_err0     ),
  .experm0           (buf_data_out_experm0),
  .iprot_viol0       (dbuf_iprot_viol0),
  .icache_way0       (buf_data_out_way0     ),
  .ecc_enable0         (buf_data_out_ecc_enable0),
  .bta0              (buf_data_out_bta0       ),
  .first_word0       (buf_data_out_first_word0),
  .bank_ctl0         (buf_data_out_bank_ctl0  ),
  .br_pkt0           (branch_info_fb0         ),
    .inst1             (buf_data_out_w1[128/2-1:0] ),    

  .ecc_code1         (buf_data_out_w1[78-1:64] ),
  .vld1              (buf_data_out_vld1     ),
  .err1              (buf_data_out_err1     ),
  .experm1           (buf_data_out_experm1),
  .iprot_viol1       (dbuf_iprot_viol1),
  .icache_way1       (buf_data_out_way1     ),
  .ecc_enable1         (buf_data_out_ecc_enable1),
  .bta1              (buf_data_out_bta1       ),
  .first_word1       (buf_data_out_first_word1),
  .bank_ctl1         (buf_data_out_bank_ctl1  ),
  .br_pkt1           (branch_info_fb1         ),
  .ifu_bit_error_r    (ifu_bit_error_r      ),
  .buf_taken          (buf_taken            ),
  .buf_taken_single   (buf_taken_single     ),
  .buf_taken_count_nxt(buf_taken_count_nxt  ),


  .al_icache_ecc_err  (al_icache_ecc_err_int    ),
  .al_icache_ecc_sb_err (al_icache_ecc_sb_err ),
//      `if (0 == 1) // { 4
  .fs_ic_data_bank00_ecc_sb_error_r (fs_ic_data_bank00_ecc_sb_error_r),
  .fs_ic_data_bank00_ecc_db_error_r (fs_ic_data_bank00_ecc_db_error_r),
  .fs_ic_data_bank00_syndrome_r  (fs_ic_data_bank00_syndrome_r     ),
  .fs_ic_data_bank01_ecc_sb_error_r (fs_ic_data_bank01_ecc_sb_error_r),
  .fs_ic_data_bank01_ecc_db_error_r (fs_ic_data_bank01_ecc_db_error_r),
  .fs_ic_data_bank01_syndrome_r  (fs_ic_data_bank01_syndrome_r     ),
  .fs_ic_data_bank10_ecc_sb_error_r (fs_ic_data_bank10_ecc_sb_error_r),
  .fs_ic_data_bank10_ecc_db_error_r (fs_ic_data_bank10_ecc_db_error_r),
  .fs_ic_data_bank10_syndrome_r  (fs_ic_data_bank10_syndrome_r     ),
  .fs_ic_data_bank11_ecc_sb_error_r (fs_ic_data_bank11_ecc_sb_error_r),
  .fs_ic_data_bank11_ecc_db_error_r (fs_ic_data_bank11_ecc_db_error_r),
  .fs_ic_data_bank11_syndrome_r  (fs_ic_data_bank11_syndrome_r     ),
//      `endif               // } 4

  .ecc_ifu_disable    (ecc_ifu_disable      ),
  .ecc_ifu_expn_disable (ecc_ifu_expn_disable ),

//Mispredict signals
  .mpd_mispred        (mpd_mispred          ),  
  .mpd_direction      (mpd_direction        ), 
  .mpd_error_branch   (mpd_error_branch     ),       
  .mpd_type           (mpd_type             ),

//Mispredict branch info
  .mpd_brinfo_full    (mpd_branch_info_full_new ), // branch info for the mispredict from mpd
  .wa_brinfo_full     (wa_branch_info_full_new  ),

  .al_exception        (al_exception        ),
  .al_excpn_type       (al_excpn_type       ),
                                            
  .al_excpn_info       (al_excpn_info       ),
  .al_ifu_err_nxtpg    (al_ifu_err_nxtpg    ),

  .al_iprot_viol       (al_iprot_viol       ),

// Branch Prediction outputs
  .al_is_predicted     (al_is_predicted_int ),  
  .al_prediction       (al_prediction       ),     
  .al_predicted_bta    (al_predicted_bta    ), 
  .al_prediction_type  (al_prediction_type  ), 
  .al_error_branch     (al_error_branch     ),   
  .al_brinfo_full      (al_brinfo_full      ), 
  .al_with_dslot       (al_with_dslot       ),
  .brinfo_tos_index    (al_tosq_indx        ),
// Instruction issue to next stage 
  .brq_holdup         (brq_holdup           ),

  .stall_in           (da_holdup            ),
  .al_pass            (al_pass              ), // Instruction valid
  .al_inst_nxt        (al_inst              ), // Instruction
  .al_limm_nxt        (al_limm              )  // 32-bit LIMM
   );

////////////////////////////////////////////////////////////////////////////////
// Branch Information Buffer
// Branch information from the Branch Prediction Unit(BPU) after aligning to  
// the instruction is stored in this buffer. Branch information is retrieved 
// from the buffer based on the mispredict and commit infomation from the EXU
////////////////////////////////////////////////////////////////////////////////
wire [2:0] al_branch_buf_info;
wire [2:0] mpd_branch_buf_info;
wire [2:0] wa_branch_buf_info;
npuarc_alb_ifu_brinfo_buf ualb_ifu_brinfo_buf
   (
  .clk             (clk                ), // clock input 
  .rst_a           (rst_a              ), // async reset in

  .fch_restart     (fch_restart_int    ), // single pulse Restart from EXU

// Interfac to the alignment output of IFU 
  .br_info_valid   (al_pass            ), // branch info is valid
  .br_info         (al_brinfo_full     ), // branch info 

  .da_holdup       (da_holdup          ), // da_holdup 

  .brq_holdup      (brq_holdup         ), // holdup from branch info buffer 

// To the execute stage
  .br_info_indx    (al_branch_buf_info  ), // branch info (index) to the EXU 

// Interface to mispredict of the Execute Unit
  .mpd_mispredict  (mpd_mispred         ), // indicates a mispredict 
  .mpd_branch_indx (mpd_branch_buf_info ), // index of the mipredict branch from mpd
  .mpd_dslot       (mpd_dslot           ), // indicates delay slot
  .mpd_error_branch (mpd_error_branch   ), // index of the mispredict instruction
  .mpd_branch_info (mpd_branch_info_full), // branch info for the mispredict 
// Interface to commit of the Execute Unit
  .wa_pass         (wa_pass             ), // instruction commit 
  .wa_branch_indx  (wa_branch_buf_info  ), // index of the commit instruction  
  .wa_branch_info  (wa_branch_info_full_pre )  // branch info for the commit instruction 
   );

assign wa_branch_info_full = 
                    wa_branch_info_full_pre;


////////////////////////////////////////////////////////////////////////////////
// TOSQ index and branch info index send out as al_brach_info to EXU
//
assign al_branch_info = {al_tosq_indx,al_branch_buf_info};

////////////////////////////////////////////////////////////////////////////////
// Mispredict branch info from EXU split for TOSQ and Branch Info Buffer
//
assign mpd_branch_buf_info = mpd_branch_info[2:0];

assign mpd_branch_tosq_indx = mpd_branch_info[5: 5- 3+1];

////////////////////////////////////////////////////////////////////////////////
// Commit branch info from EXU split for TOSQ and Branch Info Buffer
//
assign wa_branch_buf_info = wa_branch_info[2:0];

assign wa_branch_tosq_indx = wa_branch_info[5: 5- 3+1];

npuarc_alb_ifu_clk_ctrl alb_ifu_clk_ctrl_u
   (
  .clk      (clk               ),
  .rst_a    (rst_a             ),
  .restart  (exu_fetch_restart ), //single pulse to enable clk2 at restart
  .mem_busy (fetch_mem_busy    ),
  .bist_en  (1'b0              ),
  .clk2_en_r(clk2_en_r         ),
  .clk2     (clk2              )
   );

assign clk2_en = clk2_en_r | (~fetch_mem_busy & exu_fetch_restart);

//assign imem_clk = clk2;

wire clk2_en_bist;

assign clk2_en_bist =  clk2_en; 



wire ic_tag_clk_en0;
// clock gate enable for I$ Tag RAMs
assign ic_tag_clk_en0 = clk2_en_bist & ic_tag_cen0
                       ;



 npuarc_clkgate uic_tag_w0_clkgate (
  .clk_in            (clk),
  .clock_enable      (ic_tag_clk_en0),
  .clk_out           (ic_tag_way0_clk)
);  

wire ic_tag_clk_en1;
// clock gate enable for I$ Tag RAMs
assign ic_tag_clk_en1 = clk2_en_bist & ic_tag_cen1
                       ;



 npuarc_clkgate uic_tag_w1_clkgate (
  .clk_in            (clk),
  .clock_enable      (ic_tag_clk_en1),
  .clk_out           (ic_tag_way1_clk)
);  

wire ic_tag_clk_en2;
// clock gate enable for I$ Tag RAMs
assign ic_tag_clk_en2 = clk2_en_bist & ic_tag_cen2
                       ;



 npuarc_clkgate uic_tag_w2_clkgate (
  .clk_in            (clk),
  .clock_enable      (ic_tag_clk_en2),
  .clk_out           (ic_tag_way2_clk)
);  

wire ic_tag_clk_en3;
// clock gate enable for I$ Tag RAMs
assign ic_tag_clk_en3 = clk2_en_bist & ic_tag_cen3
                       ;



 npuarc_clkgate uic_tag_w3_clkgate (
  .clk_in            (clk),
  .clock_enable      (ic_tag_clk_en3),
  .clk_out           (ic_tag_way3_clk)
);  


wire ic_data_clk_en0;
// clock gate enable for I$ Data RAM0
assign ic_data_clk_en0 = clk2_en_bist & ic_data_cen0
                        ;



npuarc_clkgate uic_data_bank0_clkgate (
  .clk_in            (clk),
  .clock_enable      (ic_data_clk_en0),
  .clk_out           (ic_data_bank0_clk)
);
wire ic_data_clk_en1;
// clock gate enable for I$ Data RAM1
assign ic_data_clk_en1 = clk2_en_bist & ic_data_cen1
                        ;



npuarc_clkgate uic_data_bank1_clkgate (
  .clk_in            (clk),
  .clock_enable      (ic_data_clk_en1),
  .clk_out           (ic_data_bank1_clk)
);



//AUX register blocks

npuarc_alb_bpu_aux alb_bpu_aux_u (
  .clk               (clk),
  .rst_a             (rst_a),

  .aux_read          (aux_read),
  .sr_wdata_r        (aux_wdata),
  .aux_bpu_ren_r     (aux_bpu_ren_r),       //  (X3) Aux Reg Enable
  .aux_bpu_wen_r     (aux_bpu_wen_r),       //  (WA) Aux Reg Enable
  .aux_bpu_raddr_r   (aux_bpu_raddr_r),
  .aux_bpu_waddr_r   (aux_bpu_waddr_r),
  .bpu_aux_rdata     (bpu_aux_rdata),       //  (X3) LR read data
  .bpu_aux_illegal   (bpu_aux_illegal),     //  (X3) SR/LR illegal
  .bpu_aux_k_rd      (bpu_aux_k_rd),        //  (X3) need Kernel Read
  .bpu_aux_k_wr      (bpu_aux_k_wr),        //  (X3) needs Kernel W perm
  .bpu_aux_unimpl    (bpu_aux_unimpl),      //  (X3) Invalid Reg
  .bpu_aux_serial_sr (bpu_aux_serial_sr),   //  (X3) SR group flush pipe
  .bpu_aux_strict_sr (bpu_aux_strict_sr),   //  (X3) SR flush pipe
  .bpu_flush         (bpu_flush),
  .bpu_ctrl          (bpu_ctrl),
  .start_prediction  (start_prediction),
  .bpu_ctrl_2cyc     (bpu_ctrl_2cyc),


  .bpu_flush_ack     (bpu_flush_ack)
);



///////////////////////////////////////////////////////////////////////////////

npuarc_itlb u_itlb (
  ////////// General input signals ///////////////////////////////////////////
  //
  .clk                  (clk),            // Processor clock
  .rst                  (rst_a),          // Global reset
  .rst_init_disable_r   (dbg_cache_rst_disable_r),

  .clk2_en              (clk2_en),
  .mmu_ready            (mmu_ready),

  .mmu_clock_req_r      (1'b0),           // jtlb active
  .utlb_active          (itlb_active),    // itlb/jtlb active

  // Enable uTLB
  .utlb_en_r            (mmu_en_r),       // Enable TLB lookups
  .mpu_en_r             (mpu_en_r),  
  .va_in_transl_range   (va_in_transl_range),

  // cancel look-up when restart process is completing
  .lkup0_cancel         (bpu_fetch_restart),
  .tlb_busy             (mmu_cmd_active),
  .hlt_stall            (hlt_stall),

  .debug_op             (db_active_r),    // op originated from debug


  // Shared lib
  .shared_en_r          (shared_en_r),    // Shared lib enable (PID)
  .sasid_r              (sasid_r),        // Current pid slib membership

  ////////// Interface to translation client(s): fetch or dmp ///////////////
  //
  // Request bus 0 for uTLB lookup ---------------------------------------------
  // late inputs

  .lkup0_valid_r        (itlb_lkup0_valid   ),
  .lkup0_vaddr_r        (itlb_lkup0_vaddr   ),

  .lkup0_asid_r         (asid_r),

  .lkup0_stall_nxt      (itlb_lkup0_stall_nxt),

  // Lookup result 
  .rslt0_valid          (itlb_rslt0_valid),
  .rslt0_valid2         (itlb_rslt0_valid2), // extended to clk2
  .rslt0_accept         (rslt0_accept),
  .rslt0_match          (itlb_rslt0_match),
  .rslt0_multiple_match (itlb_rslt0_multiple_match),
  .rslt0_tlb_err        (itlb_rslt0_ecc_err), // jtlb ecc err

  .rslt0_paddr          (itlb_rslt0_paddr),
  .rslt0_paddr_r        (itlb_rslt0_paddr_r),
  .rslt0_user_attr      (itlb_rslt0_user_attr),
  .rslt0_wr_thru        (itlb_rslt0_wr_thru),
  .rslt0_perm           (itlb_rslt0_perm),
  .rslt0_cached         (itlb_rslt0_cached),

  ////////// Interface to jtlb //////////////////////////////////////////////
  //
  // Consolidated jtlb update request
  .jtlb_update_req      (itlb_update_req),
  .jtlb_update_req_vpn  (itlb_update_req_vpn),

  // jtlb response to update request
  .jrsp_update          (jrsp_itlb_update), 
  .jrsp_update_hit      (jrsp_itlb_update_hit),
  .jrsp_multi_hit       (jrsp_itlb_multi_hit),
  .jrsp_tlb_err         (jrsp_itlb_tlb_err),

  // Entry data for update from jtlb; also used for lookups by jtlb
  .entry_update_data    (jtlb_update_data), // new entry from jtlb
             
  // Inval / insert / update operations from jtlb
  .jtlb_cmd_r           (jtlb_itlb_cmd_r),    // command from jtlb
  .jtlb_index_r         (jtlb_itlb_index_r),  // Index for read/write

  // Interface to read utlb entries
  .entry_rd_val         (itlb_rd_val),   // rd data valid
  .entry_rd_data        (itlb_rd_data)   // LR read data (entry)
);


//////////////////////////////////////////////////////////////////////////////
// Instruction fetch protection
//
npuarc_alb_ifu_iprot u_alb_ifu_iprot (
  .fa_ifp_rgn           (ifetch_chk_addr[31:28]),
  .fa_ifp_viol          (ifetch_iprot_viol),

  .fch_restart_rgn      (fch_target[31:28]),
  .fch_restart          (fch_restart),
  .fch_restart_vec      (fch_restart_vec),

  .fch_iprot_replay     (fch_iprot_replay),
  .wa_ifp_clear_all     (bpu_flush),

  .mmu_en_r             (mmu_en_r),
  .clk                  (clk),
  .rst_a                (rst_a)
);



// Performance monitoring signals
assign   ifu_issue_stall_r   =  (!al_pass) & (!da_holdup);




endmodule
