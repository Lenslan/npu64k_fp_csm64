// Library ARCv2HS-3.5.999999999
///---------------------------------------------------------------------------
///
/// Copyright (C) 2012-2016 Synopsys, Inc. All rights reserved.
///
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary 
/// work of Synopsys, Inc., and is fully protected under copyright and 
/// trade secret laws. You may not view, use, disclose, copy, or distribute 
/// this file or any information contained herein except pursuant to a 
/// valid written license from Synopsys, Inc.
///
/// The entire notice above must be reproduced on all authorized copies.
///
///---------------------------------------------------------------------------

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"


//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }
  
//////////////////////////////////////////////////////////////////////////////80
module npuarc_alb_bpu (

//////////////////////////
// Fetch-restart interface
  input                    fch_restart,           
  // Global pipeline restart signal; 1 => start execution at fch_target

  input fch_restart_vec,
  // indicates if fch_target is an exception vector; 
  // 1=> it is an exception vector
  // 0=> it is not an exception vector
                
  input [`npuarc_PC_RANGE]        fch_target,            
  // absolute target of br, jmp from execution unit
// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ:  unused port range
  input [`npuarc_IM_LINE_BITS:3]  fch_target_successor,  
// leda NTL_CON13C on
// leda NTL_CON37 on
  // carry plus address of the next 64-bit instruction fetch block: 
  // {carry, fch_target_successor[`IM_LINE_BITS-1:3]} 
  //     = target[`IM_LINE_BITS-1:3] + 1;
  // this is calculated early to relieve a critical timing path

  output reg               start_prediction,
  input [2:0]              bpu_ctrl,          // BPU_CTRL AUX register
  input [2:0]              bpu_ctrl_2cyc, 

///////////////////////
// Mispredict interface
// mispredict info from the Execution Unit
  input                    mpd_mispred,           
  // 1 => triggers a mispredict and start of instruction fetch at target

  input                    mpd_direction,         
  // was the branch taken or not taken? 1: taken, 0: not taken

  input [`npuarc_BR_TYPE_RANGE]   mpd_type,              
  // type of the mispredicted branch               
  input [`npuarc_PC_RANGE]        mpd_seq_next_pc,       
  // PC of the instruction sequentially following the branch 
  // and potential delay slot

  input                    mpd_error_branch,       
  // error prediction, need to delete this prediction from branch cache; 
  // also deletes fragged instructions

  input                    mpd_is_predicted,      
  // was a prediction made for this branch?

  input                    mpd_mispred_outcome,   
  // was the direction (taken/not taken) mispredicted?

  input                    mpd_mispred_bta,       
  // was the BTA mispredicted?



  input                    mpd_tail_pc_3,      // Similar to wa_tail_pc_3:
                                                  // Bit 3 of PC-2 of the instruction following branch
                                                  // or delay slot, indicating the fetch block where the
                                                  // tail of the instruction is located

  input                    mpd_dslot,          // similar to wa_dslot
  input [`npuarc_ISIZE_RANGE]     mpd_commit_size,    // Similar to wa_commit_size: Size of branch

  input                    mpd_secondary,
       // Similar to wa_secondary: Indicates if this instruction can be a secondary branch
// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ:  unused port or some addr bits not used 
  input [`npuarc_PC_RANGE]        mpd_pc,            // Similar to wa_pc: PC of the branch instruction
// spyglass disable_block W240
// SMD: input declared but not read
// SJ:  no functional issue and removal requires modification of many files at end of release
  input                    mpd_early,  
// spyglass enable_block W240
// leda NTL_CON13C on
// leda NTL_CON37 on
      // indicates if a mispredict is early (in the X2 stage) or late (in the WB stage).
      // 0: mispredict is late
      // 1: mispredict is early

//////////////////////////
// Branch commit interface
// commit info from the Execution Unit about committed branches

  input                    wa_pass,              
  // Request to commit a branch to IFU

  input [`npuarc_BR_TYPE_RANGE]   wa_type,              
  // prediction type, like al_prediction_type               

  input                    wa_secondary,
  // Indicates if this instruction can be a secondary branch
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  unused port or some addr bits not used 
  input [`npuarc_PC_RANGE]        wa_pc,                
  // pc of the branch that is committed
// leda NTL_CON13C on
  input                    wa_tail_pc_3,         
  // bit 3 of PC-2 of the instruction following branch or delay slot 
  // instruction, 
  // indicating the fetch block where the tail of the instruction is

  input                    wa_dslot,             
  // does this branch instruction have a delay slot?

  input [`npuarc_PC_RANGE]        wa_target,            
  // branch target address of the branch/jump that is committed

//  input [`PC_RANGE]        wa_seq_next_pc,       
  // PC of the instruction sequentially following the branch 
  // and potential delay slot

  input [`npuarc_ISIZE_RANGE] wa_commit_size,       
  // size of the branch instruction plus optional delay slot instruction 
  // (multiple of 16 bit): 1, 2, 3 or 4 half-words
  // encoded as wa_size=size-1, 
  // so wa_size==0 indicates instruction size is 1 half-word, etc.

  input                    wa_direction,         
  // was the branch taken or not taken? 1: taken, 0: not taken

  input                    wa_error_branch,      
  // error prediction, need to delete this prediction from branch cache; 
  // also deletes fragged instructions

  input                    wa_is_predicted,       
  // was a prediction made for this branch?

  input                    wa_mispred_outcome,   
  // was the direction (taken/not taken) mispredicted?

  input                    wa_commit_mispred_bta,       
  // was the BTA mispredicted?

// issue interface
  input                    al_pass,

//////////////////////////////////////////////////////////////////////////////80
////////////////
// AUX registers
// The following are interfaces to the BPU AUX registers from the IFU AUX 
// register module.
// Protocol: assert bpu_read or bpu_write with all other inputs stable until 
// bpu_aux_ack is asserted.

  input bpu_flush, // flush and initialize branch predictor
  output reg bpu_flush_ack, // handshake signal

  // bpu_init_r indicates that the BPU is busy with initialization or flush.
  // During this time debug instructions need to be disabled.
  // We do this by turning ifu_idle_r off when bpu_init_r is asserted.
  output reg       bpu_init_r, 
                
  // performance counters
  output reg cycle2_r,

  ///////// Interface to Branch predictor RAM banks
  // Gshare predictor.
  // Branch predictor RAMs have individual bit write enables, 
  // wem (write enable mask).

  output reg [`npuarc_BR_BC_DATA_RANGE]  bc_din0,
  output reg [`npuarc_BR_BC_IDX_RANGE]    bc_addr0,
  output reg                bc_me0,
  output reg                bc_we0,
  output reg [`npuarc_BR_BC_DATA_RANGE]  bc_wem0,
  input  [`npuarc_BR_BC_DATA_RANGE]  bc_dout0,

  output reg [`npuarc_BR_BC_DATA_RANGE]  bc_din1,
  output reg [`npuarc_BR_BC_IDX_RANGE]    bc_addr1,
  output reg                bc_me1,
  output reg                bc_we1,
  output reg [`npuarc_BR_BC_DATA_RANGE]  bc_wem1,
  input  [`npuarc_BR_BC_DATA_RANGE]  bc_dout1,

//output reg [7:0]       gs_din0,
  output reg [`npuarc_BR_PT_DATA_RANGE]   gs_din0,
  output reg [`npuarc_BR_PT_RANGE] gs_addr0,
  output reg             gs_me0,
  output reg             gs_we0,
//output reg [7:0]       gs_wem0,
  output reg [`npuarc_BR_PT_DATA_RANGE]   gs_wem0,
//input  [7:0]       gs_dout0,
  input  [`npuarc_BR_PT_DATA_RANGE]       gs_dout0,

//output reg [7:0]                 gs_din1,
  output reg [`npuarc_BR_PT_DATA_RANGE]   gs_din1,
  output reg [`npuarc_BR_PT_RANGE] gs_addr1,
  output reg             gs_me1,
  output reg             gs_we1,
//output reg [7:0]       gs_wem1,
  output reg [`npuarc_BR_PT_DATA_RANGE]   gs_wem1,
//input  [7:0]       gs_dout1,
  input  [`npuarc_BR_PT_DATA_RANGE]       gs_dout1,

// gated clocks for BPU RAMs
  output bc_ram0_clk,
  output bc_ram1_clk,
  output pt_ram0_clk,
  output pt_ram1_clk,

// gated clock enables for BPU RAMs
  output bc_ram0_clk_en,
  output bc_ram1_clk_en,
  output pt_ram0_clk_en,
  output pt_ram1_clk_en,

/////////////////////////////////////////////////////////////////////////////
// interface with instruction memory, icache or ICCM

// handshake
  output reg mem_req, // start a memory access
  input mem_busy, // indicator from the Icache/ICCM that it cannot accept an access now.

// fetch control signals
  output reg restart, // a restart occurred, so flush the pipeline
  output reg unaligned_out, // 1: the 128-bit fetch block starts in bank 1; 0: the 128-bit fetch block starts in bank 0
  output reg kill_2nd, // skip the 2nd fetch block that is being fetched in the current fetch cycle.
// the signals fetch0 and fetch1 determine if 1 or 2 banks are used and which
  output reg fetch0, // 1: enable a fetch from bank0 at address fa0; 0: disable fetch from bank0
  output reg fetch1, // 1: enable a fetch from bank1 at address fa1; 0: disable fetch from bank1

// addresses
  output reg [`npuarc_PC_RANGE] fa0_out,  // Full fetch address for bank 0, including BTA offset 
  output reg [`npuarc_IM_LINE_BITS-1:4] fa1_out_diff, // fetch address for bank 1, only the bits that are different from fa0

// selection between Icache, IFQUEUE, ICCM0 and ICCM1

// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ:  unused port range

// leda NTL_CON13C on
// leda NTL_CON37 on

   output fetch_icache,

// way prediction
  output reg [`npuarc_IC_WAYS_BITS_RANGE] way_pred_gated, // Predicted way of the fetch, not valid when fetch_tail_r
  output reg way_valid_out,            // way prediction is valid; fast timing excludes mpd_mispred case
  output reg way_valid_detect,

  output reg way_sec,              // is the way pred for a secondary branch?
  output reg way_seq,              // sequential access; turn tags off
  output reg way_req,              // request to provide way prediction when way_valid=0

  // Branch cache input port for icache to set way prediction
  input wr_way,            // Write control for way prediction
  input [`npuarc_IC_WAYS_BITS_RANGE] way_in, // Predicted way of the fetch
  input way_in_sec,                   // Is the way for a secondary branch?
  input [`npuarc_BR_BC_IDX_RANGE] way_index, // Branch cache index for the way
  input way_bank, // Bank for the way

 
// BTA miss handling
  output reg bta_miss,
  output reg [`npuarc_BR_INFO_OFFSET_RANGE] bta_offset_out,
  input [`npuarc_PC_RANGE] bta_displ,
  input bta_displ_valid,
           
// address input from Icache/ICCM control
//  input fa_misc_sel, // select the misc address in the address mux
//  input [`PC_RANGE] fa_misc, // Miscellaneous address for bus and aux access

// info attached to fetch blocks
  output reg [`npuarc_BR_FB_INFO_RANGE] branch_info_fb_out, // branch prediction related info that needs to be attached to the fetch block with the branch
  output reg write_tosq_r, // TOS queue control
  output [`npuarc_BR_BC_BTA_RANGE] top_of_stack, // TOS

// only for branches predicted taken
  output reg taken_out, // indicates if the current prediction has a taken branch
  output reg [`npuarc_BR_INFO_OFFSET_RANGE] offset_out, // the offset of the branch instruction in the fetch block; can be 128 bits
  output reg [`npuarc_BR_BC_BTA_RANGE] bta_pred_out, // the BTA of the predicted taken branch
  output reg bta_valid, // indicates if bta_pred is valid; will be delayed in case of BTA miss
  output reg fetch_tail, // indicates that the next fetch is the tail of the current branch instruction

// interface with predicted branch queue
  input [`npuarc_BR_FULL_INFO_RANGE]   mispredict_branch_info,   // fully expanded branch_info from mpd_branch_info
  input [`npuarc_BR_FULL_INFO_RANGE]   commit_branch_info,       // fully expanded branch_info from wa_branch_info



// global signals
  input clk,
  input rst_a

);

// spyglass disable_block Ar_converge02
// SMD: Reset signal converge on reset and data pins
// SJ:  Reset convergence does not cause any functional issue

  reg restart_captured_r;
  reg restart_captured_next;

  reg [`npuarc_BR_INFO_OFFSET_RANGE] bta_offset;
  reg [`npuarc_BR_FB_INFO_RANGE] branch_info_fb; 
  reg taken;
  reg [`npuarc_BR_INFO_OFFSET_RANGE] offset; 
  reg [`npuarc_BR_BC_BTA_RANGE] bta_pred;
  reg fetch_tail_r_2cyc;
  reg fetch_tail_next_2cyc;
  wire fetch_tail_r;

// way prediction
  reg [`npuarc_IC_WAYS_BITS_RANGE] way_pred; // Predicted way of the fetch

always @*
begin: bpu_suppr_PROC
  if (restart_captured_r || fetch_tail_r)
  begin
    bta_offset_out = `npuarc_BR_INFO_OFFSET_SIZE'b0;
    branch_info_fb_out = {`npuarc_BR_FB_INFO_SIZE{1'b0}}; 
    taken_out = 1'b0;
    offset_out = `npuarc_BR_INFO_OFFSET_SIZE'b0; 
  end
  else
  begin
    bta_offset_out = bta_offset;
    branch_info_fb_out = branch_info_fb; 
    taken_out = taken;
    offset_out = offset; 
  end
end

always @*
begin: bpu_suppr_bta_PROC
  if (restart_captured_r )
  begin
    bta_pred_out = {`npuarc_BR_BC_BTA_SIZE{1'b0}};
  end
  else
  begin
    bta_pred_out = bta_pred;
  end
end


always @*
begin: bpu_way_pred_PROC
  way_pred_gated = way_pred;
end


  
///////////////////////////
// State Encoding of BPU state machine
  parameter RESET                = 4'd0;
  parameter INIT                 = 4'd1;
  parameter BTA_MISS1            = 4'd2;
  parameter START                = 4'd3;

// states that assert mem_req; group together with a separate state bit
  parameter TAIL_WAIT            = 4'd4;
  parameter BTA_MISS_TAIL_WAIT   = 4'd5;
  parameter BTA_MISS2            = 4'd6;

// state that asserts select_restart
// use a single state bit to make it very fast
  parameter PREDICT              = 4'd8;

// End of state encoding
/////////

///////////////
// Registers //
///////////////  
///////////////////
// 2-cycle registes
// These are registers that start a 2-cycle path

// 2-cycle timing checkers
// All multi cycle paths are checked with alb_2cyc_checker modules.


// pipeline registers
// leda NTL_STR76 off
// LMD: A non-tristate net can have only one non-tristate driver
// LJ: The 2-cycle checkers use forces on wires


  reg [`npuarc_BR_BC_BTA_MSB:`npuarc_IM_LINE_BITS] fa_high_r_2cyc;
  wire [`npuarc_BR_BC_BTA_MSB:`npuarc_IM_LINE_BITS] fa_high_r;
//reg [1:0]    fa_offset_r_2cyc;
  reg [`npuarc_BR_OFFSET_RANGE]    fa_offset_r_2cyc; 
//wire [1:0]    fa_offset_r;
  wire [`npuarc_BR_OFFSET_RANGE]    fa_offset_r;   
  reg [`npuarc_BR_FA_DIFF_RANGE]   fa0_diff_r_2cyc;
  wire [`npuarc_BR_FA_DIFF_RANGE]  fa0_diff_r;
  reg [`npuarc_BR_FA_DIFF_RANGE]   fa1_diff_r_2cyc;
  wire [`npuarc_BR_FA_DIFF_RANGE]  fa1_diff_r;
  reg unaligned_r_2cyc;
  wire unaligned_r;
  reg cross_line_r_2cyc;
  wire cross_line_r;
  reg restart_vec_r_2cyc;
  wire restart_vec_next_2cyc;
  wire restart_vec_r;

  wire start_init_force_r;
  reg start_init_force_r_2cyc;
  wire start_init_force_next_2cyc;

// GHR
  reg [`npuarc_BR_PT_RANGE] ghr_r;
  // path from ghr_r to ghr_r, bc_ram, pt_ram, icache/iccm is a 2-cycle path
  // path from input to ghr_r is a single cycle path


  reg bta_bank_r_2cyc;
  wire bta_bank_r;
  reg bta_offset_r_2cyc;
  wire bta_offset_r;
  reg [`npuarc_IC_WAYS_BITS_RANGE] bta_miss_way_r;
  reg bta_miss_way_valid_r;
// BPU Bypass buffer
// The bypass path from the bypass buffer to the BPU logic is a 2-cycle path
  wire                      byp_full_r;
  wire                      byp_clear_secondary_r;
  wire                      byp_set_primary_r;
  wire                      byp_bank_r;
  wire [`npuarc_BR_BC_IDX_RANGE]   byp_index_r;
  wire [`npuarc_BR_BC_TAG_RANGE]   byp_tag_r; 
  wire [`npuarc_BR_OFFSET_RANGE]   byp_offset_r;
  wire [`npuarc_BR_TYPE_RANGE]     byp_type_r;
  wire [`npuarc_BR_BC_BTA_RANGE]   byp_bta_r;
  wire [1:0]                byp_size_r;
  wire                      byp_d_bit_r;
  wire                      byp_f_bit_r;
  
  reg                       byp_clear_secondary_r_2cyc;
  reg                       byp_set_primary_r_2cyc;
  reg                       byp_bank_r_2cyc;
  reg                       byp_full_r_2cyc;
  reg [`npuarc_BR_BC_IDX_RANGE]    byp_index_r_2cyc;
  reg [`npuarc_BR_BC_TAG_RANGE]    byp_tag_r_2cyc; 
  reg [`npuarc_BR_OFFSET_RANGE]    byp_offset_r_2cyc;
  reg [`npuarc_BR_TYPE_RANGE]      byp_type_r_2cyc;
  reg [`npuarc_BR_BC_BTA_RANGE]    byp_bta_r_2cyc;
  reg [1:0]                 byp_size_r_2cyc;
  reg                       byp_d_bit_r_2cyc;
  reg                       byp_f_bit_r_2cyc;

  reg                       byp_full_next_2cyc;
  reg                       byp_set_primary_next_2cyc;
  reg                       byp_clear_secondary_next_2cyc;
  reg [`npuarc_BR_TYPE_RANGE]      byp_type_next_2cyc;
  reg                       byp_bank_next_2cyc;
  reg [`npuarc_BR_BC_IDX_RANGE]    byp_index_next_2cyc;
  reg [`npuarc_BR_BC_TAG_RANGE]    byp_tag_next_2cyc; 
  reg [`npuarc_BR_OFFSET_RANGE]    byp_offset_next_2cyc;
  reg [`npuarc_BR_BC_BTA_RANGE]    byp_bta_next_2cyc; 
  reg                       byp_f_bit_next_2cyc;
  reg [1:0]                 byp_size_next_2cyc;
  reg                       byp_d_bit_next_2cyc;

  wire [`npuarc_BR_RS_RANGE] stack_ptr_r;

// Stack registers
// The top_of_stack and stack_ptr_r are 2-cycle registers located in the stack module

// leda NTL_STR76 on  
// end of 2-cycle registers
////////////////////////////
  
// single cycle registers
// Registers for which the output may be used in the next cycle.
 
  // priority register 
  reg bc_needed_r;

  // capture registers
//  reg [`PC_RANGE] target_r;
  reg [`npuarc_BR_BC_BTA_RANGE] target_r;
  reg [`npuarc_BR_BC_BTA_RANGE] target_next;
  reg fch_restart_vec_r;
  reg fch_restart_vec_next;
  reg captured_r;
  reg capture_not_taken_r;
  reg ghr_captured_r;
  reg start_prediction_r;

  wire cycle2_next;
  reg captured_next;
  reg capture_not_taken_next;
  reg ghr_captured_next;

  // state register
  reg [3:0] state_r;
  wire[3:0] state_nxt;
  reg [3:0] state_next;

  reg       bpu_init_next;

  // way prediction
  reg [`npuarc_IC_WAYS_BITS_RANGE] captured_way_r;
  reg                       captured_way_valid_r;
  reg                       captured_way_sec_r;
  reg                       captured_way_req_r;
  reg                       way_req_r;
  // way queue
  reg                       wayq_full_r;
  reg [`npuarc_IC_WAYS_BITS_RANGE] way_in_r;
  reg                       way_in_sec_r;
  reg [`npuarc_BR_BC_IDX_RANGE]    way_index_r;
  reg                       way_bank_r;

  reg                       way_req_response;
  reg                       way_byp_full_r;
  reg                       way_byp_full_r_r;
  reg [`npuarc_IC_WAYS_BITS_RANGE] way_byp_in_r;

  reg                       way_is_valid;
  reg                       way_is_valid0;
  reg                       way_is_valid1;
  reg                       secondary_way_is_valid0;
  reg                       secondary_way_is_valid1;
  reg                       way_valid;          // way prediction is valid

  reg [`npuarc_IC_WAYS_BITS_RANGE] captured_way_next;
  reg                       captured_way_valid_next;
  reg                       captured_way_sec_next;
  reg                       captured_way_req_next;

  reg                       way_req_next;
  reg                       wayq_full_next;
  reg                       way_byp_full_next;
  reg                       way_byp_full_r_next;

// BC write buffer
  reg                          bwq_clear_secondary_r;
  reg                          bwq_set_primary_r;
  reg                          bwq_full_r;
  reg                          bwq_high_priority_r;
  reg                          al_pass_r;
  reg                          bwq_bank_r;
  reg [`npuarc_BR_BC_IDX_RANGE]       bwq_index_r;
  reg [`npuarc_BR_BC_TAG_RANGE]       bwq_tag_r; 
  reg [`npuarc_BR_OFFSET_RANGE]       bwq_offset_r;
  reg [`npuarc_BR_TYPE_RANGE]         bwq_type_r;
  reg [`npuarc_BR_BC_BTA_RANGE]       bwq_bta_r;
  reg [1:0]                    bwq_size_r;
  reg                          bwq_d_bit_r;
  reg                          bwq_f_bit_r;

  reg                          bwq_clear_secondary_next;
  reg                          bwq_set_primary_next;
  reg                          bwq_full_next;
  reg                          bwq_high_priority_next;
  reg                          al_pass_next;
  reg                          bwq_bank_next;
  reg [`npuarc_BR_BC_IDX_RANGE]       bwq_index_next;
  reg [`npuarc_BR_BC_TAG_RANGE]       bwq_tag_next;
  reg [`npuarc_BR_OFFSET_RANGE]       bwq_offset_next;
  reg [`npuarc_BR_TYPE_RANGE]         bwq_type_next;
  reg [`npuarc_BR_BC_BTA_RANGE]       bwq_bta_next;
  reg [1:0]                    bwq_size_next;
  reg                          bwq_d_bit_next;
  reg                          bwq_f_bit_next;

  // write_tosq registers
  reg write_tosq0_r;

// end register declarations
/////////////////////////////

//////////////////////////////////
  // Combinatorial 2-cycle signals
  reg select_bta_miss_2cyc;
  wire select_bta_miss_next_2cyc;
  wire select_bta_miss;

  reg                      byp0_hit;
  reg                      byp1_hit;

  reg write_tosq;
  reg restart_vec;
  reg capture_not_taken;
  reg capture_bta_miss;
  reg bta_delayed_valid;
  wire allow_bta_miss;
  reg unaligned;
  reg cross_line_out;
  reg [`npuarc_IC_WAYS_BITS_RANGE] bta_miss_way;
  reg                       bta_miss_way_valid;
  reg                       way_req_detect;
  reg                       bta_miss_detected;



  reg brtype_cond; // the type of the predicted branch instruction if it is a primary branch

  reg [`npuarc_BR_BC_BTA_RANGE] fa_seq;
  reg [`npuarc_PC_MSB:3] fa_p;

  reg [`npuarc_BR_BC_TAG_RANGE] fa0_tag;
  reg [`npuarc_BR_BC_TAG_RANGE] fa1_tag;
// leda NTL_CON13A off
// LMD: non driving internal net Range
// LJ:  Used in some configs and assertion
  reg select_bta_pred;
// leda NTL_CON13A on

  reg select_restart;
  reg select_seq;
  reg [`npuarc_BR_BC_BTA_RANGE] fa;
  reg [`npuarc_BR_BC_BTA_RANGE] fa_out;
  reg fa_seq_carry;
  reg [`npuarc_BR_BC_BTA_MSB:`npuarc_IM_LINE_BITS] fa_high;
//reg [1:0] fa_offset;
  reg [`npuarc_BR_OFFSET_RANGE] fa_offset;
//  reg [`IM_LINE_BITS-1:4] fa0_diff;
  reg [`npuarc_BR_FA_DIFF_RANGE] fa0_diff;
  reg [`npuarc_BR_BC_BTA_MSB:`npuarc_IM_LINE_BITS] fa_out_high;
//reg [1:0] fa_out_offset;
  reg [`npuarc_BR_OFFSET_RANGE] fa_out_offset;
  reg [`npuarc_IM_LINE_BITS-1:4] fa0_out_diff;
//  reg [`BR_FA_DIFF_RANGE] fa0_out_diff;
// leda NTL_CON12A off
// leda NTL_CON13A off
// LMD: undriven internal net Ranges
// LJ:  every bit has been driven
  reg [`npuarc_PC_RANGE] fa0;
  reg [`npuarc_PC_RANGE] fa1;
// leda NTL_CON12A on
// leda NTL_CON13A on
//  reg [`PC_RANGE] fa1_out;
//  reg [`IM_LINE_BITS-1:4] fa1_diff;
  reg [`npuarc_BR_FA_DIFF_RANGE] fa1_diff;
// leda NTL_CON12A off
// leda NTL_CON13A off
// LMD: undriven internal net Ranges
// LJ:  every bit has been driven
  reg [`npuarc_IM_LINE_BITS:3]  fa_succ;
  reg [`npuarc_IM_LINE_BITS:3]  fa_out_succ;
// leda NTL_CON12A on  
// leda NTL_CON13A on  
  reg [`npuarc_IM_LINE_BITS:3] bta_pred_succ;
  reg cross_line;
  reg [`npuarc_BR_BC_IDX_RANGE] bc_addr0_pre;
  reg [`npuarc_BR_BC_IDX_RANGE] bc_addr1_pre;
  reg [`npuarc_BR_PT_RANGE] gs_addr0_pre;
  reg [`npuarc_BR_PT_RANGE] gs_addr1_pre;
  reg [`npuarc_BR_BC_BTA_MSB:3] fa0_p;
  reg [`npuarc_BR_BC_BTA_MSB:3] fa1_p;
 
  reg [`npuarc_BR_TYPE_RANGE] type0;
//reg [1:0] offset0; 
  reg [`npuarc_BR_OFFSET_RANGE] offset0; 
  reg [`npuarc_BR_BC_TAG_RANGE] tag0; 
  reg [`npuarc_BR_BC_TAG_RANGE] tag0_sec; 
  reg [`npuarc_BR_BC_BTA_RANGE] bta0; 
  reg [`npuarc_PC_RANGE] bta0_full; 
  reg d_bit0;
  reg br_d_bit0;
  reg br_d_bit1;
  reg f_bit0;
  reg br_f_bit0;
  reg br_f_bit1;
  reg [`npuarc_BR_TYPE_RANGE] type1;
  reg [`npuarc_BR_TYPE_RANGE] br_type0;
  reg [`npuarc_BR_TYPE_RANGE] br_type1;
//reg [1:0] offset1;
  reg [`npuarc_BR_OFFSET_RANGE] offset1;
  reg [`npuarc_BR_BC_TAG_RANGE] tag1; 
  reg [`npuarc_BR_BC_TAG_RANGE] tag1_sec; 
  reg [`npuarc_BR_BC_BTA_RANGE] bta1;
  reg [`npuarc_PC_RANGE] bta1_full;
  reg d_bit1;
  reg f_bit1;
  reg bank;
  reg br_primary_strength0;
  reg br_primary_strength1;
  reg br_secondary_strength0;
  reg br_secondary_strength1;
//reg [1:0] br_offset0;
  reg [`npuarc_BR_OFFSET_RANGE] br_offset0;
//reg [1:0] br_offset1;
  reg [`npuarc_BR_OFFSET_RANGE] br_offset1;
  reg [`npuarc_IM_LINE_BITS:3] bta_succ0;
  reg [`npuarc_IM_LINE_BITS:3] bta_succ1;
//reg [7:0] gshare0;
  reg [`npuarc_BR_PT_DATA_RANGE] gshare0;
//reg [7:0] gshare1;
  reg [`npuarc_BR_PT_DATA_RANGE] gshare1;
// leda NTL_CON13A off
// LMD: non driving internal net Range
// LJ:  Not all bits of bus used
  reg [`npuarc_IC_WAYS_BITS_RANGE] secondary_way0;
  reg [`npuarc_IC_WAYS_BITS_RANGE] secondary_way1;
// leda NTL_CON13A on
  reg                       secondary_f_bit0;
  reg                       secondary_f_bit1;
  reg [`npuarc_IC_WAYS_BITS_RANGE] br_secondary_way0;
  reg [`npuarc_IC_WAYS_BITS_RANGE] br_secondary_way1;
  reg [`npuarc_IC_WAYS_BITS_RANGE] br_primary_way0;
  reg [`npuarc_IC_WAYS_BITS_RANGE] br_primary_way1;  

  reg                       br_secondary_taken0;
  reg                       br_secondary_taken1;
  reg                       br_secondary_valid0;
  reg                       br_secondary_valid1;
  reg                       br_secondary_f_bit0;
  reg                       br_secondary_f_bit1;
  reg [`npuarc_BR_OFFSET_RANGE]    br_secondary_offset0;
  reg [`npuarc_BR_OFFSET_RANGE]    br_secondary_offset1;


//reg [3:0] predict_taken_vec0;
  reg [`npuarc_BR_PT_PRED_VEC_RANGE] predict_taken_vec0;
//reg [3:0] predict_taken_vec1;
  reg [`npuarc_BR_PT_PRED_VEC_RANGE] predict_taken_vec1;
  reg       prediction0;
  reg       sec_prediction0;
  reg       prediction1;
  reg       sec_prediction1;
//reg [3:0] strength_vec0;
  reg [`npuarc_BR_PT_PRED_VEC_RANGE] strength_vec0;
//reg [3:0] strength_vec1;
  reg [`npuarc_BR_PT_PRED_VEC_RANGE] strength_vec1;

  reg tag0_hit;
  reg tag1_hit;
  reg tag0_sec_hit;
  reg tag1_sec_hit;

//reg [1:0] secondary_offset0;
  reg [`npuarc_BR_OFFSET_RANGE] secondary_offset0;
//reg [1:0] secondary_offset1;
  reg [`npuarc_BR_OFFSET_RANGE] secondary_offset1;
  reg       secondary_valid0;
  reg       secondary_valid1;
  reg       nt4;
  reg       nt2_0;
  reg       nt2_1;
  

  reg       valid0;
  reg       valid1;
//  reg conditional0;
  reg unconditional0;
  reg subcall0;
  reg subreturn0;
 // reg conditional1;
  reg unconditional1;
  reg subcall1;
  reg subreturn1;
  reg subreturn;
  reg subcall;

  reg primary_valid0;
  reg primary_predict_taken0;
  reg primary_taken0;
  reg primary_not_taken0;
  reg secondary_vld0;
  reg secondary_predict_taken0;
  reg secondary_taken0;
  reg secondary_not_taken0;
  reg secondary_smaller0;
  reg secondary_nt_smaller0;
  reg primary_nt_smaller0;

  reg primary_valid1;
  reg primary_predict_taken1;
  reg primary_taken1;
  reg primary_not_taken1;
  reg secondary_vld1;
  reg secondary_predict_taken1;
  reg secondary_taken1;
  reg secondary_not_taken1;
  reg secondary_smaller1;
  reg secondary_nt_smaller1;
  reg primary_nt_smaller1;

  reg taken0;
  reg taken1; 
  reg any_taken0;
  reg any_taken1; 
  reg br_taken0;
  reg br_taken1;
  reg primary_strength0;
  reg primary_strength1;
  reg secondary_strength0;
  reg secondary_strength1;
  reg bta_miss0;
  reg bta_miss1;

//reg [1:0] num_nt;
  reg [1:0] num_nt;

  reg [`npuarc_BR_PT_RANGE] ghr_next;
  reg [`npuarc_BR_PT_RANGE] ghr_restore;
  reg [`npuarc_BR_PT_RANGE] ghr_pred;
  reg [`npuarc_BR_PT_RANGE] ghr_new;

  reg detect_fetch_tail;

  reg capture_bta;
  reg release_capture;
  reg bc_needed;
  reg cycle_steal;

  reg select_captured_target;

  reg mp_alt_way_valid; 
  reg [`npuarc_IC_WAYS_BITS_RANGE] mp_alt_way;
  reg                      mp_way_sec;


  reg [`npuarc_PC_RANGE] mp_tos;
  reg [`npuarc_BR_RS_RANGE] mp_tosp;
  reg [1:0] mp_num_nt;
  reg [`npuarc_BR_PT_RANGE] mp_ghr;
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  upper guard bit unused in this implementation
  reg mp_c;
  reg cm_alt_way_valid; 
  reg [`npuarc_IC_WAYS_BITS_RANGE] cm_alt_way;
  reg                      cm_way_sec;
  reg unused_carry0;
  reg unused_carry1;
  reg unused_carry2;
  reg unused_carry3;
  reg unused_carry4;
  reg unused_carry5;
  reg unused_carry6;
//  reg [1:0] fa_succ_carry; 
//  reg fa0_diff_carry; 
//  reg fa1_diff_carry; 

// leda NTL_CON13A on
//reg [1:0] mp_primary_offset;
  reg [`npuarc_BR_OFFSET_RANGE] mp_primary_offset;
  reg       mp_primary_valid;

  reg [`npuarc_BR_BC_BTA_RANGE] cm_tos ;
  reg [`npuarc_BR_RS_RANGE] cm_tosp;
  reg [1:0] cm_num_nt;
  reg [`npuarc_BR_PT_RANGE] cm_ghr;
  reg                cm_c_in;
  reg cm_c;
  reg cm_p;
//reg [1:0] cm_primary_offset;
  reg [`npuarc_BR_OFFSET_RANGE] cm_primary_offset;
  reg       cm_primary_valid;
  reg[`npuarc_BR_TYPE_RANGE] cm_type;
  reg                 cm_f_bit;
  reg cm_bank;
//reg [1:0] cm_offset;
  reg [`npuarc_BR_OFFSET_RANGE] cm_offset; 
  reg [`npuarc_BR_PT_RANGE] ghr_restart;

  reg clear_secondary;
  reg set_primary;
  reg primary_match;
  reg mp_primary_match;
  reg mp_uncond;

  reg [`npuarc_BR_PTQ_DATA_RANGE] wq0_din;
  wire [`npuarc_BR_PTQ_DATA_RANGE] wq0_dout;
  reg wq0_write;
  wire wq0_full;
  reg wq0_read;
  wire wq0_empty;
  wire wq0_high_priority;

  reg [`npuarc_BR_PTQ_DATA_RANGE] wq1_din;
  wire [`npuarc_BR_PTQ_DATA_RANGE] wq1_dout;
  reg wq1_write;
  wire wq1_full;
  reg wq1_read;
  wire wq1_empty;
  wire wq1_high_priority;

  reg [1:0] wq0_pred;
  reg [`npuarc_BR_PT_RANGE] wq0_index;
//reg [1:0] wq0_offset;
  reg [`npuarc_BR_OFFSET_RANGE] wq0_offset;

  reg [1:0] wq1_pred;
  reg [`npuarc_BR_PT_RANGE] wq1_index;
//reg [1:0] wq1_offset;
  reg [`npuarc_BR_OFFSET_RANGE] wq1_offset; 

  reg bwq_write;
  reg bwq_read;
  reg wayq_read;
  reg [`npuarc_BR_BC_DATA_RANGE] bc_entry;
 // reg [`BR_BC_DATA_RANGE] set_primary_wem;
//  reg [`BR_BC_DATA_RANGE] set_secondary_wem;
 // reg [`BR_BC_DATA_RANGE] set_primary_way_wem;
  //reg [`BR_BC_DATA_RANGE] set_secondary_way_wem;

  reg init_finished;
  reg start_init_force;
// leda NTL_CON13A off
// LMD: non driving internal net Range
// LJ:  Not all bits of bus used
  reg [`npuarc_IC_WAYS_BITS_RANGE] way0;
  reg [`npuarc_IC_WAYS_BITS_RANGE] way1;
// leda NTL_CON13A on
  reg [1:0] size0;
  reg [1:0] size1;

  reg init;
  reg bpu_wctl;

  reg write_tos;
  reg write_tosp;
  reg push_tosp;
  reg pop_tosp;
  reg [`npuarc_BR_RS_RANGE] tosp_new;
  reg [`npuarc_BR_BC_BTA_RANGE] tos_new;
  reg [`npuarc_IM_LINE_BITS:3] top_of_stack_succ;
  reg prediction_used;
  reg [`npuarc_BR_BC_BTA_RANGE] sub_tos;
  reg sub_carry;
  reg [1:0] size_pred;
 
  reg force_strong_2cyc;
  reg bc_freeze;
  reg bc_disable;
  reg bc_disable_2cyc;
  reg ghr_freeze;
  reg pt_freeze;
  reg pt_no_new;
  reg stack_freeze;

// Register the BPU RAMs output 
// BPU memories are accessed on alternate core clock cycles. The data output from the memory used on the second clock after the memory access 
// The register here captures the data on the first clock after the memory access, and makes the data available for use on the second cycle
// The signal used for capturing, cycle2_r, goes high for 1 cycle after a BPU memory access and is used to capture the data
// No reset needed as this register captures only the data
//
reg  bc_dout0_en;
reg  bc_dout1_en;
reg  gs_dout0_en;
reg  gs_dout1_en;

reg [`npuarc_BR_BC_DATA_RANGE] bc_dout0_r;
reg [`npuarc_BR_BC_DATA_RANGE] bc_dout1_r;
reg [`npuarc_BR_PT_DATA_RANGE] gs_dout0_r;
reg [`npuarc_BR_PT_DATA_RANGE] gs_dout1_r;
// spyglass disable_block Ar_resetcross01 STARC-2.3.4.3
// SMD: unsynchronized reset crossing between flops in data path
// SJ:  Done on purpose, causes no issues, no resets required for these regs
always @(posedge clk )
begin: bpu_bc0_ram_reg_PROC
  if (cycle2_r && bc_dout0_en) begin
     bc_dout0_r <= bc_dout0;
  end
end

always @(posedge clk )
begin: bpu_bc1_ram_reg_PROC
  if (cycle2_r && bc_dout1_en) begin
     bc_dout1_r <= bc_dout1;
  end
end

always @(posedge clk )
begin: bpu_gs0_ram_reg_PROC
  if (cycle2_r & gs_dout0_en) begin
     gs_dout0_r <= gs_dout0;
  end
end

always @(posedge clk )
begin: bpu_gs1_ram_reg_PROC
  if (cycle2_r & gs_dout1_en) begin
     gs_dout1_r <= gs_dout1;
  end
end

always @(posedge clk or posedge rst_a)
begin: bpu_ram_en_reg_PROC
  if (rst_a == 1'b1) begin
    bc_dout0_en <= 1'b0;
    bc_dout1_en <= 1'b0;
    gs_dout0_en <= 1'b0;
    gs_dout1_en <= 1'b0;
  end
  else begin
    bc_dout0_en <= (bc_me0 & !bc_we0);
    bc_dout1_en <= (bc_me1 & !bc_we1);
    gs_dout0_en <= (gs_me0 & !gs_we0);
    gs_dout1_en <= (gs_me1 & !gs_we1);
  end
end

// spyglass enable_block Ar_resetcross01 STARC-2.3.4.3

// ICCM regions

// direct the request to either ICCM0, ICCM1, Icache or IFQ
// Icache and IFQ are mutually exclusive, i.e. they can't be both configured, although both can be missing



reg icache_region_hit;
assign fetch_icache = icache_region_hit
                    ;

//////////////////////////////////////////////////////////////////////////////80
// Setup stage: mux addresses and prepare for RAM setup                 ////////
//////////////////////////////////////////////////////////////////////////////80




// mux select checker


  reg [`npuarc_BR_BC_BTA_RANGE] fch_target_bta;
  reg [`npuarc_BR_BC_BTA_RANGE] mpd_seq_next_pc_bta;

always @*
begin: bpu_addr_mux_PROC
//--------------------------------------------------------------------------
// leda B_3430 off
// LMD: Port is initialized before fake synopsys full case
// LJ: Defaults set prior to the case statement in the context of the always block, not "full_case"
  unused_carry5 = 1'b0;
  unused_carry6 = 1'b0;
  fch_target_bta = fch_target[`npuarc_BR_BC_BTA_RANGE];
  mpd_seq_next_pc_bta = mpd_seq_next_pc[`npuarc_BR_BC_BTA_RANGE];


// set up addresses for the RAMs.
// FA address bits:
//   0    : always 0, due to 16-bit aligned instructions
//  2:1   : offset within 64-bit fetch block
//   3    : bank selection in 2-bank organization
//  5:4   : location within 64B cache block
//  14:6  : memory index, 32KB ICCM
//  31:15 : high order address for ICCM
//  12:6  : set index, 32KB 4-way Icache
//  31:13 : high order address for Icache tags

// select between mispredicted BTA, predicted BTA or sequential address
restart_vec = 1'b0;
  fa_out = bta_pred;
  fa_out_succ = bta_pred_succ;

// default values
  fa = bta_pred; 
  fa_succ = bta_pred_succ;
  fa_out = fa; 
  fa_out_succ = fa_succ;



      icache_region_hit = 1'b1;
// leda B_3430 on

// leda W71 off
// LMD: Case statement without default clause and not all cases are covered
// LJ: Defaults set prior to the case statement in the context of the always block
// leda VER_2_8_5_1 off
// LMD: synopsys parrallel_case is not allowed
// LJ: Speed up one-hot encoded mux selectors; an assertion checks for violation of the one-hot property
// leda C_5C_R off
// LMD: synopsys parrallel_case is not allowed
// LJ: Speed up one-hot encoded mux selectors; an assertion checks for violation of the one-hot property
// leda FM_2_13 off
// LMD: synopsys parrallel_case is not allowed
// LJ: Speed up one-hot encoded mux selectors; an assertion checks for violation of the one-hot property
// spyglass disable_block STARC05-2.8.5.1
// SMD: Synopsys parallel case not allowed
// SJ:  Speed up one-hot encoded mux selectors; an assertion checks for violation of the one-hot property
  casez ({select_restart, select_captured_target, select_seq}) // synopsys parallel_case
// spyglass enable_block STARC05-2.8.5.1
// leda VER_2_8_5_1 on
// leda C_5C_R on
// leda FM_2_13 on
3'b100:
begin
  fa = fch_target_bta[`npuarc_BR_BC_BTA_MSB:1];
  fa_succ = fch_target_successor[`npuarc_IM_LINE_BITS:3];
  restart_vec = fch_restart_vec;



      icache_region_hit = 1'b1;

end // case: 3'b100
3'b010:
begin
  fa = target_r;

// leda B_3208 off
// LMD: Unequal length LHS and RHS in assignment
// LJ: arithmetic calculation has a potential dont_care carry bit
  {unused_carry5, fa_succ} = {1'b0, target_r[`npuarc_IM_LINE_BITS-1:3]} + 1;
// leda B_3208 on
  fa_out = fa; 
  fa_out_succ = fa_succ;
  restart_vec = fch_restart_vec_r;



      icache_region_hit = 1'b1;

end // case: 3'b010
3'b001:
begin
  fa = fa_seq; 
// leda B_3208 off
// LMD: Unequal length LHS and RHS in assignment
// LJ: arithmetic calculation has a potential dont_care carry bit
  {unused_carry6, fa_succ[`npuarc_IM_LINE_BITS:3]} = {1'b0, fa_seq[`npuarc_IM_LINE_BITS-1:3]} + 1;
// leda B_3208 on
  fa_out = fa; 
  fa_out_succ = fa_succ;



      icache_region_hit = 1'b1;

end // case: 3'b001
// spyglass disable_block W193
default: ;
// spyglass enable_block W193
endcase // casez({select_restart, select_captured_target, select_seq})
// leda W71 on
//--------------------------------------------------------------------------



init_finished = fa_seq_carry | fa_seq[`npuarc_BR_INIT_FINISHED];

// odd or even numbered 64-bit block:
unaligned = fa[3];   
unaligned_out = fa_out[3];   

//--------------------------------------------------------------------------

cross_line = fa_succ[`npuarc_IM_LINE_BITS]; 
cross_line_out = fa_out_succ[`npuarc_IM_LINE_BITS]; 

if (fetch_tail)
begin
//  fetch0 = mem_req & (~unaligned);
//  fetch1 = mem_req & unaligned;
// for timing optimization leave mem_req out of the expression and generate outside of the BPU
  fetch0 = ~unaligned_out;
  fetch1 = unaligned_out;
end
else
begin
//  fetch0 = mem_req & (~cross_line); 
  fetch0 = ~cross_line_out; 
  // when fetching the tail of a branch only bank 0 is used and bank 1 is turned off  
  // turn off fetch_tail_r when there is a restart
  //fetch1 = mem_req & (~(fetch_tail_r & (~restart))); 
  fetch1 = 1'b1; 
end
//--------------------------------------------------------------------------

// set up instruction memory addresses
// fa0 goes to bank 0 and fa1 goes to bank 1
// fa0 and fa1 share most address bits except the diff bits
fa_high = fa[`npuarc_BR_BC_BTA_MSB:`npuarc_IM_LINE_BITS]; // high order bits of FA
//fa_offset = fa[2:1]; // BTA offset inside fetch block
fa_offset = fa[`npuarc_BR_OFFSET_SIZE:1]; // BTA offset inside fetch block 


fa_out_high = fa_out[`npuarc_BR_BC_BTA_MSB:`npuarc_IM_LINE_BITS]; // high order bits of FA
//fa_out_offset = fa_out[2:1]; // BTA offset inside fetch block
fa_out_offset = fa_out[`npuarc_BR_OFFSET_SIZE:1]; // BTA offset inside fetch block 


//fa0_out_diff[`IM_LINE_BITS-1:4] = unaligned_out ? fa_out_succ[`IM_LINE_BITS-1:4] : fa_out[`IM_LINE_BITS-1:4];
fa0_out_diff[`npuarc_IM_LINE_BITS-1:4] = unaligned_out ? fa_out_succ[`npuarc_IM_LINE_BITS-1:4] : fa_out[`npuarc_IM_LINE_BITS-1:4];
fa1_out_diff[`npuarc_IM_LINE_BITS-1:4] = unaligned_out ? fa_out[`npuarc_IM_LINE_BITS-1:4] : fa_out_succ[`npuarc_IM_LINE_BITS-1:4]; 


fa0_diff[`npuarc_BR_FA_DIFF_RANGE] = unaligned ? fa_succ[`npuarc_BR_FA_DIFF_RANGE] : fa[`npuarc_BR_FA_DIFF_RANGE]; // bank 0 address, only the bits that are different between both banks
fa1_diff[`npuarc_BR_FA_DIFF_RANGE] = unaligned ? fa[`npuarc_BR_FA_DIFF_RANGE] : fa_succ[`npuarc_BR_FA_DIFF_RANGE]; // bank 1 address, only the bits that are different between both banks

  fa0[`npuarc_PC_RANGE] = {fa_high, fa0_diff, 1'b0, fa_offset};
  fa1[`npuarc_PC_RANGE] = {fa_high, fa1_diff, 1'b1, fa_offset};
  fa0_out[`npuarc_PC_RANGE] = {fa_out_high, fa0_out_diff, 1'b0, fa_out_offset};

//--------------------------------------------------------------------------
// setup the address for the BC RAM
bc_addr0_pre[`npuarc_BR_BC_IDX_RANGE] = fa0[`npuarc_BR_BC_IDX_RANGE];
bc_addr1_pre[`npuarc_BR_BC_IDX_RANGE] = fa1[`npuarc_BR_BC_IDX_RANGE];
//--------------------------------------------------------------------------
// set up the gshare address
// calculate the gshare hash function: gshare table index = Ghr XOR fetch block address 
gs_addr0_pre[`npuarc_BR_PT_RANGE] = {(ghr_next[`npuarc_BR_PT_RANGE] & {`npuarc_BR_PT_ADDR_SIZE{~bpu_wctl}}) ^ fa0[`npuarc_BR_PT_RANGE]};
gs_addr1_pre[`npuarc_BR_PT_RANGE] = {(ghr_next[`npuarc_BR_PT_RANGE] & {`npuarc_BR_PT_ADDR_SIZE{~bpu_wctl}}) ^ fa1[`npuarc_BR_PT_RANGE]};
//--------------------------------------------------------------------------
end

  

//////////////////////////////////////////////////////////////////////////////80
// Prediction stage: read RAM outputs and make a prediction                  ///
//////////////////////////////////////////////////////////////////////////////80


always @*
begin: bpu_fa_PROC

///////////////////////////////////////////////
// Receive RAM outputs
//--------------------------------------------------------------------------
// assemble full pipelined FA0_p and FA1_p from registered components of FA0 and FA1
fa0_p[31:3] = {fa_high_r, fa0_diff_r, 1'b0};
fa1_p[31:3] = {fa_high_r, fa1_diff_r, 1'b1};
//--------------------------------------------------------------------------

//--------------------------------------------------------------------------
fa_p[31:3] = unaligned_r ? fa1_p : fa0_p; // the addr of the first 64-bit block
//--------------------------------------------------------------------------


//--------------------------------------------------------------------------
if (cross_line_r | (~unaligned_r))
begin
// leda B_3208 off
// LMD: Unequal length LHS and RHS in assignment
// LJ: arithmetic calculation has a potential dont_care carry bit
  {fa_seq_carry, fa_seq} = {fa1_p[31:4] + 1, 1'b0, 2'b00};
// leda B_3208 on
end
else
begin
  fa_seq = {fa0_p[31:4], 1'b1, 2'b00};
  fa_seq_carry = 1'b0;
end


unused_carry0 = 1'b0;
unused_carry1 = 1'b0;

if (select_bta_miss)
begin
  if (bta_bank_r)
// leda B_3208 off
// LMD: Unequal length LHS and RHS in assignment
// LJ: arithmetic calculation has a potential dont_care carry bit
// spyglass disable_block W164b
// SMD: Unequal length LHS and RHS in assignment
// SJ:  taking into account carry bit
    {unused_carry0, fa_seq} = {fa1_p[31:4], 1'b1, bta_offset_r, 1'b0} + bta_displ[`npuarc_PC_RANGE];
  else
    {unused_carry1, fa_seq} = {fa0_p[31:4], 1'b0, bta_offset_r, 1'b0} + bta_displ[`npuarc_PC_RANGE];
// leda B_3208 on
// spyglass enable_block W164b
end


if (start_init_force_r)
    // used during the initalization sequence
    {fa_seq_carry, fa_seq} = {(`npuarc_BR_BC_BTA_SIZE + 1){1'b0}};

//--------------------------------------------------------------------------


fa0_tag = fa0_p[`npuarc_BR_BC_TAG_RANGE]; 
fa1_tag = fa1_p[`npuarc_BR_BC_TAG_RANGE]; 

end // block: bpu_pred_logic_PROC

always @*
begin: bpu_ctrl_PROC

// Check BPU_CTRL to force prediction direction or freeze GHR, branch cache or return stack
// BPU_CTRL:
//
//   #        prediction  GHR      STACK  PT_RAM  BC_RAM 
//  
//   0        regular
//   1        taken       freeze          freeze
//   2        not taken   freeze          freeze
//   3        taken       freeze          freeze  freeze
//   4        not taken   freeze          freeze  freeze
//   6        not taken   freeze   freeze freeze  freeze+disable
//   7        regular                     no_new  freeze

//   5  is reserved and values are don't care


// If bpu_ctrl is used to force prediction, then set strength to 1.
// 2-cycle clock domain
force_strong_2cyc = (   (bpu_ctrl_2cyc == 3'd1) 
                      | (bpu_ctrl_2cyc == 3'd2)
                      | (bpu_ctrl_2cyc == 3'd3)
                      | (bpu_ctrl_2cyc == 3'd4)
                    )
                  ;

// Disable prediction. Ignore branch cache entries.
// 2-cycle clock domain
bc_disable      = (bpu_ctrl       == 3'd6);
bc_disable_2cyc = (bpu_ctrl_2cyc  == 3'd6);

// Freeze the branch cache depending on BPU_CTRL
bc_freeze = (   (bpu_ctrl == 3'd3) 
              | (bpu_ctrl == 3'd4)
              | (bpu_ctrl == 3'd6)
              | (bpu_ctrl == 3'd7)
            )
           ;



// Freeze the global history register depending on BPU_CTRL
ghr_freeze = (   (bpu_ctrl != 3'd0) 
               & (bpu_ctrl != 3'd7)
             )
           ;

// Freeze the PT RAM depending on BPU_CTRL

pt_freeze = (    (bpu_ctrl != 3'd0) 
               & (bpu_ctrl != 3'd7)
             )
           ;

pt_no_new = (bpu_ctrl == 3'd7);

// Freeze the return stack depending on BPU_CTRL
stack_freeze = (   (bpu_ctrl == 3'd6) 
               )
             ;

end

always @*
begin: bpu_pt_ram_PROC



//gshare0 = gs_dout0[7:0];
gshare0 = gs_dout0_r;
gshare1 = gs_dout1_r;

// get Gshare prediction and strength bits
  

//predict_taken_vec0 = {gshare0[7],gshare0[5],gshare0[3],gshare0[1]};
//strength_vec0 = {gshare0[6],gshare0[4],gshare0[2],gshare0[0]} | {4{force_strong_2cyc}};
//predict_taken_vec1 = {gshare1[7],gshare1[5],gshare1[3],gshare1[1]};
//strength_vec1 = {gshare1[6],gshare1[4],gshare1[2],gshare1[0]} | {4{force_strong_2cyc}};


   predict_taken_vec0 = {
                             gshare0[7] ,
                             gshare0[5] ,
                             gshare0[3] ,
                             gshare0[1] 
   };
   strength_vec0 = {{
                             gshare0[6] ,
                             gshare0[4] ,
                             gshare0[2] ,
                             gshare0[0] }
                            |{`npuarc_BR_PT_PRED_VEC_SIZE{force_strong_2cyc}}
   };

   predict_taken_vec1 = {
                             gshare1[7] ,
                             gshare1[5] ,
                             gshare1[3] ,
                             gshare1[1] 
   };
   strength_vec1 = {{
                             gshare1[6] ,
                             gshare1[4] ,
                             gshare1[2] ,
                             gshare1[0] }
                            |{`npuarc_BR_PT_PRED_VEC_SIZE{force_strong_2cyc}}
   };


end

always @*
begin: bpu_predvec_PROC
// Force taken or not taken prediction depending on BPU_CTRL:
// BPU_CTRL:
//   0        regular prediction
//   1        taken
//   2        not taken
//   3        taken
//   4        not taken
//   5        reserved, use regular
//   6        not taken
//   7        regular prediction

  case (bpu_ctrl_2cyc)
  3'd1,
  3'd3:
    begin
      prediction0 = 1'b1;
      prediction1 = 1'b1;
      sec_prediction0 = 1'b1;
      sec_prediction1 = 1'b1;
    end
  3'd2,
  3'd4,
  3'd6:
    begin
      prediction0 = 1'b0;
      prediction1 = 1'b0;
      sec_prediction0 = 1'b0;
      sec_prediction1 = 1'b0;
    end
  default:
    begin
      prediction0 = predict_taken_vec0[offset0];
      prediction1 = predict_taken_vec1[offset1];
      sec_prediction0 = predict_taken_vec0[secondary_offset0];
      sec_prediction1 = predict_taken_vec1[secondary_offset1];
    end
  endcase
end

always @*
begin: bpu_bc_ram_PROC

// retrieve the branch cache entry from the output of the BC RAMs.
//--------------------------------------------------------------------------
// assign default values in case the configuration excludes assignments to them
  secondary_way0 = {`npuarc_IC_WAYS_BITS{1'b0}};
//secondary_offset0 = 2'b0;
  secondary_offset0 = {`npuarc_BR_OFFSET_SIZE{1'b0}};
  secondary_valid0 = 1'b0;
  secondary_f_bit0 = 1'b0;
  way0 = {`npuarc_IC_WAYS_BITS{1'b0}};
  secondary_way1 = {`npuarc_IC_WAYS_BITS{1'b0}};
//secondary_offset1 = 2'b0;
  secondary_offset1 = {`npuarc_BR_OFFSET_SIZE{1'b0}};
  secondary_valid1 = 1'b0;
  secondary_f_bit1 = 1'b0;
  way1 = {`npuarc_IC_WAYS_BITS{1'b0}};
//--------------------------------------------------------------------------
  {
   secondary_way0[`npuarc_IC_WAYS_BITS_RANGE],
   secondary_offset0[`npuarc_BR_OFFSET_RANGE], // secondary branch
   secondary_valid0,
   secondary_f_bit0,

   tag0[`npuarc_BR_BC_TAG_RANGE], 
   offset0[`npuarc_BR_OFFSET_RANGE], // primary branch
   type0[`npuarc_BR_TYPE_RANGE],
   bta0[`npuarc_BR_BC_BTA_RANGE], 
   way0[`npuarc_IC_WAYS_BITS_RANGE], 
   size0[1:0], 
   d_bit0, 
   f_bit0
  } = bc_dout0_r[`npuarc_BR_BC_DATA_RANGE];
//--------------------------------------------------------------------------
  {
   secondary_way1[`npuarc_IC_WAYS_BITS_RANGE],
   secondary_offset1[`npuarc_BR_OFFSET_RANGE], // secondary branch
   secondary_valid1,
   secondary_f_bit1,

   tag1[`npuarc_BR_BC_TAG_RANGE], 
   offset1[`npuarc_BR_OFFSET_RANGE], // primary branch
   type1[`npuarc_BR_TYPE_RANGE],
   bta1[`npuarc_BR_BC_BTA_RANGE], 
   way1[`npuarc_IC_WAYS_BITS_RANGE], 
   size1[1:0], 
   d_bit1, 
   f_bit1
  } = bc_dout1_r[`npuarc_BR_BC_DATA_RANGE];
//--------------------------------------------------------------------------

  tag0_sec = tag0;
  tag1_sec = tag1;
//--------------------------------------------------------------------------

 // get the prediction strength of the branches
  primary_strength0 = strength_vec0[offset0];
  primary_strength1 = strength_vec1[offset1];
  secondary_strength0 = strength_vec0[secondary_offset0];
  secondary_strength1 = strength_vec1[secondary_offset1];
//--------------------------------------------------------------------------



  // bank 0
  byp0_hit = byp_full_r & (~byp_bank_r) & (fa0_p[`npuarc_BR_BC_IDX_RANGE] == byp_index_r);
  // bank 1
  byp1_hit = byp_full_r & byp_bank_r & (fa1_p[`npuarc_BR_BC_IDX_RANGE] == byp_index_r);
 
  way_is_valid0 = 1'b1;
  way_is_valid1 = 1'b1;
  secondary_way_is_valid0 = 1'b1;
  secondary_way_is_valid1 = 1'b1;
//--------------------------------------------------------------------------
  if (byp0_hit)
  begin
    if (byp_set_primary_r)
    begin
      tag0 = byp_tag_r;
      offset0 = byp_offset_r;
      type0 = byp_type_r;
      bta0 = byp_bta_r;
      way0 = way_byp_in_r;
      way_is_valid0 = way_byp_full_r_r;
      size0 = byp_size_r;
      d_bit0 = byp_d_bit_r;
      f_bit0 = byp_f_bit_r;  
      // clear secondary if needed
      if (byp_clear_secondary_r)
      begin
        secondary_valid0 = 1'b0;
      end

  
    end
    else
    begin
      secondary_way0 = way_byp_in_r;
      secondary_way_is_valid0 = way_byp_full_r_r;
      secondary_offset0 = byp_offset_r;
      secondary_valid0 = 1'b1;
      secondary_f_bit0 = byp_f_bit_r;
    end

  end
//--------------------------------------------------------------------------
  if (byp1_hit)
  begin
    if (byp_set_primary_r)
    begin
      tag1 = byp_tag_r;
      offset1 = byp_offset_r;
      type1 = byp_type_r;
      bta1 = byp_bta_r;
      way1 = way_byp_in_r;
      way_is_valid1 = way_byp_full_r_r;
      size1 = byp_size_r;
      d_bit1 = byp_d_bit_r;
      f_bit1 = byp_f_bit_r;  
      // clear secondary if needed
      if (byp_clear_secondary_r)
      begin
        secondary_valid1 = 1'b0;  
      end 
    end
    else
    begin
      secondary_way1 = way_byp_in_r;
      secondary_way_is_valid1 = way_byp_full_r_r;
      secondary_offset1 = byp_offset_r;
      secondary_valid1 = 1'b1;
      secondary_f_bit1 = byp_f_bit_r;
    end
  end

//--------------------------------------------------------------------------

unused_carry2 = 1'b0;
unused_carry3 = 1'b0;
// leda B_3208 off
// LMD: Unequal length LHS and RHS in assignment
// LJ: arithmetic calculations have a potential dont_care carry bit
{unused_carry2, bta_succ0[`npuarc_IM_LINE_BITS:3]} = {1'b0, bta0[`npuarc_IM_LINE_BITS-1:3]} + 1;  
{unused_carry3, bta_succ1[`npuarc_IM_LINE_BITS:3]} = {1'b0, bta1[`npuarc_IM_LINE_BITS-1:3]} + 1; 

unused_carry4 = 1'b0;
{unused_carry4, top_of_stack_succ[`npuarc_IM_LINE_BITS:3]} = {1'b0, top_of_stack[`npuarc_IM_LINE_BITS-1:3]} + 1;  
// leda B_3208 on
//--------------------------------------------------------------------------
end

always @*
begin: bpu_type_PROC

// spyglass disable_block W193
// SMD: empty statement
// SJ:  statement kept for cases, no action required in case
valid0 = 1'b1;
unconditional0 = type0[0];
subcall0 = 1'b0;
subreturn0 = 1'b0;
case(type0)
  `npuarc_BR_NOT_PREDICTED,
  `npuarc_BR_EI_S: 
    begin
      valid0 = 1'b0;
      subcall0 = 1'b0;
      subreturn0 = 1'b0;
    end
  `npuarc_BR_UNCONDITIONAL: 
    begin
      unconditional0 = 1'b1;
    end
  `npuarc_BR_COND_CALL: 
    begin
      subcall0 = 1'b1;
    end
  `npuarc_BR_COND_RETURN: 
    begin
      subreturn0 = 1'b1;
    end
  `npuarc_BR_CALL: 
    begin
      unconditional0 = 1'b1;
      subcall0 = 1'b1;
    end
  `npuarc_BR_RETURN: 
    begin
      unconditional0 = 1'b1;
      subreturn0 = 1'b1;
    end
  `npuarc_BR_CONDITIONAL: ;
endcase

valid1 = 1'b1;
unconditional1 = type1[0];
subcall1 = 1'b0;
subreturn1 = 1'b0;
case(type1)
  `npuarc_BR_EI_S, 
  `npuarc_BR_NOT_PREDICTED: 
    begin
      valid1 = 1'b0;
      subcall1 = 1'b0;
      subreturn1 = 1'b0;
    end
  `npuarc_BR_UNCONDITIONAL: 
    begin
      unconditional1 = 1'b1;
    end
  `npuarc_BR_COND_CALL: 
    begin
      subcall1 = 1'b1;
    end
  `npuarc_BR_COND_RETURN: 
    begin
      subreturn1 = 1'b1;
    end
  `npuarc_BR_CALL: 
    begin
      unconditional1 = 1'b1;
      subcall1 = 1'b1;
    end
  `npuarc_BR_RETURN: 
    begin
      unconditional1 = 1'b1;
      subreturn1 = 1'b1;
    end
  `npuarc_BR_CONDITIONAL: ;
endcase
// spyglass enable_block W193
//--------------------------------------------------------------------------





tag0_hit = (tag0 == fa0_tag) & ~bc_disable_2cyc;
tag1_hit = (tag1 == fa1_tag) & ~bc_disable_2cyc;

tag0_sec_hit = (tag0_sec == fa0_tag) & ~bc_disable_2cyc;
tag1_sec_hit = (tag1_sec == fa1_tag) & ~bc_disable_2cyc;

end // block: bpu_type_PROC


////////////////////////////////////////////////////////
// Branch prediction
// Branch prediction logic for each of the banks.
// Determine if there is a taken branch.

always @*
begin: bpu_pred_PROC
//--------------------------------------------------------------------------
if (unaligned_r)
  begin
//  primary_valid1 = valid1 & (offset1 >= fa_offset_r[1:0]) & (~fetch_tail_r) & (~restart_vec_r);
//  secondary_vld1 = secondary_valid1 & (secondary_offset1 >= fa_offset_r[1:0]) & (~fetch_tail_r) & (~restart_vec_r);

    primary_valid1 = valid1 &           (offset1           >= fa_offset_r[`npuarc_BR_OFFSET_RANGE]) & (~fetch_tail_r) & (~restart_vec_r);
    secondary_vld1 = secondary_valid1 & (secondary_offset1 >= fa_offset_r[`npuarc_BR_OFFSET_RANGE]) & (~fetch_tail_r) & (~restart_vec_r);
    primary_valid0 = valid0 & (~fetch_tail_r) & (~cross_line_r) & (~restart_vec_r);
    secondary_vld0 = secondary_valid0 & (~fetch_tail_r) & (~cross_line_r) & (~restart_vec_r);
  end
else
  begin
//  primary_valid0 = valid0 & (offset0 >= fa_offset_r[1:0]) & (~fetch_tail_r) & (~restart_vec_r);
//  secondary_vld0 = secondary_valid0 & (secondary_offset0 >= fa_offset_r[1:0]) & (~fetch_tail_r) & (~restart_vec_r);
    primary_valid0 = valid0 &           (offset0           >= fa_offset_r[`npuarc_BR_OFFSET_RANGE]) & (~fetch_tail_r) & (~restart_vec_r);
    secondary_vld0 = secondary_valid0 & (secondary_offset0 >= fa_offset_r[`npuarc_BR_OFFSET_RANGE]) & (~fetch_tail_r) & (~restart_vec_r);
    primary_valid1 = valid1 & (~fetch_tail_r) & (~restart_vec_r);
    secondary_vld1 = secondary_valid1 & (~fetch_tail_r) & (~restart_vec_r);
  end
//--------------------------------------------------------------------------
  primary_predict_taken0 = (prediction0 & (~unconditional0)) | unconditional0;

  primary_taken0 = primary_predict_taken0 & primary_valid0;
  primary_not_taken0 = ~primary_predict_taken0 & primary_valid0;

  primary_predict_taken1 = (prediction1 & (~unconditional1)) | unconditional1;
  primary_taken1 = primary_predict_taken1 & primary_valid1;
  primary_not_taken1 = ~primary_predict_taken1 & primary_valid1;
//--------------------------------------------------------------------------
  // secondary branches are always conditional, if BR_HAS_SECONDARY==1
  secondary_predict_taken0 = sec_prediction0;
  secondary_taken0 = secondary_predict_taken0 & secondary_vld0;
  secondary_not_taken0 = ~secondary_predict_taken0 & secondary_vld0;
  secondary_smaller0 = (secondary_offset0 < offset0);

  secondary_predict_taken1 = sec_prediction1;
  secondary_taken1 = secondary_predict_taken1 & secondary_vld1;
  secondary_not_taken1 = ~secondary_predict_taken1 & secondary_vld1;
  secondary_smaller1 = (secondary_offset1 < offset1);
//--------------------------------------------------------------------------
  any_taken0 = (tag0_hit & primary_taken0) | (tag0_sec_hit & secondary_taken0);
  taken0 = tag0_hit & primary_taken0 & (~(tag0_sec_hit & secondary_taken0 & secondary_smaller0));
  bta_miss0 = tag0_sec_hit & secondary_taken0 & (~(tag0_hit & primary_taken0) | secondary_smaller0);

  primary_nt_smaller0 = primary_not_taken0 & (~secondary_smaller0);
  secondary_nt_smaller0 = secondary_not_taken0 & secondary_smaller0;
//--------------------------------------------------------------------------
  any_taken1 = (tag1_hit & primary_taken1) | (tag1_sec_hit & secondary_taken1);
  taken1 = tag1_hit & primary_taken1 & (~(tag1_sec_hit & secondary_taken1 & secondary_smaller1));
  bta_miss1 = tag1_sec_hit & secondary_taken1 & (~(tag1_hit & primary_taken1) | secondary_smaller1);
  primary_nt_smaller1 = primary_not_taken1 & (~secondary_smaller1);
  secondary_nt_smaller1 = secondary_not_taken1 & secondary_smaller1;
//--------------------------------------------------------------------------

  nt4 = tag0_hit & primary_not_taken0 & tag0_sec_hit & secondary_not_taken0
         & tag1_hit & primary_not_taken1 & tag1_sec_hit & secondary_not_taken1;

  nt2_0 = tag0_hit & primary_not_taken0 & tag0_sec_hit & secondary_not_taken0;
  nt2_1 = tag1_hit & primary_not_taken1 & tag1_sec_hit & secondary_not_taken1;
//--------------------------------------------------------------------------

//--------------------------------------------------------------------------
num_nt[1:0] = 2'd0;
if (any_taken0 | any_taken1)
  begin
    if (unaligned_r)
      begin
        if (taken1)
          begin
            num_nt[0] = tag1_sec_hit & secondary_nt_smaller1;
          end
        else if (bta_miss1)
          begin
            num_nt[0] = tag1_hit & primary_nt_smaller1;
          end
        else if (taken0)
          begin
              case ({tag1_hit & primary_not_taken1, tag1_sec_hit & secondary_not_taken1})
                2'b11: num_nt[1:0] = {1'b1, tag0_sec_hit & secondary_nt_smaller0};
                2'b01, 
                  2'b10: num_nt[1:0] = (tag0_sec_hit & secondary_nt_smaller0) ? 2'b10 : 2'b01;
                2'b00: num_nt[0] = tag0_sec_hit & secondary_nt_smaller0;                     
              endcase
          end // if (taken0)
        else // bta_miss0
          begin
              case ({tag1_hit & primary_not_taken1, tag1_sec_hit & secondary_not_taken1})
                2'b11: num_nt[1:0] = {1'b1, tag0_hit & primary_nt_smaller0};
                2'b01, 
                  2'b10: num_nt[1:0] = (tag0_hit & primary_nt_smaller0) ? 2'b10 : 2'b01;
                2'b00: num_nt[0] = tag0_hit & primary_nt_smaller0;                     
              endcase
          end
      end // if (unaligned_r)
    else
      begin
        if (taken0)
          begin
            num_nt[0] = tag0_sec_hit & secondary_nt_smaller0;
          end
        else if (bta_miss0)
          begin
            num_nt[0] = tag0_hit & primary_nt_smaller0;
          end
        else if (taken1)
          begin
              case ({tag0_hit & primary_not_taken0, tag0_sec_hit & secondary_not_taken0})
                2'b11: num_nt[1:0] = {1'b1, tag1_sec_hit & secondary_nt_smaller1};
                2'b01, 
                  2'b10: num_nt[1:0] = (tag1_sec_hit & secondary_nt_smaller1) ? 2'b10 : 2'b01;
                2'b00: num_nt[0] = tag1_sec_hit & secondary_nt_smaller1;                     
              endcase
          end // if (taken1)
        else // bta_miss1
          begin
              case ({tag0_hit & primary_not_taken0, tag0_sec_hit & secondary_not_taken0})
                2'b11: num_nt[1:0] = {1'b1, tag1_hit & primary_nt_smaller1};
                2'b01, 
                  2'b10: num_nt[1:0] = (tag1_hit & primary_nt_smaller1) ? 2'b10 : 2'b01;
                2'b00: num_nt[0] = tag1_hit & primary_nt_smaller1;                     
              endcase
          end
      end // else: !if(unaligned_r)
  end // if (taken0 | taken1)
else 
  begin
            if (~((tag0_hit & primary_not_taken0) | (tag0_sec_hit & secondary_not_taken0) 
                  | (tag1_hit & primary_not_taken1) | (tag1_sec_hit & secondary_not_taken1)))
              // if all zeros, then num_nt=0
              num_nt[1:0] = 2'b00;
            else if (nt2_0 | nt2_1)
              // if 2 branches on one of the sides, then num_nt=2 or 3
              num_nt[1:0] = {1'b1, nt2_0 ? 
                             (tag1_hit & primary_not_taken1) | (tag1_sec_hit & secondary_not_taken1) 
                             : (tag0_hit & primary_not_taken0) | (tag0_sec_hit & secondary_not_taken0)};
            else if (((tag0_hit & primary_not_taken0) | (tag0_sec_hit & secondary_not_taken0)) 
                     & ((tag1_hit & primary_not_taken1) | (tag1_sec_hit & secondary_not_taken1)))
              // if 1 branch on both sides: num_nt=2
              num_nt[1:0] = 2'b10;
            else
              // remaining cases: num_nt=1
              num_nt[1:0] = 2'b01;            
  end
//--------------------------------------------------------------------------

  bta0_full = {bta0[`npuarc_BR_BC_BTA_MSB:`npuarc_BR_BC_BTA_MSB-3], bta0[`npuarc_BR_BC_BTA_MSB-4:`npuarc_BR_BC_BTA_LSB]};
  bta1_full = {bta1[`npuarc_BR_BC_BTA_MSB:`npuarc_BR_BC_BTA_MSB-3], bta1[`npuarc_BR_BC_BTA_MSB-4:`npuarc_BR_BC_BTA_LSB]};
//--------------------------------------------------------------------------

//////////////////////////////////////////////////
// Combine prediction results of both fetch blocks
// 
// overall branch prediction result combined from both banks
//--------------------------------------------------------------------------

taken = taken0 | taken1;

//--------------------------------------------------------------------------

  bta_miss_detected = 1'b0;
case ({unaligned_r, any_taken0, any_taken1})
3'b0_00, // default, don't care
3'b1_00, // default, don't care
3'b0_10,
3'b0_11,
3'b1_10
        : // bank 0 provides the prediction
        begin
          // if a subroutine return, take the top of the return address stack, otherwise, the BTA from the branch cache
          bta_pred = subreturn0 ? top_of_stack : bta0_full; 
          bta_pred_succ = subreturn0 ? top_of_stack_succ : bta_succ0;
//        offset[2:0] = {unaligned_r, offset0};
          offset[`npuarc_BR_INFO_OFFSET_RANGE] = {unaligned_r, offset0};
//        bta_offset[2:0] = {unaligned_r, secondary_offset0};
          bta_offset[`npuarc_BR_INFO_OFFSET_RANGE] = {unaligned_r, secondary_offset0};
          brtype_cond = ~type0[0]; // is the taken branch a conditional branch
          size_pred = size0;
          bank = 1'b0;
          subreturn = subreturn0;
          subcall = subcall0;
          bta_miss_detected = allow_bta_miss & bta_miss0;
        end

3'b0_01,
3'b1_01,
3'b1_11
        : // bank 1 provides the prediction
        begin
          bta_pred = subreturn1 ? top_of_stack : bta1_full;
          bta_pred_succ = subreturn1 ? top_of_stack_succ : bta_succ1;
//        offset[2:0] = {~unaligned_r, offset1};
          offset[`npuarc_BR_INFO_OFFSET_RANGE] = {~unaligned_r, offset1};
//        bta_offset[2:0] = {~unaligned_r, secondary_offset1};
          bta_offset[`npuarc_BR_INFO_OFFSET_RANGE] = {~unaligned_r, secondary_offset1};
          brtype_cond = ~type1[0]; 
          size_pred = size1;
          bank = 1'b1;
          subreturn = subreturn1;
          subcall = subcall1;
          bta_miss_detected = allow_bta_miss & bta_miss1;
        end

endcase

if (select_bta_miss)
  bta_pred = fa_seq;
end // block: bpu_pred_PROC

//--------------------------------------------------------------------------
 
always @*
begin: bpu_branch_info_fb_PROC

//--------------------------------------------------------------------------

if (unaligned_r)
begin


  br_secondary_f_bit1 = secondary_f_bit0;
  br_secondary_offset1 = secondary_offset0;
  br_secondary_strength1 = secondary_strength0;
  br_secondary_valid1 = tag0_sec_hit & secondary_valid0 & (~restart_vec_r);              
  br_secondary_taken1 = secondary_taken0;
  br_d_bit1 = d_bit0;
  br_type1[`npuarc_BR_TYPE_RANGE] = tag0_hit & (~restart_vec_r) ? type0 : `npuarc_BR_NOT_PREDICTED;
  br_f_bit1 = f_bit0;
//br_offset1[1:0] = offset0;
  br_offset1[`npuarc_BR_OFFSET_RANGE] = offset0;
  br_primary_strength1 = primary_strength0;
  br_taken1 = primary_taken0;
  br_secondary_way0 = secondary_way1;
  br_secondary_way1 = secondary_way0;
  br_primary_way0 = way1;
  br_primary_way1 = way0;

  br_secondary_f_bit0 = secondary_f_bit1;
  br_secondary_offset0 = secondary_offset1;
  br_secondary_strength0 = secondary_strength1;
  br_secondary_valid0 = tag1_sec_hit & secondary_valid1 & (~restart_vec_r);              
  br_secondary_taken0 = secondary_taken1;
  br_d_bit0 = d_bit1;
  br_type0[`npuarc_BR_TYPE_RANGE] = tag1_hit & (~restart_vec_r) ? type1 : `npuarc_BR_NOT_PREDICTED;
  br_f_bit0 = f_bit1;
//br_offset0[1:0] = offset1;
  br_offset0[`npuarc_BR_OFFSET_RANGE] = offset1;
  br_primary_strength0 = primary_strength1;
  br_taken0 = primary_taken1;
end
else
begin



  br_secondary_f_bit1 = secondary_f_bit1;
  br_secondary_offset1 = secondary_offset1;
  br_secondary_strength1 = secondary_strength1;
  br_secondary_valid1 = tag1_sec_hit & secondary_valid1 & (~restart_vec_r);              
  br_secondary_taken1 = secondary_taken1;
  br_d_bit1 = d_bit1;
  br_type1[`npuarc_BR_TYPE_RANGE] = tag1_hit & (~restart_vec_r) ? type1 : `npuarc_BR_NOT_PREDICTED;
  br_f_bit1 = f_bit1;
//br_offset1[1:0] = offset1;
  br_offset1[`npuarc_BR_OFFSET_RANGE] = offset1;
  br_primary_strength1 = primary_strength1;
  br_taken1 = primary_taken1;
  br_secondary_way0 = secondary_way0;
  br_secondary_way1 = secondary_way1;
  br_primary_way0 = way0;
  br_primary_way1 = way1;

  br_secondary_f_bit0 = secondary_f_bit0;
  br_secondary_offset0 = secondary_offset0;
  br_secondary_strength0 = secondary_strength0;
  br_secondary_valid0 = tag0_sec_hit & secondary_valid0 & (~restart_vec_r);              
  br_secondary_taken0 = secondary_taken0;
  br_d_bit0 = d_bit0;
  br_type0[`npuarc_BR_TYPE_RANGE] = tag0_hit & (~restart_vec_r) ? type0 : `npuarc_BR_NOT_PREDICTED;
  br_f_bit0 = f_bit0;
//br_offset0[1:0] = offset0;
  br_offset0[`npuarc_BR_OFFSET_RANGE] = offset0;
  br_primary_strength0 = primary_strength0;
  br_taken0 = primary_taken0;


end
//--------------------------------------------------------------------------




if (cross_line_r)
begin
  detect_fetch_tail = f_bit1 & taken1 | secondary_f_bit1 & bta_miss1; 
end
else
begin
  detect_fetch_tail = (unaligned_r ? 
                       (f_bit0 & taken0 | secondary_f_bit0 & bta_miss0) & (~any_taken1) 
                       : (f_bit1 & taken1 | secondary_f_bit1 & bta_miss1) & (~any_taken0)); 
end
//--------------------------------------------------------------------------

kill_2nd = unaligned_r 
           ? (~f_bit1) & taken1 | (~secondary_f_bit1) & bta_miss1
           : (~f_bit0) & taken0 | (~secondary_f_bit0) & bta_miss0;


//--------------------------------------------------------------------------

branch_info_fb[`npuarc_BR_FB_INFO_RANGE] = {

   top_of_stack[`npuarc_BR_BC_BTA_RANGE],     // Return Stack: Top of Stack value
   stack_ptr_r [`npuarc_BR_RS_RANGE],   // Return Stack: Top of Stack Pointer

   br_secondary_way1[`npuarc_IC_WAYS_BITS_RANGE], // Way prediction
   br_primary_way1[`npuarc_IC_WAYS_BITS_RANGE], 

   br_secondary_f_bit1, 
   br_secondary_offset1[`npuarc_BR_OFFSET_RANGE],
   br_secondary_strength1,
   br_secondary_valid1,              
   br_secondary_taken1, 
   
   br_d_bit1,                    
   br_type1[`npuarc_BR_TYPE_RANGE],     
   br_f_bit1, 
   br_offset1[`npuarc_BR_OFFSET_RANGE], 
   br_primary_strength1,                 
   br_taken1,

   br_secondary_way0[`npuarc_IC_WAYS_BITS_RANGE], 
   br_primary_way0[`npuarc_IC_WAYS_BITS_RANGE], 

   br_secondary_f_bit0,                // indicates the predicted branch needs to fetch one more 64-bit block before the branch takes effect
   br_secondary_offset0[`npuarc_BR_OFFSET_RANGE], // 2-bit offset in 64-bit block
   br_secondary_strength0,           // Gshare confidence
   br_secondary_valid0,          // is this branch predicted? Yes: 1
   br_secondary_taken0,               // Gshare prediction; 1: taken branch, 0: not taken

   br_d_bit0,                // has this branch a delay slot? Yes: 1
   br_type0[`npuarc_BR_TYPE_RANGE], // the type of the branch; set to 0 if no tag_hit
   br_f_bit0,                // indicates the predicted branch needs to fetch one more 64-bit block before the branch takes effect
   br_offset0[`npuarc_BR_OFFSET_RANGE], // 2-bit offset in 64-bit block
   br_primary_strength0,             // Gshare confidence
   br_taken0                  // Gshare prediction; 1: taken branch, 0: not taken
};
//--------------------------------------------------------------------------

end 
//--------------------------------------------------------------------------
//--------------------------------------------------------------------------

//////////////////////////////
// Way prediction
always @*
begin: bpu_waypred_PROC


//--------------------------------------------------------------------------

  bta_miss_way = bank ? secondary_way1 : secondary_way0;
  bta_miss_way_valid = bank ? secondary_way_is_valid1 : secondary_way_is_valid0;
//--------------------------------------------------------------------------


//--------------------------------------------------------------------------

  // select the way prediction output
  way_valid = 1'b0;
  way_seq = 1'b0;
  way_req = 1'b0;
  way_sec = 1'b0;



  way_seq = ~(&fa_p[`npuarc_IM_LINE_BITS-1:4]) & select_seq & (~select_bta_miss) & ~fch_restart; 



  //way_pred = bank ? way1 : way0;
  way_pred = cycle2_r ? `npuarc_IC_WAYS_BITS'd0 : (bank ? way1 : way0);     
  way_is_valid = bank ? way_is_valid1 : way_is_valid0;
  way_valid = select_bta_pred & (~subreturn) & way_is_valid;

  if (select_bta_miss)
  begin
    way_pred = bta_miss_way_r;
    way_valid = bta_miss_way_valid_r;
    way_sec = 1'b1;
  end

  if (select_captured_target)  
  begin  
    if (restart_captured_r)             
    begin  
      way_pred = `npuarc_IC_WAYS_BITS'd0;
      way_valid = 1'b0;
      way_sec = 1'b0;
      way_req = 1'b0;
    end
    else 
    begin  
      way_pred = captured_way_r;
      way_valid = captured_way_valid_r;
      way_sec = captured_way_sec_r;
      way_req = captured_way_req_r & icache_region_hit;
    end
  end
//--------------------------------------------------------------------------code suddenly jump to L1
  
  way_valid_detect = mpd_mispred & fch_restart & mp_alt_way_valid & (~mpd_error_branch) 
                     & mpd_is_predicted & mpd_mispred_outcome
                     & (~((mpd_type == `npuarc_BR_COND_RETURN) & mpd_direction));
//--------------------------------------------------------------------------

  way_valid_out = way_valid;
//  way_pred_out = way_pred;

//--------------------------------------------------------------------------
      way_req_detect = mpd_mispred  & fch_restart & (~mpd_error_branch) & mpd_direction
                & (~mpd_is_predicted | (mpd_mispred_bta & (~mpd_mispred_outcome)))
                & (mpd_type != `npuarc_BR_RETURN) & (mpd_type != `npuarc_BR_COND_RETURN);

//--------------------------------------------------------------------------

//--------------------------------------------------------------------------code suddenly jump from L1

  if (fch_restart)
  begin
//    if (mpd_mispred & restart)
    if (mpd_mispred)
    begin
      way_pred = mp_alt_way;
      way_sec = mp_way_sec;
      way_req = way_req_detect & icache_region_hit;
    end
    else
    begin
      way_pred = {`npuarc_IC_WAYS_BITS{1'b0}};
      way_sec = 1'b0;
      way_req = 1'b0;
    end
  end 
//  else
//  begin
//
//`// suppress 2-cycle path for way_pred when fetch_tail_r
//    if (fetch_tail_r)
//    begin
//      way_pred = {`IC_WAYS_BITS{1'b0}};
//      way_sec = 1'b0;
//    end
//    
//  end
end
//--------------------------------------------------------------------------
//--------------------------------------------------------------------------
//--------------------------------------------------------------------------
  


// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
//
always @(posedge clk)
begin: bpu_nr_regs_PROC
  if (start_prediction | init)
  begin
    // these are all registers that start 2-cycle paths
    fa_high_r_2cyc     <= fa_high;
    fa_offset_r_2cyc   <= fa_offset;
    fa0_diff_r_2cyc    <= fa0_diff;
    fa1_diff_r_2cyc    <= fa1_diff;
    cross_line_r_2cyc  <= cross_line;
    unaligned_r_2cyc   <= unaligned;
  end
end
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01

always @(posedge clk or posedge rst_a)
begin: bpu_regs_PROC
  if (rst_a == 1'b1)
  begin
    cycle2_r                   <= 1'b0;
    captured_r                 <= 1'b0;
    restart_captured_r         <= 1'b0;
    capture_not_taken_r        <= 1'b0;
    fetch_tail_r_2cyc          <= 1'b0;
    ghr_captured_r             <= 1'b0;

    fch_restart_vec_r          <= 1'b0;
    restart_vec_r_2cyc         <= 1'b0;
    start_prediction_r         <= 1'b0;

    start_init_force_r_2cyc    <= 1'b0;

    captured_way_valid_r       <= 1'b0;
    captured_way_sec_r         <= 1'b0;
    captured_way_req_r         <= 1'b0;
  end
  else
  begin
    cycle2_r                   <= cycle2_next;
    captured_r                 <= captured_next;
    restart_captured_r         <= restart_captured_next;
    capture_not_taken_r        <= capture_not_taken_next;
    fetch_tail_r_2cyc          <= fetch_tail_next_2cyc;
    ghr_captured_r             <= ghr_captured_next;

    fch_restart_vec_r          <= fch_restart_vec_next;
    restart_vec_r_2cyc         <= restart_vec_next_2cyc;
    start_prediction_r         <= start_prediction;

    start_init_force_r_2cyc    <= start_init_force_next_2cyc;

    captured_way_valid_r       <= captured_way_valid_next;
    captured_way_sec_r         <= captured_way_sec_next;
    captured_way_req_r         <= captured_way_req_next;
  end
end // bpu_regs_PROC

// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
// spyglass disable_block STARC05-1.3.1.3 AsyncResetOtherUse
// SMD: Asynchronous reset signal used as non-reset/synchronous-reset
// SJ:  No asynchronous reset for registers like target_r; no functional issue
//
always @(posedge clk)
begin: bpu_data_regs_PROC
  target_r                <= target_next;
  captured_way_r          <= captured_way_next;
end // bpu_data_regs_PROC

always @(posedge clk)
begin: bta_miss_capture_PROC
  if (capture_bta_miss)
  begin
    bta_bank_r_2cyc      <= bank;
    bta_offset_r_2cyc    <= bta_offset[1];
    bta_miss_way_r       <= bta_miss_way;
    bta_miss_way_valid_r <= bta_miss_way_valid;
  end
end // bta_miss_capture_PROC
// spyglass enable_block STARC05-1.3.1.3 AsyncResetOtherUse
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01

always@ (*)
begin: fetch_tail_PROC
  fetch_tail_next_2cyc      = fetch_tail_r_2cyc;

  if (fetch_tail_r_2cyc & start_prediction)
     fetch_tail_next_2cyc   = 1'b0;
  else if (~fetch_tail_r_2cyc & (~cycle2_r))
     fetch_tail_next_2cyc   = fetch_tail;
end

assign start_init_force_next_2cyc = (~cycle2_r) ? start_init_force
                                                : start_init_force_r_2cyc;   

assign restart_vec_next_2cyc      = (start_prediction | init) ? restart_vec
                                                              : restart_vec_r_2cyc;
                                  
// Capture of restart needed, because there is no flow control on restart interface
always@ (*)
begin: capture_restart_PROC
  target_next                 = target_r;
  fch_restart_vec_next        = fch_restart_vec_r;
  captured_way_next           = captured_way_r;
  captured_way_valid_next     = captured_way_valid_r;
  captured_way_sec_next       = captured_way_sec_r;
  captured_way_req_next       = captured_way_req_r;

  if (fch_restart & (~restart))
  begin
    target_next               = fch_target_bta;
    fch_restart_vec_next      = fch_restart_vec;
    captured_way_next         = mp_alt_way;
    captured_way_valid_next   = way_valid_detect;
    captured_way_sec_next     = mp_way_sec;
    captured_way_req_next     = way_req_detect;
  end
  else if (capture_bta)
  begin
    target_next               = bta_pred;
    fch_restart_vec_next      = 1'b0;
    if (select_bta_miss)
    begin
      captured_way_next       = bta_miss_way_r;
      captured_way_valid_next = bta_miss_way_valid_r;
      captured_way_sec_next   = 1'b1;
      captured_way_req_next   = 1'b0;
    end
    else
    begin
      captured_way_next       = bank ? way1 : way0;
      captured_way_valid_next = taken & way_is_valid;
      captured_way_sec_next   = 1'b0;
      captured_way_req_next   = 1'b0;
    end
  end
  else if (release_capture)
  begin
    fch_restart_vec_next      = 1'b0;
    captured_way_valid_next   = 1'b0;
    captured_way_sec_next     = 1'b0;
    captured_way_req_next     = 1'b0;
  end
end // capture_restart_PROC

always@ (*)
begin: capture_PROC
  captured_next               = captured_r;
  restart_captured_next       = restart_captured_r;
  capture_not_taken_next      = capture_not_taken_r;

  if ((fch_restart & (~restart)) | capture_bta)
  begin
    captured_next             = 1'b1;
    restart_captured_next     = fch_restart;       // remember if the capture is related to a restart
    capture_not_taken_next    = capture_not_taken; // remember if the capture is for a not taken branch
  end
  else if (release_capture) 
  begin
    captured_next             = 1'b0;
    restart_captured_next     = 1'b0;
    capture_not_taken_next    = 1'b0;
  end
end // capture_PROC

always@ (*)
begin: bpu_capture_ghr_PROC
  ghr_captured_next = ghr_captured_r;
  if ((fch_restart & (~restart)) | capture_bta | capture_bta_miss)
  begin
    ghr_captured_next = 1'b1; // state register indicating ghr_next has been captured
  end
  else if (start_prediction)
  begin
    ghr_captured_next = 1'b0;
  end
end // bpu_capture_ghr_PROC

assign cycle2_next = (start_prediction | cycle_steal | init | start_init_force | bpu_flush_ack )
                   ? 1'b1 : 1'b0; 

always @*
begin: bta_valid_PROC
  bta_valid = start_prediction_r & (~cycle2_r) & (~bta_miss) | bta_delayed_valid;
end


//  STATE 
//

assign state_nxt =
         state_next;

always @(posedge clk or posedge rst_a) 
begin : state_r_PROC
  if (rst_a == 1'b1)
    state_r          <= RESET;
  else
    state_r          <= state_nxt;
end // block : state_r_PROC

always @(posedge clk or posedge rst_a)
begin: bpu_state_PROC
  if (rst_a == 1'b1)
  begin
    bpu_init_r              <= 1'b1;
    select_bta_miss_2cyc    <= 1'b0;
  end
  else
  begin
    select_bta_miss_2cyc    <= select_bta_miss_next_2cyc;
    bpu_init_r              <= bpu_init_next;
  end
end // bpu_state_PROC

assign select_bta_miss_next_2cyc = ((state_next == BTA_MISS1) || (state_next == BTA_MISS2))
                                 ? 1'b1 : 1'b0; 

assign allow_bta_miss = (state_r == PREDICT); 

always @*
begin: bpu_fsm_PROC
  // default values for registers
  state_next = state_r;

  // default values for combinatorial signals
  start_init_force = 1'b0;
  init = 1'b0;
  bpu_flush_ack = 1'b0;
  select_restart = 1'b0;
  select_bta_pred = 1'b0;
  select_seq = 1'b0; 
  select_captured_target = 1'b0;
  capture_bta = 1'b0;
  capture_bta_miss = 1'b0;
  capture_not_taken = 1'b0;
  release_capture = 1'b0;
  start_prediction = 1'b0;
  bpu_wctl = 1'b0;
  mem_req = 1'b0;
  restart = 1'b0;
  fetch_tail = 1'b0;
  prediction_used = 1'b0;
  bta_delayed_valid = 1'b0;
  bpu_init_next = 1'b0;

  if (bpu_flush)
  begin
    if (~cycle2_r)
    begin
      bpu_init_next = 1'b1;
      bpu_flush_ack = 1'b1; // handshake to acknowledge the completion of the AUX register operation
      state_next = RESET;
    end
  end
  else
  begin
  case(state_r)
   RESET:
     begin
       bpu_init_next = 1'b1;

        if (~cycle2_r)
        begin
          start_init_force = 1'b1;
          state_next = INIT;
        end
      end
   INIT:
      begin
        bpu_init_next = 1'b1;
        bpu_wctl = 1'b1; 
        select_seq = 1'b1; 
        if (~cycle2_r)
        begin
          init = 1'b1; 
          if (init_finished)
          begin
            state_next = START;
          end
        end
      end
   START:
     begin
        if (captured_r)
        begin
          if (~cycle2_r)
          begin
            state_next = PREDICT;
          end
        end
          end
   PREDICT:
      begin
        //++++++++++++++++++++++++++++++++++++++++++
        if (fch_restart)
        begin
          select_restart = 1'b1; 

          if (~(mem_busy | cycle2_r)) 
          begin

            start_prediction = 1'b1;
            restart = 1'b1;
            release_capture = 1'b1;             
          end
        end
        //++++++++++++++++++++++++++++++++++++++++++
        else if (captured_r)
        begin
          if (capture_not_taken_r)
            select_seq = 1'b1;
          else
            select_captured_target = 1'b1;

          if (~(mem_busy | cycle2_r | bc_needed_r))
          begin
            mem_req = 1'b1;
            start_prediction = 1'b1;
            restart = restart_captured_r; // if replaying a restart, the restart signal must be asserted
            release_capture = 1'b1; // release the captured FA
          end
        end
        else if (bta_miss_detected & (~cycle2_r))
        begin
          state_next = BTA_MISS1;
          capture_bta_miss = 1'b1;

          if (detect_fetch_tail) 
          begin
             select_seq = 1'b1;
             select_bta_pred = 1'b0;             
             fetch_tail = 1'b1;            
             if (mem_busy)
             begin
               state_next = BTA_MISS_TAIL_WAIT;
             end
             else
             begin
               mem_req = 1'b1;
             end
          end

        end
        //++++++++++++++++++++++++++++++++++++++++++
        else
        begin
          if (taken)
          begin
             select_bta_pred = 1'b1;             
          end
          else
          begin
             select_seq = 1'b1;
          end

          if (detect_fetch_tail & (~cycle2_r)) // check for cycle2 because otherwise taken is not valid
          begin
             capture_bta = 1'b1; 
             select_seq = 1'b1;
             select_bta_pred = 1'b0;             
             fetch_tail = 1'b1;            
             if (mem_busy)
             begin
               state_next = TAIL_WAIT;
             end
             else
             begin
               mem_req = 1'b1;
             end
             prediction_used = 1'b1;
          end
          else if (~(mem_busy | cycle2_r | bc_needed_r))
          begin
            // regular branch prediction and instruction fetch to fill the fetch buffer
            mem_req = 1'b1;
            start_prediction = 1'b1;
            prediction_used = 1'b1;
          end
          else if (~cycle2_r)
          begin 
            if (cycle_steal)
            begin
              capture_bta = 1'b1;
              capture_not_taken = ~taken;
              prediction_used = taken;
            end
          end

        end     
      end

   TAIL_WAIT:
     begin
        select_seq = 1'b1; // set address mux to sequential for the tail address 
        fetch_tail = 1'b1;            
        if (fch_restart)
        begin
          state_next = PREDICT;
        end
        else
        begin
          if (~mem_busy)
          begin
            mem_req = 1'b1;
            state_next = PREDICT;
          end
        end
      end
   BTA_MISS_TAIL_WAIT:
     begin
        select_seq = 1'b1; // set address mux to sequential for the tail address 
        fetch_tail = 1'b1;            
        if (fch_restart)
        begin
          state_next = PREDICT;
        end
        else if (bta_displ_valid)
        begin
           fetch_tail = 1'b0;            
           state_next = BTA_MISS2;        
        end
        else
        begin
          if (~mem_busy)
          begin
            mem_req = 1'b1;
            state_next = BTA_MISS1;
          end
        end
      end
    BTA_MISS1:
     begin
       select_seq = 1'b1;
       if (fch_restart)
       begin
         state_next = PREDICT;
       end
       else if (bta_displ_valid)
       begin
           state_next = BTA_MISS2;        
       end
     end
    BTA_MISS2:
     begin
       select_seq = 1'b1;
       bta_delayed_valid = 1'b1;
       if (fch_restart)
       begin
         state_next = PREDICT;
       end
       else
       begin
         if (~(mem_busy | cycle2_r | bc_needed_r))
         begin
           // regular branch prediction and instruction fetch to fill the fetch buffer
           mem_req = 1'b1;
           start_prediction = 1'b1;
         end
         else
         begin
           capture_bta = 1'b1;
         end
         state_next = PREDICT;
        end     
     end
    default:
// leda W192 off
// leda B_3400 off
// LMD: empty block statements
// LJ: default case clause that explicitly expresses that the default assignments made earlier are kept
      begin
         // keep default assignments
      end
// leda W192 on
// leda B_3400 on
  endcase // case(state_r)
  end
end

always @*
begin: bpu_bta_miss_PROC
  bta_miss = capture_bta_miss; 
end

always @*
begin: bpu_misc_PROC


  bc_needed = wq0_high_priority | wq1_high_priority 
              | (bwq_high_priority_r & (~(way_req_r & (~wayq_full_r))))
              | (~way_req_r) & wayq_full_r; 

end

always @(posedge clk or posedge rst_a)
begin: bpu_bc_needed_PROC
if (rst_a == 1'b1)
begin
  bc_needed_r <= 1'b0;
end
else
begin
  bc_needed_r <= bc_needed;
end

end // bpu_bc_needed_PROC




always @*
begin: bpu_ghr_next_PROC


ghr_next = ghr_r;
  mp_alt_way_valid = 1'b0;
  mp_alt_way = {`npuarc_IC_WAYS_BITS{1'b0}};
  mp_way_sec = 1'b0;


  mp_tos = {`npuarc_PC_BITS{1'b0}};
//mp_primary_offset = 2'b0;
  mp_primary_offset = {`npuarc_BR_OFFSET_SIZE{1'b0}};
  mp_primary_valid = 1'b0;
  
{ 
   mp_alt_way_valid,            // the alt way is valid
   mp_alt_way [`npuarc_IC_WAYS_BITS_RANGE], // Alternate predicted way to be used in case of a mispredict
   mp_way_sec,               // is the alt way from a secondary branch?

   mp_tos [`npuarc_BR_BC_BTA_RANGE],      // Return Stack Top of Stack value
// mp_primary_offset[1:0],
   mp_primary_offset[`npuarc_BR_OFFSET_RANGE],
   mp_primary_valid,
   mp_tosp [`npuarc_BR_RS_RANGE],     // Return Stack Top Of Stack Pointer
   mp_num_nt[1:0],       // number of not taken branches in the 128-bit fetch block between the entry point and the current branch 
   mp_ghr[`npuarc_BR_PT_RANGE],    // Global history register as valid at the start of the fetch block (can be 64-bit or 128-bit)
   mp_c                    // Gshare confidence

} = mispredict_branch_info [`npuarc_BR_FULL_INFO_RANGE] ;
//--------------------------------------------------------------------------

//mp_primary_match = (mp_primary_offset == mpd_pc[2:1]);
mp_primary_match = (mp_primary_offset == mpd_pc[`npuarc_BR_OFFSET_SIZE:1]); 
  mp_uncond = mpd_type[0] & (mpd_type != `npuarc_BR_NOT_PREDICTED);
  
//--------------------------------------------------------------------------
//--------------------------------------------------------------------------

  if (mpd_error_branch 
      )
    begin
      ghr_restore = mp_ghr;
    end
  else if (mp_uncond)
  begin
      case(mp_num_nt[1:0])
        2'd0: ghr_restore = mp_ghr;
        2'd1: ghr_restore = {mp_ghr[`npuarc_BR_PT_MSB-1:`npuarc_BR_PT_LSB], 1'b0};
        2'd2: ghr_restore = {mp_ghr[`npuarc_BR_PT_MSB-2:`npuarc_BR_PT_LSB], 2'b00};
        2'd3: ghr_restore = {mp_ghr[`npuarc_BR_PT_MSB-3:`npuarc_BR_PT_LSB], 3'b000};
      endcase        
  end
  else
    begin
      
      case(mp_num_nt[1:0])
        2'd0: ghr_restore = {mp_ghr[`npuarc_BR_PT_MSB-1:`npuarc_BR_PT_LSB], mpd_direction};
        2'd1: ghr_restore = {mp_ghr[`npuarc_BR_PT_MSB-2:`npuarc_BR_PT_LSB], 1'b0, mpd_direction};
        2'd2: ghr_restore = {mp_ghr[`npuarc_BR_PT_MSB-3:`npuarc_BR_PT_LSB], 2'b00, mpd_direction};
        2'd3: ghr_restore = {mp_ghr[`npuarc_BR_PT_MSB-4:`npuarc_BR_PT_LSB], 3'b000, mpd_direction};
      endcase        
    end // if (mp_brcond)

//--------------------------------------------------------------------------
//--------------------------------------------------------------------------

if ((taken & brtype_cond) | bta_miss)
begin
  case(num_nt[1:0])
    2'd0: ghr_pred = {ghr_r[`npuarc_BR_PT_MSB-1:`npuarc_BR_PT_LSB], 1'b1};
    2'd1: ghr_pred = {ghr_r[`npuarc_BR_PT_MSB-2:`npuarc_BR_PT_LSB], 2'b01};
    2'd2: ghr_pred = {ghr_r[`npuarc_BR_PT_MSB-3:`npuarc_BR_PT_LSB], 3'b001};
    2'd3: ghr_pred = {ghr_r[`npuarc_BR_PT_MSB-4:`npuarc_BR_PT_LSB], 4'b0001};
  endcase        
end
else // if (not_taken)
begin
  case({nt4,num_nt[1:0]})
    {1'b0, 2'd0}: ghr_pred = ghr_r;
    {1'b0, 2'd1}: ghr_pred = {ghr_r[`npuarc_BR_PT_MSB-1:`npuarc_BR_PT_LSB], 1'b0};
    {1'b0, 2'd2}: ghr_pred = {ghr_r[`npuarc_BR_PT_MSB-2:`npuarc_BR_PT_LSB], 2'b00};
    {1'b0, 2'd3}: ghr_pred = {ghr_r[`npuarc_BR_PT_MSB-3:`npuarc_BR_PT_LSB], 3'b000};
    default: ghr_pred = {ghr_r[`npuarc_BR_PT_MSB-4:`npuarc_BR_PT_LSB], 4'b0000};
  endcase        
end
//--------------------------------------------------------------------------

  case(cm_num_nt[1:0])
    2'd0: ghr_restart = cm_ghr;
    2'd1: ghr_restart = {cm_ghr[`npuarc_BR_PT_MSB-1:`npuarc_BR_PT_LSB], 1'b0};
    2'd2: ghr_restart = {cm_ghr[`npuarc_BR_PT_MSB-2:`npuarc_BR_PT_LSB], 2'b00};
    2'd3: ghr_restart = {cm_ghr[`npuarc_BR_PT_MSB-3:`npuarc_BR_PT_LSB], 3'b000};
  endcase        
//--------------------------------------------------------------------------



if (mpd_mispred & fch_restart)
begin
  ghr_next = ghr_restore;
end
else if (fch_restart)
  begin
  ghr_next = ghr_restart;
  end  
else if (ghr_captured_r)
begin
  ghr_next = ghr_r; 
end
else if((~cycle2_r) & (capture_bta | capture_bta_miss | start_prediction))
begin
  ghr_next = ghr_pred;

end


end
//--------------------------------------------------------------------------
//--------------------------------------------------------------------------
//--------------------------------------------------------------------------

always @(posedge clk or posedge rst_a)
begin: bpu_ghr_PROC
  if (rst_a == 1'b1)
  begin
    ghr_r   <= {`npuarc_BR_PT_ADDR_SIZE{1'b0}}; 
  end
  else
  begin
    ghr_r   <= ghr_new;
  end
end // bpu_ghr_PROC

always @(*)
begin: bpu_ghr_update_PROC
  ghr_new = ghr_r;

  if (bpu_wctl)
  begin
    ghr_new = {`npuarc_BR_PT_ADDR_SIZE{1'b0}}; 
  end
  else
  begin
  
    // check BPU_CTRL if GHR should be updated
    if (~ghr_freeze)
    begin
      ghr_new = ghr_next;
    end
  end
end // bpu_ghr_update_PROC 


always @*
begin: bpu_commit_PROC

  // initialize queue control
  bwq_write = 1'b0;
  wq0_write = 1'b0;
  wq1_write = 1'b0;

  clear_secondary = 1'b0;
  set_primary = 1'b0;
  primary_match = 1'b0;

//--------------------------------------------------------------------------
  cm_alt_way_valid = 1'b0;
  cm_alt_way = {`npuarc_IC_WAYS_BITS{1'b0}};
  cm_way_sec = 1'b0;
  cm_tos = {`npuarc_BR_BC_BTA_SIZE{1'b0}};
//cm_primary_offset = 2'b0;
  cm_primary_offset =  {`npuarc_BR_OFFSET_SIZE{1'b0}};
  cm_primary_valid = 1'b0;

  { 
    cm_alt_way_valid,            // the alt way is valid
    cm_alt_way [`npuarc_IC_WAYS_BITS_RANGE], // Alternate predicted way to be used in case of a mispredict
    cm_way_sec,               // is the alt way from a secondary branch?
  
    cm_tos [`npuarc_BR_BC_BTA_RANGE],      // Return Stack Top of Stack value
//  cm_primary_offset[1:0],
    cm_primary_offset[`npuarc_BR_OFFSET_RANGE], 
    cm_primary_valid,
    cm_tosp [`npuarc_BR_RS_RANGE],     // Return Stack Top Of Stack Pointer
    cm_num_nt[1:0],       // number of not taken branches in the 128-bit fetch block between the entry point and the current branch 
    cm_ghr[`npuarc_BR_PT_RANGE],    // Global history register as valid at the start of the fetch block (can be 64-bit or 128-bit)
    cm_c_in                    // Gshare confidence
  } = commit_branch_info [`npuarc_BR_FULL_INFO_RANGE] ;
//--------------------------------------------------------------------------
  
//cm_bank = wa_pc[3];
  cm_bank = wa_pc[`npuarc_IC_BANK_SEL]; 
//cm_offset = wa_pc[2:1];
  cm_offset = wa_pc[`npuarc_BR_OFFSET_SIZE:1]; 
  cm_p = wa_direction;
  cm_c = cm_c_in;
  cm_type = wa_type;
  cm_f_bit = wa_tail_pc_3 ^ cm_bank;
  primary_match = (cm_primary_offset == cm_offset);
 
  if (wa_pass 
      & (~wa_error_branch)
      & (
         (wa_type == `npuarc_BR_CONDITIONAL) 
         | (wa_type == `npuarc_BR_COND_CALL)
         | (wa_type == `npuarc_BR_COND_RETURN)
         )
      )
  begin
    if (wa_is_predicted)
    begin
      if (wa_mispred_outcome)
      begin
        if (cm_c_in)
        begin
          cm_c = 1'b0;
          cm_p = ~wa_direction; 
        end
        wq0_write = ~cm_bank & (~wq0_full) & ~pt_freeze;
        wq1_write = cm_bank & (~wq1_full) & ~pt_freeze;
      end
      else
      begin
        if (~cm_c_in)
        begin
          cm_c = 1'b1;
          cm_p = wa_direction;
          wq0_write = ~cm_bank & (~wq0_full) & ~pt_freeze;
          wq1_write = cm_bank & (~wq1_full) & ~pt_freeze;
        end
      end
    end
    else if (wa_direction)
    begin

      cm_p = 1'b1;
      cm_c = 1'b0;
      wq0_write = ~cm_bank & (~wq0_full) & ~pt_freeze & ~pt_no_new;
      wq1_write = cm_bank & (~wq1_full) & ~pt_freeze & ~pt_no_new;
    end  
  end
//--------------------------------------------------------------------------



  wq0_din[`npuarc_BR_PTQ_DATA_RANGE] = {cm_p, cm_c, wa_pc[`npuarc_BR_PT_RANGE] ^ cm_ghr[`npuarc_BR_PT_RANGE], cm_offset};
  wq1_din = wq0_din;
//--------------------------------------------------------------------------



  if (wa_pass)
  begin
    if (wa_error_branch & ~bc_disable)
    begin
      clear_secondary = 1'b1;
      set_primary = 1'b1;
      cm_type = {`npuarc_BR_TYPE_BITS{1'b0}};//`BR_NOT_PREDICTED;

      if (~bwq_full_r)
      begin
        bwq_write = 1'b1;
      end
    end
    else if (
             (
              (wa_is_predicted & (~wa_mispred_outcome) & wa_commit_mispred_bta)
              |
              (~wa_is_predicted)
              )
             &
             wa_direction
             &
             (wa_type != `npuarc_BR_NOT_PREDICTED) 
             &
             (~bc_freeze) 
        
             )
    begin
      if (wa_secondary & (~wa_dslot))
      begin
        if (cm_primary_valid)
        begin
          if (primary_match)
            set_primary = 1'b1;
        end
        else
        begin
          set_primary = 1'b1;
          clear_secondary = 1'b1;
        end
      end
      else
      begin
        set_primary = 1'b1;
        clear_secondary = ~cm_primary_valid;
      end

   
      if (~bwq_full_r)
      begin
        bwq_write = 1'b1;
      end
    end
  end // if (wa_pass)
end // always@

//--------------------------------------------------------------------------
//--------------------------------------------------------------------------
//--------------------------------------------------------------------------



always @(posedge clk or posedge rst_a)
begin: bpu_bwq_PROC
  if (rst_a == 1'b1)
  begin
    bwq_full_r                    <= 1'b0; 
    bwq_high_priority_r           <= 1'b0;
    al_pass_r                     <= 1'b0;
    bwq_set_primary_r             <= 1'b0;
    bwq_clear_secondary_r         <= 1'b0;
    bwq_bank_r                    <= 1'b0;
    bwq_index_r                   <= `npuarc_BR_BC_IDX_SIZE'd0;
    bwq_offset_r                  <= `npuarc_BR_OFFSET_SIZE'd0;
    bwq_type_r                    <= `npuarc_BR_TYPE_BITS'd0;
    bwq_size_r                    <= 2'b0;
    bwq_d_bit_r                   <= 1'b0;
    bwq_f_bit_r                   <= 1'b0;
    bwq_bta_r                     <= `npuarc_PC_BITS'd0;
    bwq_tag_r                     <= `npuarc_BR_BC_TAG_SIZE'd0;          
  end
  else
  begin
    bwq_full_r                    <= bwq_full_next;
    bwq_high_priority_r           <= bwq_high_priority_next;
    al_pass_r                     <= al_pass_next;
    bwq_set_primary_r             <= bwq_set_primary_next;
    bwq_clear_secondary_r         <= bwq_clear_secondary_next;
    bwq_bank_r                    <= bwq_bank_next;
    bwq_index_r                   <= bwq_index_next;
    bwq_offset_r                  <= bwq_offset_next;
    bwq_type_r                    <= bwq_type_next;
    bwq_size_r                    <= bwq_size_next;
    bwq_d_bit_r                   <= bwq_d_bit_next;
    bwq_f_bit_r                   <= bwq_f_bit_next;
    bwq_bta_r                     <= bwq_bta_next;
    bwq_tag_r                     <= bwq_tag_next;
  end
end // block: bpu_bwq_PROC

always @(*)
begin: bpu_bwq_update_PROC
  bwq_full_next                   = bwq_full_r;
  bwq_high_priority_next          = bwq_high_priority_r;
  al_pass_next                    = al_pass_r;
  bwq_set_primary_next            = bwq_set_primary_r;
  bwq_clear_secondary_next        = bwq_clear_secondary_r;
  bwq_bank_next                   = bwq_bank_r;
  bwq_index_next                  = bwq_index_r;
  bwq_offset_next                 = bwq_offset_r;
  bwq_type_next                   = bwq_type_r;
  bwq_size_next                   = bwq_size_r[1:0];
  bwq_d_bit_next                  = bwq_d_bit_r;
  bwq_f_bit_next                  = bwq_f_bit_r;
  bwq_bta_next                    = bwq_bta_r;
  bwq_tag_next                    = bwq_tag_r;

  if (init)
  begin
    bwq_full_next                 = 1'b0; 
    bwq_high_priority_next        = 1'b0;
    al_pass_next                  = 1'b0;
    bwq_set_primary_next          = 1'b0;
    bwq_clear_secondary_next      = 1'b0;
  end
  else if (bwq_write)
  begin
    // keep track if there is something in the write buffer
    bwq_full_next               = 1'b1;
    bwq_set_primary_next        = set_primary;
    bwq_clear_secondary_next    = clear_secondary;
    bwq_bank_next               = cm_bank;
    bwq_index_next              = wa_pc[`npuarc_BR_BC_IDX_RANGE];
    bwq_tag_next                = wa_pc[`npuarc_BR_BC_TAG_RANGE]; 
    bwq_offset_next             = cm_offset;
    bwq_type_next               = cm_type;
    
    if (wa_error_branch)
    begin
      bwq_size_next[1:0]        = 2'b0;
      bwq_d_bit_next            = 1'b0;
      bwq_f_bit_next            = 1'b0;
      bwq_bta_next              = `npuarc_PC_BITS'd0;
    end
    else
    begin
      bwq_size_next[1:0]        = wa_commit_size;
      bwq_d_bit_next            = wa_dslot;
      bwq_f_bit_next            = cm_f_bit;
      bwq_bta_next              = wa_target[`npuarc_BR_BC_BTA_RANGE];
    end
  end // if (bwq_write)

  else if (bwq_read)
  begin
    bwq_full_next               = 1'b0;
  end // bwq_read


  if (bwq_write & wa_error_branch)
  begin
      bwq_high_priority_next    = 1'b1;
  end
  else if (fch_restart | (bwq_high_priority_r & bwq_read))
  begin
    al_pass_next                = 1'b0;
    bwq_high_priority_next      = 1'b0;
  end
  else
  begin
    if (al_pass)
      al_pass_next              = 1'b1;
    if (al_pass_r & bwq_full_r & (~bwq_read))
      bwq_high_priority_next    = 1'b1;
  end
end // block: bpu_bwq_update_PROC

      

always @(posedge clk or posedge rst_a)
begin: bpu_byp_ctrl_PROC
  if (rst_a == 1'b1)
  begin    
    byp_full_r_2cyc                      <= 1'b0;
    byp_set_primary_r_2cyc               <= 1'b0;
    byp_clear_secondary_r_2cyc           <= 1'b0;
  end
  else 
  begin
    byp_full_r_2cyc                      <= byp_full_next_2cyc;
    byp_set_primary_r_2cyc               <= byp_set_primary_next_2cyc;
    byp_clear_secondary_r_2cyc           <= byp_clear_secondary_next_2cyc;
  end
end // bpu_byp_ctrl_PROC

// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
// leda NTL_RST03 off
// LMD: a flipflop without a reset
// LJ: pipeline registers that don't need initialization
always @(posedge clk)
begin: bpu_byp_data_PROC
  byp_type_r_2cyc                        <= byp_type_next_2cyc;
  byp_bank_r_2cyc                        <= byp_bank_next_2cyc;
  byp_index_r_2cyc                       <= byp_index_next_2cyc;
  byp_tag_r_2cyc                         <= byp_tag_next_2cyc;
  byp_offset_r_2cyc                      <= byp_offset_next_2cyc;
  byp_bta_r_2cyc                         <= byp_bta_next_2cyc;
  byp_f_bit_r_2cyc                       <= byp_f_bit_next_2cyc;
  byp_size_r_2cyc                        <= byp_size_next_2cyc;
  byp_d_bit_r_2cyc                       <= byp_d_bit_next_2cyc;
end // bpu_byp_data_PROC
// leda NTL_RST03 on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01

always@ (*)
begin: bpu_byp_updates_PROC

  byp_full_next_2cyc                      =  byp_full_r_2cyc;
  byp_set_primary_next_2cyc               =  byp_set_primary_r_2cyc;
  byp_clear_secondary_next_2cyc           =  byp_clear_secondary_r_2cyc;
  byp_type_next_2cyc                      =  byp_type_r_2cyc;
  byp_bank_next_2cyc                      =  byp_bank_r_2cyc;
  byp_index_next_2cyc                     =  byp_index_r_2cyc;
  byp_tag_next_2cyc                       =  byp_tag_r_2cyc; 
  byp_offset_next_2cyc                    =  byp_offset_r_2cyc;
  byp_bta_next_2cyc                       =  byp_bta_r_2cyc; 
  byp_f_bit_next_2cyc                     =  byp_f_bit_r_2cyc;
  byp_size_next_2cyc                      =  byp_size_r_2cyc;
  byp_d_bit_next_2cyc                     =  byp_d_bit_r_2cyc;

  if (init)
  begin
    byp_full_next_2cyc                    = 1'b0;
    byp_set_primary_next_2cyc             = 1'b0;
    byp_clear_secondary_next_2cyc         = 1'b0;
  end
  else if (mpd_mispred & fch_restart)
  begin
    if (mpd_error_branch & ~bc_disable)
    begin
      byp_full_next_2cyc                  = 1'b1;
      byp_clear_secondary_next_2cyc       = 1'b1;
      byp_set_primary_next_2cyc           = 1'b1;
      byp_type_next_2cyc                  = {`npuarc_BR_TYPE_BITS{1'b0}}; // `BR_NOT_PREDICTED;
      byp_bank_next_2cyc                  = mpd_pc[`npuarc_IC_BANK_SEL];
      byp_index_next_2cyc                 = mpd_pc[`npuarc_BR_BC_IDX_RANGE];
      byp_tag_next_2cyc                   = mpd_pc[`npuarc_BR_BC_TAG_RANGE]; 
      byp_offset_next_2cyc                = mpd_pc[`npuarc_BR_OFFSET_SIZE:1];
      byp_bta_next_2cyc                   = fch_target_bta; 

      byp_f_bit_next_2cyc                 = 1'b0;
      byp_size_next_2cyc[1:0]             = 2'b0;
      byp_d_bit_next_2cyc                 = 1'b0;

    end
    else if (
              (
                (mpd_is_predicted & (~mpd_mispred_outcome) & mpd_mispred_bta)
                |
                (~mpd_is_predicted)
              )
              &
              mpd_direction
              &
              (mpd_type != `npuarc_BR_NOT_PREDICTED)
              & 
              (~bc_freeze)        
            )
    begin
      byp_full_next_2cyc                  = 1'b1;
      byp_type_next_2cyc                  = mpd_type;
      byp_bank_next_2cyc                  = mpd_pc[`npuarc_IC_BANK_SEL];
      byp_index_next_2cyc                 = mpd_pc[`npuarc_BR_BC_IDX_RANGE];
      byp_tag_next_2cyc                   = mpd_pc[`npuarc_BR_BC_TAG_RANGE]; 
      byp_offset_next_2cyc                = mpd_pc[`npuarc_BR_OFFSET_SIZE:1];
      byp_bta_next_2cyc                   = fch_target_bta; 
      byp_size_next_2cyc[1:0]             = mpd_commit_size;
      byp_d_bit_next_2cyc                 = mpd_dslot;
      byp_f_bit_next_2cyc                 = mpd_tail_pc_3 ^ mpd_pc[`npuarc_IC_BANK_SEL];

      if (mpd_secondary & (~mpd_dslot))
      begin
        //++++++++++++++++++++mp_primary_valid
        if (mp_primary_valid)
        begin
          if (mp_primary_match)
          begin
            byp_set_primary_next_2cyc     = 1'b1;
            byp_clear_secondary_next_2cyc = 1'b0;
          end
          else
          begin
            byp_set_primary_next_2cyc     = 1'b0; 
            byp_clear_secondary_next_2cyc = 1'b0;
          end
        end
        //++++++++++++++++++++end mp_primary_valid
        else
        begin
          byp_set_primary_next_2cyc       = 1'b1;
          byp_clear_secondary_next_2cyc   = 1'b1;
        end
      end
      //++++++++++++++++if (mpd_secondary & (~mpd_dslot))
      else
      begin
        byp_set_primary_next_2cyc         = 1'b1;
        byp_clear_secondary_next_2cyc     = ~mp_primary_valid;
      end
    end
    else
    begin
      byp_full_next_2cyc                  = 1'b0;
    end
  end 
  //--------------------------------------------------------------------------end (mpd_mispred & fch_restart)
  else if (fch_restart)
  begin
    byp_full_next_2cyc                    = 1'b0;
  end
end // bpu_byp_updates_PROC



always @*
begin: way_req_response_PROC
  way_req_response = wr_way & way_req_r;
end

always@ (*)
begin: way_req_PROC 
  way_req_next   = way_req_r;

  if (restart)
    way_req_next = way_req & ~bc_freeze;
  else if (wayq_read)
    way_req_next = 1'b0;
end // way_req_PROC

always @(*)
begin: wayq_full_PROC
  wayq_full_next   = wayq_full_r;

  if (fch_restart) 
    wayq_full_next = 1'b0;
  else if (wr_way & ~bc_freeze)
    wayq_full_next = 1'b1;
  else if (wayq_read) 
    wayq_full_next = 1'b0;
end // wayq_full_PROC

always @(*)
begin: way_byp_full_PROC
  way_byp_full_next = way_byp_full_r;

  if (fch_restart) 
    way_byp_full_next = 1'b0;
  else if (way_req_response)
    way_byp_full_next = 1'b1;
end // way_byp_full_PROC

always @(*)
begin: way_byp_full_delayed_PROC
  way_byp_full_r_next   = way_byp_full_r_r;

  // to avoid a 2-cycle path hazard, create 2-cycle delay after the response
  if (fch_restart)
  begin
    way_byp_full_r_next = 1'b0;
  end
  else
  begin
    way_byp_full_r_next = way_byp_full_r;
  end
end // way_byp_full_delayed_PROC

always @(posedge clk or posedge rst_a)
begin: bpu_wayqA_PROC
  if (rst_a == 1'b1)
  begin
    way_req_r          <= 1'b0;
    wayq_full_r        <= 1'b0; 
    way_byp_full_r     <= 1'b0;
    way_byp_full_r_r   <= 1'b0;
  end
  else
  begin
    way_req_r          <= way_req_next;
    wayq_full_r        <= wayq_full_next; 
    way_byp_full_r     <= way_byp_full_next;
    way_byp_full_r_r   <= way_byp_full_r_next;
  end
end // bpu_wayqA_PROC

always @(posedge clk or posedge rst_a)
begin: bpu_wayqB_PROC
  if (rst_a == 1'b1)
  begin
    way_in_r      <= {`npuarc_IC_WAYS_BITS{1'b0}};
    way_in_sec_r  <= 1'b0;
    way_index_r   <= {`npuarc_BR_BC_IDX_SIZE{1'b0}};
    way_bank_r    <= 1'b0;
  end
  else if (wr_way & (~wayq_full_r | wayq_read) & ~bc_freeze)
  begin
    way_in_r      <= way_in;
    way_in_sec_r  <= way_in_sec;
    way_index_r   <= way_index;
    way_bank_r    <= way_bank;
  end
end // bpu_wayqB_PROC

always @(posedge clk or posedge rst_a)
begin: bpu_wayqC_PROC
  if (rst_a == 1'b1)
  begin
    way_byp_in_r         <= {`npuarc_IC_WAYS_BITS{1'b0}};
  end
  else if (way_req_response & (~way_byp_full_r))
  begin
    way_byp_in_r         <= way_in;
  end
end // bpu_wayqC_PROC


always @*
begin: bpu_queues_PROC



  bc_entry = 
  {
   way_in_r[`npuarc_IC_WAYS_BITS_RANGE],
   bwq_offset_r[`npuarc_BR_OFFSET_RANGE], // secondary branch
   ~bwq_set_primary_r, //secondary_valid,
   bwq_f_bit_r,
   bwq_tag_r[`npuarc_BR_BC_TAG_RANGE], 
   bwq_offset_r[`npuarc_BR_OFFSET_RANGE], // primary branch
   bwq_type_r[`npuarc_BR_TYPE_RANGE],
   bwq_bta_r[`npuarc_BR_BC_BTA_RANGE], 
   way_in_r[`npuarc_IC_WAYS_BITS_RANGE], 
   bwq_size_r[1:0], 
   bwq_d_bit_r, 
   bwq_f_bit_r
   };
//--------------------------------------------------------------------------


/*   set_primary_wem = 
  {
   {`npuarc_IC_WAYS_BITS{1'b0}}, // bwq_way_r[`IC_WAYS_BITS_RANGE],
   {`npuarc_BR_OFFSET_SIZE{1'b0}}, // bwq_offset_r[`BR_OFFSET_RANGE], // secondary branch
   bwq_clear_secondary_r, // secondary_valid,
   1'b0, // bwq_f_bit_r,
   {`npuarc_BR_BC_TAG_SIZE{1'b1}}, //bwq_tag_r[`BR_BC_TAG_RANGE], 
   {`npuarc_BR_OFFSET_SIZE{1'b1}}, //bwq_offset_r[`BR_OFFSET_RANGE], // primary branch
   {`npuarc_BR_TYPE_BITS{1'b1}}, //bwq_type_r[`BR_TYPE_RANGE],
   {`npuarc_BR_BC_BTA_SIZE{1'b1}}, //bwq_bta_r[`BR_BC_BTA_RANGE], 
   {`npuarc_IC_WAYS_BITS{way_req_r}}, //bwq_way_r[`IC_WAYS_BITS_RANGE], 
   2'b11, //bwq_size_r[1:0], 
   1'b1, //bwq_d_bit_r, 
   1'b1 //bwq_f_bit_r
   };

   set_primary_way_wem = 
  {
   {`npuarc_IC_WAYS_BITS{1'b0}}, // bwq_way_r[`IC_WAYS_BITS_RANGE],
   {`npuarc_BR_OFFSET_SIZE{1'b0}}, // bwq_offset_r[`BR_OFFSET_RANGE], // secondary branch
   1'b0, // secondary_valid,
   1'b0, // bwq_f_bit_r,
   {`npuarc_BR_BC_TAG_SIZE{1'b0}}, //bwq_tag_r[`BR_BC_TAG_RANGE], 
   {`npuarc_BR_OFFSET_SIZE{1'b0}}, //bwq_offset_r[`BR_OFFSET_RANGE], // primary branch
   {`npuarc_BR_TYPE_BITS{1'b0}}, //bwq_type_r[`BR_TYPE_RANGE],
   {`npuarc_BR_BC_BTA_SIZE{1'b0}}, //bwq_bta_r[`BR_BC_BTA_RANGE], 
   {`npuarc_IC_WAYS_BITS{1'b1}}, //bwq_way_r[`IC_WAYS_BITS_RANGE], 
   2'b00, //bwq_size_r[1:0], 
   1'b0, //bwq_d_bit_r, 
   1'b0 //bwq_f_bit_r
   };
     
  set_secondary_wem = 
  {
   {`npuarc_IC_WAYS_BITS{way_req_r}}, // bwq_way_r[`IC_WAYS_BITS_RANGE],
   {`npuarc_BR_OFFSET_SIZE{1'b1}}, // bwq_offset_r[`BR_OFFSET_RANGE], // secondary branch
   1'b1, // secondary_valid,
   1'b1, // bwq_f_bit_r,
   {`npuarc_BR_BC_TAG_SIZE{1'b0}}, //bwq_tag_r[`BR_BC_TAG_RANGE], 
   {`npuarc_BR_OFFSET_SIZE{1'b0}}, //bwq_offset_r[`BR_OFFSET_RANGE], // primary branch
   {`npuarc_BR_TYPE_BITS{1'b0}}, //bwq_type_r[`BR_TYPE_RANGE],
   {`npuarc_BR_BC_BTA_SIZE{1'b0}}, //bwq_bta_r[`BR_BC_BTA_RANGE], 
   {`npuarc_IC_WAYS_BITS{1'b0}}, //bwq_way_r[`IC_WAYS_BITS_RANGE], 
   2'b00, //bwq_size_r[1:0], 
   1'b0, //bwq_d_bit_r, 
   1'b0 //bwq_f_bit_r
 };
  
  set_secondary_way_wem = 
  {
   {`npuarc_IC_WAYS_BITS{1'b1}}, // bwq_way_r[`IC_WAYS_BITS_RANGE],
   {`npuarc_BR_OFFSET_SIZE{1'b0}}, // bwq_offset_r[`BR_OFFSET_RANGE], // secondary branch
   1'b0, // secondary_valid,
   1'b0, // bwq_f_bit_r,
   {`npuarc_BR_BC_TAG_SIZE{1'b0}}, //bwq_tag_r[`BR_BC_TAG_RANGE], 
   {`npuarc_BR_OFFSET_SIZE{1'b0}}, //bwq_offset_r[`BR_OFFSET_RANGE], // primary branch
   {`npuarc_BR_TYPE_BITS{1'b0}}, //bwq_type_r[`BR_TYPE_RANGE],
   {`npuarc_BR_BC_BTA_SIZE{1'b0}}, //bwq_bta_r[`BR_BC_BTA_RANGE], 
   {`npuarc_IC_WAYS_BITS{1'b0}}, //bwq_way_r[`IC_WAYS_BITS_RANGE], 
   2'b00, //bwq_size_r[1:0], 
   1'b0, //bwq_d_bit_r, 
   1'b0 //bwq_f_bit_r
 };
  
*/



  bc_din0 = bpu_wctl ? {`npuarc_BR_BC_DATA_BITS{1'b0}} : bc_entry ; // branch cache entry
//--------------------------------------------------------------------------


//--------------------------------------------------------------------------  bc_wem0 

  if (bpu_wctl)
  begin
    bc_wem0 = {`npuarc_BR_BC_DATA_BITS{1'b1}};
  end
  else if (bwq_set_primary_r)
 //   bc_wem0 = set_primary_wem;
    bc_wem0 =    
      {
   {`npuarc_IC_WAYS_BITS{1'b0}}, // bwq_way_r[`IC_WAYS_BITS_RANGE],
   {`npuarc_BR_OFFSET_SIZE{1'b0}}, // bwq_offset_r[`BR_OFFSET_RANGE], // secondary branch
   bwq_clear_secondary_r, // secondary_valid,
   1'b0, // bwq_f_bit_r,
   {`npuarc_BR_BC_TAG_SIZE{1'b1}}, //bwq_tag_r[`BR_BC_TAG_RANGE], 
   {`npuarc_BR_OFFSET_SIZE{1'b1}}, //bwq_offset_r[`BR_OFFSET_RANGE], // primary branch
   {`npuarc_BR_TYPE_BITS{1'b1}}, //bwq_type_r[`BR_TYPE_RANGE],
   {`npuarc_BR_BC_BTA_SIZE{1'b1}}, //bwq_bta_r[`BR_BC_BTA_RANGE], 
   {`npuarc_IC_WAYS_BITS{way_req_r}}, //bwq_way_r[`IC_WAYS_BITS_RANGE], 
   2'b11, //bwq_size_r[1:0], 
   1'b1, //bwq_d_bit_r, 
   1'b1 //bwq_f_bit_r
   };
    
  else
 //   bc_wem0 = set_secondary_wem;
     bc_wem0 =    
    {
   {`npuarc_IC_WAYS_BITS{way_req_r}}, // bwq_way_r[`IC_WAYS_BITS_RANGE],
   {`npuarc_BR_OFFSET_SIZE{1'b1}}, // bwq_offset_r[`BR_OFFSET_RANGE], // secondary branch
   1'b1, // secondary_valid,
   1'b1, // bwq_f_bit_r,
   {`npuarc_BR_BC_TAG_SIZE{1'b0}}, //bwq_tag_r[`BR_BC_TAG_RANGE], 
   {`npuarc_BR_OFFSET_SIZE{1'b0}}, //bwq_offset_r[`BR_OFFSET_RANGE], // primary branch
   {`npuarc_BR_TYPE_BITS{1'b0}}, //bwq_type_r[`BR_TYPE_RANGE],
   {`npuarc_BR_BC_BTA_SIZE{1'b0}}, //bwq_bta_r[`BR_BC_BTA_RANGE], 
   {`npuarc_IC_WAYS_BITS{1'b0}}, //bwq_way_r[`IC_WAYS_BITS_RANGE], 
   2'b00, //bwq_size_r[1:0], 
   1'b0, //bwq_d_bit_r, 
   1'b0 //bwq_f_bit_r
 };  
//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++bc_wem0 . goto L3

bc_din1 = bc_din0;
bc_wem1 = bc_wem0;

//--------------------------------------------------------------------------




  wq0_read = 1'b0;
  {wq0_pred, wq0_index, wq0_offset} = wq0_dout; 
  gs_me0 = 1'b0;
  gs_we0 = 1'b0;
//--------------------------------------------------------------------------
//gs_din0 = bpu_wctl ? 8'b10101010 : {4{wq0_pred[1:0]}};
  gs_din0 = bpu_wctl ? {`npuarc_BR_GHR_SIZE{8'b10101010}} : {`npuarc_BR_GHR_SIZE{{4{wq0_pred[1:0]}}}}; 
  case (wq0_offset)
    2'b00: gs_wem0 = 8'b00_00_00_11;
    2'b01: gs_wem0 = 8'b00_00_11_00;
    2'b10: gs_wem0 = 8'b00_11_00_00;
    2'b11: gs_wem0 = 8'b11_00_00_00;
  endcase

//gs_wem0 = { {`BR_PT_DATA_SIZE{1'b0}}, {2'b11}}    << wq0_offset;  
  
  if (bpu_wctl) 
     gs_wem0 = {`npuarc_BR_GHR_SIZE{8'b11111111}};
//--------------------------------------------------------------------------

  wq1_read = 1'b0;
  {wq1_pred, wq1_index, wq1_offset} = wq1_dout; 
  gs_me1 = 1'b0;
  gs_we1 = 1'b0;
//--------------------------------------------------------------------------
//gs_din1 =  bpu_wctl ? 8'b10101010 : {4{wq1_pred[1:0]}};
  gs_din1 =  bpu_wctl ? {`npuarc_BR_GHR_SIZE{8'b10101010}} : {`npuarc_BR_GHR_SIZE{{4{wq1_pred[1:0]}}}}; 

  case (wq1_offset)
    2'b00: gs_wem1 = 8'b00_00_00_11;
    2'b01: gs_wem1 = 8'b00_00_11_00;
    2'b10: gs_wem1 = 8'b00_11_00_00;
    2'b11: gs_wem1 = 8'b11_00_00_00;
  endcase
//  gs_wem1 = { {`BR_PT_DATA_SIZE{1'b0}}, {2'b11}}    << wq1_offset;  

  if (bpu_wctl) 
     gs_wem1= {`npuarc_BR_GHR_SIZE{8'b11111111}};
//--------------------------------------------------------------------------



  bwq_read = 1'b0; // default value
  wayq_read = 1'b0;
  bc_me0 = 1'b0;
  bc_me1 = 1'b0;
  bc_we0 = 1'b0;
  cycle_steal = 1'b0;

  gs_addr0 = gs_addr0_pre;
  gs_addr1 = gs_addr1_pre;
  bc_addr0 = bc_addr0_pre;
  bc_addr1 = bc_addr1_pre;  

  if (start_prediction)
  begin 
     gs_me0 = ~cross_line & ~pt_freeze; 
     gs_we0 = 1'b0;

     gs_me1 = ~pt_freeze;
     gs_we1 = 1'b0;

     bc_me0 = ~cross_line;
     bc_we0 = 1'b0;
 
     bc_me1 = 1'b1;

  end
  else if (init)
  begin 
     gs_me0 = 1'b1;
     gs_we0 = 1'b1;
     gs_me1 = 1'b1;
     gs_we1 = 1'b1;
     bc_me0 = 1'b1;
     bc_we0 = 1'b1;
     bc_me1 = 1'b1;
  end // if (init)
  else if (~cycle2_r & (~restart_captured_r | bc_needed_r))
  begin


     if (~wq0_empty)
     begin
       gs_addr0 = wq0_index;
       gs_me0 = 1'b1;
       gs_we0 = 1'b1;
       wq0_read = 1'b1;
       cycle_steal = 1'b1;
     end

     if (~wq1_empty)
     begin
       gs_addr1 = wq1_index;
       gs_me1 = 1'b1;
       gs_we1 = 1'b1;
       wq1_read = 1'b1;
       cycle_steal = 1'b1;
     end

    if (way_req_r & bwq_full_r & wayq_full_r)
     begin
       // activate the correct bank
       // read both queues
       bc_me0 = ~bwq_bank_r;
       bc_me1 = bwq_bank_r;
       bc_addr0 = bwq_index_r;
       bc_addr1 = bc_addr0;
       bc_we0 = 1'b1;
       bwq_read = 1'b1; 
       wayq_read = 1'b1;
       cycle_steal = 1'b1;
     end
    else if (~way_req_r & bwq_full_r)
    begin
       bc_me0 = ~bwq_bank_r;
       bc_me1 = bwq_bank_r;
       bc_addr0 = bwq_index_r;
       bc_addr1 = bc_addr0;
       bc_we0 = 1'b1;
       bwq_read = 1'b1;
       cycle_steal = 1'b1;
     end
    else if (~way_req_r & wayq_full_r)
    begin
      bc_me0 = ~way_bank_r;
      bc_me1 = way_bank_r;
      bc_addr0 = way_index_r;
      bc_addr1 = bc_addr0;
      bc_we0 = 1'b1;
      wayq_read = 1'b1;
      cycle_steal = 1'b1;
      if (way_in_sec_r)
//        bc_wem0 = set_secondary_way_wem;
       bc_wem0 = 
        {
   {`npuarc_IC_WAYS_BITS{1'b1}}, // bwq_way_r[`IC_WAYS_BITS_RANGE],
   {`npuarc_BR_OFFSET_SIZE{1'b0}}, // bwq_offset_r[`BR_OFFSET_RANGE], // secondary branch
   1'b0, // secondary_valid,
   1'b0, // bwq_f_bit_r,
   {`npuarc_BR_BC_TAG_SIZE{1'b0}}, //bwq_tag_r[`BR_BC_TAG_RANGE], 
   {`npuarc_BR_OFFSET_SIZE{1'b0}}, //bwq_offset_r[`BR_OFFSET_RANGE], // primary branch
   {`npuarc_BR_TYPE_BITS{1'b0}}, //bwq_type_r[`BR_TYPE_RANGE],
   {`npuarc_BR_BC_BTA_SIZE{1'b0}}, //bwq_bta_r[`BR_BC_BTA_RANGE], 
   {`npuarc_IC_WAYS_BITS{1'b0}}, //bwq_way_r[`IC_WAYS_BITS_RANGE], 
   2'b00, //bwq_size_r[1:0], 
   1'b0, //bwq_d_bit_r, 
   1'b0 //bwq_f_bit_r
 };
   
      else
  //      bc_wem0 = set_primary_way_wem;
      bc_wem0 =
  {
   {`npuarc_IC_WAYS_BITS{1'b0}}, // bwq_way_r[`IC_WAYS_BITS_RANGE],
   {`npuarc_BR_OFFSET_SIZE{1'b0}}, // bwq_offset_r[`BR_OFFSET_RANGE], // secondary branch
   1'b0, // secondary_valid,
   1'b0, // bwq_f_bit_r,
   {`npuarc_BR_BC_TAG_SIZE{1'b0}}, //bwq_tag_r[`BR_BC_TAG_RANGE], 
   {`npuarc_BR_OFFSET_SIZE{1'b0}}, //bwq_offset_r[`BR_OFFSET_RANGE], // primary branch
   {`npuarc_BR_TYPE_BITS{1'b0}}, //bwq_type_r[`BR_TYPE_RANGE],
   {`npuarc_BR_BC_BTA_SIZE{1'b0}}, //bwq_bta_r[`BR_BC_BTA_RANGE], 
   {`npuarc_IC_WAYS_BITS{1'b1}}, //bwq_way_r[`IC_WAYS_BITS_RANGE], 
   2'b00, //bwq_size_r[1:0], 
   1'b0, //bwq_d_bit_r, 
   1'b0 //bwq_f_bit_r
   };

     bc_wem1 = bc_wem0;

     end


  end

bc_we1 = bc_we0;



end // always@



wire                buff_init;
assign buff_init = init
                 ;
npuarc_alb_bpu_write_queue4 #(.WIDTH(`npuarc_BR_PTQ_DATA_BITS)) gs_wq0 (
  .din(wq0_din),
  .write(wq0_write
         ),
  .full(wq0_full),

  .read(wq0_read),
  .dout(wq0_dout),
  .empty(wq0_empty),
  .high_priority(wq0_high_priority),

  .init(buff_init),
  .clk(clk),
  .rst_a(rst_a)

);

npuarc_alb_bpu_write_queue4 #(.WIDTH(`npuarc_BR_PTQ_DATA_BITS)) gs_wq1 (
  .din(wq1_din),
  .write(wq1_write
         ),
  .full(wq1_full),

  .read(wq1_read),
  .dout(wq1_dout),
  .empty(wq1_empty),
  .high_priority(wq1_high_priority),

  .init(buff_init),
  .clk(clk),
  .rst_a(rst_a)

);




always @*
begin: bpu_subtos_PROC  

// leda B_3208 off
// LMD: Unequal length LHS and RHS in assignment
// LJ: arithmetic calculation has a potential dont_care carry bit
  {sub_carry, sub_tos[3:1]} = {fa_p[3], 2'b00} + offset[2:0] + {1'b0, size_pred[1:0]} + 3'b001;
// leda B_3208 on

  sub_tos[`npuarc_BR_BC_BTA_MSB:4] = sub_carry ? fa_seq[`npuarc_BR_BC_BTA_MSB:4] : fa_p[`npuarc_BR_BC_BTA_MSB:4];
   
end
//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
// return stack control
always @*
begin: bpu_stackctrl_PROC
  write_tos = 1'b0;
  write_tosp = 1'b0;
  push_tosp= 1'b0;
  pop_tosp= 1'b0;
  write_tosq = 1'b0;


  if (mpd_mispred & fch_restart)
  begin
      write_tosp = 1'b1;
      write_tos = 1'b1;

      if ((mpd_type == `npuarc_BR_CALL) | (mpd_direction & (mpd_type == `npuarc_BR_COND_CALL)))
      begin
        push_tosp = 1'b1;
        write_tosq = 1'b1;
      end 
      else if ((mpd_type == `npuarc_BR_RETURN) | (mpd_direction & (mpd_type == `npuarc_BR_COND_RETURN)))
      begin
        pop_tosp = 1'b1;
        write_tosq = 1'b1;
        write_tos = 1'b0;
      end
  end // if (mpd_mispred)
  else if (fch_restart)
    begin
      write_tosp = 1'b1;
      write_tos = 1'b1;
      
    end
  else if (prediction_used & taken) 
  begin
    if (subcall)
    begin
      push_tosp = 1'b1;
      write_tos = 1'b1;
      write_tosq = 1'b1;
    end
    else if (subreturn)
    begin
      pop_tosp = 1'b1;
      write_tosq = 1'b1;
    end
  end
  

end
//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

always @*
begin: bpu_mptos_PROC
  tosp_new = mp_tosp;
  tos_new = mp_tos; 
 
  if (mpd_direction & ((mpd_type == `npuarc_BR_CALL) | (mpd_type == `npuarc_BR_COND_CALL)))
  begin
    tos_new = mpd_seq_next_pc_bta;
  end

  if (~(mpd_mispred & fch_restart))
  begin
    tos_new = sub_tos;
  end

  if (fch_restart & (~mpd_mispred))
    begin
      tosp_new = cm_tosp;
      tos_new = cm_tos; 
    end
  
end // always@*
//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++


wire write_tosq_next;

always @(posedge clk or posedge rst_a)
begin: bpu_tosq_PROC
if (rst_a == 1'b1)
begin
  write_tosq_r  <= 1'b0;
  write_tosq0_r <= 1'b0;
end
else
begin
  write_tosq0_r <= write_tosq;
  write_tosq_r  <= write_tosq_next;
end // else: !if(rst_a)
end

assign write_tosq_next = fch_restart ? 1'b0 : write_tosq0_r;


npuarc_alb_bpu_stack ualb_bpu_stack (
  .write_tos    (write_tos),    // write 'din' to the stack
  .write_tosp   (write_tosp),   // write 'tosp_new' to the stack pointer
  .push_tosp    (push_tosp),    // increment stack pointer
  .pop_tosp     (pop_tosp),     // decrement stack pointer

  .tosp_new     (tosp_new),  // new value written to TOSP
  .tos_new      (tos_new),  // data input written to new top of stack
  .top_of_stack (top_of_stack), // top of stack value
  .stack_ptr_r  (stack_ptr_r), // stack pointer

  .stack_freeze (stack_freeze),
  .init         (buff_init),
  .clk          (clk),
  .rst_a        (rst_a)

);

////////////////////////////
// clk gates for BPU RAMs

assign bc_ram0_clk_en = bc_me0
                      ;
assign bc_ram1_clk_en = bc_me1
                      ;
assign pt_ram0_clk_en = gs_me0
                      ;
assign pt_ram1_clk_en = gs_me1
                      ;


npuarc_clkgate u_bc0_clkgate (
  .clk_in            (clk),
  .clock_enable      (bc_ram0_clk_en),
  .clk_out           (bc_ram0_clk)
);

npuarc_clkgate u_bc1_clkgate (
  .clk_in            (clk),
  .clock_enable      (bc_ram1_clk_en),
  .clk_out           (bc_ram1_clk)
);

npuarc_clkgate u_pt0_clkgate (
  .clk_in            (clk),
  .clock_enable      (pt_ram0_clk_en),
  .clk_out           (pt_ram0_clk)
);

npuarc_clkgate u_pt1_clkgate (
  .clk_in            (clk),
  .clock_enable      (pt_ram1_clk_en),
  .clk_out           (pt_ram1_clk)
);





  

  npuarc_alb_2cyc_checker #(.WIDTH(`npuarc_BR_BC_BTA_MSB-`npuarc_IM_LINE_BITS+1)) u0_alb_2cyc_checker 
     (
      .data_in  (fa_high_r_2cyc),
      .data_out (fa_high_r),
      .clk (clk));
//alb_2cyc_checker #(.WIDTH(2)) u1_alb_2cyc_checker 
//alb_2cyc_checker #(.WIDTH(`BR_FA_DIFF_SIZE)) u1_alb_2cyc_checker 
  npuarc_alb_2cyc_checker #(.WIDTH(`npuarc_BR_OFFSET_SIZE)) u1_alb_2cyc_checker 
     (
      .data_in  (fa_offset_r_2cyc),
      .data_out (fa_offset_r),
      .clk (clk));
//  alb_2cyc_checker #(.WIDTH(`IM_LINE_BITS-1-4+1)) u2_alb_2cyc_checker 
  npuarc_alb_2cyc_checker #(.WIDTH(`npuarc_BR_FA_DIFF_SIZE)) u2_alb_2cyc_checker 
     (
      .data_in  (fa0_diff_r_2cyc),
      .data_out (fa0_diff_r),
      .clk (clk));
//  alb_2cyc_checker #(.WIDTH(`IM_LINE_BITS-1-4+1)) u3_alb_2cyc_checker 
  npuarc_alb_2cyc_checker #(.WIDTH(`npuarc_BR_FA_DIFF_SIZE)) u3_alb_2cyc_checker 
     (
      .data_in  (fa1_diff_r_2cyc),
      .data_out (fa1_diff_r),
      .clk (clk));

  npuarc_alb_2cyc_checker #(.WIDTH(1)) u4_alb_2cyc_checker 
     (
      .data_in  (unaligned_r_2cyc),
      .data_out (unaligned_r),
      .clk (clk));

  npuarc_alb_2cyc_checker #(.WIDTH(1)) u5_alb_2cyc_checker 
     (
      .data_in  (cross_line_r_2cyc),
      .data_out (cross_line_r),
      .clk (clk));

  npuarc_alb_2cyc_checker #(.WIDTH(1)) u6_alb_2cyc_checker 
     (
      .data_in  (fetch_tail_r_2cyc),
      .data_out (fetch_tail_r),
      .clk (clk));

  npuarc_alb_2cyc_checker #(.WIDTH(1)) u7_alb_2cyc_checker 
     (
      .data_in  (restart_vec_r_2cyc),
      .data_out (restart_vec_r),
      .clk (clk));


  npuarc_alb_2cyc_checker #(.WIDTH(1)) u10_alb_2cyc_checker 
     (
      .data_in  (start_init_force_r_2cyc),
      .data_out (start_init_force_r),
      .clk (clk));

  npuarc_alb_2cyc_checker #(.WIDTH(1)) u11_alb_2cyc_checker 
     (
      .data_in  (bta_bank_r_2cyc),
      .data_out (bta_bank_r),
      .clk (clk));

  npuarc_alb_2cyc_checker #(.WIDTH(1)) u12_alb_2cyc_checker 
     (
      .data_in  (bta_offset_r_2cyc),
      .data_out (bta_offset_r),
      .clk (clk));





  npuarc_alb_2cyc_checker #(.WIDTH(1)) u16_alb_2cyc_checker 
     (
      .data_in  (
                  byp_full_r_2cyc
                 ),
      .data_out (
                  byp_full_r
                 ),
      .clk (clk));

  npuarc_alb_2cyc_checker #(.WIDTH(1)) u17_alb_2cyc_checker 
     (
      .data_in  (
                  byp_bank_r_2cyc
                 ),
      .data_out (
                  byp_bank_r
                 ),
      .clk (clk));

  npuarc_alb_2cyc_checker #(.WIDTH(1)) u18_alb_2cyc_checker 
     (
      .data_in  (
                 byp_clear_secondary_r_2cyc
                 ),
      .data_out (
                 byp_clear_secondary_r
                 ),
      .clk (clk));

  npuarc_alb_2cyc_checker #(.WIDTH(1)) u19_alb_2cyc_checker 
     (
      .data_in  (
                  byp_set_primary_r_2cyc
                 ),
      .data_out (
                  byp_set_primary_r
                 ),
      .clk (clk));

  npuarc_alb_2cyc_checker #(.WIDTH(`npuarc_BR_BC_IDX_SIZE)) u20_alb_2cyc_checker 
     (
      .data_in  (
                  byp_index_r_2cyc
                 ),
      .data_out (
                  byp_index_r
                 ),
      .clk (clk));

  npuarc_alb_2cyc_checker #(.WIDTH(`npuarc_BR_BC_TAG_SIZE)) u21_alb_2cyc_checker 
     (
      .data_in  (
                  byp_tag_r_2cyc 
                 ),
      .data_out (
                  byp_tag_r 
                 ),
      .clk (clk));

  npuarc_alb_2cyc_checker #(.WIDTH(`npuarc_BR_OFFSET_SIZE)) u22_alb_2cyc_checker 
     (
      .data_in  (
                  byp_offset_r_2cyc
                 ),
      .data_out (
                  byp_offset_r
                 ),
      .clk (clk));

  npuarc_alb_2cyc_checker #(.WIDTH(`npuarc_BR_TYPE_BITS)) u23_alb_2cyc_checker 
     (
      .data_in  (
                  byp_type_r_2cyc
                 ),
      .data_out (
                  byp_type_r
                 ),
      .clk (clk));

  npuarc_alb_2cyc_checker #(.WIDTH(`npuarc_BR_BC_BTA_SIZE)) u24_alb_2cyc_checker 
     (
      .data_in  (
                  byp_bta_r_2cyc
                 ),
      .data_out (
                  byp_bta_r
                 ),
      .clk (clk));

  npuarc_alb_2cyc_checker #(.WIDTH(2)) u25_alb_2cyc_checker 
     (
      .data_in  (
                  byp_size_r_2cyc
                 ),
      .data_out (
                  byp_size_r
                 ),
      .clk (clk));

  npuarc_alb_2cyc_checker #(.WIDTH(1)) u26_alb_2cyc_checker 
     (
      .data_in  (
                  byp_d_bit_r_2cyc
                 ),
      .data_out (
                  byp_d_bit_r
                 ),
      .clk (clk));

  npuarc_alb_2cyc_checker #(.WIDTH(1)) u27_alb_2cyc_checker 
     (
      .data_in  (
                  byp_f_bit_r_2cyc
                 ),
      .data_out (
                  byp_f_bit_r
                 ),
      .clk (clk));


  npuarc_alb_2cyc_checker #(.WIDTH(1)) u30_alb_2cyc_checker 
     (
      .data_in  (
                  select_bta_miss_2cyc
                 ),
      .data_out (
                  select_bta_miss
                 ),
      .clk (clk));

// spyglass enable_block Ar_converge02

endmodule

