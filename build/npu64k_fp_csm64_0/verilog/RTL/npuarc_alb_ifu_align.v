// Library ARCv2HS-3.5.999999999
//------------------------------------------------------------------------------
//
// Copyright (C) 2012-2013 Synopsys, Inc. All rights reserved.
//
///  SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary 
// work of Synopsys, Inc., and is fully protected under copyright and 
// trade secret laws. You may not view, use, disclose, copy, or distribute 
// this file or any information contained herein except pursuant to a 
// valid written license from Synopsys, Inc.
//
// The entire notice above must be reproduced on all authorized copies.
//
//------------------------------------------------------------------------------
//
//   #    ######  #    #            ##    #          #     ####   #    #
//   #    #       #    #           #  #   #          #    #    #  ##   #
//   #    #####   #    #          #    #  #          #    #       # #  #
//   #    #       #    #          ######  #          #    #  ###  #  # #
//   #    #       #    #          #    #  #          #    #    #  #   ##
//   #    #        ####  #######  #    #  ######     #     ####   #    #
//
//------------------------------------------------------------------------------
//  Description
//  This module implements the instruction alignment of the IFU. The inputs 
//  to this module are the 64 bit instruction words fetched from ICCM/I$ or 
//  external memory. The alignment unit aligns the instructions contained in 
//  the word and outputs the instructions to the EXU at the rate of one
//  instruction per clock. In adddition to the intructions, alignment unit also
//  decodes and aligns the branch prediction related data.
//    
//------------------------------------------------------------------------------

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"


module npuarc_alb_ifu_align (
input                      clk,          //core clock
input                      rst_a,        //reset

////////////////////////////////////////////////////////////////////////////////
// Restart, flush control inputs
//
  input                       flush,            // restart from EXU. Plus restart from loop buffer
  input                       restart,          // restart from BPU
  input [`npuarc_PC_RANGE]           restart_pc,       // restart PC

////////////////////////////////////////////////////////////////////////////////
// Bank 0 input
//
input                      vld0,         //validate word0
input [`npuarc_FCH_EXCPN_1H_RANGE] err0,        // data error on word0
input [`npuarc_ITLB_EXEC_PERM_RANGE] experm0,    // data error on word0
input                      iprot_viol0, // fetch prot viol in word0
  input [`npuarc_IM_DWIDTH/2-1:0]    inst0,            // fetch word0
input [`npuarc_ECC_BANK_BITS-1:0] ecc_code0,
input                 ecc_enable0,
input [`npuarc_IC_WAYS_BITS-1:0]  icache_way0,


input [`npuarc_PC_RANGE]          bta0,         //fetch pc for word0
input [`npuarc_BR_FB_INFO64_RANGE]  br_pkt0,      //br info packet
input                      first_word0,
input [`npuarc_IM_BANKS-1:0]      bank_ctl0,

////////////////////////////////////////////////////////////////////////////////
// Bank 1 input
//
input                      vld1,         //validate word1, 
input [`npuarc_FCH_EXCPN_1H_RANGE] err1,        // data error on word1
input [`npuarc_ITLB_EXEC_PERM_RANGE] experm1,    // data error on word1
input                      iprot_viol1, // fetch prot viol in word1
  input [`npuarc_IM_DWIDTH/2-1:0]    inst1,            // fetch word1
input [`npuarc_ECC_BANK_BITS-1:0] ecc_code1,
input                 ecc_enable1,
input [`npuarc_IC_WAYS_BITS-1:0]  icache_way1,


// leda NTL_CON13C off
// LMD: non driving port
// LJ:  unused port range
input [`npuarc_PC_RANGE]          bta1,         //fetch pc for word1
input [`npuarc_BR_FB_INFO64_RANGE]  br_pkt1,      //br info packet
input                      first_word1,
  input [`npuarc_IM_BANKS-1:0]       bank_ctl1,

////////////////////////////////////////////////////////////////////////////////
// Control outputs to the previous stage
//
output reg                 buf_taken,         //to shift word0 in 
output reg                 buf_taken_single,  //only inst0 is taken
output reg [1:0]           buf_taken_count_nxt,  

////////////////////////////////////////////////////////////////////////////////
//   output the ECC corrected data  and address to the ICCM
//



output             al_icache_ecc_err,
output             al_icache_ecc_sb_err,
//   `if (`HAS_SAFETY == 1) // {
output reg         fs_ic_data_bank00_ecc_sb_error_r,
output reg         fs_ic_data_bank00_ecc_db_error_r,
output reg [`npuarc_SYNDROME_MSB:0]  fs_ic_data_bank00_syndrome_r,
output reg         fs_ic_data_bank01_ecc_sb_error_r,
output reg         fs_ic_data_bank01_ecc_db_error_r,
output reg [`npuarc_SYNDROME_MSB:0]  fs_ic_data_bank01_syndrome_r,
output reg         fs_ic_data_bank10_ecc_sb_error_r,
output reg         fs_ic_data_bank10_ecc_db_error_r,
output reg [`npuarc_SYNDROME_MSB:0]  fs_ic_data_bank10_syndrome_r,
output reg         fs_ic_data_bank11_ecc_sb_error_r,
output reg         fs_ic_data_bank11_ecc_db_error_r,
output reg [`npuarc_SYNDROME_MSB:0]  fs_ic_data_bank11_syndrome_r,
//    `endif // }

  // leda NTL_CON37 off
  // leda NTL_CON13C off
  // LMD: non driving port range
  // LJ:  Ecc status signal
input              ecc_ifu_disable,
  // spyglass disable_block W240
  // SMD: input declared but not used
  // SJ:  unused in some configs
input              ecc_ifu_expn_disable,
  // spyglass enable_block W240
  // leda NTL_CON13C on
  // leda NTL_CON37 on
////////////////////////////////////////////////////////////////////////////////
// From mispredict interface:
//
  input                       mpd_mispred,      // 1 => trigger a mispredict and
                                            // start of instruction fetch at 
                                            // target      
  input                       mpd_direction,    // was branch taken or not taken
                                            // 1: taken, 0: not taken      
input                    mpd_error_branch,       
input [`npuarc_BR_TYPE_RANGE]      mpd_type,              

input [`npuarc_BR_FULL_INFO_RANGE] mpd_brinfo_full,
input [`npuarc_BR_FULL_INFO_RANGE] wa_brinfo_full,
 
////////////////////////////////////////////////////////////////////////////////
// Exception signals
//
output                      al_exception,   // indicates current instruction 
                                            // raised exception
output [`npuarc_FCH_EXCPN_RANGE]   al_excpn_type,  // type of exception

output [`npuarc_FCH_EINFO_RANGE]   al_excpn_info,  // info of exception

output reg                  al_ifu_err_nxtpg,

output                      al_iprot_viol,

////////////////////////////////////////////////////////////////////////////////
// Hold up signal from branch info buffer
//
input                    brq_holdup,        //stall from branch info buffer

////////////////////////////////////////////////////////////////////////////////
// Branch Prediction outputs for the current instruction
//

output                      al_is_predicted,    // 1: predicted branch, which
                                                // may predicted taken or
                                                // not-taken
                                                // 0: no assosiated prediction
output                      al_prediction,      // 1: Predicts the branch is 
                                                //    taken
                                                // 0: No branch or predicts 
                                                //    branch no taken
output [`npuarc_PC_RANGE]          al_predicted_bta,   // The predicted BTA 
output [`npuarc_BR_TYPE_RANGE]     al_prediction_type, // Type of prediction
output                      al_error_branch,    // 1: stale branch detected and
                                                // and current instrn is invalid
                                                // Requires misprediction from 
                                                // current PC and a commit
                                                // error response
output [`npuarc_BR_BUF_INFO_RANGE] al_brinfo_full,    // branch predict info
output                       al_with_dslot,     // Indicates branch with delay 
                                                // slot
output [`npuarc_BR_TOSQ_RANGE]    brinfo_tos_index,

output                      ifu_bit_error_r,
////////////////////////////////////////////////////////////////////////////////
// Instruction Interface to EXU
//
input                    stall_in,          //stall input

output                   al_pass,           // indicates a valid instruction 
output     [`npuarc_DATA_RANGE] al_inst_nxt,       // instruction
output     [`npuarc_DATA_RANGE] al_limm_nxt        // limm for the instruction

                         );


// Signal Declarations
//
wire       inst_vld_out;
reg        is_16bit;
reg        has_limm;

wire                      shift;    // when parse reaches end of the half word
reg        shift_int;
reg        first;
reg [ 1:0] first_word_r;
wire       parse_last;
reg        restart_r;

reg [`npuarc_FCH_EXCPN_1H_RANGE]  err0_r;
reg [`npuarc_FCH_EXCPN_1H_RANGE]  err1_r;
reg [`npuarc_ITLB_EXEC_PERM_RANGE] experm0_r;
reg [`npuarc_ITLB_EXEC_PERM_RANGE] experm1_r;
reg                        iprot_viol0_r;
reg                        iprot_viol1_r;

reg [`npuarc_IC_WAYS_BITS-1:0]  icache_way0_r;
reg [`npuarc_IC_WAYS_BITS-1:0]  icache_way1_r;


reg [`npuarc_PC_RANGE] pc0_r;
reg [`npuarc_PC_RANGE] pc1_r;
reg [`npuarc_BR_OFFSET_RANGE]   offset_r;

// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  bank select bit unused
reg [ 1:0]      bank_ctl0_r;
reg [ 1:0]      bank_ctl1_r;
// leda NTL_CON32 on
reg [`npuarc_BR_FB_INFO64_RANGE] br_pkt0_r;
reg [`npuarc_BR_FB_INFO64_RANGE] br_pkt1_r;

reg  [`npuarc_IM_DWIDTH/2-1:0]    inst0_r;            // instruction buffer register 0
reg  [`npuarc_IM_DWIDTH/2-1:0]    inst1_r;            // instruction buffer register 1
reg  [`npuarc_IM_DWIDTH/2-1:0]    inst_out;           // selected instruction output
reg  [`npuarc_BR_OFFSET_RANGE]  next_offset;        // next offset in inst window




wire  [31:0]              inst_vs0;          // predecoder instruction input

// vector predecoder signals
//
wire [1:0]    size0;
wire                      shift0;
wire [`npuarc_BR_OFFSET_RANGE]  next_offset0;
wire [`npuarc_IM_DWIDTH/2-1:0]    inst_out0;
wire                      is_16bit0;
wire                      has_limm0;

// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  Unused ports of instruction pre-decoder
wire                      pd0_is_cond_inst_unused;  // conditional instruction
wire                      pd0_limm_r0_unused;       // Port 0 is a LIMM
wire                      pd0_limm_r1_unused;       // Port 1 is a LIMM
wire [`npuarc_RGF_ADDR_RANGE]    pd0_rf_ra0_unused;        // Register address src 0
wire [`npuarc_RGF_ADDR_RANGE]    pd0_rf_ra1_unused;        // Register address src 1
wire                      pd0_rf_renb0_64_unused;   // Port 0 is a 64-bit read
wire                      pd0_rf_renb1_64_unused;   // Port 1 is a 64-bit read
wire                      pd0_rf_renb0_unused;      // Read enable for port 0
wire                      pd0_rf_renb1_unused;      // Read enable for port 1
// leda NTL_CON13A on

wire  [31:0]              inst_vs1;          // predecoder instruction input

// vector predecoder signals
//
wire [1:0]    size1;
wire                      shift1;
wire [`npuarc_BR_OFFSET_RANGE]  next_offset1;
wire [`npuarc_IM_DWIDTH/2-1:0]    inst_out1;
wire                      is_16bit1;
wire                      has_limm1;

// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  Unused ports of instruction pre-decoder
wire                      pd1_is_cond_inst_unused;  // conditional instruction
wire                      pd1_limm_r0_unused;       // Port 0 is a LIMM
wire                      pd1_limm_r1_unused;       // Port 1 is a LIMM
wire [`npuarc_RGF_ADDR_RANGE]    pd1_rf_ra0_unused;        // Register address src 0
wire [`npuarc_RGF_ADDR_RANGE]    pd1_rf_ra1_unused;        // Register address src 1
wire                      pd1_rf_renb0_64_unused;   // Port 0 is a 64-bit read
wire                      pd1_rf_renb1_64_unused;   // Port 1 is a 64-bit read
wire                      pd1_rf_renb0_unused;      // Read enable for port 0
wire                      pd1_rf_renb1_unused;      // Read enable for port 1
// leda NTL_CON13A on

wire  [31:0]              inst_vs2;          // predecoder instruction input

// vector predecoder signals
//
wire [1:0]    size2;
wire                      shift2;
wire [`npuarc_BR_OFFSET_RANGE]  next_offset2;
wire [`npuarc_IM_DWIDTH/2-1:0]    inst_out2;
wire                      is_16bit2;
wire                      has_limm2;

// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  Unused ports of instruction pre-decoder
wire                      pd2_is_cond_inst_unused;  // conditional instruction
wire                      pd2_limm_r0_unused;       // Port 0 is a LIMM
wire                      pd2_limm_r1_unused;       // Port 1 is a LIMM
wire [`npuarc_RGF_ADDR_RANGE]    pd2_rf_ra0_unused;        // Register address src 0
wire [`npuarc_RGF_ADDR_RANGE]    pd2_rf_ra1_unused;        // Register address src 1
wire                      pd2_rf_renb0_64_unused;   // Port 0 is a 64-bit read
wire                      pd2_rf_renb1_64_unused;   // Port 1 is a 64-bit read
wire                      pd2_rf_renb0_unused;      // Read enable for port 0
wire                      pd2_rf_renb1_unused;      // Read enable for port 1
// leda NTL_CON13A on

wire  [31:0]              inst_vs3;          // predecoder instruction input

// vector predecoder signals
//
wire [1:0]    size3;
wire                      shift3;
wire [`npuarc_BR_OFFSET_RANGE]  next_offset3;
wire [`npuarc_IM_DWIDTH/2-1:0]    inst_out3;
wire                      is_16bit3;
wire                      has_limm3;

// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  Unused ports of instruction pre-decoder
wire                      pd3_is_cond_inst_unused;  // conditional instruction
wire                      pd3_limm_r0_unused;       // Port 0 is a LIMM
wire                      pd3_limm_r1_unused;       // Port 1 is a LIMM
wire [`npuarc_RGF_ADDR_RANGE]    pd3_rf_ra0_unused;        // Register address src 0
wire [`npuarc_RGF_ADDR_RANGE]    pd3_rf_ra1_unused;        // Register address src 1
wire                      pd3_rf_renb0_64_unused;   // Port 0 is a 64-bit read
wire                      pd3_rf_renb1_64_unused;   // Port 1 is a 64-bit read
wire                      pd3_rf_renb0_unused;      // Read enable for port 0
wire                      pd3_rf_renb1_unused;      // Read enable for port 1
// leda NTL_CON13A on



wire       load;
wire       stall;

reg [1:0]  ins_vld;

wire            curr_instr_wait;
wire            instr_in_word1;
wire            eos_load;
reg             eos_wait;

// Branch info related signal declarations
wire [`npuarc_PC_RANGE]           brinfo_bta;
wire [`npuarc_BR_RS_RANGE]        brinfo_tosp;
wire [`npuarc_IC_WAYS_BITS_RANGE] brinfo_pri_way; 
wire [`npuarc_IC_WAYS_BITS_RANGE] brinfo_sec_way; 

wire [`npuarc_BR_TYPE_RANGE] brinfo_brtype;
wire [`npuarc_BR_OFFSET_RANGE]   brinfo_offset;
wire                brinfo_strength;
wire                brinfo_f_bit;
wire                brinfo_d_bit;
wire                brinfo_taken;

wire                brinfo_sec_f_bit;                // indicates the predicted branch needs one more 64bit block
wire [`npuarc_BR_OFFSET_RANGE]   brinfo_sec_offset;    // 2-bit offset in 64-bit block
wire                brinfo_sec_strength;           // Gshare confidence
wire                brinfo_sec_valid;          // is this branch predicted? Yes: 1
wire                brinfo_sec_taken;               // Gshare prediction; 1: taken branch, 0: not taken

wire                current_primary; // indicates if the current instruction is the primary branch
wire                current_secondary;

wire              branch_instr;
reg               dslot_branch;

reg  [`npuarc_PC_INC_RANGE]      align_pc_incr;
wire [`npuarc_PC_RANGE] next_seq_pc;
reg  [`npuarc_PC_RANGE] align_pc_nxt;
reg  [`npuarc_PC_RANGE] align_pc /* verilator public_flat */;
wire             error_branch2;
wire             err_branch1_t1;
reg              err1_chk_en;
reg              err1_chk_sec_en;
wire             err_branch1_t2;
wire             err_branch1_t3;
reg  [3:0]       al_num_nt;
reg              al_error_branch_r;

wire             restart_state;     //period of restart

wire             al_prediction_pri;
wire             al_prediction_sec;

reg              mp_uncond;
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  unused signal

wire                       cm_alt_way_valid; 
wire [`npuarc_IC_WAYS_BITS_RANGE] cm_alt_way;
wire                       cm_way_sec;
wire [`npuarc_PC_RANGE]           cm_tos ;
wire [`npuarc_BR_OFFSET_RANGE]   cm_primary_offset;
wire                       cm_primary_valid;
wire [`npuarc_BR_RS_RANGE]        cm_tosp;
wire                       cm_c_in;

// leda NTL_CON13A on
wire [1:0]                 cm_num_nt;
wire [`npuarc_BR_PT_RANGE]        cm_ghr;


reg [`npuarc_ECC_BANK_BITS-1:0]  ecc_code0_r;
reg [`npuarc_ECC_BANK_BITS-1:0]  ecc_code1_r;
wire                      ecc_holdup;     
reg                       ecc_load0;
reg                       ecc_load1;
wire                      ecc_db_error;
// leda NTL_CON13A off
// LMD: non driving internal net Range
// LJ:  Not used in all configs
wire                      ecc_error;
// leda NTL_CON13A on

wire [`npuarc_IM_DWIDTH/2-1:0] ecc_data0;
wire [`npuarc_IM_DWIDTH/2-1:0] ecc_data1;

reg                       ecc_enable0_r;
reg                       ecc_enable1_r;
////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
// Alignment unit extracts the intructions from the incoming intruction 
// words (64 bit) and present it to the EXU at the rate of one instruction per 
// clock. The alignment unit registers all incoming signals, acting as a pipeline
// stage. The alignment unit can store up to two 64 bit instruction words.
// When an intruction word is received, the alignment unit starts processing it.  
// If the next instruction word arrives at the same time, it is stored in the second 
// second word register. If all the instructions in the current word are processed,  
// or if part of the current instruction is in the next word, data from the second 
// word is used if it is valid. If the data in word1 is not valid,the alignment
// unit waits until a new instruction word arrives. 
// The alignment unit also extracts the branch prediction related information 
// for each instruction. For each instruction word, there is an associated branch 
// info. It is assumed that the instruction and branch info are aligned at the 
// word level at the previous stages.    
// The alignment unit also detects the error branches by keeping track of the 
// offsets of the current instruction offset and prediction offsets.
// If an error branch is detected, it is flagged and EXU takes appropriate 
// actions to remove the entries from the branch cache that causes the error
// branch.  
////////////////////////////////////////////////////////////////////////////////


assign stall = stall_in || 
               ecc_holdup ||
               brq_holdup;

///////////////////////////////////////////////////////////////////////////////
// restart_state is held high from fch_restart to the restart from the BPU
// It is used to keep the internal states in reset
//
assign restart_state = flush || restart_r;

///////////////////////////////////////////////////////////////////////////////
// Indicates the current instruction needs data from word1, but word1 does not 
// have valid data
//

assign instr_in_word1     = ((offset_r == {`npuarc_BR_OFFSET_SIZE{1'b1}}) 
                          & !is_16bit)
                          ? 1'b1
                          : shift_int & (next_offset !=0)
                          ;                       


assign curr_instr_wait = !ins_vld[1] & instr_in_word1;

///////////////////////////////////////////////////////////////////////////////
// Indicates the next instruction needs data from word1, but word1 does not 
// have valid data
//
assign nxt_instr_in_word1     = ((offset_r == {`npuarc_BR_OFFSET_SIZE{1'b1}}) 
                          & !is_16bit)
                          ? 1'b0
                          : shift_int & (next_offset ==0)
                          ;                       


assign nxt_instr_wait = !ins_vld[1] & nxt_instr_in_word1;

///////////////////////////////////////////////////////////////////////////////
// End of sequence needs to load data from the ext buffer 
//
assign eos_load = parse_last & ((!ins_vld[1] & (!instr_in_word1) ) || 
                                (ins_vld[1] & instr_in_word1   )  );

///////////////////////////////////////////////////////////////////////////////
// Load data after reset or end of sequence 
//
assign load = (first || eos_load ) & vld0;

///////////////////////////////////////////////////////////////////////////////
// Shift the contents of the register 
//
assign shift = ((shift_int & (!curr_instr_wait) & (!parse_last) ) || 
                                                  (parse_last & ins_vld[1]))
             & (!(parse_last & instr_in_word1))
             ;

///////////////////////////////////////////////////////////////////////////////
// Load the registers 0 and 1 if it completely runs out of instructions 
//
assign load_word01 = 
                    (nxt_instr_wait || (!ins_vld[0])) & vld0;

///////////////////////////////////////////////////////////////////////////////
// Load the register1, when it is empty 
//
assign load_word1 = 
                   (ins_vld == 2'b01) & (!(parse_last));


///////////////////////////////////////////////////////////////////////////////
//
// end of a sequence  wait condition
//
///////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin: eos_wait_reg_PROC
  if (rst_a == 1'b1) begin
     eos_wait <= 1'b0;
  end
  else if(!stall) begin
    if(eos_load & (!vld0)) begin
      eos_wait <= 1'b1;
    end
    else if(load ) begin
      eos_wait <= 1'b0;
    end
  end
end  // block: eos_wait_reg_PROC

///////////////////////////////////////////////////////////////////////////////
//
// flag indicating restart state
// set by the flush signal (fch_restart) and reset by 
// restart from BPU
//
///////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin: restart_reg_PROC
  if (rst_a == 1'b1) begin
     restart_r <= 1'b0;
  end
  else if (restart) begin
     restart_r <= 1'b0;
  end
  else if (flush
           ) begin
     restart_r <= 1'b1;
   end 
end // block: restart_reg_PROC

///////////////////////////////////////////////////////////////////////////////
// indicates conditions for valid instruction output
//
assign inst_vld_out = ins_vld[0] & (!eos_wait) & (!curr_instr_wait);

wire offset_load;
wire offset_incr_en;
///////////////////////////////////////////////////////////////////////////////
// offset is loaded during reset and during the end of a sequence 
// terminated by a taken branch
//
assign offset_load = load || (parse_last & shift);

///////////////////////////////////////////////////////////////////////////////
// offset is incremented during an instruction sequence when
// when the complete instruction is available and not the 
// end of a sequence
//
assign offset_incr_en = ins_vld[0] & (!parse_last) & (!curr_instr_wait);

///////////////////////////////////////////////////////////////////////////////
//
// offset of the current instruction within the 64bit word
//
///////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin : offset_reg_PROC
  if (rst_a == 1'b1) begin
    offset_r <= `npuarc_BR_OFFSET_SIZE'b0;
  end
  else if(!stall) begin
    if (offset_load)
    begin
      offset_r <= pc0_r[`npuarc_PC_LSB+(`npuarc_BR_OFFSET_SIZE-1):`npuarc_PC_LSB];
    end
    else if (offset_incr_en) begin
      offset_r <= next_offset;
    end
  end
end // block: offset_reg_PROC

// fb_cross indicates the instruction fetch is crossing fetch block boundary.
// Fetch block (FB) can be 8 or 16bytes, based on the branch prediction and 
// cache line boundary
// Fetch block crossing occurs after restarting,  
// after braching to a predicted branch,  after fetch sequencially crosses a 128bit 
// boundary.
wire fb_cross;
assign fb_cross = bank_ctl0_r[0] & shift_int |                      //  // 64bit FB cross
                  (!bank_ctl0_r[0]) & (!first_word_r[0]) & shift_int |   // 128bit FB cross
                  offset_load;                                    // FB cross due to restart and taken branches

///////////////////////////////////////////////////////////////////////////////
// indicates to the fecth buffer, the status of the incoming words
//  00 : incoming words are not used
//  01 : word0 is consumed
//  10 : not used
//  11 : both word0 and word1 are used consumed
wire [1:0] buf_taken_nxt;

assign buf_taken_nxt[0] = !stall & (!restart_state) & 
                                           (load                || 
                                            load_word01         || 
                                            (load_word1 & vld0) || 
                                            (shift & vld0)
                                            );
assign buf_taken_nxt[1] = !stall & (!restart_state) &
                                             ((load & vld1) ||
                                                      (load_word01 & vld1)
                                                     );
reg       buf_taken_double_nxt;
reg       buf_taken_single_nxt;
///////////////////////////////////////////////////////////////////////////////
// Register the buf_taken and buf_taken_single signals
///////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin: buf_taken_reg_PROC
  if (rst_a == 1'b1) begin
    buf_taken <= 1'b0;
    buf_taken_single <= 1'b0;
  end
  else begin
    buf_taken <= buf_taken_double_nxt;
    buf_taken_single <= buf_taken_single_nxt;
  end
end // block: buf_taken_reg_PROC

///////////////////////////////////////////////////////////////////////////////
// This is a temporary encode to match the decoding in fetch buffer
// To be removed after updating the the fetch buffer
///////////////////////////////////////////////////////////////////////////////
always @ *
begin: buf_taken_decode_PROC
  case (buf_taken_nxt )
    2'b01 : begin 
              buf_taken_double_nxt = 1'b1;
              buf_taken_single_nxt = 1'b1;
              buf_taken_count_nxt = 2'b01;
            end
    2'b11 : begin 
              buf_taken_double_nxt = 1'b1;
              buf_taken_single_nxt = 1'b0;
              buf_taken_count_nxt = 2'b10;
            end
    default: begin 
              buf_taken_double_nxt = 1'b0;
              buf_taken_single_nxt = 1'b0;
              buf_taken_count_nxt = 2'b00;
            end
  endcase
end  // block: buf_taken_decode_PROC

///////////////////////////////////////////////////////////////////////////////
// Control signals
///////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin: control_sig_reg_PROC
  if (rst_a == 1'b1) begin
    first <= 1'b1;
  end
  else if (restart_state) begin
    first <= 1'b1;
  end
  else if (!stall) begin
    if (load ) begin
      first <= 1'b0;
    end
  end
end  //block: control_sig_reg_PROC

///////////////////////////////////////////////////////////////////////////////
// Enable loading of brinfo to reg 0 only if it is valid
// brinfo is invalid (not present ) for the branch has a tail fetch block
//
wire brinfo0_load_en; 
assign brinfo0_load_en = !(!load & load_word01 & 
                           ((al_prediction_pri & brinfo_d_bit) | dslot_branch));

///////////////////////////////////////////////////////////////////////////////
// load and shift the instruction word valid signal
///////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin: iword_vld_reg_PROC
  if (rst_a == 1'b1) begin
    ins_vld <= 2'b00;
  end
  else if (flush | restart_r) begin
      ins_vld <= 2'b00;
  end
  else if(!stall) begin
    if (load || load_word01) begin
      ins_vld[1:0] <= {vld1,1'b1};
    end
    else if (shift ) begin
      ins_vld[1:0] <= {vld0, ins_vld[1]};
    end
    else if (load_word1) begin
      ins_vld[1] <= vld0;
    end
   
  end
end  // block:iword_vld_reg_PROC

///////////////////////////////////////////////////////////////////////////////
// load register 0 with instruction word and control signals 
///////////////////////////////////////////////////////////////////////////////

// leda NTL_RST03 off
// LMD : A flipflop without reset
// LJ  : Only controls signals to be initialized during reset
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
always @(posedge clk or posedge rst_a)
begin: iword0_reg_PROC
  if (rst_a == 1'b1) begin
    first_word_r[0] <= 1'b0;
    bank_ctl0_r <= {`npuarc_IM_BANKS{1'b0}};
    err0_r <= `npuarc_FCH_EXCPN_1H_BITS'd0;
    experm0_r <= `npuarc_ITLB_EXEC_PERM_WIDTH'd0;
    iprot_viol0_r <= 1'b0;
    inst0_r <= `npuarc_IFU_INST_BITS'd0;
    ecc_code0_r <= `npuarc_ECC_BANK_BITS'd0;
    ecc_enable0_r <= 1'b0;
    icache_way0_r <= {`npuarc_IC_WAYS_BITS{1'b0}};
  end
  else if (flush | restart_r) begin
      first_word_r[0] <= 1'b0;
      bank_ctl0_r <= {`npuarc_IM_BANKS{1'b0}};
      err0_r <= `npuarc_FCH_EXCPN_1H_BITS'd0;
    experm0_r <= `npuarc_ITLB_EXEC_PERM_WIDTH'd0;
    iprot_viol0_r <= 1'b0;
  end
  else if(ecc_load0) begin
    inst0_r <= ecc_data0;
  end
  else if(!stall) begin
    if (load || load_word01) begin
      first_word_r[0] <= first_word0;
      bank_ctl0_r <= bank_ctl0;
      inst0_r <= inst0;
      ecc_code0_r <= ecc_code0;
      ecc_enable0_r <= ecc_enable0;
      err0_r <= err0;
      experm0_r <= experm0;
      iprot_viol0_r <= iprot_viol0;
      icache_way0_r <= icache_way0;
    end
    else if (shift & ins_vld[1]) begin
        first_word_r[0] <= first_word_r[1];
        bank_ctl0_r <= bank_ctl1_r;
        inst0_r <= inst1_r;
       ecc_code0_r <= ecc_code1_r;
      ecc_enable0_r <= ecc_enable1_r;
        err0_r <= err1_r;
        experm0_r <= experm1_r;
        iprot_viol0_r <= iprot_viol1_r;
        icache_way0_r <= icache_way1_r;
    end
  end
end  // block:iword0_reg_PROC
// leda NTL_RST03 on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01

///////////////////////////////////////////////////////////////////////////////
// load register 1 with instruction word and control signals 
///////////////////////////////////////////////////////////////////////////////

// leda NTL_RST03 off
// LMD : A flipflop without reset
// LJ  : Only controls signals to be initialized during reset
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset

// spyglass disable_block W552
// SMD: signal driven inside more than one sequential block
// SJ:  first_word_r different bits are used in different blocks

always @(posedge clk or posedge rst_a)
begin: iword1_reg_PROC
  if (rst_a == 1'b1) begin
    first_word_r[1] <= 1'b0;
    bank_ctl1_r <= {`npuarc_IM_BANKS{1'b0}};
    err1_r <= `npuarc_FCH_EXCPN_1H_BITS'd0;
      experm1_r <= `npuarc_ITLB_EXEC_PERM_WIDTH'd0;
      iprot_viol1_r <= 1'b0;
    inst1_r <= `npuarc_IFU_INST_BITS'd0;
    ecc_code1_r <= `npuarc_ECC_BANK_BITS'd0;
    ecc_enable1_r <= 1'b0;
    icache_way1_r <= `npuarc_IC_WAYS_BITS'd0;
  end
  else if (flush | restart_r) begin
      first_word_r[1] <= 1'b0;
      bank_ctl1_r <= {`npuarc_IM_BANKS{1'b0}};
      err1_r <= `npuarc_FCH_EXCPN_1H_BITS'd0;
      experm1_r <= `npuarc_ITLB_EXEC_PERM_WIDTH'd0;
      iprot_viol1_r <= 1'b0;
    icache_way1_r <= `npuarc_IC_WAYS_BITS'd0;
  end
  else if(ecc_load1) begin
    inst1_r <= ecc_data1;
  end
  else if(!stall) begin
    if ((load || load_word01) & vld1)begin
        first_word_r[1] <= first_word1;
        bank_ctl1_r <= bank_ctl1;
        inst1_r <= inst1;
       ecc_code1_r <= ecc_code1;
      ecc_enable1_r <= ecc_enable1;
        err1_r <= err1;
        experm1_r <= experm1;
        iprot_viol1_r <= iprot_viol1;
        icache_way1_r <= icache_way1;
    end
    else if ((shift | load_word1) & vld0) begin
        first_word_r[1] <= first_word0;
        bank_ctl1_r <= bank_ctl0;
        inst1_r <= inst0;
       ecc_code1_r <= ecc_code0;
      ecc_enable1_r <= ecc_enable0;
        err1_r <= err0;
        experm1_r <= experm0;
        iprot_viol1_r <= iprot_viol0;
        icache_way1_r <= icache_way0;
    end
  end
end  // block:iword1_reg_PROC
// leda NTL_RST03 on
// spyglass enable_block W552
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01

///////////////////////////////////////////////////////////////////////////////
// load branch info  to register 0
///////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin: brinfo0_reg_PROC
  if (rst_a == 1'b1) begin
    pc0_r <= {`npuarc_PC_BITS{1'b0}};
    br_pkt0_r  <= {`npuarc_BR_FB_INFO64_SIZE{1'b0}};
  end
  else if (flush | restart_r) begin
    if (flush) begin
      pc0_r <= restart_pc;
      br_pkt0_r  <= {`npuarc_BR_FB_INFO64_SIZE{1'b0}};
    end
  end
  else if(!stall) begin
    if ((load || load_word01) & brinfo0_load_en)begin
        pc0_r      <= bta0;
        br_pkt0_r  <= br_pkt0;
    end
    else if (shift & ins_vld[1] & (!(al_prediction_pri & brinfo_d_bit))) begin
        pc0_r      <= pc1_r;
        br_pkt0_r  <= br_pkt1_r; 
    end
  end
end  // block:brinfo0_reg_PROC

///////////////////////////////////////////////////////////////////////////////
// load branch info  to register1 
///////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin: brinfo1_reg_PROC
  if (rst_a == 1'b1) begin
    pc1_r <= {`npuarc_PC_BITS{1'b0}};
    br_pkt1_r  <= {`npuarc_BR_FB_INFO64_SIZE{1'b0}};
  end
  else if (flush | restart_r) begin
    if (flush) begin
      pc1_r <= restart_pc;
      br_pkt1_r  <= {`npuarc_BR_FB_INFO64_SIZE{1'b0}};
    end
  end
  else if(!stall) begin
    if ((load || load_word01) & vld1) begin
        pc1_r      <= bta1;
        br_pkt1_r  <= br_pkt1;
    end
    else if ((shift | load_word1) & vld0) begin
        pc1_r      <= bta0;
        br_pkt1_r  <= br_pkt0;
    end
  end
end  // block:brinfo1_reg_PROC


///////////////////////////////////////////////////////////////////////////////
// Size and next offset for instruction at offsets 0..`IFU_OFFSET_MAX
//
// leda  B_3208 off
// leda  B_3200 off
// leda  B_3219 off
// leda  BTTF_D002 off
// LMD : Unequal length LHS and RHS in assignment
// LJ  : addition of two numbers of same size and 1 needs only an additional bit
assign size0 = {has_limm0, ~is_16bit0};
assign {shift0, next_offset0} = offset_r + size0 + 1;
assign size1 = {has_limm1, ~is_16bit1};
assign {shift1, next_offset1} = offset_r + size1 + 1;
assign size2 = {has_limm2, ~is_16bit2};
assign {shift2, next_offset2} = offset_r + size2 + 1;
assign size3 = {has_limm3, ~is_16bit3};
assign {shift3, next_offset3} = offset_r + size3 + 1;
// leda  BTTF_D002 on
// leda  B_3208 on
// leda  B_3200 on
// leda  B_3219 on
///////////////////////////////////////////////////////////////////////////////
// Instruction words at offsets  0..`IFU_OFFSET_MAX
//
assign  inst_out0 = inst0_r;
assign  inst_out1 = {inst1_r[15:0],inst0_r[63:16]};
assign  inst_out2 = {inst1_r[31:0],inst0_r[63:32]};
assign  inst_out3 = {inst1_r[47:0],inst0_r[63:48]};



////////////////////////////////////////////////////////////////////////////////
// Select the instruction based on the current offset
////////////////////////////////////////////////////////////////////////////////
always @*
begin: next_inst_PROC
  case (offset_r)
    2'd0: inst_out = inst_out0;
    2'd1: inst_out = inst_out1;
    2'd2: inst_out = inst_out2;
    2'd3: inst_out = inst_out3;
  endcase
end // block: next_inst_PROC

////////////////////////////////////////////////////////////////////////////////
// Select the instruction properties based on the current offset
////////////////////////////////////////////////////////////////////////////////
always @*
begin: next_offset_PROC
  case (offset_r)
    2'd0:
          begin
            next_offset      = next_offset0;
            shift_int        = shift0;
            is_16bit         = is_16bit0;
            has_limm         = has_limm0;
          end

    2'd1:
          begin
            next_offset      = next_offset1;
            shift_int        = shift1;
            is_16bit         = is_16bit1;
            has_limm         = has_limm1;
          end

    2'd2:
          begin
            next_offset      = next_offset2;
            shift_int        = shift2;
            is_16bit         = is_16bit2;
            has_limm         = has_limm2;
          end

    2'd3:
          begin
            next_offset      = next_offset3;
            shift_int        = shift3;
            is_16bit         = is_16bit3;
            has_limm         = has_limm3;
          end

  endcase
end // block: next_offset_PROC

assign inst_vs0 = {inst_out0[15:0],inst_out0[31:16]};

// Predecode the scalar instruction at offset 0
//
npuarc_alb_predecode u0_predecode (
  .inst             (inst_vs0               ),
  .is_16bit         (is_16bit0              ),
  .is_cond_inst     (pd0_is_cond_inst_unused),
  .has_limm         (has_limm0              ),
  .limm_r0          (pd0_limm_r0_unused     ),
  .limm_r1          (pd0_limm_r1_unused     ),
  .rf_ra0           (pd0_rf_ra0_unused      ),
  .rf_ra1           (pd0_rf_ra1_unused      ),
  .rf_renb0_64      (pd0_rf_renb0_64_unused ),
  .rf_renb1_64      (pd0_rf_renb1_64_unused ),
  .rf_renb0         (pd0_rf_renb0_unused    ),
  .rf_renb1         (pd0_rf_renb1_unused    )
   );

assign inst_vs1 = {inst_out1[15:0],inst_out1[31:16]};

// Predecode the scalar instruction at offset 1
//
npuarc_alb_predecode u1_predecode (
  .inst             (inst_vs1               ),
  .is_16bit         (is_16bit1              ),
  .is_cond_inst     (pd1_is_cond_inst_unused),
  .has_limm         (has_limm1              ),
  .limm_r0          (pd1_limm_r0_unused     ),
  .limm_r1          (pd1_limm_r1_unused     ),
  .rf_ra0           (pd1_rf_ra0_unused      ),
  .rf_ra1           (pd1_rf_ra1_unused      ),
  .rf_renb0_64      (pd1_rf_renb0_64_unused ),
  .rf_renb1_64      (pd1_rf_renb1_64_unused ),
  .rf_renb0         (pd1_rf_renb0_unused    ),
  .rf_renb1         (pd1_rf_renb1_unused    )
   );

assign inst_vs2 = {inst_out2[15:0],inst_out2[31:16]};

// Predecode the scalar instruction at offset 2
//
npuarc_alb_predecode u2_predecode (
  .inst             (inst_vs2               ),
  .is_16bit         (is_16bit2              ),
  .is_cond_inst     (pd2_is_cond_inst_unused),
  .has_limm         (has_limm2              ),
  .limm_r0          (pd2_limm_r0_unused     ),
  .limm_r1          (pd2_limm_r1_unused     ),
  .rf_ra0           (pd2_rf_ra0_unused      ),
  .rf_ra1           (pd2_rf_ra1_unused      ),
  .rf_renb0_64      (pd2_rf_renb0_64_unused ),
  .rf_renb1_64      (pd2_rf_renb1_64_unused ),
  .rf_renb0         (pd2_rf_renb0_unused    ),
  .rf_renb1         (pd2_rf_renb1_unused    )
   );

assign inst_vs3 = {inst_out3[15:0],inst_out3[31:16]};

// Predecode the scalar instruction at offset 3
//
npuarc_alb_predecode u3_predecode (
  .inst             (inst_vs3               ),
  .is_16bit         (is_16bit3              ),
  .is_cond_inst     (pd3_is_cond_inst_unused),
  .has_limm         (has_limm3              ),
  .limm_r0          (pd3_limm_r0_unused     ),
  .limm_r1          (pd3_limm_r1_unused     ),
  .rf_ra0           (pd3_rf_ra0_unused      ),
  .rf_ra1           (pd3_rf_ra1_unused      ),
  .rf_renb0_64      (pd3_rf_renb0_64_unused ),
  .rf_renb1_64      (pd3_rf_renb1_64_unused ),
  .rf_renb0         (pd3_rf_renb0_unused    ),
  .rf_renb1         (pd3_rf_renb1_unused    )
   );



////////////////////////////////////////////////////////////////////////////////
// Compute the PC increment from the predecoded size of the next instruction
////////////////////////////////////////////////////////////////////////////////
// leda  W484 off
// leda  B_3200 off
// leda  B_3208 off
// LMD : Unequal length LHS and RHS in assignment
// LJ  : address wrap around, no extra bits needed
always @ *
begin: pc_incr_PROC
  case({is_16bit,has_limm})
       2'b00 : align_pc_incr = 3'd2;
       2'b01 : align_pc_incr = 3'd4;
       2'b10 : align_pc_incr = 3'd1;
       2'b11 : align_pc_incr = 3'd3;
  endcase
end // block: pc_incr_PROC
// leda  W484 on
// leda  B_3200 on
// leda  B_3208 on
////////////////////////////////////////////////////////////////////////////////
// Calculate the next PC
//
// leda  BTTF_D002 off
// leda  B_3200 off
// leda  B_3219 off
// leda  W484 off
// LMD : Unequal length LHS and RHS in assignment
// LJ  : address wrap around, no extra bits needed
// spyglass disable_block W484 W164a
// SMD: Possible assignment overflow
// SJ:  address wrap around, no extra bits needed
assign next_seq_pc = align_pc + align_pc_incr;
// leda  W484 on
// leda  B_3200 on
// leda  B_3219 on
//leda  BTTF_D002 on
// spyglass enable_block W484 W164a


////////////////////////////////////////////////////////////////////////////////
// This is the internal PC maintained by the alignment unit
// PC is updated to fch_restart target during fch_restart. For a taken branch
// is updated to BTA provided by the Branch Prediction. For sequential fetch,
// PC is incremented based on the instruction size
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// Clock gate enable for align_pc
//
wire align_pc_cg0;
assign align_pc_cg0 = flush | (!stall & (parse_last | inst_vld_out));

////////////////////////////////////////////////////////////////////////////////
// align_pc registered
////////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin: align_pc_reg_PROC
  if (rst_a == 1'b1) 
    align_pc <= {`npuarc_PC_BITS{1'b0}};
  else if(align_pc_cg0)
    align_pc <= align_pc_nxt;
end

////////////////////////////////////////////////////////////////////////////////
// Calculate the next value for align_pc 
////////////////////////////////////////////////////////////////////////////////
always @ *
begin: align_pc_nxt_PROC
  if (flush) begin
    align_pc_nxt = restart_pc;
  end
  else if(!stall & parse_last ) begin
    align_pc_nxt = brinfo_bta;
  end
  else begin
    align_pc_nxt = next_seq_pc;
  end
end // block: align_pc_nxt_PROC

////////////////////////////////////////////////////////////////////////////////
// If the delay slot bit is set and if branch is taken, delay the PC update
// for one more instruction
////////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin: dslot_br_reg_PROC
  if (rst_a == 1'b1) begin
    dslot_branch <= 1'b0;
  end
  else if (flush) begin
    dslot_branch <= 1'b0;
  end
  else if(!stall) begin
    if(brinfo_d_bit & al_prediction_pri & (!curr_instr_wait)) begin
      dslot_branch <= 1'b1;
    end
    else if (load || (shift & ins_vld[1])) begin
      dslot_branch <= 1'b0;
    end
  end
end // block: dslot_br_reg_PROC

////////////////////////////////////////////////////////////////////////////////
// Parse last is adjusted based on the delay slot
// If delay slot instruction is present, pase_last happens with delay slot
//
assign parse_last = (!brinfo_d_bit & branch_instr & (!curr_instr_wait)) | 
           (al_prediction_sec & (!curr_instr_wait)) |
           (dslot_branch & ins_vld[0] & (!curr_instr_wait));
     

////////////////////////////////////////////////////////////////////////////////
// branch target address stored in pc0_r is used here
//
assign brinfo_bta      = pc0_r;

////////////////////////////////////////////////////////////////////////////////
// unpack the branch info from the Predictor
//
assign {
  brinfo_tos_index[`npuarc_BR_TOSQ_RANGE],
  brinfo_tosp[`npuarc_BR_RS_RANGE],

   brinfo_sec_way[`npuarc_IC_WAYS_BITS_RANGE], 
   brinfo_pri_way[`npuarc_IC_WAYS_BITS_RANGE], 

   brinfo_sec_f_bit,                // indicates the predicted branch needs to fetch one more 64-bit block before the branch takes effect
   brinfo_sec_offset[`npuarc_BR_OFFSET_RANGE], // 2-bit offset in 64-bit block
   brinfo_sec_strength,           // Gshare confidence
   brinfo_sec_valid,          // is this branch predicted? Yes: 1
   brinfo_sec_taken,               // Gshare prediction; 1: taken branch, 0: not taken

  brinfo_d_bit,
  brinfo_brtype[`npuarc_BR_TYPE_RANGE],
  brinfo_f_bit,
  brinfo_offset,
  brinfo_strength,
  brinfo_taken  
  } = br_pkt0_r[`npuarc_BR_FB_INFO64_RANGE];


////////////////////////////////////////////////////////////////////////////////
// find out if the current instruction is the primary branch of this fetch block
//
wire brinfo_valid;
assign brinfo_valid = (brinfo_brtype != `npuarc_BR_NOT_PREDICTED );


assign current_primary = brinfo_valid & (brinfo_offset == offset_r);


////////////////////////////////////////////////////////////////////////////////
// Secondary branch condition valid
//

assign current_secondary = ~current_primary & brinfo_sec_valid & (brinfo_sec_offset == offset_r);

////////////////////////////////////////////////////////////////////////////////
// Indicates the current instruction is branch
//
assign al_is_predicted = (current_primary | current_secondary | al_error_branch) & 
                                                                         al_pass & 
                                                                     (!dslot_branch); 

reg al_predict_en;
////////////////////////////////////////////////////////////////////////////////
// Indicates the current instruction is taken branch
// Only the primary branch can be taken
//
assign al_prediction_pri = current_primary & brinfo_taken; 

assign branch_instr = current_primary & brinfo_taken;

////////////////////////////////////////////////////////////////////////////////
// Indicates current secondary is taken
//
assign al_prediction_sec = current_secondary & brinfo_sec_taken; 


////////////////////////////////////////////////////////////////////////////////
// if primary or secondary taken and if it is the first taken in a word
// al_prediction is true
//
assign al_prediction = (   (al_prediction_pri | al_prediction_sec)
                         & al_predict_en
                         & (!dslot_branch)
                       )
                     ;

////////////////////////////////////////////////////////////////////////////////
// This flag is set after crossing a word boundary 
// It is reset if the branch offset matches the instruction offset within a word
////////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin: pred_en_reg_PROC
  if (rst_a == 1'b1) begin
    al_predict_en <= 1'b1;
  end
  else if (!stall) begin
    if (shift || load || load_word01) begin
       al_predict_en <= 1'b1;
    end
    else if ((al_prediction_pri | al_prediction_sec) & (!curr_instr_wait)) begin
      al_predict_en <= 1'b0;
    end
  end
end // block: pred_en_reg_PROC


////////////////////////////////////////////////////////////////////////////////
// The predicted BTA of the current current instruction
//
assign al_predicted_bta = brinfo_bta;

////////////////////////////////////////////////////////////////////////////////
// Type of prediction
// For primary branches it's from the branch_info_fb.
// For secondary branches from B-bits the type is a conditional branch.
//
assign al_prediction_type = current_primary ? brinfo_brtype : `npuarc_BR_CONDITIONAL;

////////////////////////////////////////////////////////////////////////////////
// dslot 
//
assign al_with_dslot = current_primary ? brinfo_d_bit : 1'b0;

////////////////////////////////////////////////////////////////////////////////
// Error in branch 
// 1 -> stale branch was detected and current instrn is invalid
// Requires misprediction from current PC and a commit error response
//
////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
// This flag is set after crossing a word boundary 
// It is reset if the branch offset matches the instruction offset within a word
////////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin: err_chk_en_reg_PROC
  if (rst_a == 1'b1) begin
    err1_chk_en <= 1'b1;
  end
  else if (!stall) begin
    if (shift || load || load_word01) begin
       err1_chk_en <= 1'b1;
    end
    else if (al_prediction_pri) begin
      err1_chk_en <= 1'b0;
    end
  end
end // block: err_chk_en_reg_PROC

////////////////////////////////////////////////////////////////////////////////
// This flag is set after crossing a word boundary 
// It is reset if the branch offset matches the instruction offset within a word
////////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin: err_chk_sec_en_reg_PROC
  if (rst_a == 1'b1) begin
    err1_chk_sec_en <= 1'b1;
  end
  else if (!stall) begin
    if (shift || load || load_word01) begin
       err1_chk_sec_en <= 1'b1;
    end
    else if (al_prediction_sec) begin
      err1_chk_sec_en <= 1'b0;
    end
  end
end // block: err_chk_sec_en_reg_PROC

reg br_instr_word_x;
////////////////////////////////////////////////////////////////////////////////
// check if the branch with delay slot crosses a word boundary. Used for error
// branch check
////////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin: br_instr_word_reg_PROC
  if (rst_a ==1'b1) begin
    br_instr_word_x <= 1'b0;
  end
  else if (flush) begin
    br_instr_word_x <= 1'b0;
  end
  else if(!stall) begin
    if(brinfo_d_bit & al_prediction & (!curr_instr_wait) & shift_int) begin
      br_instr_word_x <= 1'b1;
    end
    else if (load || (shift & ins_vld[1])) begin
      br_instr_word_x <= 1'b0;
    end
  end
end // block: br_instr_word_reg_PROC

////////////////////////////////////////////////////////////////////////////////
// The three assignments below are for detecting the error branch condition1
// caused by predicted taken error branches which is not aligned to the 
// current instruction sequence
//
assign err_branch1_t1 = !shift_int & brinfo_taken & brinfo_valid & (brinfo_offset > offset_r)  & 
                                             (brinfo_offset < next_offset);
   
assign err_branch1_t2 = err1_chk_en & brinfo_taken & brinfo_valid & ins_vld[0] & 
                                                  (brinfo_offset < offset_r);

assign err_branch1_t3 = shift_int & brinfo_taken & brinfo_valid & (brinfo_offset > offset_r) & ins_vld[0];

////////////////////////////////////////////////////////////////////////////////
// If a branch instruction needs word from next sequential address and if the 
// f_bit is not set, it indicates an aliasing error and flags this as error branch
// Similarly, error branch is generated if the branch plus delay slot doesn't need 
// word from the next word, but the f_bit is set; 
wire err_branch1_t4;
assign err_branch1_t4 = !brinfo_d_bit & al_prediction_pri & (brinfo_f_bit ^ instr_in_word1) |
                         brinfo_d_bit & al_prediction_pri & (!brinfo_f_bit & instr_in_word1) |
                         dslot_branch & (brinfo_f_bit ^ (instr_in_word1 | br_instr_word_x));


////////////////////////////////////////////////////////////////////////////////
// Find the error conditions for the secondary bracnh
//
wire err_branch1_sec_t1;
wire err_branch1_sec_t2;
wire err_branch1_sec_t3;
wire err_branch1_sec_t4;

// Detect the branch error condition when the branch offset is greater than the
// current offset and less than the next offset 
//
assign err_branch1_sec_t1 = !shift_int & brinfo_sec_taken & brinfo_sec_valid & 
                                             (brinfo_sec_offset > offset_r)  & 
                                             (brinfo_sec_offset < next_offset);
   
// Detect the branch error condition when the branch offset is less than the 
// first instruction offset in the word
// 
assign err_branch1_sec_t2 = err1_chk_sec_en & brinfo_sec_taken & brinfo_sec_valid & ins_vld[0] & 
                                                  (brinfo_sec_offset < offset_r);

// Detect the branch error condition when the branch offset is greater than
// the last instruction offset within that word 
//
assign err_branch1_sec_t3 = shift_int & brinfo_sec_taken & brinfo_sec_valid & (brinfo_sec_offset > offset_r) & ins_vld[0];

////////////////////////////////////////////////////////////////////////////////
// If a branch instruction needs word from next sequential address and if the 
// f_bit is not set, it indicates an aliasing error and flags this as error branch
// Similarly, error branch is generated if the branch plus delay slot doesn't need 
// word from the next word, but the f_bit is set; 
assign err_branch1_sec_t4 = al_prediction_sec & (brinfo_sec_f_bit ^ instr_in_word1);

////////////////////////////////////////////////////////////////////////////////
// First error branch condition
//
assign error_branch1 =  err_branch1_t1 | 
                        err_branch1_t2 | 
                        err_branch1_t3 |
                        err_branch1_t4 |
                        err_branch1_sec_t1 |
                        err_branch1_sec_t2 |
                        err_branch1_sec_t3 | 
                        err_branch1_sec_t4; 

wire error_branch2_chk1;
wire error_branch2_chk2;
wire error_branch2_chk3;
////////////////////////////////////////////////////////////////////////////////
// Second error branch condition. BTA fragments instructions
// Logic to be implemented
// error_branch2 = ((brinfo_bta > align_pc)                   && 
//                        (brinfo_bta < next_seq_pc) && 
//                         al_prediction
//                       );
// To reduce the timing on the path the following logci is implemented
// Find the difference between the BTA and the current PC. If the BTA is 
// less than the current PC, BTA cannot fragment the instruction. If the 
// difference between the BTA and the PC is less than then the PC increament 
// value the BTA fragments the isntruction and flag an error branch
// 
wire [`npuarc_PC_MSB:0] bta_pc_diff;
wire [`npuarc_PC_INC_RANGE]   bta_pc_diff_clip;

// leda  W484 off
// leda  BTTF_D002 off
// LMD : Unequal length LHS and RHS in assignment
// LD  : difference of 2 positive numbers, extra bits already added to operands
assign bta_pc_diff = {1'b0,brinfo_bta} - {1'b0,align_pc};
//leda  BTTF_D002 on
// leda  W484 on

assign bta_pc_diff_clip = (bta_pc_diff[`npuarc_PC_MSB-1:2] == 0) ? bta_pc_diff[`npuarc_PC_INC_RANGE]  :
                                                           3'b100;
// check if BTA is between the current PC and next seq PC 
assign error_branch2_chk1 = bta_pc_diff_clip < align_pc_incr;  

// check to make sure BTA is greater than current PC 
assign error_branch2_chk2 = bta_pc_diff_clip != 0;  

// check to see if BTA is greater than current PC and prediction is true
assign error_branch2_chk3 = !bta_pc_diff[`npuarc_PC_MSB] & al_prediction_pri;  

assign error_branch2 = error_branch2_chk1 & error_branch2_chk2 & error_branch2_chk3; 

////////////////////////////////////////////////////////////////////////////////
// Flag error if branch error condition 1 or 2 present
//
assign al_error_branch = error_branch1 | error_branch2;

always @(posedge clk or posedge rst_a)
begin: al_err_reg_PROC
  if (rst_a == 1'b1) begin
    al_error_branch_r <= 1'b0;
  end
  else if (flush == 1'b1) begin
    al_error_branch_r <= 1'b0;
  end
  else if ((al_error_branch == 1'b1) & (al_pass == 1'b1) & (stall_in == 1'b0)) begin
    al_error_branch_r <= 1'b1;
  end
end

////////////////////////////////////////////////////////////////////////////////
// Count the number of number of non taken branches in a Fetch block
////////////////////////////////////////////////////////////////////////////////
// leda  W484 off
// leda  BTTF_D002 off
// LMD : Unequal length LHS and RHS in assignment
// LJ  : al_num_nt cannot exceed 8
always @(posedge clk or posedge rst_a)
begin: al_num_nt_reg_PROC
  if (rst_a == 1'b1) begin
    al_num_nt <= 4'b0000;
  end
  else if(!stall) begin
    if(fb_cross) begin
      al_num_nt <= 4'b0000;
    end
    else if(al_is_predicted & (!al_prediction)) begin
      al_num_nt <= al_num_nt +1;
    end
  end 
end // al_num_nt_reg_PROC
//leda  BTTF_D002 on
// leda  W484 on

wire [1:0] al_num_nt_clip;
// clip the num_nt count to a max of 3 
assign al_num_nt_clip = (al_num_nt[3:2] == 0) ? al_num_nt[1:0] :
                                                2'b11;


// variables
reg [`npuarc_BR_PT_RANGE] ghr_r;
reg [`npuarc_BR_PT_RANGE] ghr_next;
reg [`npuarc_BR_PT_RANGE] ghr_new_r;
reg [`npuarc_BR_PT_RANGE] ghr_new_next;
reg [`npuarc_BR_PT_RANGE] ghr_restore;
reg [`npuarc_BR_PT_RANGE] ghr_restart;
wire                predicted_branch;
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  unused signal range
wire                mp_alt_way_valid;
wire [`npuarc_IC_WAYS_BITS_RANGE] mp_alt_way;
wire                mp_way_secondary;
wire [`npuarc_PC_RANGE]    mp_brinfo_tos;
wire [`npuarc_BR_RS_RANGE] mp_brinfo_tosp;
wire                mp_brinfo_strength;
wire [`npuarc_BR_OFFSET_RANGE]          mp_brinfo_offset; // offset of the primary branch
wire                mp_brinfo_valid;  // is the primary branch valid?
// leda NTL_CON13A on
wire [1:0]          mp_num_nt;
wire [`npuarc_BR_PT_RANGE] mp_ghr;


////////////////////////////////////////////////////////////////////////////////
// mispredict branch info paramters  
// 
assign {
        mp_alt_way_valid    , 
        mp_alt_way[`npuarc_IC_WAYS_BITS_RANGE],
        mp_way_secondary,
        mp_brinfo_tos [`npuarc_PC_RANGE],      // Return Stack Top of Stack value
        mp_brinfo_offset, // offset of the primary branch
        mp_brinfo_valid,       // is the primary branch valid?
        mp_brinfo_tosp [`npuarc_BR_RS_RANGE],
        mp_num_nt[1:0]       ,
        mp_ghr[`npuarc_BR_PT_RANGE] ,
        mp_brinfo_strength       // indicates if the primary branch is predicted (taken or not taken)
        } = mpd_brinfo_full;

////////////////////////////////////////////////////////////////////////////////
// commit branch info paramters  
// 
assign { 
      cm_alt_way_valid,                 // the alt way is valid
      cm_alt_way [`npuarc_IC_WAYS_BITS_RANGE], // Alternate predicted way to be used in case of a mispredict
      cm_way_sec,              // is the alt way from a secondary branch?
      cm_tos [`npuarc_PC_RANGE],      // Return Stack Top of Stack value
      cm_primary_offset,
      cm_primary_valid,
      cm_tosp [`npuarc_BR_RS_RANGE], // Return Stack Top Of Stack Pointer
      cm_num_nt[1:0],         // number of not taken branches in the 128-bit fetch block between 
                              // the entry point and the current branch 
      cm_ghr[`npuarc_BR_PT_RANGE],   // Global history register as valid at the start of the fetch block
      cm_c_in                 // Gshare confidence
      } = wa_brinfo_full [`npuarc_BR_FULL_INFO_RANGE] ;

////////////////////////////////////////////////////////////////////////////////
// GHR calculation
//////////////////////////////////////////////////////////////////////////////// 
always @*
begin : ghr_calc_PROC

  mp_uncond = mpd_type[0] & (mpd_type != `npuarc_BR_NOT_PREDICTED);

// GHR restore logic copied from BPU
  ghr_next = ghr_r;
  ghr_new_next = ghr_new_r;

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
       0: ghr_restore = {mp_ghr[`npuarc_BR_PT_MSB-1:`npuarc_BR_PT_LSB], mpd_direction};
       1: ghr_restore = {mp_ghr[`npuarc_BR_PT_MSB-2:`npuarc_BR_PT_LSB], 1'b0, mpd_direction};
       2: ghr_restore = {mp_ghr[`npuarc_BR_PT_MSB-3:`npuarc_BR_PT_LSB], 2'b00, mpd_direction};
       3: ghr_restore = {mp_ghr[`npuarc_BR_PT_MSB-4:`npuarc_BR_PT_LSB], 3'b000, mpd_direction};
      endcase        
    end

  // GHR for restart without mispredict
  case(cm_num_nt[1:0])
    2'd0: ghr_restart = cm_ghr;
    2'd1: ghr_restart = {cm_ghr[`npuarc_BR_PT_MSB-1:`npuarc_BR_PT_LSB], 1'b0};
    2'd2: ghr_restart = {cm_ghr[`npuarc_BR_PT_MSB-2:`npuarc_BR_PT_LSB], 2'b00};
    2'd3: ghr_restart = {cm_ghr[`npuarc_BR_PT_MSB-3:`npuarc_BR_PT_LSB], 3'b000};
  endcase        

  // maintain ghr_new on the fly in the current fetch block, while keeping ghr the same
  if (predicted_branch)
    ghr_new_next = {ghr_new_r[`npuarc_BR_PT_MSB-1:`npuarc_BR_PT_LSB],  al_prediction};


  // determine GHR
  // For a restart that is captured in the BPU, we immediately assign the restore value in the align stage.
  if (mpd_mispred)
  begin
    // in case of mispredict restore ghr from mispredict info
    ghr_next = ghr_restore;
    ghr_new_next = ghr_restore;
  end
  else if (flush) // flush == fch_restart
  begin
    ghr_next = ghr_restart;
    ghr_new_next = ghr_restart;
  end  
  else if (fb_cross)
  begin
    // when entering a new fetch block (taken branch or sequential) update GHR from GHR_new
    ghr_next = ghr_new_next; 
  end

end

always @(posedge clk or posedge rst_a)
begin : ghr_reg_PROC
  if (rst_a == 1'b1)
  begin
    ghr_r <= {`npuarc_BR_PT_ADDR_SIZE{1'b0}}; 
    ghr_new_r <= {`npuarc_BR_PT_ADDR_SIZE{1'b0}}; 
  end
  else if (~stall | flush)
  begin 
    ghr_r <= ghr_next;
    ghr_new_r <= ghr_new_next;
  end
end
assign predicted_branch = al_pass & al_is_predicted &
     ( (al_prediction_type == `npuarc_BR_CONDITIONAL) |
      (al_prediction_type == `npuarc_BR_COND_CALL) |
      (al_prediction_type == `npuarc_BR_COND_RETURN));


// End GHR calculation

////////////////////////////////////////////////////////////////////////////////
// Find the alternate way for predicted branches if I$ present   
//               
wire                       al_alt_way_valid;
wire [`npuarc_IC_WAYS_BITS_RANGE] al_alt_way; 
wire [`npuarc_IC_WAYS_BITS_RANGE] brinfo_way; 
wire                       new_cache_line;

// find if the next pc is in a different cache line
//
assign new_cache_line = (align_pc[`npuarc_IC_LINE_BITS] != align_pc_nxt[`npuarc_IC_LINE_BITS]); 

////////////////////////////////////////////////////////////////////////////////
// alt_way is valid if the current PC speads into a new cache line or if the 
// current PC and next PC in the same cache line and if no delay slot or 
// if the current PC and next PC are in the same cache line and PC is not within
// the last 8 bytes of the cache line if delay slot is present
//
assign  al_alt_way_valid = al_is_predicted & 
                           ((new_cache_line & (align_pc_nxt[2:1] != 0)) || 
                            (!new_cache_line & (!brinfo_d_bit)          ) ||
                            (   !new_cache_line & brinfo_d_bit
                              & (align_pc[`npuarc_IC_LINE_BITS-1:3] != {(`npuarc_IC_LINE_BITS-3){1'b1}}))
                           );

assign al_alt_way = al_prediction ? icache_way0_r : brinfo_way;

assign brinfo_way = (current_primary) ? brinfo_pri_way :
                                          brinfo_sec_way;
assign al_way_secondary = al_prediction_sec;

// Select the strength based on the predition is for primary or secondary
wire al_strength;
assign al_strength = (current_primary) ? brinfo_strength :
                                         brinfo_sec_strength;
////////////////////////////////////////////////////////////////////////////////
// Group the branch info signals to write to the branch info buffer
// The contents of the branch info buffer is used by BPU during branch commit 
// branch mispredicts
//
assign al_brinfo_full[`npuarc_BR_BUF_INFO_RANGE] = {
                         al_alt_way_valid, 
                         al_alt_way[`npuarc_IC_WAYS_BITS_RANGE], 
                         al_way_secondary,
//                       brinfo_offset[1:0],         // offset of the primary branch
                         brinfo_offset,              // offset of the primary branch
                         brinfo_valid,       // is the primary branch valid?
                         brinfo_tosp [`npuarc_BR_RS_RANGE],  // Return Stack Top Of Stack Pointer
                         al_num_nt_clip[1:0],        // number of NT branches in FB
                         ghr_r[`npuarc_BR_PT_RANGE],    // Global history register 
                         al_strength    // Gshare confidence
                        };             




///////////////////////////////////////////////////////////////////////////////
//output swap based on the instruction length
///////////////////////////////////////////////////////////////////////////////
wire [`npuarc_DATA_RANGE] al_limm_nxt_reg;
wire [`npuarc_DATA_RANGE] al_inst_nxt_reg;

reg [`npuarc_DATA_RANGE] align_inst_nxt;
reg [`npuarc_DATA_RANGE] align_limm_nxt;
wire [`npuarc_DATA_RANGE] align_limm_err;
assign {al_limm_nxt_reg,al_inst_nxt_reg} = inst_out;

always @(*) 
begin: inst_final_mux_PROC
  case (is_16bit)
     1'b0: begin
             align_inst_nxt = {al_inst_nxt_reg[15:0], al_inst_nxt_reg[31:16]};
             align_limm_nxt = {al_limm_nxt_reg[15:0], al_limm_nxt_reg[31:16]};
           end
     1'b1: begin
             align_inst_nxt = {al_inst_nxt_reg[15:0], al_inst_nxt_reg[31:16]};
             align_limm_nxt = {al_inst_nxt_reg[31:16], al_limm_nxt_reg[15:0]};
           end
  endcase
end // block: inst_final_mux_PROC


///////////////////////////////////////////////////////////////////////////////
// vec inst output for 64/128 bits
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// If there is bus error instert the PC in the limm   
//
assign align_limm_err = (|err0_r) ? {align_pc,1'b0} : align_limm_nxt;


///////////////////////////////////////////////////////////////////////////////
// Mux IFU outputs with debug  
///////////////////////////////////////////////////////////////////////////////


assign al_pass =  (inst_vld_out & (!brq_holdup) & 
                                  (!ecc_holdup) & 
                              //    !ecc_wr_holdup & 
                  (~al_error_branch_r) &
                             (!flush)); 

assign al_inst_nxt = align_inst_nxt; 
  assign al_limm_nxt = align_limm_err;



///////////////////////////////////////////////////////////////////////////////
// Exception Generation
// This section handles the generation of exception signals  
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Pass the error as al_exeption
//
assign al_exception = al_pass & (al_excpn_type != 0) & (~al_error_branch);

///////////////////////////////////////////////////////////////////////////////
// Exception type
// 0 - FCH_NO_ERR     - No exception condition detected
// 1 - FCH_BUS_ERR    - Bus Error
// 2 - FCH_ECC_ERR    - ECC Error
// 3 - FCH_ADDR_ERR   - ICCM addr blackhole Error
// 4 - FCH_ITLB_ERR   - Duplicate or overlapping ITLB entries
// 5 - FCH_ITLB_MISS  - ITLB Miss
// 6 - FCH_ITLB_ECC_ERR - ITLB Protection violation
// 7 - FCH_MPU_PROV   - MPU Protection Violation
//
assign al_excpn_type = 
    (err0_r[`npuarc_FCH_ITLB_ECC_ERR_1H] || (err1_r[`npuarc_FCH_ITLB_ECC_ERR_1H] & instr_in_word1) ) ? `npuarc_FCH_EXCPN_BITS'd6 : 
    (err0_r[`npuarc_FCH_ITLB_ERR_1H]     || (err1_r[`npuarc_FCH_ITLB_ERR_1H]     & instr_in_word1) ) ? `npuarc_FCH_EXCPN_BITS'd4 : 
    (err0_r[`npuarc_FCH_ITLB_MISS_1H]  || (err1_r[`npuarc_FCH_ITLB_MISS_1H]  & instr_in_word1) ) ? `npuarc_FCH_EXCPN_BITS'd5 : 
    (err0_r[`npuarc_FCH_BUS_ERR_1H]    || (err1_r[`npuarc_FCH_BUS_ERR_1H]    & instr_in_word1) ) ? `npuarc_FCH_EXCPN_BITS'd1 : 
    (err0_r[`npuarc_FCH_ADDR_ERR_1H]   || (err1_r[`npuarc_FCH_ADDR_ERR_1H]   & instr_in_word1) ) ? `npuarc_FCH_EXCPN_BITS'd3 :
    (ecc_db_error & (!ecc_ifu_expn_disable)      ) ? `npuarc_FCH_EXCPN_BITS'd2 :
                                                   `npuarc_FCH_EXCPN_BITS'd0;


assign al_excpn_info = {instr_in_word1, experm1_r,  experm0_r};

// Determine if itlb err occured in [pc] page or next page when instr spans page boundary
//  -winning err is used to determine the err page
always @*
begin : al_ifu_err_nxtpg_PROC 
  case (al_excpn_type) // find winning itlb err
    `npuarc_FCH_EXCPN_BITS'd`npuarc_FCH_ITLB_ECC_ERR: // 6
      al_ifu_err_nxtpg = instr_in_word1 & err1_r[`npuarc_FCH_ITLB_ECC_ERR_1H] & (!err0_r[`npuarc_FCH_ITLB_ECC_ERR_1H]);
    `npuarc_FCH_EXCPN_BITS'd`npuarc_FCH_ITLB_ERROR: // 4
      al_ifu_err_nxtpg = instr_in_word1 & err1_r[`npuarc_FCH_ITLB_ERR_1H] & (!err0_r[`npuarc_FCH_ITLB_ERR_1H]);
    `npuarc_FCH_EXCPN_BITS'd`npuarc_FCH_ITLB_MISS:  // 5
      al_ifu_err_nxtpg = instr_in_word1 & err1_r[`npuarc_FCH_ITLB_MISS_1H] & (!err0_r[`npuarc_FCH_ITLB_MISS_1H]);
    default: al_ifu_err_nxtpg  = instr_in_word1;
  endcase
end

assign al_iprot_viol = !al_error_branch && (iprot_viol0_r || (iprot_viol1_r && instr_in_word1));




//////////////////////////////////////////////////////////////////////////////
// ECC 
//
///////////////////////////////////////////////////////////////////////////////


wire        ecc_err0;     
wire        ecc_err1;     
wire        ecc_sb_err0;     
wire        ecc_sb_err1;     
wire        ecc_db_err0;     
wire        ecc_db_err1;     

// wire        ecc_error;     



   wire                ecc0_enable;
   // Enable ECC checking based on source
   assign ecc0_enable = (ecc_enable0_r 
                           ) & (!ecc_ifu_disable);


   wire                ecc_err00;
   wire                ecc_sb_err00;
   wire                ecc_db_err00;
   wire [`npuarc_SYNDROME_MSB:0] syndrome00;
   wire [31:0]         ecc_data00;

   npuarc_alb_ecc_cac32_c  u_alb_ecc_cac32_00(
                      .clk               (clk),
                      .rst_a             (rst_a),

                      .data_in           (inst0_r[31:0]    ),    // 32-bit data in
                      .ecc_code_in       (ecc_code0_r[6:0]),

                      .ecc_chk           ({
                                           1'b0,
                                           ecc_enable0_r}  ),  

                      .ecc_error         (ecc_err00),
                      .sb_error          (ecc_sb_err00),    // single bit error detected
                      .db_error          (ecc_db_err00),    // double bit error detected
                      .syndrome       (syndrome00),
                      .data_out          (ecc_data00)     // corrected data out

   );
   wire                ecc_err01;
   wire                ecc_sb_err01;
   wire                ecc_db_err01;
   wire [`npuarc_SYNDROME_MSB:0] syndrome01;
   wire [31:0]         ecc_data01;

   npuarc_alb_ecc_cac32_c  u_alb_ecc_cac32_01(
                      .clk               (clk),
                      .rst_a             (rst_a),

                      .data_in           (inst0_r[63:32]    ),    // 32-bit data in
                      .ecc_code_in       (ecc_code0_r[13:7]),

                      .ecc_chk           ({
                                           1'b0,
                                           ecc_enable0_r}  ),  

                      .ecc_error         (ecc_err01),
                      .sb_error          (ecc_sb_err01),    // single bit error detected
                      .db_error          (ecc_db_err01),    // double bit error detected
                      .syndrome       (syndrome01),
                      .data_out          (ecc_data01)     // corrected data out

   );
   wire                ecc1_enable;
   // Enable ECC checking based on source
   assign ecc1_enable = (ecc_enable1_r 
                           ) & (!ecc_ifu_disable);


   wire                ecc_err10;
   wire                ecc_sb_err10;
   wire                ecc_db_err10;
   wire [`npuarc_SYNDROME_MSB:0] syndrome10;
   wire [31:0]         ecc_data10;

   npuarc_alb_ecc_cac32_c  u_alb_ecc_cac32_10(
                      .clk               (clk),
                      .rst_a             (rst_a),

                      .data_in           (inst1_r[31:0]    ),    // 32-bit data in
                      .ecc_code_in       (ecc_code1_r[6:0]),

                      .ecc_chk           ({
                                           1'b0,
                                           ecc_enable1_r}  ),  

                      .ecc_error         (ecc_err10),
                      .sb_error          (ecc_sb_err10),    // single bit error detected
                      .db_error          (ecc_db_err10),    // double bit error detected
                      .syndrome       (syndrome10),
                      .data_out          (ecc_data10)     // corrected data out

   );
   wire                ecc_err11;
   wire                ecc_sb_err11;
   wire                ecc_db_err11;
   wire [`npuarc_SYNDROME_MSB:0] syndrome11;
   wire [31:0]         ecc_data11;

   npuarc_alb_ecc_cac32_c  u_alb_ecc_cac32_11(
                      .clk               (clk),
                      .rst_a             (rst_a),

                      .data_in           (inst1_r[63:32]    ),    // 32-bit data in
                      .ecc_code_in       (ecc_code1_r[13:7]),

                      .ecc_chk           ({
                                           1'b0,
                                           ecc_enable1_r}  ),  

                      .ecc_error         (ecc_err11),
                      .sb_error          (ecc_sb_err11),    // single bit error detected
                      .db_error          (ecc_db_err11),    // double bit error detected
                      .syndrome       (syndrome11),
                      .data_out          (ecc_data11)     // corrected data out

   );


//////////////////////////////////////////////////////////////////////////////
// To prevent uninitialized sections of the 64bit word propagating x on the 
// ECC controls following masking logic is used to mask the ECC error
// If the instruction in fully within the current word following conditions 
// apply
// if offset_r == 2 or 3, then we dont need to check ecc_err01
// if next offset != 3 or 0, then we don't need to check ecc_err00
// if the instruction in partly in word1 following conditions apply
// if next offset != 3, we dont need to check ecc_err10

assign ecc_err0 = (((offset_r == 0) || (offset_r == 1)) && ecc_err00) || 
                  (((next_offset ==3) || (next_offset ==0) || instr_in_word1) && ecc_err01);

assign ecc_err1 = ecc_err10 | ((next_offset ==3) & ecc_err11);



//assign ecc_sb_err0 = ecc_sb_err01 | ecc_sb_err00;

//assign ecc_sb_err1 = ecc_sb_err11 | ecc_sb_err10;

//assign ecc_sb_err0 = (((offset_r == 0) || (offset_r == 1)) && ecc_sb_err00) | 
//                     (((next_offset ==3) || (next_offset ==0) || instr_in_word1) && ecc_sb_err01);
wire ecc_sb_chk_err00;
wire ecc_sb_chk_err01;
wire ecc_sb_chk_err10;
reg  ecc_sb_disable00;
reg  ecc_sb_disable01;
reg  ecc_sb_disable10;
reg  ecc_sb_disable11;
wire ecc_sb_chk_err11;
assign ecc_sb_chk_err00 = (((offset_r == 0) || (offset_r == 1)) && ecc_sb_err00 && (!ecc_sb_disable00));

assign ecc_sb_chk_err01 = (((next_offset ==3) || (next_offset ==0) || instr_in_word1) && ecc_sb_err01 & (!ecc_sb_disable01));

assign ecc_sb_err0  = ecc_sb_chk_err00 | ecc_sb_chk_err01;

//assign ecc_sb_err1 = ecc_sb_err10 | ((next_offset ==3) & ecc_sb_err11);
assign ecc_sb_chk_err10 = ecc_sb_err10 & (!ecc_sb_disable10);

assign ecc_sb_chk_err11 = ((next_offset ==3) & ecc_sb_err11 & (!ecc_sb_disable11));

assign ecc_sb_err1 = ecc_sb_chk_err10 | ecc_sb_chk_err11;

// assign ecc_db_err0 = ecc_db_err01 | ecc_db_err00;

// assign ecc_db_err1 = ecc_db_err11 | ecc_db_err10;

assign ecc_db_err0 = (((offset_r == 0) || (offset_r == 1)) && ecc_db_err00) | 
                     (((next_offset ==3) || (next_offset ==0) || instr_in_word1) && ecc_db_err01);

assign ecc_db_err1 = ecc_db_err10 | ((next_offset ==3) & ecc_db_err11);


assign ecc_data0 = {
                       ecc_data01
                                           ,
                       ecc_data00
                                           };
assign ecc_data1 = {
                       ecc_data11
                                           ,
                       ecc_data10
                                           };








// If error detected in word0 or word1, hold the state
assign ecc_error = (ecc_err0 & ins_vld[0]) | (ecc_err1 & instr_in_word1 & ins_vld[1]);
wire ecc_sb_error;
// Detect Single bit error in word 0 or word1
wire ecc_sb_error0; 
wire ecc_sb_error1; 

assign ecc_sb_error0 = (ecc_sb_err0 & ecc0_enable & ins_vld[0] & (!eos_wait)); 

assign ecc_sb_error1 = (ecc_sb_err1 & ecc1_enable & instr_in_word1 & ins_vld[1] & (!eos_wait));

assign ecc_sb_error = ecc_sb_error0 | ecc_sb_error1; 

assign ecc_holdup = ecc_sb_error;
//assign ecc_holdup = 0;

assign ecc_db_error = (ecc_db_err0 & ecc0_enable & ins_vld[0] & (!eos_wait)) | 
                      (ecc_db_err1 & ecc1_enable & instr_in_word1 & ins_vld[1] & (!eos_wait));

// Find the source generated the ECC error for storing in the fault status reg


wire icache_addr_hit;
assign  icache_addr_hit =
                         1'b1; 

assign al_icache_ecc_err = icache_addr_hit  
                         & ecc_db_error
                         & (!(al_error_branch_r | al_error_branch))
                         & ins_vld[0];

assign al_icache_ecc_sb_err = icache_addr_hit 
                            & ecc_load0
                            & (!(al_error_branch_r | al_error_branch))
                            & ins_vld[0];



////////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin: al_ecc_state_reg_PROC
  if (rst_a == 1'b1) begin
    ecc_load0 <= 1'b0;
  end
  else if(ecc_load0 == 1'b1) begin
    ecc_load0 <= 1'b0;
  end
  else if(ecc_sb_error0 == 1'b1) begin
    ecc_load0 <= 1'b1;
  end
end

always @(posedge clk or posedge rst_a)
begin: al_ecc_state1_reg_PROC
  if (rst_a == 1'b1) begin
    ecc_load1 <= 1'b0;
  end
  else if(ecc_load1 == 1'b1) begin
    ecc_load1 <= 1'b0;
  end
  else if(ecc_sb_error1 == 1'b1) begin
    ecc_load1 <= 1'b1;
  end
end

////////////////////////////////////////////////////////////////////////////////
// If the 1bit corruption is in the ECC code, after reloading the data (ecc_load) 
// the error condition still exists as we don't correct the ecc code
// The following flag is used to disable ecc error condition under such 
// conditions until next load or shift  
always @(posedge clk or posedge rst_a)
begin: al_ecc_sb_disable_reg_PROC
  if (rst_a == 1'b1) begin
    ecc_sb_disable00 <= 1'b0;
    ecc_sb_disable01 <= 1'b0;
    ecc_sb_disable10 <= 1'b0;
    ecc_sb_disable11 <= 1'b0;
  end
  else if (!stall & (shift || load || load_word01)) begin
    ecc_sb_disable00 <= 1'b0;
    ecc_sb_disable01 <= 1'b0;
    ecc_sb_disable10 <= 1'b0;
    ecc_sb_disable11 <= 1'b0;
  end
  else begin
    if(ecc_load0 & ecc_sb_chk_err00) begin
      ecc_sb_disable00 <= 1'b1;
    end
    if(ecc_load0 & ecc_sb_chk_err01) begin
      ecc_sb_disable01 <= 1'b1;
    end
    if(ecc_load1 & ecc_sb_chk_err10) begin
      ecc_sb_disable10 <= 1'b1;
    end
    if(ecc_load1 & ecc_sb_chk_err11) begin
      ecc_sb_disable11 <= 1'b1;
    end
end
end


//////////////////////////For pct //////////////////////////////////////////////
assign     ifu_bit_error_r = 1'b0
                           | ecc_sb_error
                   ;






  
wire [(`npuarc_IC_ECC_SIZE*2)-1:0] sb_ecc_err0;
wire [(`npuarc_IC_ECC_SIZE*2)-1:0] sb_ecc_error0;
wire [(`npuarc_IC_ECC_SIZE*2)-1:0] db_ecc_err0;
wire [(`npuarc_IC_ECC_SIZE*2)-1:0] db_ecc_error0;
wire [(`npuarc_IC_ECC_SIZE*2)-1:0] sb_ecc_err1;
wire [(`npuarc_IC_ECC_SIZE*2)-1:0] sb_ecc_error1;
wire [(`npuarc_IC_ECC_SIZE*2)-1:0] db_ecc_err1;
wire [(`npuarc_IC_ECC_SIZE*2)-1:0] db_ecc_error1;

wire [(`npuarc_IC_ECC_SIZE*4)-1:0] sb_ecc_error;
wire [(`npuarc_IC_ECC_SIZE*4)-1:0] db_ecc_error;

wire [(`npuarc_IC_ECC_SIZE*4)-1:0] ifu_sb_ecc_error;
wire [(`npuarc_IC_ECC_SIZE*4)-1:0] ifu_db_ecc_error;

reg                         ifu_ecc_enable0_r;
reg                         ifu_ecc_enable1_r;

reg                         ifu_bank0_ecc_enable_r;
reg                         ifu_bank1_ecc_enable_r;

wire                        bank_shift;
reg                         bank_shift_r;

reg [`npuarc_SYNDROME_MSB:0]       ifu_data_bank00_syndrome;
reg [`npuarc_SYNDROME_MSB:0]       ifu_data_bank01_syndrome;
reg [`npuarc_SYNDROME_MSB:0]       ifu_data_bank10_syndrome;
reg [`npuarc_SYNDROME_MSB:0]       ifu_data_bank11_syndrome;

// Generate single/double bit error vector


assign sb_ecc_err0 = {ecc_sb_chk_err01, ecc_sb_chk_err00};
assign sb_ecc_err1 = {ecc_sb_chk_err11, ecc_sb_chk_err10};

assign db_ecc_err0 = {(((next_offset ==3) || (next_offset ==0) || instr_in_word1) && ecc_db_err01), 
                      (((offset_r == 0) || (offset_r == 1)) && ecc_db_err00)};

assign db_ecc_err1 = {((next_offset ==3) & ecc_db_err11), ecc_db_err10};


assign sb_ecc_error0 = sb_ecc_err0 & {(`npuarc_IC_ECC_SIZE*2){ecc0_enable & ins_vld[0] & (!eos_wait)}};
assign sb_ecc_error1 = sb_ecc_err1 & {(`npuarc_IC_ECC_SIZE*2){ecc1_enable & instr_in_word1 & ins_vld[1] & (!eos_wait)}};

assign sb_ecc_error = {sb_ecc_error1, sb_ecc_error0} & {(`npuarc_IC_ECC_SIZE*4){(!(al_error_branch_r | al_error_branch))}};

assign db_ecc_error0 = db_ecc_err0 & {(`npuarc_IC_ECC_SIZE*2){ecc0_enable & ins_vld[0] & (!eos_wait)}};
assign db_ecc_error1 = db_ecc_err1 & {(`npuarc_IC_ECC_SIZE*2){ecc1_enable & instr_in_word1 & ins_vld[1] & (!eos_wait)}};

assign db_ecc_error = {db_ecc_error1, db_ecc_error0} & {(`npuarc_IC_ECC_SIZE*4){(!(al_error_branch_r | al_error_branch))}};

assign bank_shift =   ((first_word_r[0]) && ((bank_ctl0_r == 2'd2) || (bank_ctl0_r == 2'd3))) ||
                      (!(first_word_r[0]) && ((bank_ctl0_r == 2'd0) || (bank_ctl0_r == 2'd1))) ||
                      ((first_word_r[1]) && ((bank_ctl1_r == 2'd0) || (bank_ctl1_r == 2'd1))) ||
                      (!(first_word_r[1]) && ((bank_ctl1_r == 2'd2) || (bank_ctl1_r == 2'd3))) ;


assign ifu_sb_ecc_error = bank_shift ? {sb_ecc_error[1:0], sb_ecc_error[3:2]} : sb_ecc_error;

assign ifu_db_ecc_error = bank_shift ? {db_ecc_error[1:0], db_ecc_error[3:2]} : db_ecc_error;


always @(posedge clk or posedge rst_a)
begin: ecc_enable0_reg_PROC
  if (rst_a == 1'b1) begin
      ifu_ecc_enable0_r      <= 1'b0;
  end
  else if(!stall) begin
    if (load || load_word01) begin
      ifu_ecc_enable0_r <= ecc_enable0;
    end
    else if (shift & ins_vld[1]) begin
      ifu_ecc_enable0_r <= ecc_enable1_r;
    end
  end
end  

always @(posedge clk or posedge rst_a)
begin: ecc_enable1_reg_PROC
  if (rst_a == 1'b1) begin
    ifu_ecc_enable1_r <= 1'b0;
  end
  else if(!stall) begin
    if ((load || load_word01) & vld1)begin
      ifu_ecc_enable1_r <= ecc_enable1;
    end
    else if ((shift | load_word1) & vld0) begin
      ifu_ecc_enable1_r <= ecc_enable0;
    end
  end
end

always @(posedge clk or posedge rst_a)
begin: bank_shift_reg_PROC
  if (rst_a == 1'b1) begin
    bank_shift_r <= 1'b0;
  end
  else begin
    bank_shift_r <= bank_shift;
  end
end

always @ *
begin: ifu_data_bank_syndrome_PROC
  if (bank_shift)
  begin
        ifu_data_bank00_syndrome = syndrome10;
        ifu_data_bank01_syndrome = syndrome11;
        ifu_data_bank10_syndrome = syndrome00;
        ifu_data_bank11_syndrome = syndrome01;
  end
  else
  begin
       ifu_data_bank00_syndrome = syndrome00;
       ifu_data_bank01_syndrome = syndrome01;
       ifu_data_bank10_syndrome = syndrome10;
       ifu_data_bank11_syndrome = syndrome11;
  end
end

always @ *
begin
  if(bank_shift_r)
  begin
    ifu_bank0_ecc_enable_r = ifu_ecc_enable1_r;
    ifu_bank1_ecc_enable_r = ifu_ecc_enable0_r;
  end
  else
  begin
    ifu_bank0_ecc_enable_r = ifu_ecc_enable0_r;
    ifu_bank1_ecc_enable_r = ifu_ecc_enable1_r;
  end
end



wire [(`npuarc_IC_ECC_SIZE*4)-1:0] ic_data_ecc_sb_error;
wire [(`npuarc_IC_ECC_SIZE*4)-1:0] ic_data_ecc_db_error;

assign ic_data_ecc_sb_error = icache_addr_hit ? ifu_sb_ecc_error : {(`npuarc_IC_ECC_SIZE*4){1'b0}};
assign ic_data_ecc_db_error = icache_addr_hit ? ifu_db_ecc_error : {(`npuarc_IC_ECC_SIZE*4){1'b0}};

  // Register SBE signal

  always @(posedge clk or posedge rst_a)
  begin : ic_data_ecc_sb_error_reg_PROC
    if (rst_a == 1'b1)
    begin
       fs_ic_data_bank00_ecc_sb_error_r <= 1'b0;
       fs_ic_data_bank01_ecc_sb_error_r <= 1'b0;
       fs_ic_data_bank10_ecc_sb_error_r <= 1'b0;
       fs_ic_data_bank11_ecc_sb_error_r <= 1'b0;
    end
    else
    begin
        fs_ic_data_bank00_ecc_sb_error_r <= ic_data_ecc_sb_error[0];
        fs_ic_data_bank01_ecc_sb_error_r <= ic_data_ecc_sb_error[1];
        fs_ic_data_bank10_ecc_sb_error_r <= ic_data_ecc_sb_error[2];
        fs_ic_data_bank11_ecc_sb_error_r <= ic_data_ecc_sb_error[3];
    end
  end

  // Register DBE signal

  always @(posedge clk or posedge rst_a)
  begin : ic_data_ecc_db_error_reg_PROC
    if (rst_a == 1'b1)
    begin
       fs_ic_data_bank00_ecc_db_error_r <= 1'b0;
       fs_ic_data_bank01_ecc_db_error_r <= 1'b0;
       fs_ic_data_bank10_ecc_db_error_r <= 1'b0;
       fs_ic_data_bank11_ecc_db_error_r <= 1'b0;
    end
    else
    begin
        fs_ic_data_bank00_ecc_db_error_r <= ic_data_ecc_db_error[0];
        fs_ic_data_bank01_ecc_db_error_r <= ic_data_ecc_db_error[1];
        fs_ic_data_bank10_ecc_db_error_r <= ic_data_ecc_db_error[2];
        fs_ic_data_bank11_ecc_db_error_r <= ic_data_ecc_db_error[3];
    end
  end


  // Register syndrome

  always @(posedge clk or posedge rst_a)
  begin : ic_data_syndrome_reg_PROC
    if (rst_a == 1'b1)
    begin
       fs_ic_data_bank00_syndrome_r <= {`npuarc_SYNDROME_MSB+1{1'b0}};
       fs_ic_data_bank01_syndrome_r <= {`npuarc_SYNDROME_MSB+1{1'b0}};
       fs_ic_data_bank10_syndrome_r <= {`npuarc_SYNDROME_MSB+1{1'b0}};
       fs_ic_data_bank11_syndrome_r <= {`npuarc_SYNDROME_MSB+1{1'b0}};
    end
    else
    begin
       if (ifu_bank0_ecc_enable_r)
       begin
       fs_ic_data_bank00_syndrome_r <= ifu_data_bank00_syndrome;
       fs_ic_data_bank01_syndrome_r <= ifu_data_bank01_syndrome;
       end

       if (ifu_bank1_ecc_enable_r)
       begin
       fs_ic_data_bank10_syndrome_r <= ifu_data_bank10_syndrome;
       fs_ic_data_bank11_syndrome_r <= ifu_data_bank11_syndrome;
       end
    end
  end






      
endmodule  //  alb_ifu_align
