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
//    ####   #####   ####         #####  ###  #      #####
//    #   #  #      #    #        #       #   #      #
//    #   #  #      #             #       #   #      #
//    #   #  #      #             #       #   #      #
//    ####   ####   #             ####    #   #      ####
//    ##     #      #  ###        #       #   #      #
//    # #    #      #    #        #       #   #      #
//    #  #   #      #   ##        #       #   #      #
//    #   #  #####   ### #        #      ###  #####  #####
//
// ===========================================================================
//
// Description:
//
//  The regfile_2r2w module is a synthesised flip-flop based register file
//  with two asynchronous read ports and one or two synchronous write ports.
//
//  The number of registers and the width of each register can be configured
//  by setting the configuration macros which begin with the RGF prefix.
//  Note: the `RGF_NUM_REGS macro can take values in the set {16, 32} only.
//
//  The number of write ports is set by the RGF_WR_PORTS macro, which can be
//  either 1 or 2. This module will be configured to have the required
//  number of write ports defined by RGF_WR_PORTS.
//
//  If LL64_OPTION is set to 1, then one of the read ports and both write
//  ports are 64-bits wide. The 64-bit read port (port 1) allows Store data
//  for 64-bit stores to be read in a single cycle. The 64-bit write ports
//  allow 64-bit Load data and/or 64-bit multiplier products to be retired
//  to the register file simultaneously.
//
//  If SRC64_OPTION is set to 1, then both read ports are 64-bits wide,
//  allowing register pairs to be read from both ports.
//
//  When writing a 32-bit single register, the write data must be presented
//  on both the upper and lower 32-bit halves of the write ports. 
//  When writing a 64-bit double register, the write register address must
//  be an even numbered register R. The lower 32 bits of write data will be
//  written to register R, and the upper 32 bits of write data will be
//  written to register R+1.
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_regfile_2r2w (
  ////////// General input signals /////////////////////////////////////////
  //
  // leda NTL_CON13C off
  // LMD: non driving port range
  // LJ:  General input signals

  input                         clk,          // clock
// spyglass disable_block W240
// SMD: input declared but not used
// SJ:  standard interface rst, unused in some configs
  input                         rst_a,        // asynchronous reset
// spyglass enable_block W240
  // leda NTL_CON13C on
  ////////// Read port 0 ///////////////////////////////////////////////////
  //
  input      [`npuarc_RGF_ADDR_RANGE]  ra0,          // read address 0
  output     [`npuarc_RGF_SLICE_RANGE] rdata0,       // read data 0
  output     [`npuarc_RGF_SLICE_RANGE] rdata0_hi,    // read data 0 (upper 32 bits)
  ////////// Read port 1 ///////////////////////////////////////////////////
  //
  input      [`npuarc_RGF_ADDR_RANGE]  ra1,          // read address 1
  output     [`npuarc_RGF_SLICE_RANGE] rdata1,       // read data 1
  output     [`npuarc_RGF_SLICE_RANGE] rdata1_hi,    // read data 1 (upper 32 bits)


  ////////// Write port 0 //////////////////////////////////////////////////
  //
  input                         wenb0,        // write enable 0
  input      [`npuarc_RGF_ADDR_RANGE]  wa0,          // write address 0
  input      [`npuarc_RGF_SLICE_RANGE] wdata0,       // write data low 32 bits 0
  input                         wenb0_64,     // 64-bit write control 0
  input      [`npuarc_RGF_SLICE_RANGE] wdata0_hi,    // write data high 32 bits 0

  ////////// Write port 1 //////////////////////////////////////////////////
  //
  input      [`npuarc_RGF_ADDR_RANGE]  wa1,          // write address 1
  input                         wenb1,        // write enable 1
  input      [`npuarc_RGF_SLICE_RANGE] wdata1,       // write data 1
  input                         wenb1_64,     // 64-bit write control 1
  input      [`npuarc_RGF_SLICE_RANGE] wdata1_hi,    // write data high 32 bits 1

  ////////// Accumulator read port /////////////////////////////////////////
  //
  output reg [`npuarc_RGF_SLICE_RANGE] accl_r,       // ACCL register value (r58)
  output reg [`npuarc_RGF_SLICE_RANGE] acch_r,       // ACCH register value (r59)

  ////////// Accumulator write port ////////////////////////////////////////
  //
  input      [`npuarc_RGF_SLICE_RANGE] accl_nxt,     // next implicit ACCL wr data
  input      [`npuarc_RGF_SLICE_RANGE] acch_nxt,     // next implicit ACCH wr data
  input                         acc_wenb,     // ACCL/ACCH write enable



  ////////// Read-only registers ///////////////////////////////////////////
  //
  input      [`npuarc_LPC_RANGE]       lp_count_r,   // loop-count register
  input      [`npuarc_PC_MSB:2]        pcl           // current PC, for PCL
);

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Declare the register file storage elements                             //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_0_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_1_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_2_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_3_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_4_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_5_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_6_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_7_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_8_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_9_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_10_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_11_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_12_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_13_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_14_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_15_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_16_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_17_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_18_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_19_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_20_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_21_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_22_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_23_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_24_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_25_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_26_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_27_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_28_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_29_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_30_r;
reg     [`npuarc_RGF_SLICE_RANGE]  gpr_b0_31_r;

reg [`npuarc_RGF_SLICE_RANGE_EDC] rdata0_prel;       // read data 0
reg [`npuarc_RGF_SLICE_RANGE_EDC] rdata0_hi_prel;    // read data 0 (upper 32 bits)

reg [`npuarc_RGF_SLICE_RANGE_EDC] rdata1_prel;       // read data 1
reg [`npuarc_RGF_SLICE_RANGE_EDC] rdata1_hi_prel;    // read data 1 (upper 32 bits)


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Declare intermediate signals for reading and writing registers         //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

reg     [`npuarc_DATA_RANGE]       one_hot_0;    // one-hot dec from wa0
reg     [`npuarc_DATA_RANGE]       one_hot_0_hi; // rotated-left and gated for 64-bit
reg     [`npuarc_DATA_RANGE]       w_enb_0;      // write enb for port 0
reg     [`npuarc_DATA_RANGE]       one_hot_1;    // one-hot dec from wa1
reg     [`npuarc_DATA_RANGE]       one_hot_1_hi; // rotated-left and gated for 64-bit
reg     [`npuarc_DATA_RANGE]       w_enb_1;      // write enb for port 1
// leda NTL_CON13A off
// LMD: non driving internal net Range
// LJ:  write enb for each reg
reg     [`npuarc_DATA_RANGE]       wr_enb;       // write enb for each reg
// leda NTL_CON13A on

reg                         accl_w0;      // one-hot write ACCL on port 0
reg                         acch_w0;      // one-hot write ACCH on port 0
reg                         accl_w1;      // one-hot read ACCL on port 1
reg                         acch_w1;      // one-hot read ACCH on port 1
reg                         wr_accl;      // consolidated write enable ACCL
reg                         wr_acch;      // consolidated write enable ACCH

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Asynchronous write port address decode logic                           //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : rgf_write_PROC

  // Define the one-hot decoding
  //
  case (wa0)
    6'd0: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 0);
    6'd1: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 1);
    6'd2: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 2);
    6'd3: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 3);
    6'd4: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 4);
    6'd5: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 5);
    6'd6: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 6);
    6'd7: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 7);
    6'd8: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 8);
    6'd9: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 9);
    6'd10: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 10);
    6'd11: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 11);
    6'd12: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 12);
    6'd13: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 13);
    6'd14: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 14);
    6'd15: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 15);
    6'd16: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 16);
    6'd17: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 17);
    6'd18: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 18);
    6'd19: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 19);
    6'd20: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 20);
    6'd21: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 21);
    6'd22: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 22);
    6'd23: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 23);
    6'd24: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 24);
    6'd25: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 25);
    6'd26: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 26);
    6'd27: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 27);
    6'd28: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 28);
    6'd29: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 29);
    6'd30: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 30);
    6'd31: one_hot_0 = (`npuarc_DATA_SIZE'b1 << 31);
    default:            one_hot_0 = 32'd0;
  endcase

  case (wa1)
    6'd0: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 0);
    6'd1: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 1);
    6'd2: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 2);
    6'd3: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 3);
    6'd4: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 4);
    6'd5: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 5);
    6'd6: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 6);
    6'd7: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 7);
    6'd8: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 8);
    6'd9: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 9);
    6'd10: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 10);
    6'd11: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 11);
    6'd12: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 12);
    6'd13: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 13);
    6'd14: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 14);
    6'd15: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 15);
    6'd16: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 16);
    6'd17: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 17);
    6'd18: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 18);
    6'd19: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 19);
    6'd20: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 20);
    6'd21: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 21);
    6'd22: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 22);
    6'd23: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 23);
    6'd24: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 24);
    6'd25: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 25);
    6'd26: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 26);
    6'd27: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 27);
    6'd28: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 28);
    6'd29: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 29);
    6'd30: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 30);
    6'd31: one_hot_1 = (`npuarc_DATA_SIZE'b1 << 31);
    default:            one_hot_1 = 32'd0;
  endcase

  // Generate port 0 one-hot write enable for upper 32-bits of 
  // 64-bit write by rotating the one-hot vector for the lower 32-bit
  // register. This allows any pair of registers {a, (a+1)%32} to be 
  // written simultaneously.
  //
  one_hot_0_hi = {one_hot_0[30:0], 1'b0};

  // Generate port 1 one-hot write enable for upper 32-bits of 
  // 64-bit write by rotating the one-hot vector for the lower 32-bit
  // register. This allows any pair of registers {a, (a+1)%32} to be 
  // written simultaneously.
  //
  one_hot_1_hi = {one_hot_1[30:0], 1'b0};

  // Gate each decoded one-hot write-select with its write enable
  //
  w_enb_0 = (one_hot_0 & {32{wenb0}}) | (one_hot_0_hi & {32{wenb0_64}});
  w_enb_1 = (one_hot_1 & {32{wenb1}}) | (one_hot_1_hi & {32{wenb1_64}});

  // Generate a combined write enable for each register
  // from both ports' one-hot write enable vectors
  //
  wr_enb = w_enb_0 | w_enb_1;

  // Generate write enables for ACCL and ACCH from each write port
  //
  accl_w0 = (wa0 == `npuarc_ACCL_REG) & wenb0;
  acch_w0 = (wa0[`npuarc_RGF_PAIR_RANGE] == `npuarc_ACC_PAIR)
          & ((wa0[0] & wenb0) | wenb0_64);
  accl_w1 = (wa1 == `npuarc_ACCL_REG) & wenb1;
  acch_w1 = (wa1[`npuarc_RGF_PAIR_RANGE] == `npuarc_ACC_PAIR)
          & ((wa1[0] & wenb1) | wenb1_64);
  
  wr_accl = accl_w0
            | accl_w1
            | acc_wenb
            ;
  wr_acch = acch_w0
            | acch_w1
            | acc_wenb
            ;

end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Asynchronous read port logic                                           //
//                                                                        //
//  This logic includes the reading of PCL and LP_COUNT, but those two    //
//  registers are never written by the register file module.              //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

// Select output registers using ra0 and ra1

always @*
begin : rgf_port0_PROC

  case (ra0)
    6'd0:   rdata0_prel = gpr_b0_0_r;
    6'd1:   rdata0_prel = gpr_b0_1_r;
    6'd2:   rdata0_prel = gpr_b0_2_r;
    6'd3:   rdata0_prel = gpr_b0_3_r;
    6'd4:   rdata0_prel = gpr_b0_4_r;
    6'd5:   rdata0_prel = gpr_b0_5_r;
    6'd6:   rdata0_prel = gpr_b0_6_r;
    6'd7:   rdata0_prel = gpr_b0_7_r;
    6'd8:   rdata0_prel = gpr_b0_8_r;
    6'd9:   rdata0_prel = gpr_b0_9_r;
    6'd10:   rdata0_prel = gpr_b0_10_r;
    6'd11:   rdata0_prel = gpr_b0_11_r;
    6'd12:   rdata0_prel = gpr_b0_12_r;
    6'd13:   rdata0_prel = gpr_b0_13_r;
    6'd14:   rdata0_prel = gpr_b0_14_r;
    6'd15:   rdata0_prel = gpr_b0_15_r;
    6'd16:   rdata0_prel = gpr_b0_16_r;
    6'd17:   rdata0_prel = gpr_b0_17_r;
    6'd18:   rdata0_prel = gpr_b0_18_r;
    6'd19:   rdata0_prel = gpr_b0_19_r;
    6'd20:   rdata0_prel = gpr_b0_20_r;
    6'd21:   rdata0_prel = gpr_b0_21_r;
    6'd22:   rdata0_prel = gpr_b0_22_r;
    6'd23:   rdata0_prel = gpr_b0_23_r;
    6'd24:   rdata0_prel = gpr_b0_24_r;
    6'd25:   rdata0_prel = gpr_b0_25_r;
    6'd26:   rdata0_prel = gpr_b0_26_r;
    6'd27:   rdata0_prel = gpr_b0_27_r;
    6'd28:   rdata0_prel = gpr_b0_28_r;
    6'd29:   rdata0_prel = gpr_b0_29_r; // ILINK is not duplicated
    6'd30:   rdata0_prel = gpr_b0_30_r;
    6'd31:   rdata0_prel = gpr_b0_31_r;
        6'd58:   rdata0_prel =  {accl_r};
        6'd59:   rdata0_prel =  {acch_r};
      6'd60:   rdata0_prel = {lp_count_r};
      6'd63:   rdata0_prel = {pcl, 2'b00 };
    default: rdata0_prel = `npuarc_RGF_BITS'd0;
  endcase

  case (ra0[5:1])
    5'd0:   rdata0_hi_prel = gpr_b0_1_r;
    5'd1:   rdata0_hi_prel = gpr_b0_3_r;
    5'd2:   rdata0_hi_prel = gpr_b0_5_r;
    5'd3:   rdata0_hi_prel = gpr_b0_7_r;
    5'd4:   rdata0_hi_prel = gpr_b0_9_r;
    5'd5:   rdata0_hi_prel = gpr_b0_11_r;
    5'd6:   rdata0_hi_prel = gpr_b0_13_r;
    5'd7:   rdata0_hi_prel = gpr_b0_15_r;
    5'd8:   rdata0_hi_prel = gpr_b0_17_r;
    5'd9:   rdata0_hi_prel = gpr_b0_19_r;
    5'd10:   rdata0_hi_prel = gpr_b0_21_r;
    5'd11:   rdata0_hi_prel = gpr_b0_23_r;
    5'd12:   rdata0_hi_prel = gpr_b0_25_r;
    5'd13:   rdata0_hi_prel = gpr_b0_27_r;
    5'd14:   rdata0_hi_prel = gpr_b0_29_r; // ILINK is not duplicated
    5'd15:   rdata0_hi_prel = gpr_b0_31_r;
          5'd29:   rdata0_hi_prel = {acch_r};
    default: rdata0_hi_prel = `npuarc_RGF_BITS'd0;
  endcase

end

always @*
begin : rgf_port1_PROC

  case (ra1)
    6'd0:   rdata1_prel = gpr_b0_0_r;
    6'd1:   rdata1_prel = gpr_b0_1_r;
    6'd2:   rdata1_prel = gpr_b0_2_r;
    6'd3:   rdata1_prel = gpr_b0_3_r;
    6'd4:   rdata1_prel = gpr_b0_4_r;
    6'd5:   rdata1_prel = gpr_b0_5_r;
    6'd6:   rdata1_prel = gpr_b0_6_r;
    6'd7:   rdata1_prel = gpr_b0_7_r;
    6'd8:   rdata1_prel = gpr_b0_8_r;
    6'd9:   rdata1_prel = gpr_b0_9_r;
    6'd10:   rdata1_prel = gpr_b0_10_r;
    6'd11:   rdata1_prel = gpr_b0_11_r;
    6'd12:   rdata1_prel = gpr_b0_12_r;
    6'd13:   rdata1_prel = gpr_b0_13_r;
    6'd14:   rdata1_prel = gpr_b0_14_r;
    6'd15:   rdata1_prel = gpr_b0_15_r;
    6'd16:   rdata1_prel = gpr_b0_16_r;
    6'd17:   rdata1_prel = gpr_b0_17_r;
    6'd18:   rdata1_prel = gpr_b0_18_r;
    6'd19:   rdata1_prel = gpr_b0_19_r;
    6'd20:   rdata1_prel = gpr_b0_20_r;
    6'd21:   rdata1_prel = gpr_b0_21_r;
    6'd22:   rdata1_prel = gpr_b0_22_r;
    6'd23:   rdata1_prel = gpr_b0_23_r;
    6'd24:   rdata1_prel = gpr_b0_24_r;
    6'd25:   rdata1_prel = gpr_b0_25_r;
    6'd26:   rdata1_prel = gpr_b0_26_r;
    6'd27:   rdata1_prel = gpr_b0_27_r;
    6'd28:   rdata1_prel = gpr_b0_28_r;
    6'd29:   rdata1_prel = gpr_b0_29_r; // ILINK is not duplicated
    6'd30:   rdata1_prel = gpr_b0_30_r;
    6'd31:   rdata1_prel = gpr_b0_31_r;
        6'd58:   rdata1_prel =  {accl_r};
        6'd59:   rdata1_prel =  {acch_r};
      6'd60:   rdata1_prel = {lp_count_r};
      6'd63:   rdata1_prel = {pcl, 2'b00 };
    default: rdata1_prel = `npuarc_RGF_BITS'd0;
  endcase

  case (ra1[5:1])
    5'd0:   rdata1_hi_prel = gpr_b0_1_r;
    5'd1:   rdata1_hi_prel = gpr_b0_3_r;
    5'd2:   rdata1_hi_prel = gpr_b0_5_r;
    5'd3:   rdata1_hi_prel = gpr_b0_7_r;
    5'd4:   rdata1_hi_prel = gpr_b0_9_r;
    5'd5:   rdata1_hi_prel = gpr_b0_11_r;
    5'd6:   rdata1_hi_prel = gpr_b0_13_r;
    5'd7:   rdata1_hi_prel = gpr_b0_15_r;
    5'd8:   rdata1_hi_prel = gpr_b0_17_r;
    5'd9:   rdata1_hi_prel = gpr_b0_19_r;
    5'd10:   rdata1_hi_prel = gpr_b0_21_r;
    5'd11:   rdata1_hi_prel = gpr_b0_23_r;
    5'd12:   rdata1_hi_prel = gpr_b0_25_r;
    5'd13:   rdata1_hi_prel = gpr_b0_27_r;
    5'd14:   rdata1_hi_prel = gpr_b0_29_r; // ILINK is not duplicated
    5'd15:   rdata1_hi_prel = gpr_b0_31_r;
          5'd29:   rdata1_hi_prel = {acch_r};
    default: rdata1_hi_prel = `npuarc_RGF_BITS'd0;
  endcase

end




assign rdata0    = rdata0_prel[`npuarc_RGF_SLICE_RANGE];       // read data 0
assign rdata0_hi = rdata0_hi_prel[`npuarc_RGF_SLICE_RANGE];    // read data 0 (upper 32 bits)

assign rdata1    = rdata1_prel[`npuarc_RGF_SLICE_RANGE];       // read data 1
assign rdata1_hi = rdata1_hi_prel[`npuarc_RGF_SLICE_RANGE];    // read data 1 (upper 32 bits)

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous write port logic                                           //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
// leda S_1C_R off
// leda NTL_RST03 off
// leda S_1C_R off
// LMD: A flipflop without reset
// LJ:  register-file contents are not cleared on reset, by design
// leda G_551_1_K off
// leda G_551_1_C off
// LMD: There should be at most one synchronous reset/set/load signal in a sequential block
// LJ:  Each register is loaded once, with an independent enable
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
always @(posedge clk)
begin : gpr_write_PROC
  if (wr_enb[0] == 1'b1)
    gpr_b0_0_r <= (w_enb_1[0] == 1) ? wdata1 : wdata0;
  if (wr_enb[1] == 1'b1)
    gpr_b0_1_r <= (w_enb_1[1] == 1) ? wdata1_hi : wdata0_hi;
  if (wr_enb[2] == 1'b1)
    gpr_b0_2_r <= (w_enb_1[2] == 1) ? wdata1 : wdata0;
  if (wr_enb[3] == 1'b1)
    gpr_b0_3_r <= (w_enb_1[3] == 1) ? wdata1_hi : wdata0_hi;
  if (wr_enb[4] == 1'b1)
    gpr_b0_4_r <= (w_enb_1[4] == 1) ? wdata1 : wdata0;
  if (wr_enb[5] == 1'b1)
    gpr_b0_5_r <= (w_enb_1[5] == 1) ? wdata1_hi : wdata0_hi;
  if (wr_enb[6] == 1'b1)
    gpr_b0_6_r <= (w_enb_1[6] == 1) ? wdata1 : wdata0;
  if (wr_enb[7] == 1'b1)
    gpr_b0_7_r <= (w_enb_1[7] == 1) ? wdata1_hi : wdata0_hi;
  if (wr_enb[8] == 1'b1)
    gpr_b0_8_r <= (w_enb_1[8] == 1) ? wdata1 : wdata0;
  if (wr_enb[9] == 1'b1)
    gpr_b0_9_r <= (w_enb_1[9] == 1) ? wdata1_hi : wdata0_hi;
  if (wr_enb[10] == 1'b1)
    gpr_b0_10_r <= (w_enb_1[10] == 1) ? wdata1 : wdata0;
  if (wr_enb[11] == 1'b1)
    gpr_b0_11_r <= (w_enb_1[11] == 1) ? wdata1_hi : wdata0_hi;
  if (wr_enb[12] == 1'b1)
    gpr_b0_12_r <= (w_enb_1[12] == 1) ? wdata1 : wdata0;
  if (wr_enb[13] == 1'b1)
    gpr_b0_13_r <= (w_enb_1[13] == 1) ? wdata1_hi : wdata0_hi;
  if (wr_enb[14] == 1'b1)
    gpr_b0_14_r <= (w_enb_1[14] == 1) ? wdata1 : wdata0;
  if (wr_enb[15] == 1'b1)
    gpr_b0_15_r <= (w_enb_1[15] == 1) ? wdata1_hi : wdata0_hi;
  if (wr_enb[16] == 1'b1)
    gpr_b0_16_r <= (w_enb_1[16] == 1) ? wdata1 : wdata0;
  if (wr_enb[17] == 1'b1)
    gpr_b0_17_r <= (w_enb_1[17] == 1) ? wdata1_hi : wdata0_hi;
  if (wr_enb[18] == 1'b1)
    gpr_b0_18_r <= (w_enb_1[18] == 1) ? wdata1 : wdata0;
  if (wr_enb[19] == 1'b1)
    gpr_b0_19_r <= (w_enb_1[19] == 1) ? wdata1_hi : wdata0_hi;
  if (wr_enb[20] == 1'b1)
    gpr_b0_20_r <= (w_enb_1[20] == 1) ? wdata1 : wdata0;
  if (wr_enb[21] == 1'b1)
    gpr_b0_21_r <= (w_enb_1[21] == 1) ? wdata1_hi : wdata0_hi;
  if (wr_enb[22] == 1'b1)
    gpr_b0_22_r <= (w_enb_1[22] == 1) ? wdata1 : wdata0;
  if (wr_enb[23] == 1'b1)
    gpr_b0_23_r <= (w_enb_1[23] == 1) ? wdata1_hi : wdata0_hi;
  if (wr_enb[24] == 1'b1)
    gpr_b0_24_r <= (w_enb_1[24] == 1) ? wdata1 : wdata0;
  if (wr_enb[25] == 1'b1)
    gpr_b0_25_r <= (w_enb_1[25] == 1) ? wdata1_hi : wdata0_hi;
  if (wr_enb[26] == 1'b1)
    gpr_b0_26_r <= (w_enb_1[26] == 1) ? wdata1 : wdata0;
  if (wr_enb[27] == 1'b1)
    gpr_b0_27_r <= (w_enb_1[27] == 1) ? wdata1_hi : wdata0_hi;
  if (wr_enb[28] == 1'b1)
    gpr_b0_28_r <= (w_enb_1[28] == 1) ? wdata1 : wdata0;
  if (wr_enb[29] == 1'b1)
    gpr_b0_29_r <= (w_enb_1[29] == 1) ? wdata1_hi : wdata0_hi;
  if (wr_enb[30] == 1'b1)
    gpr_b0_30_r <= (w_enb_1[30] == 1) ? wdata1 : wdata0;
  if (wr_enb[31] == 1'b1)
    gpr_b0_31_r <= (w_enb_1[31] == 1) ? wdata1_hi : wdata0_hi;
end


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous accumulator logic (ACCL, ACCH)                             //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : acc_reg_PROC

  if (rst_a == 1'b1)
    begin
    accl_r <= `npuarc_DATA_SIZE'd0;
    acch_r <= `npuarc_DATA_SIZE'd0;
    end
  else 
    begin
    if (wr_accl == 1'b1)
      accl_r <= acc_wenb 
              ? accl_nxt 
              : (accl_w1 ? wdata1 : wdata0)
              ;

    if (wr_acch == 1'b1)
      acch_r <= acc_wenb 
              ? acch_nxt 
              : (acch_w1 ? wdata1_hi : wdata0_hi)
              ;
    
    end
end

// leda G_551_1_K on
// leda G_551_1_C on
// leda NTL_RST03 on
// leda S_1C_R on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01

endmodule

