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
// ===========================================================================
//
//  #    #####    ####          #####   ######   ####   #   #  #    #   ####
//  #    #    #  #    #         #    #  #       #        # #   ##   #  #    #
//  #    #    #  #    #         #    #  #####    ####     #    # #  #  #
//  #    #####   #  # #         #####   #            #    #    #  # #  #
//  #    #   #   #   #          #   #   #       #    #    #    #   ##  #    #
//  #    #    #   ### # ######  #    #  ######   ####     #    #    #   ####
//
//             #    #    #
//             #    ##   #
//             #    # #  #
//             #    #  # #
//             #    #   ##
//    #######  #    #    #
//
// Description:
//
//  This module synchronizes all asynchronous interrupt lines to the CPU
//  clock. This is to reduce the possibility of metastability when
//  asynchronous inputs are sampled on the rising edge of the CPU clock.
//  Effectively a full clock cycle is provided to allow any metastability
//  to settle out of the circuit before the synchronized signals are used.
//
// ==========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

`include "const.def"

module npuarc_alb_irq_resync_in (

  ////////// Asynchronous inputs ////////////////////////////////////////////
  //
  input                       irq17_a, // Async. IRQ input
  input                       irq19_a, // Async. IRQ input
  input                       irq21_a, // Async. IRQ input
  input                       irq22_a, // Async. IRQ input
  input                       irq23_a, // Async. IRQ input
  input                       irq24_a, // Async. IRQ input
  input                       irq25_a, // Async. IRQ input
  input                       irq26_a, // Async. IRQ input
  input                       irq27_a, // Async. IRQ input
  input                       irq28_a, // Async. IRQ input
  input                       irq29_a, // Async. IRQ input
  input                       irq30_a, // Async. IRQ input
  input                       irq31_a, // Async. IRQ input
  input                       irq32_a, // Async. IRQ input
  input                       irq33_a, // Async. IRQ input
  input                       irq34_a, // Async. IRQ input
  input                       irq35_a, // Async. IRQ input
  input                       irq36_a, // Async. IRQ input
  input                       irq37_a, // Async. IRQ input
  input                       irq38_a, // Async. IRQ input
  input                       irq39_a, // Async. IRQ input
  input                       irq40_a, // Async. IRQ input
  input                       irq41_a, // Async. IRQ input
  input                       irq42_a, // Async. IRQ input
  input                       irq43_a, // Async. IRQ input
  input                       irq44_a, // Async. IRQ input
  input                       irq45_a, // Async. IRQ input
  input                       irq46_a, // Async. IRQ input
  input                       irq47_a, // Async. IRQ input
  input                       irq48_a, // Async. IRQ input
  input                       irq49_a, // Async. IRQ input
  input                       irq50_a, // Async. IRQ input
  input                       irq51_a, // Async. IRQ input
  input                       irq52_a, // Async. IRQ input
  input                       irq53_a, // Async. IRQ input
  input                       irq54_a, // Async. IRQ input

  ////////// Synchronised output ///////////////////////////////////////////
  //
  output [`npuarc_IRQE_RANGE]        irq_r,          // synchronous output
  output                      irq_sync_req_a, // request for synchronization
  input                       irq_clk_en_r,   // clk phase to qualify irq_r
  input                       clk,            // clock
// spyglass disable_block W240
// SMD: input declared but not read
// SJ:  unused in some configs, removal requires many changes close to release
  input                       rst_a           // asynchronous reset
// spyglass enable_block W240
);

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Local Declarations                                                     //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
wire [`npuarc_IRQE_RANGE]         irq_a; 
// leda NTL_CON13A off
// LMD: non driving internal net Range
// LJ:  Not used carry bit
wire                       unused;
// leda NTL_CON13A on
wire                       irq_sync_clk;
wire [`npuarc_IRQE_RANGE]         irq_2_r;

// To simply handling of the vectors, we consolidate each seperate pin
// into a single vector.
//
assign {unused, irq_a} = {   1'b0
                           , irq54_a
                           , irq53_a
                           , irq52_a
                           , irq51_a
                           , irq50_a
                           , irq49_a
                           , irq48_a
                           , irq47_a
                           , irq46_a
                           , irq45_a
                           , irq44_a
                           , irq43_a
                           , irq42_a
                           , irq41_a
                           , irq40_a
                           , irq39_a
                           , irq38_a
                           , irq37_a
                           , irq36_a
                           , irq35_a
                           , irq34_a
                           , irq33_a
                           , irq32_a
                           , irq31_a
                           , irq30_a
                           , irq29_a
                           , irq28_a
                           , irq27_a
                           , irq26_a
                           , irq25_a
                           , irq24_a
                           , irq23_a
                           , irq22_a
                           , irq21_a
                           , 1'b0
                           , irq19_a
                           , 1'b0
                           , irq17_a
                           , 1'b0
                         }
                         ;

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Create (div/2) clock for irq synchronizing flip-flops                  //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

npuarc_clkgate u_clkgate_irq (
  .clk_in            (clk),
  .clock_enable      (irq_clk_en_r), // enabled every other core clock
  .clk_out           (irq_sync_clk)  // div/2 clock
);


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining the synchronizing flip-flops                //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

// Instantiate CDC synchronizer wrappers so that the synthesis flow can 
// replace it with the proper synchronizer cell of the target library.
//

npuarc_cdc_sync u_cdc_sync_16 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[16]),
  .dout       (irq_2_r[16])
);

npuarc_cdc_sync u_cdc_sync_17 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[17]),
  .dout       (irq_2_r[17])
);

npuarc_cdc_sync u_cdc_sync_18 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[18]),
  .dout       (irq_2_r[18])
);

npuarc_cdc_sync u_cdc_sync_19 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[19]),
  .dout       (irq_2_r[19])
);

npuarc_cdc_sync u_cdc_sync_20 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[20]),
  .dout       (irq_2_r[20])
);

npuarc_cdc_sync u_cdc_sync_21 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[21]),
  .dout       (irq_2_r[21])
);

npuarc_cdc_sync u_cdc_sync_22 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[22]),
  .dout       (irq_2_r[22])
);

npuarc_cdc_sync u_cdc_sync_23 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[23]),
  .dout       (irq_2_r[23])
);

npuarc_cdc_sync u_cdc_sync_24 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[24]),
  .dout       (irq_2_r[24])
);

npuarc_cdc_sync u_cdc_sync_25 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[25]),
  .dout       (irq_2_r[25])
);

npuarc_cdc_sync u_cdc_sync_26 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[26]),
  .dout       (irq_2_r[26])
);

npuarc_cdc_sync u_cdc_sync_27 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[27]),
  .dout       (irq_2_r[27])
);

npuarc_cdc_sync u_cdc_sync_28 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[28]),
  .dout       (irq_2_r[28])
);

npuarc_cdc_sync u_cdc_sync_29 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[29]),
  .dout       (irq_2_r[29])
);

npuarc_cdc_sync u_cdc_sync_30 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[30]),
  .dout       (irq_2_r[30])
);

npuarc_cdc_sync u_cdc_sync_31 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[31]),
  .dout       (irq_2_r[31])
);

npuarc_cdc_sync u_cdc_sync_32 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[32]),
  .dout       (irq_2_r[32])
);

npuarc_cdc_sync u_cdc_sync_33 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[33]),
  .dout       (irq_2_r[33])
);

npuarc_cdc_sync u_cdc_sync_34 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[34]),
  .dout       (irq_2_r[34])
);

npuarc_cdc_sync u_cdc_sync_35 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[35]),
  .dout       (irq_2_r[35])
);

npuarc_cdc_sync u_cdc_sync_36 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[36]),
  .dout       (irq_2_r[36])
);

npuarc_cdc_sync u_cdc_sync_37 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[37]),
  .dout       (irq_2_r[37])
);

npuarc_cdc_sync u_cdc_sync_38 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[38]),
  .dout       (irq_2_r[38])
);

npuarc_cdc_sync u_cdc_sync_39 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[39]),
  .dout       (irq_2_r[39])
);

npuarc_cdc_sync u_cdc_sync_40 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[40]),
  .dout       (irq_2_r[40])
);

npuarc_cdc_sync u_cdc_sync_41 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[41]),
  .dout       (irq_2_r[41])
);

npuarc_cdc_sync u_cdc_sync_42 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[42]),
  .dout       (irq_2_r[42])
);

npuarc_cdc_sync u_cdc_sync_43 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[43]),
  .dout       (irq_2_r[43])
);

npuarc_cdc_sync u_cdc_sync_44 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[44]),
  .dout       (irq_2_r[44])
);

npuarc_cdc_sync u_cdc_sync_45 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[45]),
  .dout       (irq_2_r[45])
);

npuarc_cdc_sync u_cdc_sync_46 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[46]),
  .dout       (irq_2_r[46])
);

npuarc_cdc_sync u_cdc_sync_47 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[47]),
  .dout       (irq_2_r[47])
);

npuarc_cdc_sync u_cdc_sync_48 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[48]),
  .dout       (irq_2_r[48])
);

npuarc_cdc_sync u_cdc_sync_49 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[49]),
  .dout       (irq_2_r[49])
);

npuarc_cdc_sync u_cdc_sync_50 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[50]),
  .dout       (irq_2_r[50])
);

npuarc_cdc_sync u_cdc_sync_51 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[51]),
  .dout       (irq_2_r[51])
);

npuarc_cdc_sync u_cdc_sync_52 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[52]),
  .dout       (irq_2_r[52])
);

npuarc_cdc_sync u_cdc_sync_53 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[53]),
  .dout       (irq_2_r[53])
);

npuarc_cdc_sync u_cdc_sync_54 (
  .clk        (irq_sync_clk),     // div/2 clock
  .rst_a      (rst_a),
  .din        (irq_a[54]),
  .dout       (irq_2_r[54])
);

assign irq_r           = irq_2_r;

// leda W563 off
// LMD: reduction of single bit expression is redundant
// LJ:  configurable field may be a single bit
// spyglass disable_block Ac_conv02 Ac_conv01
// SMD: cdc sync signals converging on combinational gate
// SJ:  cdc syncs are independent and chance of glitch is very low
assign irq_sync_req_a  = |(irq_a ^ irq_r);
// spyglass enable_block Ac_conv02 Ac_conv01
// leda W563 on

endmodule // alb_irq_resync_in
