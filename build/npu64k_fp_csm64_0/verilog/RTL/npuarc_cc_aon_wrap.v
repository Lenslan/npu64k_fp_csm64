// Library ARCv2CC-3.2.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2014 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary
// work of Synopsys, Inc., and is fully protected under copyright and
// trade secret laws. You may not view, use, disclose, copy, or distribute
// this file or any information contained herein except pursuant to a
// valid written license from Synopsys, Inc.
//
// Certain materials incorporated herein are copyright (C) 2010 - 2012, The
// University Court of the University of Edinburgh. All Rights Reserved.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
//   ####    ####         #     ####   #    #     #   #   # #####    #   #####
//  #    #  #    #       # #   #    #  ##   #     #   #   # #    #  # #  #    #
//  #       #           #   #  #    #  # #  #     #   #   # #####  #   # #    #
//  #       #           #####  #    #  #  # #     #   #   # #  #   ##### #####
//  #    #  #    #      #   #  #    #  #   ##      # # # #  #   #  #   # #
//   ####    ####  ###  #   #   ####   #    # ###   #   #   #    # #   # #
//
// ===========================================================================
//
// Description:
//  Verilog source of the cc_top always-on modules:
//        -- cc_aon_reset_ctrl
//        -- cc_top_aon_regs
//        -- cc_pdm_resync_in
//        -- cc_clock_ctrl
//
// ===========================================================================

// Set simulation timescale
//
`include   "const.def"

// Macro definitions for the top-level Verilog files.
//
`include   "npuarc_cc_exported_defines.v"
`include   "npuarc_cc_defines.v"










module npuarc_cc_aon_wrap
(
  output                            cc_misc_l1_clk,

  input                             cc_aux_l1_clk_enable,
  output                            cc_aux_accept_en,

  input                                cc_top_cg_en_gaux_cmd_valid,
  output                               cc_top_cg_en_gaux_cmd_accept,
  input [`npuarc_CC_GAUX_CMD_WIDTH-1:0]       cc_top_cg_en_gaux_cmd,

  output                               cc_top_cg_en_gaux_res_valid,
  input                                cc_top_cg_en_gaux_res_accept,
  output [`npuarc_CC_GAUX_RES_WIDTH-1:0]      cc_top_cg_en_gaux_res_data,

  input                                cc_top_cg_en_gaux_wen_valid,
  input [`npuarc_CC_GAUX_WADDR_WIDTH-1:0]     cc_top_cg_en_gaux_wen_addr,
  input [`npuarc_CC_GAUX_WDATA_WIDTH-1:0]     cc_top_cg_en_gaux_wen_data,



  input                                biu_l1_clk_enable,
  output                               biu_accept_en,
  output                               biu_l1_clk,

  input                                l1_clk_enable,
  output                               l1_accept_en,
  output                               l1_clk,



  input                    cc_gaux_idle,
  // cc pdm interface with biu
  input                    biu_idle,

  output                   cc_idle,



  output                   cc_pd1_rst,
  output                   cc_pd1_rst_a,
  output                   cc_pd1_clk,





  //

  ////////// Level-1 clock gate AUX bits /////////////////////////////////////
  //
  output                  l1_cg_dis,
  output                   cc_biu_l1_cg_dis,
  output                   cc_top_l1_cg_dis,



  ////////// Global clock/reset input signals /////////////////////////////////
  input                    clk,
  input                    rst_a,
  input                    test_mode
);


// spyglass disable_block W528
// SMD: Variable set but not read
// SJ: No care about the warning
//========================== Wire declarations ===============================








//==================== Component instantiations ==============================

// spyglass disable_block Reset_info09a
// SMD: reset net unconstrained
// SJ: internal generated reset signal
  wire  cc_aon_rst;   // synchronized reset signal for cc_top_aon_regs and/or cc_pdm_top
// spyglass enable_block Reset_info09a

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Instantiate the cc_reset_ctrl module, for all modules instantiated in    //
// the cc_aon_wrap module                                                   //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
// spyglass disable_block W402b
// SMD: is gated or internally generated
// SJ: reset synchronized
npuarc_cc_reset_ctrl u_cc_aon_reset_ctrl (
  .clk                        (clk),            // clock
  .cc_rst_a                   (rst_a),          // async CC reset
  .test_mode                  (test_mode),      // test mode to bypass FFs
 // spyglass disable_block W402b
 // SMD: Reset is gated or internally generated
 // SJ: reset is controlled by testmode, do not care this wrn
  .cc_rst                     (cc_aon_rst)      // reset for cc_aon_wrap modules
 // spyglass enable_block W402b
);

npuarc_cc_reset_ctrl u_cc_pd1_reset_ctrl (
  .clk                        (clk),            // clock
  .cc_rst_a                   (cc_pd1_rst_a),   // async CC reset
  .test_mode                  (test_mode),      // test mode to bypass FFs
  .cc_rst                     (cc_pd1_rst)      // reset for PD1 domain module
                                                //    who have no its own reset-syncer
);

// spyglass enable_block W402b

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Instantiate the cc_top_aon_regs module                                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
npuarc_cc_top_aon_regs u_cc_top_aon_regs (




  .cc_top_cg_en_gaux_cmd_valid  (cc_top_cg_en_gaux_cmd_valid),
  .cc_top_cg_en_gaux_cmd_accept (cc_top_cg_en_gaux_cmd_accept),
  .cc_top_cg_en_gaux_cmd        (cc_top_cg_en_gaux_cmd),

  .cc_top_cg_en_gaux_res_valid  (cc_top_cg_en_gaux_res_valid),
  .cc_top_cg_en_gaux_res_accept (cc_top_cg_en_gaux_res_accept),
  .cc_top_cg_en_gaux_res_data   (cc_top_cg_en_gaux_res_data),

  .cc_top_cg_en_gaux_wen_valid  (cc_top_cg_en_gaux_wen_valid),
  .cc_top_cg_en_gaux_wen_addr   (cc_top_cg_en_gaux_wen_addr),
  .cc_top_cg_en_gaux_wen_data   (cc_top_cg_en_gaux_wen_data),

  .cc_top_l1_cg_dis             (cc_top_l1_cg_dis),//1 disable L1 clock gate, 0 enable
  .cc_biu_l1_cg_dis             (cc_biu_l1_cg_dis),


  .l1_cg_dis             (l1_cg_dis),

  .nmi_restart_r               (1'b0),

  .rst_a                       (cc_aon_rst),
  .clk                         (clk)
);




//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Instantiate the cc_clock_ctrl module                                     //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
npuarc_cc_clock_ctrl u_cc_clock_ctrl (
  .cc_misc_l1_clk           (cc_misc_l1_clk),
  .cc_aux_l1_clk_enable     (cc_aux_l1_clk_enable),
  .cc_aux_accept_en         (cc_aux_accept_en),
  .cc_pd1_clk              (cc_pd1_clk),
  .biu_l1_clk_enable       (biu_l1_clk_enable),
  .biu_accept_en           (biu_accept_en),
  .biu_l1_clk              (biu_l1_clk),

  .l1_clk_enable    (l1_clk_enable),
  .l1_accept_en     (l1_accept_en),
  .l1_clk           (l1_clk),

  // global clock and reset input
  .clk                     (clk),
  .nmi_restart_r           (1'b0),
  .rst_a                   (cc_aon_rst)
);



//====================     Output assigments    ==============================

  assign cc_pd1_rst_a = rst_a;





// spyglass enable_block W528


//generate cc idle signal
wire cc_idle_nxt;
reg  cc_idle_r;
// spyglass disable_block Ac_conv01
// SMD: N synchronizers converge on combinational gate
// SJ: These signals are independent with each other, no care about this
assign cc_idle_nxt = 1'b1
                     & (cc_gaux_idle
                     )
                     & (biu_idle
                     )
                     ;
// spyglass enable_block Ac_conv01

// spyglass disable_block W402b
// SMD: is gated or internally generated
// SJ: do not care this wrn
always @(posedge clk or posedge cc_aon_rst)
begin: cc_idle_r_PROC
  if(cc_aon_rst == 1'b1)begin
      cc_idle_r <= 1'b1;
  end 
  else begin
      cc_idle_r <= cc_idle_nxt;
  end
end
// spyglass enable_block W402b

assign cc_idle = cc_idle_r;





endmodule // cc_aon_wrap
