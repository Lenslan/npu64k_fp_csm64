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
//
// ===========================================================================
//
// Description:
//  Verilog module of BUS bridge within BIU
//
// ===========================================================================

// Configuration-dependent macro definitions
//

`include "npuarc_biu_defines.v"




// Set simulation timescale
//
`include "const.def"


module npuarc_biu_busb_clk_ctrl
// leda G_521_2_B off
// LMD: Use lowercase letters for all signal reg, net and port names
// LJ: Pfx may include the uppercase, so disable the lint checking rule
  (
// leda NTL_CON13C off
// LMD: non driving internal net
// LJ: Some signals bit field are indeed no driven
// leda NTL_CON37 off
// LMD: Signal/Net must read from the input port in module
// LJ: Some signals bit field are indeed not read and used




  output clk_gated_biu_cbu,

  input   bfed_core0_nllm_l2ifu_ibp_cmd_valid,
  input   bfed_core0_nllm_l2ifu_ibp_cmd_accept,
  input   bfed_core0_nllm_l2ifu_ibp_cmd_read,

  input   bfed_core0_nllm_l2ifu_ibp_rd_valid,
  input   bfed_core0_nllm_l2ifu_ibp_rd_excl_ok,
  input   bfed_core0_nllm_l2ifu_ibp_rd_accept,
  input   bfed_core0_nllm_l2ifu_ibp_err_rd,
  input   bfed_core0_nllm_l2ifu_ibp_rd_last,

  input   bfed_core0_nllm_l2ifu_ibp_wr_done,
  input   bfed_core0_nllm_l2ifu_ibp_wr_excl_done,
  input   bfed_core0_nllm_l2ifu_ibp_err_wr,
  input   bfed_core0_nllm_l2ifu_ibp_wr_resp_accept,

  input   bfed_lq_wq_ibp_cmd_valid,
  input   bfed_lq_wq_ibp_cmd_accept,
  input   bfed_lq_wq_ibp_cmd_read,

  input   bfed_lq_wq_ibp_rd_valid,
  input   bfed_lq_wq_ibp_rd_excl_ok,
  input   bfed_lq_wq_ibp_rd_accept,
  input   bfed_lq_wq_ibp_err_rd,
  input   bfed_lq_wq_ibp_rd_last,

  input   bfed_lq_wq_ibp_wr_done,
  input   bfed_lq_wq_ibp_wr_excl_done,
  input   bfed_lq_wq_ibp_err_wr,
  input   bfed_lq_wq_ibp_wr_resp_accept,

  input   bfed_dmu_rbu_dmu_wbu_ibp_cmd_valid,
  input   bfed_dmu_rbu_dmu_wbu_ibp_cmd_accept,
  input   bfed_dmu_rbu_dmu_wbu_ibp_cmd_read,

  input   bfed_dmu_rbu_dmu_wbu_ibp_rd_valid,
  input   bfed_dmu_rbu_dmu_wbu_ibp_rd_excl_ok,
  input   bfed_dmu_rbu_dmu_wbu_ibp_rd_accept,
  input   bfed_dmu_rbu_dmu_wbu_ibp_err_rd,
  input   bfed_dmu_rbu_dmu_wbu_ibp_rd_last,

  input   bfed_dmu_rbu_dmu_wbu_ibp_wr_done,
  input   bfed_dmu_rbu_dmu_wbu_ibp_wr_excl_done,
  input   bfed_dmu_rbu_dmu_wbu_ibp_err_wr,
  input   bfed_dmu_rbu_dmu_wbu_ibp_wr_resp_accept,







  // spyglass disable_block W240
  // SMD: input port declared but not read
  // SJ: No care about the warning
  input rst_a     ,
  input nmi_restart_r ,
  // spyglass enable_block W240
  input clk
// leda NTL_CON37 on
// leda NTL_CON13C on
);











  wire bfed_core0_nllm_l2ifu_ibp_rd_chnl_valid = bfed_core0_nllm_l2ifu_ibp_rd_valid | bfed_core0_nllm_l2ifu_ibp_rd_excl_ok | bfed_core0_nllm_l2ifu_ibp_err_rd;
  wire bfed_core0_nllm_l2ifu_ibp_wrsp_chnl_valid = bfed_core0_nllm_l2ifu_ibp_wr_done | bfed_core0_nllm_l2ifu_ibp_wr_excl_done | bfed_core0_nllm_l2ifu_ibp_err_wr;
  wire bfed_core0_nllm_l2ifu_ibp_idle;
  npuarc_biu_busb_ibp_idle
  #(
   .OUTSTAND_NUM  (16),
   .OUTSTAND_CNT_W(4)
    )
  u_bfed_core0_nllm_l2ifu_ibp_idle (
  .i_ibp_idle            (bfed_core0_nllm_l2ifu_ibp_idle),

  .i_ibp_cmd_chnl_valid  (bfed_core0_nllm_l2ifu_ibp_cmd_valid),
  .i_ibp_cmd_chnl_accept (bfed_core0_nllm_l2ifu_ibp_cmd_accept),
  .i_ibp_cmd_chnl_read   (bfed_core0_nllm_l2ifu_ibp_cmd_read),

  .i_ibp_rd_chnl_valid   (bfed_core0_nllm_l2ifu_ibp_rd_chnl_valid),
  .i_ibp_rd_chnl_accept  (bfed_core0_nllm_l2ifu_ibp_rd_accept),
  .i_ibp_rd_chnl_last    (bfed_core0_nllm_l2ifu_ibp_rd_last),

  .i_ibp_wrsp_chnl_valid (bfed_core0_nllm_l2ifu_ibp_wrsp_chnl_valid),
  .i_ibp_wrsp_chnl_accept(bfed_core0_nllm_l2ifu_ibp_wr_resp_accept),
  .clk        (clk),
  .nmi_restart_r (nmi_restart_r ),
  .rst_a      (rst_a)
  );

  wire bfed_lq_wq_ibp_rd_chnl_valid = bfed_lq_wq_ibp_rd_valid | bfed_lq_wq_ibp_rd_excl_ok | bfed_lq_wq_ibp_err_rd;
  wire bfed_lq_wq_ibp_wrsp_chnl_valid = bfed_lq_wq_ibp_wr_done | bfed_lq_wq_ibp_wr_excl_done | bfed_lq_wq_ibp_err_wr;
  wire bfed_lq_wq_ibp_idle;
  npuarc_biu_busb_ibp_idle
  #(
   .OUTSTAND_NUM  (16),
   .OUTSTAND_CNT_W(4)
    )
  u_bfed_lq_wq_ibp_idle (
  .i_ibp_idle            (bfed_lq_wq_ibp_idle),

  .i_ibp_cmd_chnl_valid  (bfed_lq_wq_ibp_cmd_valid),
  .i_ibp_cmd_chnl_accept (bfed_lq_wq_ibp_cmd_accept),
  .i_ibp_cmd_chnl_read   (bfed_lq_wq_ibp_cmd_read),

  .i_ibp_rd_chnl_valid   (bfed_lq_wq_ibp_rd_chnl_valid),
  .i_ibp_rd_chnl_accept  (bfed_lq_wq_ibp_rd_accept),
  .i_ibp_rd_chnl_last    (bfed_lq_wq_ibp_rd_last),

  .i_ibp_wrsp_chnl_valid (bfed_lq_wq_ibp_wrsp_chnl_valid),
  .i_ibp_wrsp_chnl_accept(bfed_lq_wq_ibp_wr_resp_accept),
  .clk        (clk),
  .nmi_restart_r (nmi_restart_r ),
  .rst_a      (rst_a)
  );

  wire bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl_valid = bfed_dmu_rbu_dmu_wbu_ibp_rd_valid | bfed_dmu_rbu_dmu_wbu_ibp_rd_excl_ok | bfed_dmu_rbu_dmu_wbu_ibp_err_rd;
  wire bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl_valid = bfed_dmu_rbu_dmu_wbu_ibp_wr_done | bfed_dmu_rbu_dmu_wbu_ibp_wr_excl_done | bfed_dmu_rbu_dmu_wbu_ibp_err_wr;
  wire bfed_dmu_rbu_dmu_wbu_ibp_idle;
  npuarc_biu_busb_ibp_idle
  #(
   .OUTSTAND_NUM  (16),
   .OUTSTAND_CNT_W(4)
    )
  u_bfed_dmu_rbu_dmu_wbu_ibp_idle (
  .i_ibp_idle            (bfed_dmu_rbu_dmu_wbu_ibp_idle),

  .i_ibp_cmd_chnl_valid  (bfed_dmu_rbu_dmu_wbu_ibp_cmd_valid),
  .i_ibp_cmd_chnl_accept (bfed_dmu_rbu_dmu_wbu_ibp_cmd_accept),
  .i_ibp_cmd_chnl_read   (bfed_dmu_rbu_dmu_wbu_ibp_cmd_read),

  .i_ibp_rd_chnl_valid   (bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl_valid),
  .i_ibp_rd_chnl_accept  (bfed_dmu_rbu_dmu_wbu_ibp_rd_accept),
  .i_ibp_rd_chnl_last    (bfed_dmu_rbu_dmu_wbu_ibp_rd_last),

  .i_ibp_wrsp_chnl_valid (bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl_valid),
  .i_ibp_wrsp_chnl_accept(bfed_dmu_rbu_dmu_wbu_ibp_wr_resp_accept),
  .clk        (clk),
  .nmi_restart_r (nmi_restart_r ),
  .rst_a      (rst_a)
  );


  wire biu_biu_cbu_any_ibp_in = 1'b0
           | bfed_core0_nllm_l2ifu_ibp_cmd_valid
           | bfed_lq_wq_ibp_cmd_valid
           | bfed_dmu_rbu_dmu_wbu_ibp_cmd_valid
           ;

  wire biu_biu_cbu_ibp_idle = 1'b1
           & bfed_core0_nllm_l2ifu_ibp_idle
           & bfed_lq_wq_ibp_idle
           & bfed_dmu_rbu_dmu_wbu_ibp_idle
           ;

  wire biu_biu_cbu_clk_en =    biu_biu_cbu_any_ibp_in
                                 | (~biu_biu_cbu_ibp_idle);

  npuarc_biu_clk_ctrl u_biu_biu_cbu_clkctrl (
    .clk_gated  (clk_gated_biu_cbu),
    .nmi_restart_r  (nmi_restart_r),
    .clkctrl_en (biu_biu_cbu_clk_en),
    .clk        (clk  ),
    .rst_a      (rst_a)
    );















// leda G_521_2_B on
endmodule // biu_busb_clk_ctrl


