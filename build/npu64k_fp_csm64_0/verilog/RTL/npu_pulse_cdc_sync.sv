/*
 * Copyright (C) 2021-2023 Synopsys, Inc. All rights reserved.
 *
 * SYNOPSYS CONFIDENTIAL - This is an unpublished, confidential, and
 * proprietary work of Synopsys, Inc., and may be subject to patent,
 * copyright, trade secret, and other legal or contractual protection.
 * This work may be used only pursuant to the terms and conditions of a
 * written license agreement with Synopsys, Inc. All other use, reproduction,
 * distribution, or disclosure of this work is strictly prohibited.
 *
 * The entire notice above must be reproduced on all authorized copies.
 */

//----------------------------------------------------------------------------
// Dual Clock Pulse Synchronizer
//----------------------------------------------------------------------------

`include "npu_defines.v"

module npu_pulse_cdc_sync
  #(
  parameter int TMR_CDC = 0,    
  parameter int SYNC_FF_LEVELS = 2      // Allowed values: 0~4
  )
  (
  input  logic  clk_s,      // source domain clk
  input  logic  rst_s,      // source domain async reset
  input  logic  clk_d,      // destination domain clk
  input  logic  rst_d,      // destination domain async reset
  input  logic  test_mode,
  input  logic  din,        // async input
  output logic  dout        // synchronized output
  );
  logic rst_s_sync_s2d;
  logic rst_d_sync_d2s;
  logic rst_s_sync;
  logic rst_d_sync;
  logic rst_s_tmp;
  logic rst_d_tmp;
  
  npu_reset_ctrl 
  u_sync_rst_d
  (
    .clk        ( clk_d     ),
    .rst_a      ( rst_d     ),
    .test_mode  ( test_mode ),
    .rst        ( rst_d_sync   )
  );

  npu_reset_ctrl 
  u_sync_rst_s
  (
    .clk        ( clk_s     ),
    .rst_a      ( rst_s     ),
    .test_mode  ( test_mode ),
    .rst        ( rst_s_sync   )
  );

  npu_reset_ctrl 
  u_sync_rst_s2d
  (
    .clk        ( clk_d     ),
    .rst_a      ( rst_s     ),
    .test_mode  ( test_mode ),
    .rst        ( rst_s_sync_s2d   )
  );


  npu_reset_ctrl 
  u_sync_rst_d2s
  (
    .clk        ( clk_s     ),
    .rst_a      ( rst_d     ),
    .test_mode  ( test_mode ),
    .rst        ( rst_d_sync_d2s   )
  );

  assign rst_s_tmp = rst_s_sync | rst_d_sync_d2s;
  assign rst_d_tmp = rst_d_sync | rst_s_sync_s2d;
  // Use CDC Sync from npu_DWbb - may be replaced with
  // specialized cells during synthesis
  npu_DWbb_bcm22_atv #(
  .REG_EVENT    (1),
  .F_SYNC_TYPE  (SYNC_FF_LEVELS),
  .VERIF_EN     (0),
  .PULSE_MODE   (0),
  .SVA_TYPE     (0),
  .TMR_CDC      (TMR_CDC)
  ) u_cdc_sync_pulse (
  .clk_s        (clk_s),
  .rst_s_n      (~rst_s_tmp),
  .event_s      (din),
  .clk_d        (clk_d),
  .rst_d_n      (~rst_d_tmp),
  .event_d      (dout)
  );

endmodule
