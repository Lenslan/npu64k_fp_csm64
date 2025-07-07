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


// APB async bridge

`include "npu_apb_macros.svh"

module npu_apb_bridge
#(
  parameter int ADDR_WIDTH   = 32,  // apb address width
  parameter int DATA_WIDTH   = 32   // apb data width
)(
  input logic iclk,            // primary side APB clock
  input logic irst_a,          // primary side async reset
  input logic tclk,            // secondary side APB clock
  input logic trst_a,          // secondary side async reset
  input logic tgt_pwr_dwn_a,   // target is power-down
  input logic test_mode,       // test mode enable
  `APBSLV(ADDR_WIDTH,DATA_WIDTH,ini_),
  `APBMST(ADDR_WIDTH,DATA_WIDTH,tgt_)
  );
  // async interface signals
  `APBASYNCWIRES(ADDR_WIDTH,DATA_WIDTH,brg_);


  //
  // primary side
  //
  npu_apb_bridge_ini
  #(
    .ADDR_WIDTH ( ADDR_WIDTH ),
    .DATA_WIDTH ( DATA_WIDTH )
  )
  u_apb_ini_inst
  (
  .pclk          ( iclk                 ),
  .rst_a         ( irst_a               ),
  .tgt_pwr_dwn_a ( tgt_pwr_dwn_a        ),
  .test_mode     ( test_mode            ),
  `APBINST(ini_,ini_),
  `APBASYNCINST(brg_,brg_)
  );

  
  //
  // secondary side
  //
  npu_apb_bridge_tgt
  #(
    .ADDR_WIDTH ( ADDR_WIDTH ),
    .DATA_WIDTH ( DATA_WIDTH )
  )
  u_apb_tgt_inst
  (
  .pclk          ( tclk                 ),
  .rst_a         ( trst_a               ),
  .test_mode     ( test_mode            ),
  `APBASYNCINST(brg_,brg_),
  `APBINST(tgt_,tgt_)
  );

endmodule : npu_apb_bridge
