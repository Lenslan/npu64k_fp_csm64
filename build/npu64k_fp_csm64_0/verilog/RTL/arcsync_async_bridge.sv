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


`include "npu_defines.v"
`include "arcsync_defines.v"
`include "npu_axi_macros.svh"
`include "npu_macros.svh"


module arcsync_async_bridge
  import npu_types::*;
  #(
    parameter int AXIIDW         = 16,
    parameter int AXIDW          = 64,
    parameter int AXIAWUW        = 1,
    parameter int AXIWUW         = 1,
    parameter int AXIBUW         = 1,
    parameter int AXIARUW        = 1,
    parameter int AXIRUW         = 1,
    // FIFO depth specification
    parameter int AWFIFO_DEPTHL2 = 1,
    parameter int WFIFO_DEPTHL2  = 1,
    parameter int BFIFO_DEPTHL2  = 1,
    parameter int ARFIFO_DEPTHL2 = 1,
    parameter int RFIFO_DEPTHL2  = 1,
    parameter int CFG_INST       = 0,
    localparam PROT_WIDTH = CFG_INST ? 7 : 8,
    localparam PROT_GRNLT = CFG_INST ? 32 : 64
  )
(
   // clock and reset
   input  logic axi_slv_clk,
   input  logic axi_slv_rst_a,
   input  logic axi_mst_clk,
   input  logic axi_mst_rst_a,
   input  logic test_mode,

   input  logic                tgt_pwr_dwn_a,
   input  logic                ini_pwr_dwn_a,

   // AXI slave interface
   `AXISLV(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_slv_),

   // AXI master interface
   `AXIMST(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_mst_)


);

  logic       clk_req_a;

  `AXIASYNCWIRES(AXIIDW, AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AWFIFO_DEPTHL2,WFIFO_DEPTHL2,BFIFO_DEPTHL2,ARFIFO_DEPTHL2,RFIFO_DEPTHL2, axi_gals_);


 npu_axi_async_ini
  #(
    .AXIIDW         (AXIIDW        ),
    .AXIDW          (AXIDW         ),
    .AXIAWUW        (AXIAWUW       ),
    .AXIWUW         (AXIWUW        ),
    .AXIBUW         (AXIBUW        ),
    .AXIARUW        (AXIARUW       ),
    .AXIRUW         (AXIRUW        ),
    .AWFIFO_DEPTHL2 (AWFIFO_DEPTHL2),
    .WFIFO_DEPTHL2  (WFIFO_DEPTHL2 ),
    .BFIFO_DEPTHL2  (BFIFO_DEPTHL2 ),
    .ARFIFO_DEPTHL2 (ARFIFO_DEPTHL2),
    .RFIFO_DEPTHL2  (RFIFO_DEPTHL2 )
  )
  u_arcsync_async_ini
  (

    .tgt_pwr_dwn_a        (tgt_pwr_dwn_a        ),
    .test_mode            (test_mode            ),
    `AXIINST              (axi_slv_, axi_slv_),
    `AXIASYNCMINST        (axi_async_mst_, axi_gals_),
    .axi_slv_clk          (axi_slv_clk),
    .axi_slv_rst_a        (axi_slv_rst_a)
  );

  npu_axi_async_tgt
  #(
    .AXIIDW         (AXIIDW        ),
    .AXIDW          (AXIDW         ),
    .AXIAWUW        (AXIAWUW       ),
    .AXIWUW         (AXIWUW        ),
    .AXIBUW         (AXIBUW        ),
    .AXIARUW        (AXIARUW       ),
    .AXIRUW         (AXIRUW        ),
    .AWFIFO_DEPTHL2 (AWFIFO_DEPTHL2),
    .WFIFO_DEPTHL2  (WFIFO_DEPTHL2 ),
    .BFIFO_DEPTHL2  (BFIFO_DEPTHL2 ),
    .ARFIFO_DEPTHL2 (ARFIFO_DEPTHL2),
    .RFIFO_DEPTHL2  (RFIFO_DEPTHL2 )
  )
  u_arcsync_async_tgt
  (

    .ini_pwr_dwn_a                (ini_pwr_dwn_a         ),
    .test_mode                    (test_mode             ),
    .clk_req_a                    (clk_req_a             ),
    `AXIINST                      (axi_mst_, axi_mst_),
    `AXIASYNCSINST                (axi_async_slv_, axi_gals_),
    .axi_mst_clk                  (axi_mst_clk           ),
    .axi_mst_rst_a                (axi_mst_rst_a         )
   );

endmodule
