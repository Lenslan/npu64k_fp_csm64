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

// spyglass disable_block Clock_info03a
// SMD: clock net unconstrained
// SJ: no need to constrain
module npuarc_biu_bus_bridge
// leda G_521_2_B off
// LMD: Use lowercase letters for all signal reg, net and port names
// LJ: Pfx may include the uppercase, so disable the lint checking rule
  (
  // clock enable signal to control the 1:N clock ratios
  // spyglass disable_block W240
  // SMD: Input pin is declared but not read
  // SJ: not used in this config, do not care this wrn
  input                                mbus_clk_en,
  // spyglass enable_block W240





// leda NTL_CON13C off
// LMD: non driving internal net
// LJ: Some signals bit field are indeed no driven
// leda NTL_CON37 off
// LMD: Signal/Net must read from the input port in module
// LJ: Some signals bit field are indeed not read and used


  input                                   bfed_ifu_merg_ibp_cmd_valid,
  output                                  bfed_ifu_merg_ibp_cmd_accept,
  input                                   bfed_ifu_merg_ibp_cmd_read,
  input   [40                -1:0]       bfed_ifu_merg_ibp_cmd_addr,
  input                                   bfed_ifu_merg_ibp_cmd_wrap,
  input   [3-1:0]       bfed_ifu_merg_ibp_cmd_data_size,
  input   [4-1:0]       bfed_ifu_merg_ibp_cmd_burst_size,
  input   [2-1:0]       bfed_ifu_merg_ibp_cmd_prot,
  input   [4-1:0]       bfed_ifu_merg_ibp_cmd_cache,
  input                                   bfed_ifu_merg_ibp_cmd_lock,
  input                                   bfed_ifu_merg_ibp_cmd_excl,

  output                                  bfed_ifu_merg_ibp_rd_valid,
  output                                  bfed_ifu_merg_ibp_rd_excl_ok,
  input                                   bfed_ifu_merg_ibp_rd_accept,
  output                                  bfed_ifu_merg_ibp_err_rd,
  output  [64               -1:0]        bfed_ifu_merg_ibp_rd_data,
  output                                  bfed_ifu_merg_ibp_rd_last,

  input                                   bfed_ifu_merg_ibp_wr_valid,
  output                                  bfed_ifu_merg_ibp_wr_accept,
  input   [64               -1:0]        bfed_ifu_merg_ibp_wr_data,
  input   [8  -1:0]                    bfed_ifu_merg_ibp_wr_mask,
  input                                   bfed_ifu_merg_ibp_wr_last,

  output                                  bfed_ifu_merg_ibp_wr_done,
  output                                  bfed_ifu_merg_ibp_wr_excl_done,
  output                                  bfed_ifu_merg_ibp_err_wr,
  input                                   bfed_ifu_merg_ibp_wr_resp_accept,



  input                                   bfed_lq_wq_ibp_cmd_valid,
  output                                  bfed_lq_wq_ibp_cmd_accept,
  input                                   bfed_lq_wq_ibp_cmd_read,
  input   [40                -1:0]       bfed_lq_wq_ibp_cmd_addr,
  input                                   bfed_lq_wq_ibp_cmd_wrap,
  input   [3-1:0]       bfed_lq_wq_ibp_cmd_data_size,
  input   [4-1:0]       bfed_lq_wq_ibp_cmd_burst_size,
  input   [2-1:0]       bfed_lq_wq_ibp_cmd_prot,
  input   [4-1:0]       bfed_lq_wq_ibp_cmd_cache,
  input                                   bfed_lq_wq_ibp_cmd_lock,
  input                                   bfed_lq_wq_ibp_cmd_excl,

  output                                  bfed_lq_wq_ibp_rd_valid,
  output                                  bfed_lq_wq_ibp_rd_excl_ok,
  input                                   bfed_lq_wq_ibp_rd_accept,
  output                                  bfed_lq_wq_ibp_err_rd,
  output  [64               -1:0]        bfed_lq_wq_ibp_rd_data,
  output                                  bfed_lq_wq_ibp_rd_last,

  input                                   bfed_lq_wq_ibp_wr_valid,
  output                                  bfed_lq_wq_ibp_wr_accept,
  input   [64               -1:0]        bfed_lq_wq_ibp_wr_data,
  input   [8  -1:0]                    bfed_lq_wq_ibp_wr_mask,
  input                                   bfed_lq_wq_ibp_wr_last,

  output                                  bfed_lq_wq_ibp_wr_done,
  output                                  bfed_lq_wq_ibp_wr_excl_done,
  output                                  bfed_lq_wq_ibp_err_wr,
  input                                   bfed_lq_wq_ibp_wr_resp_accept,



  input                                   bfed_dmu_rbu_dmu_wbu_ibp_cmd_valid,
  output                                  bfed_dmu_rbu_dmu_wbu_ibp_cmd_accept,
  input                                   bfed_dmu_rbu_dmu_wbu_ibp_cmd_read,
  input   [40                -1:0]       bfed_dmu_rbu_dmu_wbu_ibp_cmd_addr,
  input                                   bfed_dmu_rbu_dmu_wbu_ibp_cmd_wrap,
  input   [3-1:0]       bfed_dmu_rbu_dmu_wbu_ibp_cmd_data_size,
  input   [4-1:0]       bfed_dmu_rbu_dmu_wbu_ibp_cmd_burst_size,
  input   [2-1:0]       bfed_dmu_rbu_dmu_wbu_ibp_cmd_prot,
  input   [4-1:0]       bfed_dmu_rbu_dmu_wbu_ibp_cmd_cache,
  input                                   bfed_dmu_rbu_dmu_wbu_ibp_cmd_lock,
  input                                   bfed_dmu_rbu_dmu_wbu_ibp_cmd_excl,

  output                                  bfed_dmu_rbu_dmu_wbu_ibp_rd_valid,
  output                                  bfed_dmu_rbu_dmu_wbu_ibp_rd_excl_ok,
  input                                   bfed_dmu_rbu_dmu_wbu_ibp_rd_accept,
  output                                  bfed_dmu_rbu_dmu_wbu_ibp_err_rd,
  output  [128               -1:0]        bfed_dmu_rbu_dmu_wbu_ibp_rd_data,
  output                                  bfed_dmu_rbu_dmu_wbu_ibp_rd_last,

  input                                   bfed_dmu_rbu_dmu_wbu_ibp_wr_valid,
  output                                  bfed_dmu_rbu_dmu_wbu_ibp_wr_accept,
  input   [128               -1:0]        bfed_dmu_rbu_dmu_wbu_ibp_wr_data,
  input   [16  -1:0]                    bfed_dmu_rbu_dmu_wbu_ibp_wr_mask,
  input                                   bfed_dmu_rbu_dmu_wbu_ibp_wr_last,

  output                                  bfed_dmu_rbu_dmu_wbu_ibp_wr_done,
  output                                  bfed_dmu_rbu_dmu_wbu_ibp_wr_excl_done,
  output                                  bfed_dmu_rbu_dmu_wbu_ibp_err_wr,
  input                                   bfed_dmu_rbu_dmu_wbu_ibp_wr_resp_accept,



  output                                  cbu_axi_arvalid,
  input                                   cbu_axi_arready,
  output  [4              -1:0]       cbu_axi_arid,
  output  [40                -1:0]       cbu_axi_araddr,
  output  [2-1:0]       cbu_axi_arburst,
  output  [4-1:0]       cbu_axi_arlen,
  output  [3-1:0]       cbu_axi_arsize,
  output  [4-1:0]       cbu_axi_arcache,
  output  [3-1:0]       cbu_axi_arprot,
  output  [2-1:0]       cbu_axi_arlock,

  input                                   cbu_axi_rvalid,
  output                                  cbu_axi_rready,
  input   [4              -1:0]       cbu_axi_rid,
  input   [64                -1:0]       cbu_axi_rdata,
  input   [2-1:0]       cbu_axi_rresp,
  input                                   cbu_axi_rlast,

  output                                  cbu_axi_awvalid,
  input                                   cbu_axi_awready,
  output  [4              -1:0]       cbu_axi_awid,
  output  [40            -1:0]           cbu_axi_awaddr,
  output  [2-1:0]       cbu_axi_awburst,
  output  [4-1:0]       cbu_axi_awlen,
  output  [3-1:0]       cbu_axi_awsize,
  output  [4-1:0]       cbu_axi_awcache,
  output  [3-1:0]       cbu_axi_awprot,
  output  [2-1:0]       cbu_axi_awlock,

  output  [4              -1:0]       cbu_axi_wid,
  output                                  cbu_axi_wvalid,
  input                                   cbu_axi_wready,
  output  [64              -1:0]         cbu_axi_wdata,
  output  [(64          /8)-1:0]         cbu_axi_wstrb,
  output                                  cbu_axi_wlast,

  input                                   cbu_axi_bvalid,
  output                                  cbu_axi_bready,
  input   [4              -1:0]       cbu_axi_bid,
  input   [2-1:0]       cbu_axi_bresp,





// leda NTL_CON37 on
// leda NTL_CON13C on
  input rst_a     ,
  input nmi_restart_r     ,
  input clk
);




  wire clk_gated_biu_cbu;





  wire clk_gated_biu_l2ifu = clk_gated_biu_cbu;



  wire                                  bfed_core0_nllm_l2ifu_ibp_cmd_valid;
  wire                                  bfed_core0_nllm_l2ifu_ibp_cmd_accept;
  wire                                  bfed_core0_nllm_l2ifu_ibp_cmd_read;
  wire  [40                -1:0]       bfed_core0_nllm_l2ifu_ibp_cmd_addr;
  wire                                  bfed_core0_nllm_l2ifu_ibp_cmd_wrap;
  wire  [3-1:0]       bfed_core0_nllm_l2ifu_ibp_cmd_data_size;
  wire  [4-1:0]       bfed_core0_nllm_l2ifu_ibp_cmd_burst_size;
  wire  [2-1:0]       bfed_core0_nllm_l2ifu_ibp_cmd_prot;
  wire  [4-1:0]       bfed_core0_nllm_l2ifu_ibp_cmd_cache;
  wire                                  bfed_core0_nllm_l2ifu_ibp_cmd_lock;
  wire                                  bfed_core0_nllm_l2ifu_ibp_cmd_excl;

  wire                                  bfed_core0_nllm_l2ifu_ibp_rd_valid;
  wire                                  bfed_core0_nllm_l2ifu_ibp_rd_excl_ok;
  wire                                  bfed_core0_nllm_l2ifu_ibp_rd_accept;
  wire                                  bfed_core0_nllm_l2ifu_ibp_err_rd;
  wire  [64               -1:0]        bfed_core0_nllm_l2ifu_ibp_rd_data;
  wire                                  bfed_core0_nllm_l2ifu_ibp_rd_last;

  wire                                  bfed_core0_nllm_l2ifu_ibp_wr_valid;
  wire                                  bfed_core0_nllm_l2ifu_ibp_wr_accept;
  wire  [64               -1:0]        bfed_core0_nllm_l2ifu_ibp_wr_data;
  wire  [8  -1:0]                    bfed_core0_nllm_l2ifu_ibp_wr_mask;
  wire                                  bfed_core0_nllm_l2ifu_ibp_wr_last;

  wire                                  bfed_core0_nllm_l2ifu_ibp_wr_done;
  wire                                  bfed_core0_nllm_l2ifu_ibp_wr_excl_done;
  wire                                  bfed_core0_nllm_l2ifu_ibp_err_wr;
  wire                                  bfed_core0_nllm_l2ifu_ibp_wr_resp_accept;


npuarc_biu_l2ifu_mst u_biu_l2ifu_mst
   (






  .bfed_ifu_merg_ibp_cmd_valid             (bfed_ifu_merg_ibp_cmd_valid),
  .bfed_ifu_merg_ibp_cmd_accept            (bfed_ifu_merg_ibp_cmd_accept),
  .bfed_ifu_merg_ibp_cmd_read              (bfed_ifu_merg_ibp_cmd_read),
  .bfed_ifu_merg_ibp_cmd_addr              (bfed_ifu_merg_ibp_cmd_addr),
  .bfed_ifu_merg_ibp_cmd_wrap              (bfed_ifu_merg_ibp_cmd_wrap),
  .bfed_ifu_merg_ibp_cmd_data_size         (bfed_ifu_merg_ibp_cmd_data_size),
  .bfed_ifu_merg_ibp_cmd_burst_size        (bfed_ifu_merg_ibp_cmd_burst_size),
  .bfed_ifu_merg_ibp_cmd_prot              (bfed_ifu_merg_ibp_cmd_prot),
  .bfed_ifu_merg_ibp_cmd_cache             (bfed_ifu_merg_ibp_cmd_cache),
  .bfed_ifu_merg_ibp_cmd_lock              (bfed_ifu_merg_ibp_cmd_lock),
  .bfed_ifu_merg_ibp_cmd_excl              (bfed_ifu_merg_ibp_cmd_excl),

  .bfed_ifu_merg_ibp_rd_valid              (bfed_ifu_merg_ibp_rd_valid),
  .bfed_ifu_merg_ibp_rd_excl_ok            (bfed_ifu_merg_ibp_rd_excl_ok),
  .bfed_ifu_merg_ibp_rd_accept             (bfed_ifu_merg_ibp_rd_accept),
  .bfed_ifu_merg_ibp_err_rd                (bfed_ifu_merg_ibp_err_rd),
  .bfed_ifu_merg_ibp_rd_data               (bfed_ifu_merg_ibp_rd_data),
  .bfed_ifu_merg_ibp_rd_last               (bfed_ifu_merg_ibp_rd_last),

  .bfed_ifu_merg_ibp_wr_valid              (bfed_ifu_merg_ibp_wr_valid),
  .bfed_ifu_merg_ibp_wr_accept             (bfed_ifu_merg_ibp_wr_accept),
  .bfed_ifu_merg_ibp_wr_data               (bfed_ifu_merg_ibp_wr_data),
  .bfed_ifu_merg_ibp_wr_mask               (bfed_ifu_merg_ibp_wr_mask),
  .bfed_ifu_merg_ibp_wr_last               (bfed_ifu_merg_ibp_wr_last),

  .bfed_ifu_merg_ibp_wr_done               (bfed_ifu_merg_ibp_wr_done),
  .bfed_ifu_merg_ibp_wr_excl_done          (bfed_ifu_merg_ibp_wr_excl_done),
  .bfed_ifu_merg_ibp_err_wr                (bfed_ifu_merg_ibp_err_wr),
  .bfed_ifu_merg_ibp_wr_resp_accept        (bfed_ifu_merg_ibp_wr_resp_accept),


  .bfed_core0_nllm_l2ifu_ibp_cmd_valid             (bfed_core0_nllm_l2ifu_ibp_cmd_valid),
  .bfed_core0_nllm_l2ifu_ibp_cmd_accept            (bfed_core0_nllm_l2ifu_ibp_cmd_accept),
  .bfed_core0_nllm_l2ifu_ibp_cmd_read              (bfed_core0_nllm_l2ifu_ibp_cmd_read),
  .bfed_core0_nllm_l2ifu_ibp_cmd_addr              (bfed_core0_nllm_l2ifu_ibp_cmd_addr),
  .bfed_core0_nllm_l2ifu_ibp_cmd_wrap              (bfed_core0_nllm_l2ifu_ibp_cmd_wrap),
  .bfed_core0_nllm_l2ifu_ibp_cmd_data_size         (bfed_core0_nllm_l2ifu_ibp_cmd_data_size),
  .bfed_core0_nllm_l2ifu_ibp_cmd_burst_size        (bfed_core0_nllm_l2ifu_ibp_cmd_burst_size),
  .bfed_core0_nllm_l2ifu_ibp_cmd_prot              (bfed_core0_nllm_l2ifu_ibp_cmd_prot),
  .bfed_core0_nllm_l2ifu_ibp_cmd_cache             (bfed_core0_nllm_l2ifu_ibp_cmd_cache),
  .bfed_core0_nllm_l2ifu_ibp_cmd_lock              (bfed_core0_nllm_l2ifu_ibp_cmd_lock),
  .bfed_core0_nllm_l2ifu_ibp_cmd_excl              (bfed_core0_nllm_l2ifu_ibp_cmd_excl),

  .bfed_core0_nllm_l2ifu_ibp_rd_valid              (bfed_core0_nllm_l2ifu_ibp_rd_valid),
  .bfed_core0_nllm_l2ifu_ibp_rd_excl_ok            (bfed_core0_nllm_l2ifu_ibp_rd_excl_ok),
  .bfed_core0_nllm_l2ifu_ibp_rd_accept             (bfed_core0_nllm_l2ifu_ibp_rd_accept),
  .bfed_core0_nllm_l2ifu_ibp_err_rd                (bfed_core0_nllm_l2ifu_ibp_err_rd),
  .bfed_core0_nllm_l2ifu_ibp_rd_data               (bfed_core0_nllm_l2ifu_ibp_rd_data),
  .bfed_core0_nllm_l2ifu_ibp_rd_last               (bfed_core0_nllm_l2ifu_ibp_rd_last),

  .bfed_core0_nllm_l2ifu_ibp_wr_valid              (bfed_core0_nllm_l2ifu_ibp_wr_valid),
  .bfed_core0_nllm_l2ifu_ibp_wr_accept             (bfed_core0_nllm_l2ifu_ibp_wr_accept),
  .bfed_core0_nllm_l2ifu_ibp_wr_data               (bfed_core0_nllm_l2ifu_ibp_wr_data),
  .bfed_core0_nllm_l2ifu_ibp_wr_mask               (bfed_core0_nllm_l2ifu_ibp_wr_mask),
  .bfed_core0_nllm_l2ifu_ibp_wr_last               (bfed_core0_nllm_l2ifu_ibp_wr_last),

  .bfed_core0_nllm_l2ifu_ibp_wr_done               (bfed_core0_nllm_l2ifu_ibp_wr_done),
  .bfed_core0_nllm_l2ifu_ibp_wr_excl_done          (bfed_core0_nllm_l2ifu_ibp_wr_excl_done),
  .bfed_core0_nllm_l2ifu_ibp_err_wr                (bfed_core0_nllm_l2ifu_ibp_err_wr),
  .bfed_core0_nllm_l2ifu_ibp_wr_resp_accept        (bfed_core0_nllm_l2ifu_ibp_wr_resp_accept),
   .clk                                      (clk_gated_biu_l2ifu),
   .nmi_restart_r (nmi_restart_r ),
   .rst_a                                    (rst_a      )
 );

 ///////////////////////////////////////////////////////////
 //                                                       //
 // protocol conversion                                   //
 // standard bus --> internal IBP bus                     //
 //                                                       //
 ///////////////////////////////////////////////////////////



npuarc_biu_busb_clk_ctrl u_biu_busb_clk_ctrl
  (




  .clk_gated_biu_cbu(clk_gated_biu_cbu),

  .bfed_core0_nllm_l2ifu_ibp_cmd_valid       (bfed_core0_nllm_l2ifu_ibp_cmd_valid       ),
  .bfed_core0_nllm_l2ifu_ibp_cmd_accept      (bfed_core0_nllm_l2ifu_ibp_cmd_accept      ),
  .bfed_core0_nllm_l2ifu_ibp_cmd_read        (bfed_core0_nllm_l2ifu_ibp_cmd_read        ),

  .bfed_core0_nllm_l2ifu_ibp_rd_valid        (bfed_core0_nllm_l2ifu_ibp_rd_valid        ),
  .bfed_core0_nllm_l2ifu_ibp_rd_excl_ok      (bfed_core0_nllm_l2ifu_ibp_rd_excl_ok      ),
  .bfed_core0_nllm_l2ifu_ibp_rd_accept       (bfed_core0_nllm_l2ifu_ibp_rd_accept       ),
  .bfed_core0_nllm_l2ifu_ibp_err_rd          (bfed_core0_nllm_l2ifu_ibp_err_rd          ),
  .bfed_core0_nllm_l2ifu_ibp_rd_last         (bfed_core0_nllm_l2ifu_ibp_rd_last         ),

  .bfed_core0_nllm_l2ifu_ibp_wr_done         (bfed_core0_nllm_l2ifu_ibp_wr_done         ),
  .bfed_core0_nllm_l2ifu_ibp_wr_excl_done    (bfed_core0_nllm_l2ifu_ibp_wr_excl_done    ),
  .bfed_core0_nllm_l2ifu_ibp_err_wr          (bfed_core0_nllm_l2ifu_ibp_err_wr          ),
  .bfed_core0_nllm_l2ifu_ibp_wr_resp_accept  (bfed_core0_nllm_l2ifu_ibp_wr_resp_accept  ),
  .bfed_lq_wq_ibp_cmd_valid       (bfed_lq_wq_ibp_cmd_valid       ),
  .bfed_lq_wq_ibp_cmd_accept      (bfed_lq_wq_ibp_cmd_accept      ),
  .bfed_lq_wq_ibp_cmd_read        (bfed_lq_wq_ibp_cmd_read        ),

  .bfed_lq_wq_ibp_rd_valid        (bfed_lq_wq_ibp_rd_valid        ),
  .bfed_lq_wq_ibp_rd_excl_ok      (bfed_lq_wq_ibp_rd_excl_ok      ),
  .bfed_lq_wq_ibp_rd_accept       (bfed_lq_wq_ibp_rd_accept       ),
  .bfed_lq_wq_ibp_err_rd          (bfed_lq_wq_ibp_err_rd          ),
  .bfed_lq_wq_ibp_rd_last         (bfed_lq_wq_ibp_rd_last         ),

  .bfed_lq_wq_ibp_wr_done         (bfed_lq_wq_ibp_wr_done         ),
  .bfed_lq_wq_ibp_wr_excl_done    (bfed_lq_wq_ibp_wr_excl_done    ),
  .bfed_lq_wq_ibp_err_wr          (bfed_lq_wq_ibp_err_wr          ),
  .bfed_lq_wq_ibp_wr_resp_accept  (bfed_lq_wq_ibp_wr_resp_accept  ),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_valid       (bfed_dmu_rbu_dmu_wbu_ibp_cmd_valid       ),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_accept      (bfed_dmu_rbu_dmu_wbu_ibp_cmd_accept      ),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_read        (bfed_dmu_rbu_dmu_wbu_ibp_cmd_read        ),

  .bfed_dmu_rbu_dmu_wbu_ibp_rd_valid        (bfed_dmu_rbu_dmu_wbu_ibp_rd_valid        ),
  .bfed_dmu_rbu_dmu_wbu_ibp_rd_excl_ok      (bfed_dmu_rbu_dmu_wbu_ibp_rd_excl_ok      ),
  .bfed_dmu_rbu_dmu_wbu_ibp_rd_accept       (bfed_dmu_rbu_dmu_wbu_ibp_rd_accept       ),
  .bfed_dmu_rbu_dmu_wbu_ibp_err_rd          (bfed_dmu_rbu_dmu_wbu_ibp_err_rd          ),
  .bfed_dmu_rbu_dmu_wbu_ibp_rd_last         (bfed_dmu_rbu_dmu_wbu_ibp_rd_last         ),

  .bfed_dmu_rbu_dmu_wbu_ibp_wr_done         (bfed_dmu_rbu_dmu_wbu_ibp_wr_done         ),
  .bfed_dmu_rbu_dmu_wbu_ibp_wr_excl_done    (bfed_dmu_rbu_dmu_wbu_ibp_wr_excl_done    ),
  .bfed_dmu_rbu_dmu_wbu_ibp_err_wr          (bfed_dmu_rbu_dmu_wbu_ibp_err_wr          ),
  .bfed_dmu_rbu_dmu_wbu_ibp_wr_resp_accept  (bfed_dmu_rbu_dmu_wbu_ibp_wr_resp_accept  ),





  .clk     (clk        ),
  .nmi_restart_r (nmi_restart_r ),
  .rst_a   (rst_a      )
);




npuarc_biu_cbu_mst u_biu_cbu_mst
   (





  .bfed_core0_nllm_l2ifu_ibp_cmd_valid             (bfed_core0_nllm_l2ifu_ibp_cmd_valid),
  .bfed_core0_nllm_l2ifu_ibp_cmd_accept            (bfed_core0_nllm_l2ifu_ibp_cmd_accept),
  .bfed_core0_nllm_l2ifu_ibp_cmd_read              (bfed_core0_nllm_l2ifu_ibp_cmd_read),
  .bfed_core0_nllm_l2ifu_ibp_cmd_addr              (bfed_core0_nllm_l2ifu_ibp_cmd_addr),
  .bfed_core0_nllm_l2ifu_ibp_cmd_wrap              (bfed_core0_nllm_l2ifu_ibp_cmd_wrap),
  .bfed_core0_nllm_l2ifu_ibp_cmd_data_size         (bfed_core0_nllm_l2ifu_ibp_cmd_data_size),
  .bfed_core0_nllm_l2ifu_ibp_cmd_burst_size        (bfed_core0_nllm_l2ifu_ibp_cmd_burst_size),
  .bfed_core0_nllm_l2ifu_ibp_cmd_prot              (bfed_core0_nllm_l2ifu_ibp_cmd_prot),
  .bfed_core0_nllm_l2ifu_ibp_cmd_cache             (bfed_core0_nllm_l2ifu_ibp_cmd_cache),
  .bfed_core0_nllm_l2ifu_ibp_cmd_lock              (bfed_core0_nllm_l2ifu_ibp_cmd_lock),
  .bfed_core0_nllm_l2ifu_ibp_cmd_excl              (bfed_core0_nllm_l2ifu_ibp_cmd_excl),

  .bfed_core0_nllm_l2ifu_ibp_rd_valid              (bfed_core0_nllm_l2ifu_ibp_rd_valid),
  .bfed_core0_nllm_l2ifu_ibp_rd_excl_ok            (bfed_core0_nllm_l2ifu_ibp_rd_excl_ok),
  .bfed_core0_nllm_l2ifu_ibp_rd_accept             (bfed_core0_nllm_l2ifu_ibp_rd_accept),
  .bfed_core0_nllm_l2ifu_ibp_err_rd                (bfed_core0_nllm_l2ifu_ibp_err_rd),
  .bfed_core0_nllm_l2ifu_ibp_rd_data               (bfed_core0_nllm_l2ifu_ibp_rd_data),
  .bfed_core0_nllm_l2ifu_ibp_rd_last               (bfed_core0_nllm_l2ifu_ibp_rd_last),

  .bfed_core0_nllm_l2ifu_ibp_wr_valid              (bfed_core0_nllm_l2ifu_ibp_wr_valid),
  .bfed_core0_nllm_l2ifu_ibp_wr_accept             (bfed_core0_nllm_l2ifu_ibp_wr_accept),
  .bfed_core0_nllm_l2ifu_ibp_wr_data               (bfed_core0_nllm_l2ifu_ibp_wr_data),
  .bfed_core0_nllm_l2ifu_ibp_wr_mask               (bfed_core0_nllm_l2ifu_ibp_wr_mask),
  .bfed_core0_nllm_l2ifu_ibp_wr_last               (bfed_core0_nllm_l2ifu_ibp_wr_last),

  .bfed_core0_nllm_l2ifu_ibp_wr_done               (bfed_core0_nllm_l2ifu_ibp_wr_done),
  .bfed_core0_nllm_l2ifu_ibp_wr_excl_done          (bfed_core0_nllm_l2ifu_ibp_wr_excl_done),
  .bfed_core0_nllm_l2ifu_ibp_err_wr                (bfed_core0_nllm_l2ifu_ibp_err_wr),
  .bfed_core0_nllm_l2ifu_ibp_wr_resp_accept        (bfed_core0_nllm_l2ifu_ibp_wr_resp_accept),


  .bfed_lq_wq_ibp_cmd_valid             (bfed_lq_wq_ibp_cmd_valid),
  .bfed_lq_wq_ibp_cmd_accept            (bfed_lq_wq_ibp_cmd_accept),
  .bfed_lq_wq_ibp_cmd_read              (bfed_lq_wq_ibp_cmd_read),
  .bfed_lq_wq_ibp_cmd_addr              (bfed_lq_wq_ibp_cmd_addr),
  .bfed_lq_wq_ibp_cmd_wrap              (bfed_lq_wq_ibp_cmd_wrap),
  .bfed_lq_wq_ibp_cmd_data_size         (bfed_lq_wq_ibp_cmd_data_size),
  .bfed_lq_wq_ibp_cmd_burst_size        (bfed_lq_wq_ibp_cmd_burst_size),
  .bfed_lq_wq_ibp_cmd_prot              (bfed_lq_wq_ibp_cmd_prot),
  .bfed_lq_wq_ibp_cmd_cache             (bfed_lq_wq_ibp_cmd_cache),
  .bfed_lq_wq_ibp_cmd_lock              (bfed_lq_wq_ibp_cmd_lock),
  .bfed_lq_wq_ibp_cmd_excl              (bfed_lq_wq_ibp_cmd_excl),

  .bfed_lq_wq_ibp_rd_valid              (bfed_lq_wq_ibp_rd_valid),
  .bfed_lq_wq_ibp_rd_excl_ok            (bfed_lq_wq_ibp_rd_excl_ok),
  .bfed_lq_wq_ibp_rd_accept             (bfed_lq_wq_ibp_rd_accept),
  .bfed_lq_wq_ibp_err_rd                (bfed_lq_wq_ibp_err_rd),
  .bfed_lq_wq_ibp_rd_data               (bfed_lq_wq_ibp_rd_data),
  .bfed_lq_wq_ibp_rd_last               (bfed_lq_wq_ibp_rd_last),

  .bfed_lq_wq_ibp_wr_valid              (bfed_lq_wq_ibp_wr_valid),
  .bfed_lq_wq_ibp_wr_accept             (bfed_lq_wq_ibp_wr_accept),
  .bfed_lq_wq_ibp_wr_data               (bfed_lq_wq_ibp_wr_data),
  .bfed_lq_wq_ibp_wr_mask               (bfed_lq_wq_ibp_wr_mask),
  .bfed_lq_wq_ibp_wr_last               (bfed_lq_wq_ibp_wr_last),

  .bfed_lq_wq_ibp_wr_done               (bfed_lq_wq_ibp_wr_done),
  .bfed_lq_wq_ibp_wr_excl_done          (bfed_lq_wq_ibp_wr_excl_done),
  .bfed_lq_wq_ibp_err_wr                (bfed_lq_wq_ibp_err_wr),
  .bfed_lq_wq_ibp_wr_resp_accept        (bfed_lq_wq_ibp_wr_resp_accept),


  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_valid             (bfed_dmu_rbu_dmu_wbu_ibp_cmd_valid),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_accept            (bfed_dmu_rbu_dmu_wbu_ibp_cmd_accept),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_read              (bfed_dmu_rbu_dmu_wbu_ibp_cmd_read),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_addr              (bfed_dmu_rbu_dmu_wbu_ibp_cmd_addr),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_wrap              (bfed_dmu_rbu_dmu_wbu_ibp_cmd_wrap),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_data_size         (bfed_dmu_rbu_dmu_wbu_ibp_cmd_data_size),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_burst_size        (bfed_dmu_rbu_dmu_wbu_ibp_cmd_burst_size),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_prot              (bfed_dmu_rbu_dmu_wbu_ibp_cmd_prot),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_cache             (bfed_dmu_rbu_dmu_wbu_ibp_cmd_cache),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_lock              (bfed_dmu_rbu_dmu_wbu_ibp_cmd_lock),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_excl              (bfed_dmu_rbu_dmu_wbu_ibp_cmd_excl),

  .bfed_dmu_rbu_dmu_wbu_ibp_rd_valid              (bfed_dmu_rbu_dmu_wbu_ibp_rd_valid),
  .bfed_dmu_rbu_dmu_wbu_ibp_rd_excl_ok            (bfed_dmu_rbu_dmu_wbu_ibp_rd_excl_ok),
  .bfed_dmu_rbu_dmu_wbu_ibp_rd_accept             (bfed_dmu_rbu_dmu_wbu_ibp_rd_accept),
  .bfed_dmu_rbu_dmu_wbu_ibp_err_rd                (bfed_dmu_rbu_dmu_wbu_ibp_err_rd),
  .bfed_dmu_rbu_dmu_wbu_ibp_rd_data               (bfed_dmu_rbu_dmu_wbu_ibp_rd_data),
  .bfed_dmu_rbu_dmu_wbu_ibp_rd_last               (bfed_dmu_rbu_dmu_wbu_ibp_rd_last),

  .bfed_dmu_rbu_dmu_wbu_ibp_wr_valid              (bfed_dmu_rbu_dmu_wbu_ibp_wr_valid),
  .bfed_dmu_rbu_dmu_wbu_ibp_wr_accept             (bfed_dmu_rbu_dmu_wbu_ibp_wr_accept),
  .bfed_dmu_rbu_dmu_wbu_ibp_wr_data               (bfed_dmu_rbu_dmu_wbu_ibp_wr_data),
  .bfed_dmu_rbu_dmu_wbu_ibp_wr_mask               (bfed_dmu_rbu_dmu_wbu_ibp_wr_mask),
  .bfed_dmu_rbu_dmu_wbu_ibp_wr_last               (bfed_dmu_rbu_dmu_wbu_ibp_wr_last),

  .bfed_dmu_rbu_dmu_wbu_ibp_wr_done               (bfed_dmu_rbu_dmu_wbu_ibp_wr_done),
  .bfed_dmu_rbu_dmu_wbu_ibp_wr_excl_done          (bfed_dmu_rbu_dmu_wbu_ibp_wr_excl_done),
  .bfed_dmu_rbu_dmu_wbu_ibp_err_wr                (bfed_dmu_rbu_dmu_wbu_ibp_err_wr),
  .bfed_dmu_rbu_dmu_wbu_ibp_wr_resp_accept        (bfed_dmu_rbu_dmu_wbu_ibp_wr_resp_accept),


  .cbu_axi_arvalid    (cbu_axi_arvalid),
  .cbu_axi_arready    (cbu_axi_arready),
  .cbu_axi_arid       (cbu_axi_arid   ),
  .cbu_axi_araddr     (cbu_axi_araddr ),
  .cbu_axi_arburst    (cbu_axi_arburst),
  .cbu_axi_arlen      (cbu_axi_arlen  ),
  .cbu_axi_arsize     (cbu_axi_arsize ),
  .cbu_axi_arcache    (cbu_axi_arcache),
  .cbu_axi_arprot     (cbu_axi_arprot ),
  .cbu_axi_arlock     (cbu_axi_arlock ),

  .cbu_axi_rvalid     (cbu_axi_rvalid),
  .cbu_axi_rready     (cbu_axi_rready),
  .cbu_axi_rid        (cbu_axi_rid   ),
  .cbu_axi_rdata      (cbu_axi_rdata ),
  .cbu_axi_rresp      (cbu_axi_rresp ),
  .cbu_axi_rlast      (cbu_axi_rlast ),

  .cbu_axi_awvalid    (cbu_axi_awvalid),
  .cbu_axi_awready    (cbu_axi_awready),
  .cbu_axi_awid       (cbu_axi_awid   ),
  .cbu_axi_awaddr     (cbu_axi_awaddr ),
  .cbu_axi_awburst    (cbu_axi_awburst),
  .cbu_axi_awlen      (cbu_axi_awlen  ),
  .cbu_axi_awsize     (cbu_axi_awsize ),
  .cbu_axi_awcache    (cbu_axi_awcache),
  .cbu_axi_awprot     (cbu_axi_awprot ),
  .cbu_axi_awlock     (cbu_axi_awlock ),

  .cbu_axi_wid         (cbu_axi_wid   ),
  .cbu_axi_wvalid      (cbu_axi_wvalid),
  .cbu_axi_wready      (cbu_axi_wready),
  .cbu_axi_wdata       (cbu_axi_wdata ),
  .cbu_axi_wstrb       (cbu_axi_wstrb ),
  .cbu_axi_wlast       (cbu_axi_wlast ),

  .cbu_axi_bvalid   (cbu_axi_bvalid),
  .cbu_axi_bready   (cbu_axi_bready),
  .cbu_axi_bid      (cbu_axi_bid   ),
  .cbu_axi_bresp    (cbu_axi_bresp ),


  .mbus_clk_en(mbus_clk_en),
   .clk                                      (clk_gated_biu_cbu),
   .nmi_restart_r (nmi_restart_r ),
   .rst_a                                    (rst_a      )
 );


// leda G_521_2_B on
endmodule // biu_bus_bridge

// spyglass enable_block Clock_info03a

