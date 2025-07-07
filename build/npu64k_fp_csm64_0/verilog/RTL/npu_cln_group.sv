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

// CLN group hierarchy
// vcs -sverilog -f ../../shared/RTL/npu_shared_manifest npu_cln_wrap.sv npu_cln_group.sv

`include "npu_defines.v"
`include "npu_defines.v"

`include "npu_axi_macros.svh"


module npu_cln_group
  import npu_types::*;
  #(
    parameter int NUMGRP  = 4, // number of groups, power of 2
    parameter int NUMSLC  = 4, // number of slices connected to group
    parameter int NUMSTU  = 2, // number of STU channels connected to group
    parameter int DEVIDW  = 3, // device port attributes
    parameter int LNKIDW  = 5, // link ID width = DEVIDW+clog2(NUMGRP)
    parameter int L2IDW   = 3, // L2 ID width
    parameter int CCMIDW  = 1, // CCM ID width
    parameter int NOCIDW  = 5, // NoC ID width
    parameter TOP_CFG_DECBASE_RST_VAL  = 0,
    parameter TOP_CFG_DECSIZE_RST_VAL  = 0,
    parameter TOP_CFG_DECMST_RST_VAL   = 0,
    parameter BOT_CFG_DECBASE_RST_VAL  = 0,
    parameter BOT_CFG_DECSIZE_RST_VAL  = 0,
    parameter BOT_CFG_DECMST_RST_VAL   = 0,
    parameter CCM_CFG_DECBASE_RST_VAL  = 0,
    parameter CCM_CFG_DECSIZE_RST_VAL  = 0,
    parameter CCM_CFG_DECMST_RST_VAL   = 0,
    parameter REMP_CFG_DECBASE_RST_VAL = 0,
    parameter REMP_CFG_DECSIZE_RST_VAL = 0,
    parameter REMP_CFG_DECMST_RST_VAL  = 0
  )
  (
    input      logic                          clk,
    input      logic                          rst_a,     // asynchronous reset, synchronously deasserted
    input      logic                          grp_pd_mem,   
    input      logic [1:0]                    ptidx_a,
    input      logic                          test_mode,
    output logic                              scm_dbank_ecc_irq,
   // report dbank sbe/dbe: to NPX top
    output logic                              scm_dbank_sbe,
    output logic                              scm_dbank_dbe,
    // configuration device port
    `AXISLV(1,32,1,1,1,1,1,axi_cfg_),
    // slice device ports
    `AXISLVN(NUMSLC,DEVIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_dev_slice_),
    // STU device ports
    `AXISLVN(NUMSTU,DEVIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_dev_stu_),
    // L2 device port
    `AXISLV(L2IDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_dev_l2_),

    // slice CCM ports
    `AXIMSTN(NUMSLC,CCMIDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,axi_ccm_slice_),
    // STU MMIO CCM ports
    `AXIMSTN(NUMSTU,CCMIDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,axi_ccm_stu_),
    // L2 CCM port
    `AXIMST(CCMIDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,axi_ccm_l2_),
    // egress links to other groups
    `AXIMSTN(NUMGRP-1,LNKIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_egress_),
    // ingress links from other groups
    `AXISLVN(NUMGRP-1,LNKIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_ingress_),
    // NoC port
    `AXIMST(NOCIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_noc_)

  );
  // local parameters
  localparam int CLN_IDX  = 0;
  localparam int TOP_IDX  = 1;
  localparam int BOT_IDX  = 2;
  localparam int REM_IDX  = 3;
  localparam int CCM_IDX  = 4;
  localparam int TOPNUMAP = 16;                      // number of apertures in top matrix
  localparam int BOTNUMAP = 16;                      // number of apertures in bottom matrix
  localparam int CCMNUMAP = NUMSLC+NUMSTU+1;         // number of apertures in ccmput matrix
  localparam int LNKSLC_O = 0;                       // number of slices on link to remote group (egress out)
  localparam int LNKSLC_I = 1;                       // number of slices on link to remote group (ingress in)
  localparam int BOTIDW   = LNKIDW+$clog2(NUMGRP+1); // output ID with of bottom matrix
  localparam int AXI_SLC_DEPTH = 2;                  // improve timing, change it from 1 to 2
  // local wires
  // configuration address map
  `AXIWIRES(1,32,1,1,1,1,1,axi_cfg_slc_);
  `AXICONFIGWIRES(5/*NUMAP*/,5/*NUMMST*/,cfg_amap_);
  `AXIWIRESN(5,1,32,1,1,1,1,1,axi_cfg_demux_);
  // configuration interfaces for top CLN(0), AXI(1), bottom AXI(2), CCM(3)
  // device inputs after slice
  `AXIWIRESN(NUMSLC+NUMSTU,DEVIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_dev_);
  `AXIWIRESN(NUMSLC,DEVIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,iaxi_dev_);
  `AXIWIRESN(NUMSLC,DEVIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,iaxi_dev_int_);
  `AXIWIRESN(NUMSLC,DEVIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,iaxi_dev_asg_);
  // top matrix address map
  `AXICONFIGWIRES(TOPNUMAP,NUMGRP+1,top_amap_);
  // links after top matrix
  `AXIWIRESN(NUMGRP+1,LNKIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_elnk_);
  `AXIWIRES(LNKIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_xm_);
  // bottom matrix address map
  `AXICONFIGWIRES(BOTNUMAP,`NPU_CSM_BANKS_PER_GRP+1,bot_amap_);
  // remap bridge address map
  `AXICONFIGWIRES(2/*NUMAP*/,1/*NUMMST*/,rem_amap_);
  `AXICONFIGWIRES(2/*NUMAP*/,1/*NUMMST*/,i1_rem_amap_);
  `AXICONFIGASGN(2,0,i1_rem_amap_,rem_amap_);

  // links to bottom matrix
  `AXIWIRESN(NUMGRP,LNKIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_ilnk_);
  `AXIWIRESN(NUMGRP,LNKIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,iaxi_ilnk_int_);
  `AXIWIRESN(NUMGRP,LNKIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,iaxi_ilnk_);
  `AXIWIRESN(NUMGRP,LNKIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,iaxi_ilnk_bc_);
  `AXIWIRESN(NUMGRP+1,LNKIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_ibot_);
  // links from bottom matrix
  `AXIWIRESN(`NPU_CSM_BANKS_PER_GRP+1,BOTIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_obot_);
  `AXIWIRESN(`NPU_CSM_BANKS_PER_GRP+1,BOTIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_slc_obot_);
  // CLN inputs
  `AXIWIRESN(`NPU_CSM_BANKS_PER_GRP,BOTIDW,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_cln_);
  // remap CSM interface
  `AXIWIRESN(`NPU_CSM_BANKS_PER_GRP,BOTIDW,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,int_axi_csm_l2_);
  // NoC internal
  `AXIWIRES(NOCIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_noc_int_);
  // wide CCM interface
  `AXIWIRES(CCMIDW,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_ccm_wid_);
  // narrow CCM interface
  `AXIWIRES(CCMIDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,axi_ccm_nar_);
  // narrow CCM interface after reg slice
  `AXIWIRES(CCMIDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,axi_ccm_nar_slice_);
  // ccm demux address map
  `AXICONFIGWIRES(CCMNUMAP,NUMSLC+NUMSTU+1,ccm_amap_);
  // ccm AXI
  `AXIWIRESN(NUMSTU+NUMSLC+1,CCMIDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,axi_ccm_demux_int_);
  `AXIWIRESN(NUMSTU+NUMSLC+1,CCMIDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,axi_ccm_demux_);
  `AXIWIRESN(1,CCMIDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,axi_ccm_grp_);
  logic rst_sync;
  npu_reset_ctrl
  u_rst_inst
  (
    .clk       ( clk      ),
    .rst_a     ( rst_a    ),
    .rst       ( rst_sync ),
    .test_mode ( test_mode)
  );

  
  //
  // Split the AXI configuration interface into 3*4KB apertures and AXI interfaces
  // cfg routine from L2 Group, only need detect addr[13:12] to decide the config target
  //
  // aperture 0: 0x0000 to 0x0FFF -> CLN config interface (dev0)
  // aperture 1: 0x1000 to 0x1FFF -> AXI top matrix config interface
  // aperture 2: 0x2000 to 0x2FFF -> AXI bottom matrix config interface
  // aperture 3: 0x3000 to 0x3FFF -> Remap bridge cofnig interface 


  assign cfg_amap_decbase[CLN_IDX  ] = 'h0;
  assign cfg_amap_decbase[TOP_IDX  ] = 'h1;
  assign cfg_amap_decbase[BOT_IDX  ] = 'h2;
  assign cfg_amap_decbase[REM_IDX  ] = 'h3;
  assign cfg_amap_decbase[CCM_IDX  ] = 'h10;


  assign cfg_amap_decsize[CLN_IDX  ] = 'h1f;
  assign cfg_amap_decsize[TOP_IDX  ] = 'h1f;
  assign cfg_amap_decsize[BOT_IDX  ] = 'h1f;
  assign cfg_amap_decsize[REM_IDX  ] = 'h1f;
  assign cfg_amap_decsize[CCM_IDX  ] = 'h1f;

  assign cfg_amap_decmst[CLN_IDX  ]  = unsigned'(1<<CLN_IDX);
  assign cfg_amap_decmst[TOP_IDX  ]  = unsigned'(1<<TOP_IDX);
  assign cfg_amap_decmst[BOT_IDX  ]  = unsigned'(1<<BOT_IDX);
  assign cfg_amap_decmst[REM_IDX  ]  = unsigned'(1<<REM_IDX);
  assign cfg_amap_decmst[CCM_IDX  ]  = unsigned'(1<<CCM_IDX);


  npu_axi_slice
  #(
    .AXIIDW       ( 1        ),
    .AXIDW        ( 32       ),
    .AXIAWUW      ( SLICE_MMIO_AWUW  ),
    .AXIWUW       ( SLICE_MMIO_WUW   ),
    .AXIBUW       ( SLICE_MMIO_BUW   ),
    .AXIARUW      ( SLICE_MMIO_ARUW  ),
    .AXIRUW       ( SLICE_MMIO_RUW   ),
    .NUMSLC       ( 1                ), //improve timing
    .AWFIFO_DEPTH ( 1        ),
    .WFIFO_DEPTH  ( 2        ),
    .BFIFO_DEPTH  ( 1        ),
    .ARFIFO_DEPTH ( 1        ),
    .RFIFO_DEPTH  ( 2        )
  )
  u_cfg_slc_inst
  (
    .clk   ( clk   ),
    .rst_a ( rst_sync ),
    `AXIINST(axi_slv_,axi_cfg_),
    `AXIINST(axi_mst_,axi_cfg_slc_)
  );

npu_axi_matrix
  #(
    .NUMSLV  ( 1    ),
    .NUMMST  ( 5    ),
    .NUMAP   ( 5    ),
    .AXIDW   ( 32   ),
    .AXISIDW ( 1    ),
    .AXIMIDW ( 1    ), 
    .AXIAWUW ( 1    ),
    .AXIWUW  ( 1    ),
    .AXIBUW  ( 1    ),
    .AXIARUW ( 1    ),
    .AXIRUW  ( 1    )
  )
u_cfg_mux_inst
  (
    .clk    ( clk   ),
    .rst_a  ( rst_sync ),
    .ptidx_a( 2'b00       ),
    .decslv ( '1    ),
    `AXIINST(axi_slv_,axi_cfg_slc_),
    `AXIINST(axi_mst_,axi_cfg_demux_),
    `AXICONFIGINST(cfg_amap_)
  );


  //
  // Register slices on DEV interfaces
  //
  for (genvar gs = 0; gs < NUMSLC; gs++)
  begin : slice_slc_GEN
    npu_axi_slice
    #(
      .AXIIDW       ( DEVIDW         ),
      .AXIDW        ( VSIZE*64       ),
      .AXIAWUW      ( SLICE_DMA_AWUW ),
      .AXIWUW       ( SLICE_DMA_WUW  ),
      .AXIBUW       ( SLICE_DMA_BUW  ),
      .AXIARUW      ( SLICE_DMA_ARUW ),
      .AXIRUW       ( SLICE_DMA_RUW  ),
      .NUMSLC       ( AXI_SLC_DEPTH  ), //improve timing
      .AWFIFO_DEPTH ( 1              ),
      .WFIFO_DEPTH  ( 2              ),
      .BFIFO_DEPTH  ( 1              ),
      .ARFIFO_DEPTH ( 1              ),
      .RFIFO_DEPTH  ( 2              )
    )
    u_slc_inst
    (
      .clk   ( clk   ),
      .rst_a ( rst_sync ),
      `AXIINSTM(gs,axi_slv_,axi_dev_slice_),
      `AXIINSTM(gs,axi_mst_,iaxi_dev_)
    );
  end : slice_slc_GEN

  npu_top_bc
    #(
    .NUMMST       ( NUMSLC         ),
    .AXIIDW       ( DEVIDW         ),
    .AXIDW        ( VSIZE*64       ),
    .AXIAWUW      ( SLICE_DMA_AWUW ),
    .AXIWUW       ( SLICE_DMA_WUW  ),
    .AXIBUW       ( SLICE_DMA_BUW  ),
    .AXIARUW      ( SLICE_DMA_ARUW ),
    .AXIRUW       ( SLICE_DMA_RUW  )
    )
  u_top_bdma_inst
  (
    .clk   ( clk   ),
    .rst_a ( rst_sync ),
    `AXIINST(axi_slv_,iaxi_dev_),
    `AXIINST(axi_mst_,iaxi_dev_int_)
  );

  for (genvar gs = 0; gs < NUMSLC; gs++)
  begin : slice_top_bdma_slc_GEN
    npu_axi_slice
    #(
      .AXIIDW       ( DEVIDW         ),
      .AXIDW        ( VSIZE*64       ),
      .AXIAWUW      ( SLICE_DMA_AWUW ),
      .AXIWUW       ( SLICE_DMA_WUW  ),
      .AXIBUW       ( SLICE_DMA_BUW  ),
      .AXIARUW      ( SLICE_DMA_ARUW ),
      .AXIRUW       ( SLICE_DMA_RUW  ),
      .NUMSLC       ( AXI_SLC_DEPTH  ), //improve timing
      .AWFIFO_DEPTH ( 1              ),
      .WFIFO_DEPTH  ( 2              ),
      .BFIFO_DEPTH  ( 1              ),
      .ARFIFO_DEPTH ( 1              ),
      .RFIFO_DEPTH  ( 2              )
    )
    u_top_bdma_slc_inst
    (
      .clk   ( clk   ),
      .rst_a ( rst_sync ),
      `AXIINSTM(gs,axi_slv_,iaxi_dev_int_),
      `AXIINSTM(gs,axi_mst_,iaxi_dev_asg_)
    );
  end : slice_top_bdma_slc_GEN

  for (genvar gh = 0; gh < NUMSLC; gh++)
  begin : islice_GEN
    `AXIASGNM(axi_dev_,gh,iaxi_dev_asg_,gh);
  end : islice_GEN

  for (genvar gt = 0; gt < NUMSTU; gt++)
  begin : stu_slc_GEN
    npu_axi_slice
    #(
      .AXIIDW       ( DEVIDW   ),
      .AXIDW        ( VSIZE*64 ),
      .AXIAWUW      ( SLICE_DMA_AWUW  ),
      .AXIWUW       ( SLICE_DMA_WUW   ),
      .AXIBUW       ( SLICE_DMA_BUW   ),
      .AXIARUW      ( SLICE_DMA_ARUW  ),
      .AXIRUW       ( SLICE_DMA_RUW   ),
      .NUMSLC       ( AXI_SLC_DEPTH   ), //improve timing
      .AWFIFO_DEPTH ( 1        ),
      .WFIFO_DEPTH  ( 2        ),
      .BFIFO_DEPTH  ( 1        ),
      .ARFIFO_DEPTH ( 1        ),
      .RFIFO_DEPTH  ( 2        )
    )
    u_slc_inst
    (
      .clk   ( clk   ),
      .rst_a ( rst_sync ),
      `AXIINSTM(gt,axi_slv_,axi_dev_stu_),
      `AXIINSTM(gt+NUMSLC,axi_mst_,axi_dev_)
    );
  end : stu_slc_GEN


  //
  // Top AXI matrix
  //
  // addres map config
  npu_axi_config
  #(
    .CFGIDW ( 1         ),
    .NUMAP  ( TOPNUMAP  ),
    .DECBASE_RST_VAL (TOP_CFG_DECBASE_RST_VAL),
    .DECSIZE_RST_VAL (TOP_CFG_DECSIZE_RST_VAL),
    .DECMST_RST_VAL  (TOP_CFG_DECMST_RST_VAL),
    .NUMMST ( NUMGRP+1  )
  )
  u_top_cfg_inst
  (
    .clk   ( clk   ),
    .rst_a ( rst_sync ),
    .swit_base ('0),
    .swit_ena  ('0),
    `AXIINSTM(TOP_IDX,axi_slv_,axi_cfg_demux_),
    `AXICONFIGINST(top_amap_)
  );
npu_axi_matrix
  #(
    .NUMSLV  ( NUMSLC+NUMSTU ),
    .NUMMST  ( NUMGRP+1      ),
    .NUMAP   ( TOPNUMAP      ),
    .AXIDW   ( VSIZE*64      ),
    .AXISIDW ( DEVIDW        ),
    .AXIMIDW ( LNKIDW        ),
    .AXIAWUW ( SLICE_DMA_AWUW       ),
    .AXIWUW  ( SLICE_DMA_WUW        ),
    .AXIBUW  ( SLICE_DMA_BUW        ),
    .AXIARUW ( SLICE_DMA_ARUW       ),
    .AXIRUW  ( SLICE_DMA_RUW        ),
    .SYNCFB  ( 68                   ),
    .SYNCFW  ( 4                    ),
    .BC      ( 1                    )
  )
u_top_mat_inst
  (
    .clk    ( clk   ),
    .rst_a  ( rst_sync ),
    .ptidx_a( ptidx_a  ),
    .decslv ( '1    ),
    `AXIINST(axi_slv_,axi_dev_),
    `AXIINST(axi_mst_,axi_elnk_),
    `AXICONFIGINST(top_amap_)
  );

  for (genvar ge = 0; ge < NUMGRP-1; ge++)
  begin : egress_slc_GEN
    // register slices on outputs
    npu_axi_slice
    #(
      .NUMSLC       ( LNKSLC_O ),
      .AXIIDW       ( LNKIDW   ),
      .AXIDW        ( VSIZE*64 ),
      .AXIAWUW      ( SLICE_DMA_AWUW  ),
      .AXIWUW       ( SLICE_DMA_WUW   ),
      .AXIBUW       ( SLICE_DMA_BUW   ),
      .AXIARUW      ( SLICE_DMA_ARUW  ),
      .AXIRUW       ( SLICE_DMA_RUW   ),
      .AWFIFO_DEPTH ( 1        ),
      .WFIFO_DEPTH  ( 2        ),
      .BFIFO_DEPTH  ( 1        ),
      .ARFIFO_DEPTH ( 1        ),
      .RFIFO_DEPTH  ( 2        )
    )
    u_slc_inst
    (
      .clk   ( clk   ),
      .rst_a ( rst_sync ),
      `AXIINSTM(ge+2,axi_slv_,axi_elnk_),
      `AXIINSTM(ge,axi_mst_,axi_egress_)
    );
  end : egress_slc_GEN

  for (genvar gi = 0; gi < NUMGRP-1; gi++)
  begin : ingress_slc_GEN
    // register slices on outputs
    npu_axi_slice
    #(
      .NUMSLC       ( LNKSLC_I ),
      .AXIIDW       ( LNKIDW   ),
      .AXIDW        ( VSIZE*64 ),
      .AXIAWUW      ( SLICE_DMA_AWUW  ),
      .AXIWUW       ( SLICE_DMA_WUW   ),
      .AXIBUW       ( SLICE_DMA_BUW   ),
      .AXIARUW      ( SLICE_DMA_ARUW  ),
      .AXIRUW       ( SLICE_DMA_RUW   ),
      .AWFIFO_DEPTH ( 1        ),
      .WFIFO_DEPTH  ( 2        ),
      .BFIFO_DEPTH  ( 1        ),
      .ARFIFO_DEPTH ( 1        ),
      .RFIFO_DEPTH  ( 2        )
    )
    u_igrs_slc_inst
    (
      .clk   ( clk   ),
      .rst_a ( rst_sync ),
      `AXIINSTM(gi,axi_slv_,axi_ingress_),
      `AXIINSTM(gi+1,axi_mst_,iaxi_ilnk_)
    );
  end : ingress_slc_GEN

  //
  // Connect ingress0 and egress0
  //
  npu_axi_slice
  #(
    .AXIIDW       ( LNKIDW         ),
    .AXIDW        ( VSIZE*64       ),
    .AXIAWUW      ( SLICE_DMA_AWUW ),
    .AXIWUW       ( SLICE_DMA_WUW  ),
    .AXIBUW       ( SLICE_DMA_BUW  ),
    .AXIARUW      ( SLICE_DMA_ARUW ),
    .AXIRUW       ( SLICE_DMA_RUW  ),
    .NUMSLC       ( AXI_SLC_DEPTH  ), //improve timing
    .AWFIFO_DEPTH ( 1              ),
    .WFIFO_DEPTH  ( 2              ),
    .BFIFO_DEPTH  ( 1              ),
    .ARFIFO_DEPTH ( 1              ),
    .RFIFO_DEPTH  ( 2              )
  )
  u_ingrs_egrs_inst
  (
    .clk   ( clk   ),
    .rst_a ( rst_sync ),
    `AXIINSTM(1, axi_slv_,axi_elnk_),
    `AXIINSTM(0, axi_mst_,iaxi_ilnk_)
  );

  //
  // Connect ingress XM and egress XM
  //
  npu_axi_slice
  #(
    .AXIIDW       ( LNKIDW         ),
    .AXIDW        ( VSIZE*64       ),
    .AXIAWUW      ( SLICE_DMA_AWUW ),
    .AXIWUW       ( SLICE_DMA_WUW  ),
    .AXIBUW       ( SLICE_DMA_BUW  ),
    .AXIARUW      ( SLICE_DMA_ARUW ),
    .AXIRUW       ( SLICE_DMA_RUW  ),
    .NUMSLC       ( AXI_SLC_DEPTH  ), //improve timing
    .AWFIFO_DEPTH ( 1              ),
    .WFIFO_DEPTH  ( 2              ),
    .BFIFO_DEPTH  ( 1              ),
    .ARFIFO_DEPTH ( 1              ),
    .RFIFO_DEPTH  ( 2              )
  )
  u_ingrs_egrs_xm_inst
  (
    .clk   ( clk   ),
    .rst_a ( rst_sync ),
    `AXIINSTM(0, axi_slv_,axi_elnk_),
    `AXIINST(axi_mst_,axi_xm_)
  );


  npu_bdma_remap_flag
  #(
    .NUM     ( NUMGRP         ),
    .AXIDW   ( 64*VSIZE       ),
    .AXIIDW  ( LNKIDW         ),
    .AXIAWUW ( SLICE_DMA_AWUW ),
    .AXIWUW  ( SLICE_DMA_WUW  ),
    .AXIBUW  ( SLICE_DMA_BUW  ),
    .AXIARUW ( SLICE_DMA_ARUW ),
    .AXIRUW  ( SLICE_DMA_RUW  )
  )
  u_bdma_remap_inst
  (
    .clk    ( clk   ),
    .rst_a  ( rst_sync ),
    `AXIINST(axi_slv_,iaxi_ilnk_),
    `AXIINST(axi_mst_,iaxi_ilnk_bc_),
    .ptidx_a (ptidx_a)
  );

  npu_bot_bc
    #(
    .NUMMST       ( NUMGRP         ),
    .AXIIDW       ( LNKIDW         ),
    .AXIDW        ( VSIZE*64       ),
    .AXIAWUW      ( SLICE_DMA_AWUW ),
    .AXIWUW       ( SLICE_DMA_WUW  ),
    .AXIBUW       ( SLICE_DMA_BUW  ),
    .AXIARUW      ( SLICE_DMA_ARUW ),
    .AXIRUW       ( SLICE_DMA_RUW  )
    )
  u_bot_bdma_inst
  (
    .clk   ( clk   ),
    .rst_a ( rst_sync ),
    `AXIINST(axi_slv_,iaxi_ilnk_bc_),
    `AXIINST(axi_mst_,iaxi_ilnk_int_)
  );

  for (genvar gs = 0; gs < NUMGRP; gs++)
  begin : slice_bot_bdma_slc_GEN
    npu_axi_slice
    #(
      .AXIIDW       ( LNKIDW         ),
      .AXIDW        ( VSIZE*64       ),
      .AXIAWUW      ( SLICE_DMA_AWUW ),
      .AXIWUW       ( SLICE_DMA_WUW  ),
      .AXIBUW       ( SLICE_DMA_BUW  ),
      .AXIARUW      ( SLICE_DMA_ARUW ),
      .AXIRUW       ( SLICE_DMA_RUW  ),
      .NUMSLC       ( AXI_SLC_DEPTH  ), //improve timing
      .AWFIFO_DEPTH ( 1              ),
      .WFIFO_DEPTH  ( 2              ),
      .BFIFO_DEPTH  ( 1              ),
      .ARFIFO_DEPTH ( 1              ),
      .RFIFO_DEPTH  ( 2              )
    )
    u_bot_bdma_slc_inst
    (
      .clk   ( clk   ),
      .rst_a ( rst_sync ),
      `AXIINSTM(gs,axi_slv_,iaxi_ilnk_int_),
      `AXIINSTM(gs,axi_mst_,axi_ilnk_)
    );
  end : slice_bot_bdma_slc_GEN

  //
  // Combine ingress and L2 ARC links
  //
  for (genvar gi = 0; gi < NUMGRP; gi++)
  begin : ibot_GEN
    `AXIASGNM(axi_ibot_,gi,axi_ilnk_,gi);
  end : ibot_GEN    
  `AXIASGN(NUMGRP,axi_ibot_,axi_dev_l2_);
  
  //
  // Bottom AXI matrix
  //
  npu_axi_config
  #(
    .CFGIDW ( 1        ),
    .NUMAP  ( BOTNUMAP ),
    .DECBASE_RST_VAL (BOT_CFG_DECBASE_RST_VAL),
    .DECSIZE_RST_VAL (BOT_CFG_DECSIZE_RST_VAL),
    .DECMST_RST_VAL  (BOT_CFG_DECMST_RST_VAL),
    .NUMMST ( `NPU_CSM_BANKS_PER_GRP+1 )
  )
  u_bot_inst
  (
    .clk   ( clk   ),
    .rst_a ( rst_sync ),
    .swit_base ('0),
    .swit_ena  ('0),
    `AXIINSTM(BOT_IDX,axi_slv_,axi_cfg_demux_),
    `AXICONFIGINST(bot_amap_)
  );
npu_axi_matrix
  #(
    .NUMSLV  ( NUMGRP+1       ),
    .NUMMST  ( `NPU_CSM_BANKS_PER_GRP+1),
    .NUMAP   ( BOTNUMAP       ),
    .AXIDW   ( VSIZE*64       ),
    .AXISIDW ( LNKIDW         ),
    .AXIMIDW ( BOTIDW         ),
    .AXIAWUW ( SLICE_DMA_AWUW ),
    .AXIWUW  ( SLICE_DMA_WUW  ),
    .AXIBUW  ( SLICE_DMA_BUW  ),
    .AXIARUW ( SLICE_DMA_ARUW ),
    .AXIRUW  ( SLICE_DMA_RUW  )
  )
  u_bot_mat_inst
  (
    .clk    ( clk   ),
    .rst_a  ( rst_sync ),
    .ptidx_a( 2'b00       ),
    .decslv ( '1    ),
    `AXIINST(axi_slv_,axi_ibot_),
    `AXIINST(axi_mst_,axi_slc_obot_),
    `AXICONFIGINST(bot_amap_)
  );
  
  for (genvar gbc = 0; gbc < `NPU_CSM_BANKS_PER_GRP+1; gbc++)
  begin : axi_bot_slc_GEN
    npu_axi_slice
    #(
      .AXIIDW       ( BOTIDW         ),
      .AXIDW        ( VSIZE*64       ),
      .AXIAWUW      ( SLICE_DMA_AWUW ),
      .AXIWUW       ( SLICE_DMA_WUW  ),
      .AXIBUW       ( SLICE_DMA_BUW  ),
      .AXIARUW      ( SLICE_DMA_ARUW ),
      .AXIRUW       ( SLICE_DMA_RUW  ),
      .NUMSLC       ( AXI_SLC_DEPTH  ), //improve timing
      .AWFIFO_DEPTH ( 1              ),
      .WFIFO_DEPTH  ( 2              ),
      .BFIFO_DEPTH  ( 1              ),
      .ARFIFO_DEPTH ( 1              ),
      .RFIFO_DEPTH  ( 2              )
    )
    u_slc_bot_inst
    (
      .clk   ( clk   ),
      .rst_a ( rst_sync ),
      `AXIINSTM(gbc,axi_slv_,axi_slc_obot_),
      `AXIINSTM(gbc,axi_mst_,axi_obot_)
    );
  end : axi_bot_slc_GEN

  //
  // Assign CLN input links
  //
  for (genvar gc = 0; gc < `NPU_CSM_BANKS_PER_GRP; gc++)
  begin : cln_GEN
    `AXIASGNM(int_axi_csm_l2_,gc,axi_obot_,gc);
  end : cln_GEN    
  
  //
  // Remap AXI Bridge Config
  //
  // addres map config
  npu_axi_config
  #(
    .CFGIDW ( 1         ),
    .DECBASE_RST_VAL (REMP_CFG_DECBASE_RST_VAL),
    .DECSIZE_RST_VAL (REMP_CFG_DECSIZE_RST_VAL),
    .DECMST_RST_VAL  (REMP_CFG_DECMST_RST_VAL),
    .NUMAP  ( 2         ),
    .NUMMST ( 1         )
  )
  u_remap_cfg_inst
  (
    .clk   ( clk   ),
    .rst_a ( rst_sync ),
    .swit_base ('0),
    .swit_ena  ('0),
    `AXIINSTM(REM_IDX,axi_slv_,axi_cfg_demux_),
    `AXICONFIGINST(rem_amap_)
  );


  for (genvar gc = 0; gc < `NPU_CSM_BANKS_PER_GRP; gc++)
  begin : cln_csm_remap_GEN
    npu_csm_remap
    #(
      .NUMMST  ( 1              ),
      .NUMAP   ( 2              ),
      .AXIDW   ( 64*VSIZE       ),
      .AXIIDW  ( BOTIDW         ),
      .AXIAWUW ( SLICE_DMA_AWUW ),
      .AXIWUW  ( SLICE_DMA_WUW  ),
      .AXIBUW  ( SLICE_DMA_BUW  ),
      .AXIARUW ( SLICE_DMA_ARUW ),
      .AXIRUW  ( SLICE_DMA_RUW  )
    )
    u_axi_csm_remap_inst
    (
      .clk    ( clk   ),
      .rst_a  ( rst_sync ),
      `AXIINSTM(gc,axi_slv_,int_axi_csm_l2_),
      `AXIINSTM(gc,axi_mst_,axi_cln_),
      `AXICONFIGINST(i1_rem_amap_)
    );
  end : cln_csm_remap_GEN

  //
  // CLN instance
  //
  npu_cln_wrap
  #(
    .DBANK   ( `NPU_CSM_BANKS_PER_GRP  ),
    .BOTIDW  ( BOTIDW          )
  )
  u_cln_inst
  (
    .clk       ( clk       ),
    .rst_a     ( rst_a     ),
    .grp_pd_mem( grp_pd_mem),
    .scm_dbank_ecc_irq(scm_dbank_ecc_irq),
    .scm_dbank_sbe(scm_dbank_sbe),
    .scm_dbank_dbe(scm_dbank_dbe),
    `AXIINST(axi_cln_,axi_cln_),
    `AXIINSTM(CLN_IDX,axi_cfg_,axi_cfg_demux_),
    .test_mode ( test_mode )
  );

  `AXIASGNID(axi_xm_,axi_noc_int_);
  assign axi_noc_int_arid     = {{(NOCIDW - LNKIDW){1'b0}},axi_xm_arid};
  assign axi_noc_int_awid     = {{(NOCIDW - LNKIDW){1'b0}},axi_xm_awid};
  assign axi_xm_rid           = axi_noc_int_rid[LNKIDW-1:0];
  assign axi_xm_bid           = axi_noc_int_bid[LNKIDW-1:0];


  npu_axi_slice
  #(
    .AXIIDW       ( NOCIDW         ),
    .AXIDW        ( VSIZE*64       ),
    .AXIAWUW      ( SLICE_DMA_AWUW ),
    .AXIWUW       ( SLICE_DMA_WUW  ),
    .AXIBUW       ( SLICE_DMA_BUW  ),
    .AXIARUW      ( SLICE_DMA_ARUW ),
    .AXIRUW       ( SLICE_DMA_RUW  ),
    .NUMSLC       ( AXI_SLC_DEPTH  ), //improve timing
    .AWFIFO_DEPTH ( 1              ),
    .WFIFO_DEPTH  ( 2              ),
    .BFIFO_DEPTH  ( 1              ),
    .ARFIFO_DEPTH ( 1              ),
    .RFIFO_DEPTH  ( 2              )
  )
  u_noc_slc_inst
  (
    .clk   ( clk   ),
    .rst_a ( rst_sync ),
    `AXIINST(axi_slv_,axi_noc_int_),
    `AXIINST(axi_mst_,axi_noc_)
  );
  

  //
  // CCM outputs have an ID and  width converter, slice and decoder, slice
  //
  npu_axi_idtrack
  #(
    .SIZE    ( DMI_OST        ),
    .AXISIDW ( BOTIDW         ),
    .AXIMIDW ( CCMIDW         ),
    .AXIDW   ( 64*VSIZE       ),
    .AXIAWUW ( SLICE_DMA_AWUW ),
    .AXIWUW  ( SLICE_DMA_WUW  ),
    .AXIBUW  ( SLICE_DMA_BUW  ),
    .AXIARUW ( SLICE_DMA_ARUW ),
    .AXIRUW  ( SLICE_DMA_RUW  )
  )
  u_ccm_idc_inst
  (
    .clk   ( clk   ),
    .rst_a ( rst_sync ),
    `AXIINSTM(`NPU_CSM_BANKS_PER_GRP,axi_slv_,axi_obot_),
    `AXIINST(axi_mst_,axi_ccm_wid_)
  );

  npu_axi_bridge
  #(
    .AXIIDW   ( CCMIDW          ),
    .AXISDW   ( VSIZE*64        ),
    .AXIMDW   ( 64              ),
    .AXISAWUW ( SLICE_DMA_AWUW  ),
    .AXISWUW  ( SLICE_DMA_WUW   ),
    .AXISBUW  ( SLICE_DMA_BUW   ),
    .AXISARUW ( SLICE_DMA_ARUW  ),
    .AXISRUW  ( SLICE_DMA_RUW   ),
    .AXIMAWUW ( SLICE_MMIO_AWUW ),
    .AXIMWUW  ( SLICE_MMIO_WUW  ),
    .AXIMBUW  ( SLICE_MMIO_BUW  ),
    .AXIMARUW ( SLICE_MMIO_ARUW ),
    .AXIMRUW  ( SLICE_MMIO_RUW  )
  )
  u_ccm_down_inst
  (
    .clk   ( clk   ),
    .rst_a ( rst_sync ),
    `AXIINST(axi_slv_,axi_ccm_wid_),
    `AXIINST(axi_mst_,axi_ccm_nar_)
  );

  npu_axi_slice
  #(
      .AXIIDW       ( CCMIDW          ),
      .AXIDW        ( 64              ),
      .AXIAWUW      ( SLICE_MMIO_AWUW ),
      .AXIWUW       ( SLICE_MMIO_WUW  ),
      .AXIBUW       ( SLICE_MMIO_BUW  ),
      .AXIARUW      ( SLICE_MMIO_ARUW ),
      .AXIRUW       ( SLICE_MMIO_RUW  ),
      .NUMSLC       ( 1               ),
      .AWFIFO_DEPTH ( 1               ),
      .WFIFO_DEPTH  ( 1               ),
      .BFIFO_DEPTH  ( 1               ),
      .ARFIFO_DEPTH ( 1               ),
      .RFIFO_DEPTH  ( 1               )
  )
  u_slc_down_inst
  (
   .clk   ( clk   ),
   .rst_a ( rst_sync ),
   `AXIINST(axi_slv_,axi_ccm_nar_),
   `AXIINST(axi_mst_,axi_ccm_nar_slice_)
  );

  // decoder
  `AXIASGN(0,axi_ccm_grp_,axi_ccm_nar_slice_);
  //
  // CCM AXI matrix
  //
  npu_axi_config
  #(
    .CFGIDW ( 1        ),
    .NUMAP  ( CCMNUMAP ),
    .DECBASE_RST_VAL (CCM_CFG_DECBASE_RST_VAL),
    .DECSIZE_RST_VAL (CCM_CFG_DECSIZE_RST_VAL),
    .DECMST_RST_VAL  (CCM_CFG_DECMST_RST_VAL),
    .NUMMST ( NUMSLC+NUMSTU+1 )
  )
  u_ccm_inst
  (
    .clk   ( clk   ),
    .rst_a ( rst_sync ),
    .swit_base ('0),
    .swit_ena  ('0),
    `AXIINSTM(CCM_IDX,axi_slv_,axi_cfg_demux_),
    `AXICONFIGINST(ccm_amap_)
  );

npu_axi_matrix
  #(
    .NUMSLV  ( 1                    ),
    .NUMMST  ( NUMSLC+NUMSTU+1      ),
    .NUMAP   ( NUMSLC+NUMSTU+1      ),
    .AXIDW   ( 64                   ),
    .AXISIDW ( CCMIDW               ),
    .AXIMIDW ( CCMIDW               ), 
    .AXIAWUW ( SLICE_MMIO_AWUW      ),
    .AXIWUW  ( SLICE_MMIO_WUW       ),
    .AXIBUW  ( SLICE_MMIO_BUW       ),
    .AXIARUW ( SLICE_MMIO_ARUW      ),
    .AXIRUW  ( SLICE_MMIO_RUW       )
  )
  u_ccm_demux_inst
  (
    .clk    ( clk   ),
    .rst_a  ( rst_sync ),
    .ptidx_a( 2'b00       ),
    .decslv ( '1    ),
    `AXIINST(axi_slv_,axi_ccm_grp_),
    `AXIINST(axi_mst_,axi_ccm_demux_int_),
    `AXICONFIGINST(ccm_amap_)
  );

  for (genvar gi = 0; gi < NUMSTU+NUMSLC+1; gi++)
  begin : ccm_demux_GEN
    `AXIASGNM(axi_ccm_demux_,gi,axi_ccm_demux_int_,gi);
  end : ccm_demux_GEN    

  for (genvar ocs = 0; ocs < NUMSLC; ocs++)
  begin : out_slc_slc_GEN
    npu_axi_slice
    #(
        .AXIIDW       ( CCMIDW          ),
        .AXIDW        ( 64              ),
        .AXIAWUW      ( SLICE_MMIO_AWUW ),
        .AXIWUW       ( SLICE_MMIO_WUW  ),
        .AXIBUW       ( SLICE_MMIO_BUW  ),
        .AXIARUW      ( SLICE_MMIO_ARUW ),
        .AXIRUW       ( SLICE_MMIO_RUW  ),
        .NUMSLC       ( AXI_SLC_DEPTH   ), //improve timing
        .AWFIFO_DEPTH ( 1               ),
        .WFIFO_DEPTH  ( 1               ),
        .BFIFO_DEPTH  ( 1               ),
        .ARFIFO_DEPTH ( 1               ),
        .RFIFO_DEPTH  ( 1               )
    )
    u_slc_inst
    (
      .clk   ( clk   ),
      .rst_a ( rst_sync ),
      `AXIINSTM(ocs,axi_slv_,axi_ccm_demux_),
      `AXIINSTM(ocs,axi_mst_,axi_ccm_slice_)
    );
  end : out_slc_slc_GEN

  for (genvar ocd = 0; ocd < NUMSTU; ocd++)
  begin : out_stu_slc_GEN
    npu_axi_slice
    #(
        .AXIIDW       ( CCMIDW          ),
        .AXIDW        ( 64              ),
        .AXIAWUW      ( SLICE_MMIO_AWUW ),
        .AXIWUW       ( SLICE_MMIO_WUW  ),
        .AXIBUW       ( SLICE_MMIO_BUW  ),
        .AXIARUW      ( SLICE_MMIO_ARUW ),
        .AXIRUW       ( SLICE_MMIO_RUW  ),
        .NUMSLC       ( AXI_SLC_DEPTH   ), //improve timing
        .AWFIFO_DEPTH ( 1               ),
        .WFIFO_DEPTH  ( 2               ),
        .BFIFO_DEPTH  ( 1               ),
        .ARFIFO_DEPTH ( 1               ),
        .RFIFO_DEPTH  ( 2               )
    )
    u_slc_inst
    (
      .clk   ( clk   ),
      .rst_a ( rst_sync ),
      `AXIINSTM(ocd+NUMSLC,axi_slv_,axi_ccm_demux_),
      `AXIINSTM(ocd,axi_mst_,axi_ccm_stu_)
    );
  end : out_stu_slc_GEN
  
  npu_axi_slice
  #(
    .AXIIDW       ( CCMIDW          ),
    .AXIDW        ( 64              ),
    .AXIAWUW      ( SLICE_MMIO_AWUW ),
    .AXIWUW       ( SLICE_MMIO_WUW  ),
    .AXIBUW       ( SLICE_MMIO_BUW  ),
    .AXIARUW      ( SLICE_MMIO_ARUW ),
    .AXIRUW       ( SLICE_MMIO_RUW  ),
    .NUMSLC       ( AXI_SLC_DEPTH   ), //improve timing
    .AWFIFO_DEPTH ( 1               ),
    .WFIFO_DEPTH  ( 2               ),
    .BFIFO_DEPTH  ( 1               ),
    .ARFIFO_DEPTH ( 1               ),
    .RFIFO_DEPTH  ( 2               )
  )
  u_l2out_inst
  (
    .clk   ( clk   ),
    .rst_a ( rst_sync ),
    `AXIINSTM(NUMSTU+NUMSLC,axi_slv_,axi_ccm_demux_),
    `AXIINST(axi_mst_,axi_ccm_l2_)
  );

endmodule // npu_cln_group


