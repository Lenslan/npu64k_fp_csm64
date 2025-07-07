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

//Configuration-dependent macro definitions
//`include "../arcsync_defines.v"
//`include_xi "../configuration.vpp"

// if has pd_fg -----> `PD1_NUM = 3 else =2
//===========================================================================
//
//    ######    #      #   #      # 
//    #     #   ##    ##   #      #
//    #     #   #  # # #   #      #
//    ######    #   #  #   #      #
//    #         #      #   #      #
//    #         #      #   #      #
//    #         #      #     ####
//
// ===========================================================================
// Description:
// Support the PDM interface from different cores' PDM 
// Access PMU MMIO registers, controll the PUCNT\RSTCNT\PDCNT
// ===========================================================================
`include "arcsync_defines.v"

module arcsync_pmu
#(
  parameter PD1_NUM      = `ARCSYNC_PDM_HAS_FG + 2,      
  parameter ADDR_WIDTH   = 32,
  parameter DATA_WIDTH   = 32,
 // parameter CORE_NUM     = 4 ,
  parameter PUCNT_W      = 16,
  parameter RSTCNT_W     = 8 , 
  parameter PDCNT_W      = 8 ,
  parameter PUCNT_LOGIC1_W      = 16      ,
  parameter PUCNT_LOGIC2_W      = 16      ,
  parameter logic [31:0] CORE_NUM       = 32'd1,
  localparam             CORE_NUM_S     = signed'(CORE_NUM), // NOTE: signed version for genvar type checking
  parameter logic [31:0] MAX_CORE_NUM   = 32'd4,
  localparam             MAX_CORE_NUM_S = signed'(MAX_CORE_NUM), // NOTE: signed version for genvar type checking
  parameter logic [31:0] CLUSTER_NUM    = 32'd1,
  localparam             CLUSTER_NUM_S  = signed'(CLUSTER_NUM) // NOTE: signed version for genvar type checking
)
(
  
// regular power interface  
  // Power interface for core 
  output    logic  [CORE_NUM-1:0]               arcsync_core_pwr_down,      // Power down signal 
  output    logic  [CORE_NUM-1:0]               arcsync_core_isolate_n,   // Isolate control signal for power domain (active low)
  output    logic  [CORE_NUM-1:0]               arcsync_core_isolate,     // Isolate control signal for power domain (active high)
  output    logic  [CORE_NUM-1:0]               arcsync_core_pd_mem,      // Power down of power domain memories
  output    logic  [CORE_NUM-1:0]               arcsync_core_pd_logic,    // Power down of power domain logic
  output    logic  [CORE_NUM-1:0]               arcsync_core_pd_logic1,    // Power down of power domain logic
  output    logic  [CORE_NUM-1:0]               arcsync_core_pd_logic2,    // Power down of power domain logic
  output    logic  [CORE_NUM-1:0]               arcsync_core_pu_rst,          // Power up reset
  input     logic  [CORE_NUM-1:0]               arcsync_core_exist,
  //power interface for group
  output    logic  [CLUSTER_NUM-1:0][3:0]             arcsync_grp_pwr_down,      // Power down signal 
  output    logic  [CLUSTER_NUM-1:0][3:0]             arcsync_grp_isolate_n,   // Isolate control signal for power domain (active low)
  output    logic  [CLUSTER_NUM-1:0][3:0]             arcsync_grp_isolate,     // Isolate control signal for power domain (active high)
  output    logic  [CLUSTER_NUM-1:0][3:0]             arcsync_grp_pd_mem,      // Power down of power domain memories
  output    logic  [CLUSTER_NUM-1:0][3:0]             arcsync_grp_pd_logic,    // Power down of power domain logic
  output    logic  [CLUSTER_NUM-1:0][3:0]             arcsync_grp_pd_logic1,    // Power down of power domain logic
  output    logic  [CLUSTER_NUM-1:0][3:0]             arcsync_grp_pd_logic2,    // Power down of power domain logic
  output    logic  [CLUSTER_NUM-1:0][3:0]             arcsync_grp_pu_rst,          // Power up reset
//interface with AXI2REG
  input     logic       [CLUSTER_NUM-1:0]   cl_enable,  // cluster enable, 0: disable, 1: enable
  input     logic       [CORE_NUM-1:0]      arcsync_core_wr_enable,
  input     logic                           mmio_sel,   // select target register group, valid at the cycle when *en is high
  input     logic       [ADDR_WIDTH-1:0]    mmio_addr,  // register address, valid at the cycle when *en is high
  input     logic                           mmio_wen,   // write enable for register
  input     logic                           mmio_ren,   // read enable for register
  input     logic       [DATA_WIDTH-1:0]    mmio_wdata, // write data, valid when wen is high

  output    logic       [DATA_WIDTH-1:0]    mmio_rdata, // read data, valid when ren is high
  output    logic       [1:0]               mmio_resp,  // {err, ack} the response is received when *en is high

    // PMode   
  input     logic  [CORE_NUM-1:0][2:0]          core_arcsync_pmode,             // Power Mode Current State

//global signal
  input     logic      iso_override,    // Isolate override control signal for power domain (used for test) when test_mode valid, isolation come from it
  input     logic      test_mode,       // Test mode, disable pd control signal
  input     logic      rst_a,           // Asynchronous reset, active high
  input     logic      clk              // Global ungated clock                
);


///////////////////////////////////////////////////////////////////////////////
//                                                                           //
//                    local wires and regs declaration                       //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////

//parameter PUCNT_W  = 16;
//parameter RSTCNT_W = 8 ;
//parameter PDCNT_W  = 8 ;
//parameter PUCNT_LOGIC1_W  = 16;
//parameter PUCNT_LOGIC2_W  = 16;
//read/write power up counter
logic  [CLUSTER_NUM-1:0]    pu2iso_cnt_p0_wr;           // power up counter write
logic  [CLUSTER_NUM-1:0]    pu2rst_cnt_p0_wr;           // reset delay counter write
logic  [CLUSTER_NUM-1:0]    iso2pd_cnt_p0_wr;           // power down counter write
logic  [PUCNT_W-1:0]        pu2iso_cnt_p0_wdata;        // power up counter write value
logic  [RSTCNT_W-1:0]       pu2rst_cnt_p0_wdata;        // reset delay counter write value
logic  [PDCNT_W-1:0]        iso2pd_cnt_p0_wdata;        // power down counter write value
logic  [CLUSTER_NUM-1:0]    pu2iso_cnt_p0_en;
logic  [CLUSTER_NUM-1:0]    pu2rst_cnt_p0_en; 
logic  [CLUSTER_NUM-1:0]    iso2pd_cnt_p0_en;
logic  [CLUSTER_NUM-1:0]    pu2iso_cnt_p0_read;         //cluster`x power-up counter read
logic  [CLUSTER_NUM-1:0]    pu2rst_cnt_p0_read;         //cluster`x reset counter read
logic  [CLUSTER_NUM-1:0]    iso2pd_cnt_p0_read;         //cluster`x power-down counter read

logic  [CLUSTER_NUM-1:0]    pu_core_lg1_cnt_p0_wr;     // power up core logic1 counter write
logic  [CLUSTER_NUM-1:0]    pu_core_lg2_cnt_p0_wr;     // power up core logic2 counter write
logic  [CLUSTER_NUM-1:0]    pu_core_lg1_cnt_p0_en;
logic  [CLUSTER_NUM-1:0]    pu_core_lg2_cnt_p0_en;
logic  [CLUSTER_NUM-1:0]    pu_core_lg1_cnt_p0_read;
logic  [CLUSTER_NUM-1:0]    pu_core_lg2_cnt_p0_read;
logic  [PUCNT_LOGIC1_W-1:0] pu_core_lg1_cnt_p0_wdata;
logic  [PUCNT_LOGIC2_W-1:0] pu_core_lg2_cnt_p0_wdata;

logic  [CLUSTER_NUM-1:0]    pu_grp_lg1_cnt_p0_wr;      // power up group logic1 counter write
logic  [CLUSTER_NUM-1:0]    pu_grp_lg2_cnt_p0_wr;      // power up group logic2 counter write
logic  [CLUSTER_NUM-1:0]    pu_grp_lg1_cnt_p0_en;
logic  [CLUSTER_NUM-1:0]    pu_grp_lg2_cnt_p0_en;
logic  [CLUSTER_NUM-1:0]    pu_grp_lg1_cnt_p0_read;
logic  [CLUSTER_NUM-1:0]    pu_grp_lg2_cnt_p0_read;
logic  [PUCNT_LOGIC1_W-1:0] pu_grp_lg1_cnt_p0_wdata;
logic  [PUCNT_LOGIC2_W-1:0] pu_grp_lg2_cnt_p0_wdata;

logic                         core_pmode_read;
logic [CLUSTER_NUM-1:0][31:0] seq_cnt_rdata;           //sequence counter radata per cluster
logic [CLUSTER_NUM-1:0]       seq_cnt_read;            //sequence counter read valid signal per cluster 
logic            [31:0]       pmu_cnt_rdata;           //sequence counter rdata ready to output

logic  [CLUSTER_NUM-1:0][PUCNT_W-1:0]   pu2iso_cnt_r;               // count from power-up to isolation release,PMU_PUCNT
logic  [CLUSTER_NUM-1:0][RSTCNT_W-1:0]  pu2rst_cnt_r;               // count from power-up isolation release to reset release, PMU_RSTCNT
logic  [CLUSTER_NUM-1:0][PDCNT_W-1:0]   iso2pd_cnt_r;               // count from isolation enabled to power-down, PMU_PDCNT
logic  [CLUSTER_NUM-1:0][PUCNT_LOGIC1_W-1:0]   pu_core_lg1_cnt_r;        // count from power-up logic1 to logic2. PMU_PU_LOGIC1
logic  [CLUSTER_NUM-1:0][PUCNT_LOGIC2_W-1:0]   pu_core_lg2_cnt_r;        // count from power-up logic2 to logic. PMU_PU_LOGIC2
logic  [CLUSTER_NUM-1:0][PUCNT_LOGIC1_W-1:0]   pu_grp_lg1_cnt_r;        // count from power-up logic1 to logic2. PMU_PU_LOGIC1
logic  [CLUSTER_NUM-1:0][PUCNT_LOGIC2_W-1:0]   pu_grp_lg2_cnt_r;        // count from power-up logic2 to logic. PMU_PU_LOGIC2

logic                  arcsync_pmu_ctrl_active;
logic [DATA_WIDTH-1:0] arcsync_pmu_rd_data;
logic                  arcsync_pmu_rd_valid;      //the same cycle of mmio_ren

logic                  mmio_ack;
logic                  mmio_error;

//////////////////////////////////////////////////////////////////////////////////////
//Register base address 
//
localparam logic [ADDR_WIDTH-1:0] ADDR_CL_GRP0_PMODE          = `ADDR_CL_GRP0_PMODE ;
localparam logic [ADDR_WIDTH-1:0] ADDR_CL_GRP1_PMODE          = `ADDR_CL_GRP1_PMODE ;
localparam logic [ADDR_WIDTH-1:0] ADDR_CL_GRP2_PMODE          = `ADDR_CL_GRP2_PMODE ;
localparam logic [ADDR_WIDTH-1:0] ADDR_CL_GRP3_PMODE          = `ADDR_CL_GRP3_PMODE ;
localparam logic [ADDR_WIDTH-1:0] ADDR_PMU_SET_PUCNT          = `ADDR_PMU_SET_PUCNT ;
localparam logic [ADDR_WIDTH-1:0] ADDR_PMU_SET_RSTCNT         = `ADDR_PMU_SET_RSTCNT;
localparam logic [ADDR_WIDTH-1:0] ADDR_PMU_SET_PDCNT          = `ADDR_PMU_SET_PDCNT ;
localparam logic [ADDR_WIDTH-1:0] ADDR_PMU_SET_CORE_LOGIC1    = `ADDR_PMU_SET_CORE_LOGIC1 ;
localparam logic [ADDR_WIDTH-1:0] ADDR_PMU_SET_CORE_LOGIC2    = `ADDR_PMU_SET_CORE_LOGIC2 ;
localparam logic [ADDR_WIDTH-1:0] ADDR_PMU_SET_GRP_LOGIC1     = `ADDR_PMU_SET_GRP_LOGIC1 ;
localparam logic [ADDR_WIDTH-1:0] ADDR_PMU_SET_GRP_LOGIC2     = `ADDR_PMU_SET_GRP_LOGIC2 ;

logic [CLUSTER_NUM-1:0] grp0_pmode_en;
logic [CLUSTER_NUM-1:0] grp1_pmode_en;
logic [CLUSTER_NUM-1:0] grp2_pmode_en;
logic [CLUSTER_NUM-1:0] grp3_pmode_en;
logic [CLUSTER_NUM-1:0] grp0_pmode_wen;
logic [CLUSTER_NUM-1:0] grp1_pmode_wen;
logic [CLUSTER_NUM-1:0] grp2_pmode_wen;
logic [CLUSTER_NUM-1:0] grp3_pmode_wen;
logic [CLUSTER_NUM-1:0] [31:0] CL_GRP0_PMODE;
logic [CLUSTER_NUM-1:0] [31:0] CL_GRP1_PMODE;
logic [CLUSTER_NUM-1:0] [31:0] CL_GRP2_PMODE;
logic [CLUSTER_NUM-1:0] [31:0] CL_GRP3_PMODE;
logic [CLUSTER_NUM-1:0] tri_grp0_pd_req;
logic [CLUSTER_NUM-1:0] tri_grp1_pd_req;
logic [CLUSTER_NUM-1:0] tri_grp2_pd_req;
logic [CLUSTER_NUM-1:0] tri_grp3_pd_req;
logic [CLUSTER_NUM-1:0] tri_grp0_pu_req;
logic [CLUSTER_NUM-1:0] tri_grp1_pu_req;
logic [CLUSTER_NUM-1:0] tri_grp2_pu_req;
logic [CLUSTER_NUM-1:0] tri_grp3_pu_req;
logic [CLUSTER_NUM-1:0][3:0] tri_grp_pd_req;
logic [CLUSTER_NUM-1:0][3:0] tri_grp_pu_req;

localparam logic [ADDR_WIDTH-1:0]    ADDR_CORE_PMODE          = `ADDR_CORE_PMODE      ; 
logic [CORE_NUM-1:0][31:0] CORE_PMODE; 

//logic [CORE_NUM-1:0][1:0]  core_pmode_nxt;
//logic [CORE_NUM-1:0][1:0]  core_pmode_r;
logic [CORE_NUM-1:0] core_pmode_wen;
logic [CORE_NUM-1:0] core_pmode_en;
logic [CORE_NUM-1:0] tri_core_pd_req;
logic [CORE_NUM-1:0] tri_core_pu_req;

logic                valid_req;
logic                valid_ren_req;
logic                valid_wen_req;
logic [31:0]         pmode_rdata;            //for core
logic [31:0]         group_pmode_rdata;      //for group
logic                 group_pmode_read;      //for group

logic [CLUSTER_NUM-1:0][3:0]       group_seq_status;
logic [CORE_NUM-1:0]               core_seq_status;
///////////////////////////////////////////////////////////////////////////////
//                                                                           //
//                             main code                                     //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////
// Sequence counter Register
////////////////////////////////////////
always_comb 
begin: sequence_counter_PROC
  logic [ADDR_WIDTH-1:0]  addr_pmu_set_pucnt  ;
  logic [ADDR_WIDTH-1:0]  addr_pmu_set_rstcnt ;
  logic [ADDR_WIDTH-1:0]  addr_pmu_set_pdcnt  ;
  logic [ADDR_WIDTH-1:0]  addr_pmu_set_core_logic1  ;
  logic [ADDR_WIDTH-1:0]  addr_pmu_set_core_logic2  ;
  logic [ADDR_WIDTH-1:0]  addr_pmu_set_grp_logic1  ;
  logic [ADDR_WIDTH-1:0]  addr_pmu_set_grp_logic2  ;
  for (int unsigned i=0;i<CLUSTER_NUM; i++)
    begin//{
    addr_pmu_set_pucnt     =  ADDR_PMU_SET_PUCNT  + 4*i;
    addr_pmu_set_rstcnt    =  ADDR_PMU_SET_RSTCNT + 4*i;
    addr_pmu_set_pdcnt     =  ADDR_PMU_SET_PDCNT  + 4*i;
    addr_pmu_set_core_logic1    =  ADDR_PMU_SET_CORE_LOGIC1 + 4*i;
    addr_pmu_set_core_logic2    =  ADDR_PMU_SET_CORE_LOGIC2 + 4*i;
    addr_pmu_set_grp_logic1    =  ADDR_PMU_SET_GRP_LOGIC1 + 4*i;
    addr_pmu_set_grp_logic2    =  ADDR_PMU_SET_GRP_LOGIC2 + 4*i;
    pu2iso_cnt_p0_en[i] = mmio_sel && (mmio_addr == addr_pmu_set_pucnt);
    pu2rst_cnt_p0_en[i] = mmio_sel && (mmio_addr == addr_pmu_set_rstcnt);
    iso2pd_cnt_p0_en[i] = mmio_sel && (mmio_addr == addr_pmu_set_pdcnt);
    pu_core_lg1_cnt_p0_en[i] = mmio_sel && (mmio_addr == addr_pmu_set_core_logic1);
    pu_core_lg2_cnt_p0_en[i] = mmio_sel && (mmio_addr == addr_pmu_set_core_logic2);
    pu_grp_lg1_cnt_p0_en[i] = mmio_sel && (mmio_addr == addr_pmu_set_grp_logic1);
    pu_grp_lg2_cnt_p0_en[i] = mmio_sel && (mmio_addr == addr_pmu_set_grp_logic2);
// power-up counter 
    pu2iso_cnt_p0_wr[i]       =  mmio_sel && cl_enable[i] && mmio_wen && (mmio_addr == addr_pmu_set_pucnt);
    pu2iso_cnt_p0_read[i]     =  mmio_sel && mmio_ren && (mmio_addr == addr_pmu_set_pucnt);
// reset delay counter 
    pu2rst_cnt_p0_wr[i]       =  mmio_sel && cl_enable[i] && mmio_wen && (mmio_addr == addr_pmu_set_rstcnt);
    pu2rst_cnt_p0_read[i]     =  mmio_sel && mmio_ren && (mmio_addr == addr_pmu_set_rstcnt);
// power-down counter
    iso2pd_cnt_p0_wr[i]       = mmio_sel && cl_enable[i] && mmio_wen &&  (mmio_addr == addr_pmu_set_pdcnt);
    iso2pd_cnt_p0_read[i]     = mmio_sel && mmio_ren &&  (mmio_addr == addr_pmu_set_pdcnt);
// from pd_logic1 to pd_logic2, power up sequence counter
    pu_core_lg1_cnt_p0_wr[i]      = mmio_sel && cl_enable[i] && mmio_wen &&  (mmio_addr == addr_pmu_set_core_logic1);
    pu_core_lg1_cnt_p0_read[i]    = mmio_sel && mmio_ren &&  (mmio_addr == addr_pmu_set_core_logic1);
    pu_grp_lg1_cnt_p0_wr[i]       = mmio_sel && cl_enable[i] && mmio_wen &&  (mmio_addr == addr_pmu_set_grp_logic1);
    pu_grp_lg1_cnt_p0_read[i]     = mmio_sel && mmio_ren &&  (mmio_addr == addr_pmu_set_grp_logic1);
// from pd_logic2 to pd_logic, power up sequence counter
    pu_core_lg2_cnt_p0_wr[i]       = mmio_sel && cl_enable[i] && mmio_wen &&  (mmio_addr == addr_pmu_set_core_logic2);
    pu_core_lg2_cnt_p0_read[i]     = mmio_sel && mmio_ren &&  (mmio_addr == addr_pmu_set_core_logic2);
    pu_grp_lg2_cnt_p0_wr[i]        = mmio_sel && cl_enable[i] && mmio_wen &&  (mmio_addr == addr_pmu_set_grp_logic2);
    pu_grp_lg2_cnt_p0_read[i]      = mmio_sel && mmio_ren &&  (mmio_addr == addr_pmu_set_grp_logic2);
    end//}
  pu2iso_cnt_p0_wdata    =  {PUCNT_W{mmio_sel & mmio_wen}}  & mmio_wdata [PUCNT_W-1:0] ;
  pu2rst_cnt_p0_wdata    =  {RSTCNT_W{mmio_sel & mmio_wen}} & mmio_wdata [RSTCNT_W-1:0];
  iso2pd_cnt_p0_wdata    =  {PDCNT_W{mmio_sel & mmio_wen}}  & mmio_wdata [PDCNT_W-1:0] ;
  pu_core_lg1_cnt_p0_wdata   =  {PUCNT_LOGIC1_W{mmio_sel & mmio_wen}}  & mmio_wdata [PUCNT_LOGIC1_W-1:0] ;
  pu_core_lg2_cnt_p0_wdata   =  {PUCNT_LOGIC2_W{mmio_sel & mmio_wen}}  & mmio_wdata [PUCNT_LOGIC2_W-1:0] ;
  pu_grp_lg1_cnt_p0_wdata    =  {PUCNT_LOGIC1_W{mmio_sel & mmio_wen}}  & mmio_wdata [PUCNT_LOGIC1_W-1:0] ;
  pu_grp_lg2_cnt_p0_wdata    =  {PUCNT_LOGIC2_W{mmio_sel & mmio_wen}}  & mmio_wdata [PUCNT_LOGIC2_W-1:0] ;
end: sequence_counter_PROC

for (genvar i=0;i<CLUSTER_NUM_S; i++) //{
begin:update_cl_cnt_value_PROC
  // set power-up counter
  always @(posedge clk or posedge rst_a)
  begin: pu2iso_cnt_r_PROC
    if(rst_a == 1'b1)
    begin
      pu2iso_cnt_r[i] <= {{PUCNT_W-1{1'b0}},1'b1};
    end
    else if(pu2iso_cnt_p0_wr[i])
    begin
      pu2iso_cnt_r[i] <= pu2iso_cnt_p0_wdata[PUCNT_W-1:0];
    end
  end
  // set reset counter
  always @(posedge clk or posedge rst_a)
  begin: pu2rst_cnt_r_PROC
    if(rst_a == 1'b1)
    begin
      pu2rst_cnt_r[i] <= {{RSTCNT_W-1{1'b0}},1'b1};
    end 
    else if(pu2rst_cnt_p0_wr[i])
    begin
      pu2rst_cnt_r[i] <= pu2rst_cnt_p0_wdata[RSTCNT_W-1:0];
    end
  end
  // set power-down counter
  always @(posedge clk or posedge rst_a)
  begin: iso2pd_cnt_r_PROC
    if(rst_a == 1'b1)
    begin
      iso2pd_cnt_r[i] <= {{PDCNT_W-1{1'b0}},1'b1};
    end 
    else if(iso2pd_cnt_p0_wr[i])
    begin
      iso2pd_cnt_r[i] <= iso2pd_cnt_p0_wdata[PDCNT_W-1:0];
    end
  end
  // set core power-up logic1 to logic2 counter
  always @(posedge clk or posedge rst_a)
  begin: pu_core_lg1_cnt_r_PROC
    if(rst_a == 1'b1)
    begin
      pu_core_lg1_cnt_r[i] <= {{PUCNT_LOGIC1_W-1{1'b0}},1'b1};
    end 
    else if(pu_core_lg1_cnt_p0_wr[i])
    begin
      pu_core_lg1_cnt_r[i] <= pu_core_lg1_cnt_p0_wdata[PUCNT_LOGIC1_W-1:0];
    end
  end
  // set core power-up logic2 to logic counter
  always @(posedge clk or posedge rst_a)
  begin: pu_core_lg2_cnt_r_PROC
    if(rst_a == 1'b1)
    begin
      pu_core_lg2_cnt_r[i] <= {{PUCNT_LOGIC2_W-1{1'b0}},1'b1};
    end 
    else if(pu_core_lg2_cnt_p0_wr[i])
    begin
      pu_core_lg2_cnt_r[i] <= pu_core_lg2_cnt_p0_wdata[PUCNT_LOGIC2_W-1:0];
    end
  end
  // set grp power-up logic1 to logic2 counter
  always @(posedge clk or posedge rst_a)
  begin: pu_grp_lg1_cnt_r_PROC
    if(rst_a == 1'b1)
    begin
      pu_grp_lg1_cnt_r[i] <= {{PUCNT_LOGIC1_W-1{1'b0}},1'b1};
    end 
    else if(pu_grp_lg1_cnt_p0_wr[i])
    begin
      pu_grp_lg1_cnt_r[i] <= pu_grp_lg1_cnt_p0_wdata[PUCNT_LOGIC1_W-1:0];
    end
  end
  // set grp power-up logic2 to logic counter
  always @(posedge clk or posedge rst_a)
  begin: pu_grp_lg2_cnt_r_PROC
    if(rst_a == 1'b1)
    begin
      pu_grp_lg2_cnt_r[i] <= {{PUCNT_LOGIC2_W-1{1'b0}},1'b1};
    end 
    else if(pu_grp_lg2_cnt_p0_wr[i])
    begin
      pu_grp_lg2_cnt_r[i] <= pu_grp_lg2_cnt_p0_wdata[PUCNT_LOGIC2_W-1:0];
    end
  end
 end:update_cl_cnt_value_PROC 
//}

//pmu sequence control register readback value
always_comb
begin:pmu_seq_counter_rdata
    pmu_cnt_rdata = {DATA_WIDTH{1'b0}};
  for (int unsigned i=0;i<CLUSTER_NUM; i++)
    begin//{
    seq_cnt_read[i]  = pu2iso_cnt_p0_read[i] | pu2rst_cnt_p0_read[i] | iso2pd_cnt_p0_read[i] 
                     | pu_core_lg1_cnt_p0_read[i] | pu_core_lg2_cnt_p0_read[i]
                     | pu_grp_lg1_cnt_p0_read[i] | pu_grp_lg2_cnt_p0_read[i];

    seq_cnt_rdata[i] = pu2iso_cnt_p0_read[i] ? {{32-PUCNT_W{1'b0}}, pu2iso_cnt_r[i]} :
                    (pu2rst_cnt_p0_read[i] ? {{32-RSTCNT_W{1'b0}}, pu2rst_cnt_r[i]} :
                    (iso2pd_cnt_p0_read[i] ? {{32-PDCNT_W{1'b0}}, iso2pd_cnt_r[i]} :
                    (pu_core_lg1_cnt_p0_read[i] ? {{32-PUCNT_LOGIC1_W{1'b0}}, pu_core_lg1_cnt_r[i]} :
                    (pu_core_lg2_cnt_p0_read[i] ? {{32-PUCNT_LOGIC2_W{1'b0}}, pu_core_lg2_cnt_r[i]} :
                    (pu_grp_lg1_cnt_p0_read[i] ? {{32-PUCNT_LOGIC1_W{1'b0}}, pu_grp_lg1_cnt_r[i]} :
                    (pu_grp_lg2_cnt_p0_read[i] ? {{32-PUCNT_LOGIC2_W{1'b0}}, pu_grp_lg2_cnt_r[i]} :
                    32'h0))))));

    pmu_cnt_rdata = pmu_cnt_rdata | ({32{seq_cnt_read[i]}} & seq_cnt_rdata[i]);
    end//}
end:pmu_seq_counter_rdata

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////PMODE REGISTER//////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
always_comb
begin: core_pmode_en_PROC
  logic [ADDR_WIDTH-1:0]  addr_core_pmode       ; 
  for (int unsigned i=0;i<CORE_NUM; i++)
  begin
    addr_core_pmode  = ADDR_CORE_PMODE + 4*i;
    // The request accesses CORE_PMODE register
    core_pmode_en[i] =  (mmio_sel && arcsync_core_exist[i]) && (mmio_addr == addr_core_pmode);
  end
end: core_pmode_en_PROC

always_comb 
begin: pmode_PROC
  pmode_rdata = 32'b0;
  for (int unsigned i=0;i<CORE_NUM; i++)
  begin 
    // write 1'b0 to bit0 to trigger power-up request 
    // or write 1'b1 to bit0 to trigger power-down to pm1
    //others ignore
    core_pmode_wen[i] = core_pmode_en[i] && arcsync_core_wr_enable[i] && mmio_wen && ((mmio_wdata[0] == 1'b0) || mmio_wdata[0] == 1'b1);

    if(mmio_ren & (|core_pmode_en))
    begin
    pmode_rdata = pmode_rdata | ({32{core_pmode_en[i]}} & CORE_PMODE[i]);
    end
  end
end: pmode_PROC 

for (genvar i=0;i<CORE_NUM_S; i++)
begin: individual_core_PROC 
  assign CORE_PMODE[i]      = {31'b0,core_seq_status[i]};
 //power down req send out PMU
  assign tri_core_pd_req[i]   = core_pmode_wen[i] && mmio_wdata[0] == 1'b1 && (core_arcsync_pmode[i]==3'h0);
 //power up req internal use
  assign tri_core_pu_req[i]   = core_pmode_wen[i] && mmio_wdata[0] == 1'b0 && (core_arcsync_pmode[i]==3'h1); 
end: individual_core_PROC

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//core pmode valid
assign core_pmode_read        = mmio_sel & mmio_ren & (|core_pmode_en);
//group pmode valid
assign group_pmode_read       =  mmio_ren & ((|grp0_pmode_en) | (|grp1_pmode_en) | (|grp2_pmode_en) | (|grp3_pmode_en));

//read data of group pmode register
always_comb
begin
    group_pmode_rdata = 32'b0;
  for (int unsigned i=0;i<CLUSTER_NUM; i++)
  begin
    if(group_pmode_read)
    begin
    group_pmode_rdata = group_pmode_rdata | ({32{grp0_pmode_en[i]}} & CL_GRP0_PMODE[i])
                                          | ({32{grp1_pmode_en[i]}} & CL_GRP1_PMODE[i])
                                          | ({32{grp2_pmode_en[i]}} & CL_GRP2_PMODE[i])
                                          | ({32{grp3_pmode_en[i]}} & CL_GRP3_PMODE[i]);
    end
  end
end
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//all register read value output 
//read data output valid signal 
assign arcsync_pmu_rd_valid = (|seq_cnt_read) | group_pmode_read | core_pmode_read ;

//read data output data
assign arcsync_pmu_rd_data  = (|seq_cnt_read) ? pmu_cnt_rdata :
                              (group_pmode_read ? group_pmode_rdata :
                              (core_pmode_read ? pmode_rdata  :
                               32'h0));
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////group PMODE REGISTER////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
always_comb 
begin: group_pmode_PROC
  logic [ADDR_WIDTH-1:0]  addr_grp0_pmode ;
  logic [ADDR_WIDTH-1:0]  addr_grp1_pmode ;
  logic [ADDR_WIDTH-1:0]  addr_grp2_pmode ;
  logic [ADDR_WIDTH-1:0]  addr_grp3_pmode ;
  for (int unsigned i=0;i<CLUSTER_NUM; i++)
  begin 
    addr_grp0_pmode  = ADDR_CL_GRP0_PMODE + 4*i;
    addr_grp1_pmode  = ADDR_CL_GRP1_PMODE + 4*i;
    addr_grp2_pmode  = ADDR_CL_GRP2_PMODE + 4*i;
    addr_grp3_pmode  = ADDR_CL_GRP3_PMODE + 4*i;
    grp0_pmode_en[i] =  mmio_sel && (mmio_addr == addr_grp0_pmode);
    grp1_pmode_en[i] =  mmio_sel && (mmio_addr == addr_grp1_pmode);
    grp2_pmode_en[i] =  mmio_sel && (mmio_addr == addr_grp2_pmode);
    grp3_pmode_en[i] =  mmio_sel && (mmio_addr == addr_grp3_pmode);
    grp0_pmode_wen[i] = grp0_pmode_en[i] && mmio_wen && cl_enable[i] && ((mmio_wdata[0] == 1'b0) || mmio_wdata[0] == 1'b1);
    grp1_pmode_wen[i] = grp1_pmode_en[i] && mmio_wen && cl_enable[i] && ((mmio_wdata[0] == 1'b0) || mmio_wdata[0] == 1'b1);
    grp2_pmode_wen[i] = grp2_pmode_en[i] && mmio_wen && cl_enable[i] && ((mmio_wdata[0] == 1'b0) || mmio_wdata[0] == 1'b1);
    grp3_pmode_wen[i] = grp3_pmode_en[i] && mmio_wen && cl_enable[i] && ((mmio_wdata[0] == 1'b0) || mmio_wdata[0] == 1'b1);
  end
end: group_pmode_PROC

for (genvar i=0;i<CLUSTER_NUM_S; i++)
begin: tri_grp_per_cl_PROC 
  assign CL_GRP0_PMODE[i]      = {30'b0,arcsync_grp_pwr_down[i][0],group_seq_status[i][0]};
  assign CL_GRP1_PMODE[i]      = {30'b0,arcsync_grp_pwr_down[i][1],group_seq_status[i][1]};
  assign CL_GRP2_PMODE[i]      = {30'b0,arcsync_grp_pwr_down[i][2],group_seq_status[i][2]};
  assign CL_GRP3_PMODE[i]      = {30'b0,arcsync_grp_pwr_down[i][3],group_seq_status[i][3]};
  assign tri_grp0_pd_req[i]   = grp0_pmode_wen[i] && mmio_wdata[0] == 1'b1 && arcsync_grp_pwr_down[i][0] == 1'b0;
  assign tri_grp0_pu_req[i]   = grp0_pmode_wen[i] && mmio_wdata[0] == 1'b0 && arcsync_grp_pwr_down[i][0] == 1'b1;
  assign tri_grp1_pd_req[i]   = grp1_pmode_wen[i] && mmio_wdata[0] == 1'b1 && arcsync_grp_pwr_down[i][1] == 1'b0;
  assign tri_grp1_pu_req[i]   = grp1_pmode_wen[i] && mmio_wdata[0] == 1'b0 && arcsync_grp_pwr_down[i][1] == 1'b1;
  assign tri_grp2_pd_req[i]   = grp2_pmode_wen[i] && mmio_wdata[0] == 1'b1 && arcsync_grp_pwr_down[i][2] == 1'b0;
  assign tri_grp2_pu_req[i]   = grp2_pmode_wen[i] && mmio_wdata[0] == 1'b0 && arcsync_grp_pwr_down[i][2] == 1'b1;
  assign tri_grp3_pd_req[i]   = grp3_pmode_wen[i] && mmio_wdata[0] == 1'b1 && arcsync_grp_pwr_down[i][3] == 1'b0;
  assign tri_grp3_pu_req[i]   = grp3_pmode_wen[i] && mmio_wdata[0] == 1'b0 && arcsync_grp_pwr_down[i][3] == 1'b1;

  //for each cluster there are 4 groups
  assign tri_grp_pd_req[i]    ={tri_grp3_pd_req[i],tri_grp2_pd_req[i],tri_grp1_pd_req[i],tri_grp0_pd_req[i]};
  assign tri_grp_pu_req[i]    ={tri_grp3_pu_req[i],tri_grp2_pu_req[i],tri_grp1_pu_req[i],tri_grp0_pu_req[i]};
end: tri_grp_per_cl_PROC

////////////////////////////////////////
// Module Instanitation
////////////////////////////////////////
//initiate cores pmu ctrl for each cluster
//for each cluster, the width of the trigger req is MAX_CORE_NUM

arcsync_pmu_ctrl #(
.PUCNT_W   (PUCNT_W),
.RSTCNT_W  (RSTCNT_W), 
.PDCNT_W   (PDCNT_W), 
.NUM       (18)//(MAX_CORE_NUM)
)
u_arcsync_npx_core_pmu_ctrl_cl0(
                              .core_pwr_down  (arcsync_core_pwr_down[MAX_CORE_NUM*0+18-1:MAX_CORE_NUM*0]),
                              .core_isolate_n (arcsync_core_isolate_n[MAX_CORE_NUM*0+18-1:MAX_CORE_NUM*0]),
                              .core_isolate   (arcsync_core_isolate[MAX_CORE_NUM*0+18-1:MAX_CORE_NUM*0]),
                              .core_pd_mem    (arcsync_core_pd_mem[MAX_CORE_NUM*0+18-1:MAX_CORE_NUM*0]),
                              .core_pd_logic1  (arcsync_core_pd_logic1[MAX_CORE_NUM*0+18-1:MAX_CORE_NUM*0]),
                              .core_pd_logic2  (arcsync_core_pd_logic2[MAX_CORE_NUM*0+18-1:MAX_CORE_NUM*0]),
                              .core_pd_logic  (arcsync_core_pd_logic[MAX_CORE_NUM*0+18-1:MAX_CORE_NUM*0]),

                              .core_pu_rst    (arcsync_core_pu_rst[MAX_CORE_NUM*0+18-1:MAX_CORE_NUM*0]),
                              .seq_status     (core_seq_status[MAX_CORE_NUM*0+18-1:MAX_CORE_NUM*0]),

                              .trigger_pd_req                       (tri_core_pd_req[MAX_CORE_NUM*0+18-1:MAX_CORE_NUM*0]),
                              .trigger_pu_req                       (tri_core_pu_req[MAX_CORE_NUM*0+18-1:MAX_CORE_NUM*0]),
                              .pu2iso_cnt                           (pu2iso_cnt_r[0]), 
                              .pu2rst_cnt                           (pu2rst_cnt_r[0]), 
                              .iso2pd_cnt                           (iso2pd_cnt_r[0]),
                              .pu_lg1_cnt                           (pu_core_lg1_cnt_r[0]),
                              .pu_lg2_cnt                           (pu_core_lg2_cnt_r[0]),
                              .iso_override                         (iso_override),
                              .test_mode                            (test_mode),
                              .clk                                  (clk),
                              .rst_a                                (rst_a)
                             );
//[MAX_CORE_NUM*0+MAX_CORE_NUM-1:MAX_CORE_NUM*0]
//[MAX_CORE_NUM*0+18-1:MAX_CORE_NUM*0] //need to instance
//[MAX_CORE_NUM*0+MAX_CORE_NUM-1:MAX_CORE_NUM*0+18]//need to tie 0
assign arcsync_core_pwr_down[MAX_CORE_NUM*0+MAX_CORE_NUM-1:MAX_CORE_NUM*0+18] = {(MAX_CORE_NUM-18){1'b0}};
assign arcsync_core_isolate_n[MAX_CORE_NUM*0+MAX_CORE_NUM-1:MAX_CORE_NUM*0+18] = {(MAX_CORE_NUM-18){1'b0}};
assign arcsync_core_isolate[MAX_CORE_NUM*0+MAX_CORE_NUM-1:MAX_CORE_NUM*0+18] = {(MAX_CORE_NUM-18){1'b0}};
assign arcsync_core_pd_mem[MAX_CORE_NUM*0+MAX_CORE_NUM-1:MAX_CORE_NUM*0+18] = {(MAX_CORE_NUM-18){1'b0}};
assign arcsync_core_pd_logic[MAX_CORE_NUM*0+MAX_CORE_NUM-1:MAX_CORE_NUM*0+18] = {(MAX_CORE_NUM-18){1'b0}};
assign arcsync_core_pd_logic1[MAX_CORE_NUM*0+MAX_CORE_NUM-1:MAX_CORE_NUM*0+18] = {(MAX_CORE_NUM-18){1'b0}};
assign arcsync_core_pd_logic2[MAX_CORE_NUM*0+MAX_CORE_NUM-1:MAX_CORE_NUM*0+18] = {(MAX_CORE_NUM-18){1'b0}};
assign arcsync_core_pu_rst[MAX_CORE_NUM*0+MAX_CORE_NUM-1:MAX_CORE_NUM*0+18] = {(MAX_CORE_NUM-18){1'b0}};
assign core_seq_status[MAX_CORE_NUM*0+MAX_CORE_NUM-1:MAX_CORE_NUM*0+18] = {(MAX_CORE_NUM-18){1'b0}};

//initiate group pmu ctrl for each npx cluster
//for each cluster, the width of the trigger req is 4
arcsync_pmu_ctrl #(
.PUCNT_W   (PUCNT_W),
.RSTCNT_W  (RSTCNT_W), 
.PDCNT_W   (PDCNT_W), 
.NUM       (4)
)
u_arcsync_group_pmu_ctrl0(
                              .core_pwr_down  (arcsync_grp_pwr_down[0] ),
                              .core_isolate_n (arcsync_grp_isolate_n[0]),
                              .core_isolate   (arcsync_grp_isolate[0]  ),
                              .core_pd_mem    (arcsync_grp_pd_mem[0]   ),
                              .core_pd_logic1  (arcsync_grp_pd_logic1[0] ),
                              .core_pd_logic2  (arcsync_grp_pd_logic2[0] ),
                              .core_pd_logic  (arcsync_grp_pd_logic[0] ),
                              .core_pu_rst    (arcsync_grp_pu_rst[0]   ),
                              .seq_status     (group_seq_status[0]),

                              .trigger_pd_req                       (tri_grp_pd_req[0]),
                              .trigger_pu_req                       (tri_grp_pu_req[0]),
                              .pu2iso_cnt                           (pu2iso_cnt_r[0]), 
                              .pu2rst_cnt                           (pu2rst_cnt_r[0]), 
                              .iso2pd_cnt                           (iso2pd_cnt_r[0]),
                              .pu_lg1_cnt                           (pu_grp_lg1_cnt_r[0]),
                              .pu_lg2_cnt                           (pu_grp_lg2_cnt_r[0]),
                              .iso_override                         (iso_override),
                              .test_mode                            (test_mode),
                              .clk                                  (clk),
                              .rst_a                                (rst_a)
                             );








arcsync_pmu_ctrl #(
.PUCNT_W   (PUCNT_W),
.RSTCNT_W  (RSTCNT_W), 
.PDCNT_W   (PDCNT_W), 
.NUM       (4)
)
u_arcsync_vpx_core_pmu_ctrl_cl1(
                              .core_pwr_down  (arcsync_core_pwr_down[MAX_CORE_NUM*1+4-1:MAX_CORE_NUM*1]),
                              .core_isolate_n (arcsync_core_isolate_n[MAX_CORE_NUM*1+4-1:MAX_CORE_NUM*1]),
                              .core_isolate   (arcsync_core_isolate[MAX_CORE_NUM*1+4-1:MAX_CORE_NUM*1]),
                              .core_pd_mem    (arcsync_core_pd_mem[MAX_CORE_NUM*1+4-1:MAX_CORE_NUM*1]),
                              .core_pd_logic1  (arcsync_core_pd_logic1[MAX_CORE_NUM*1+4-1:MAX_CORE_NUM*1]),
                              .core_pd_logic2  (arcsync_core_pd_logic2[MAX_CORE_NUM*1+4-1:MAX_CORE_NUM*1]),
                              .core_pd_logic  (arcsync_core_pd_logic[MAX_CORE_NUM*1+4-1:MAX_CORE_NUM*1]),

                              .core_pu_rst    (arcsync_core_pu_rst[MAX_CORE_NUM*1+4-1:MAX_CORE_NUM*1]),
                              .seq_status     (core_seq_status[MAX_CORE_NUM*1+4-1:MAX_CORE_NUM*1]),

                              .trigger_pd_req                       (tri_core_pd_req[MAX_CORE_NUM*1+4-1:MAX_CORE_NUM*1]),
                              .trigger_pu_req                       (tri_core_pu_req[MAX_CORE_NUM*1+4-1:MAX_CORE_NUM*1]),
                              .pu2iso_cnt                           (pu2iso_cnt_r[1]), 
                              .pu2rst_cnt                           (pu2rst_cnt_r[1]), 
                              .iso2pd_cnt                           (iso2pd_cnt_r[1]),
                              .pu_lg1_cnt                           (pu_core_lg1_cnt_r[1]),
                              .pu_lg2_cnt                           (pu_core_lg2_cnt_r[1]),
                              .iso_override                         (iso_override),
                              .test_mode                            (test_mode),
                              .clk                                  (clk),
                              .rst_a                                (rst_a)
                             );

assign arcsync_core_pwr_down[MAX_CORE_NUM*1+MAX_CORE_NUM-1:MAX_CORE_NUM*1+4] = {(MAX_CORE_NUM-4){1'b0}};
assign arcsync_core_isolate_n[MAX_CORE_NUM*1+MAX_CORE_NUM-1:MAX_CORE_NUM*1+4] = {(MAX_CORE_NUM-4){1'b0}};
assign arcsync_core_isolate[MAX_CORE_NUM*1+MAX_CORE_NUM-1:MAX_CORE_NUM*1+4] = {(MAX_CORE_NUM-4){1'b0}};
assign arcsync_core_pd_mem[MAX_CORE_NUM*1+MAX_CORE_NUM-1:MAX_CORE_NUM*1+4] = {(MAX_CORE_NUM-4){1'b0}};
assign arcsync_core_pd_logic[MAX_CORE_NUM*1+MAX_CORE_NUM-1:MAX_CORE_NUM*1+4] = {(MAX_CORE_NUM-4){1'b0}};
assign arcsync_core_pd_logic1[MAX_CORE_NUM*1+MAX_CORE_NUM-1:MAX_CORE_NUM*1+4] = {(MAX_CORE_NUM-4){1'b0}};
assign arcsync_core_pd_logic2[MAX_CORE_NUM*1+MAX_CORE_NUM-1:MAX_CORE_NUM*1+4] = {(MAX_CORE_NUM-4){1'b0}};
assign arcsync_core_pu_rst[MAX_CORE_NUM*1+MAX_CORE_NUM-1:MAX_CORE_NUM*1+4] = {(MAX_CORE_NUM-4){1'b0}};
assign core_seq_status[MAX_CORE_NUM*1+MAX_CORE_NUM-1:MAX_CORE_NUM*1+4] = {(MAX_CORE_NUM-4){1'b0}};


//set default value for npx group interfaces
assign arcsync_grp_pwr_down[1]  = {4{1'b`ARCSYNC_PMU_RESET_PMODE}};
assign arcsync_grp_isolate_n[1] = 4'b0;
assign arcsync_grp_isolate[1]   = 4'b0;
assign arcsync_grp_pd_mem[1]    = 4'b0;
assign arcsync_grp_pd_logic1[1] = 4'b0;
assign arcsync_grp_pd_logic2[1] = 4'b0;
assign arcsync_grp_pd_logic[1]  = 4'b0;
assign arcsync_grp_pu_rst[1]    = 4'b0;
assign group_seq_status[1]      = 4'b0;








//set default value for those npx interfaces
assign arcsync_core_pwr_down[MAX_CORE_NUM*2+MAX_CORE_NUM-1:MAX_CORE_NUM*2] = {(MAX_CORE_NUM){1'b0}};
assign arcsync_core_isolate_n[MAX_CORE_NUM*2+MAX_CORE_NUM-1:MAX_CORE_NUM*2] = {(MAX_CORE_NUM){1'b0}};
assign arcsync_core_isolate[MAX_CORE_NUM*2+MAX_CORE_NUM-1:MAX_CORE_NUM*2] = {(MAX_CORE_NUM){1'b0}};
assign arcsync_core_pd_mem[MAX_CORE_NUM*2+MAX_CORE_NUM-1:MAX_CORE_NUM*2] = {(MAX_CORE_NUM){1'b0}};
assign arcsync_core_pd_logic[MAX_CORE_NUM*2+MAX_CORE_NUM-1:MAX_CORE_NUM*2] = {(MAX_CORE_NUM){1'b0}};
assign arcsync_core_pd_logic1[MAX_CORE_NUM*2+MAX_CORE_NUM-1:MAX_CORE_NUM*2] = {(MAX_CORE_NUM){1'b0}};
assign arcsync_core_pd_logic2[MAX_CORE_NUM*2+MAX_CORE_NUM-1:MAX_CORE_NUM*2] = {(MAX_CORE_NUM){1'b0}};
assign arcsync_core_pu_rst[MAX_CORE_NUM*2+MAX_CORE_NUM-1:MAX_CORE_NUM*2] = {(MAX_CORE_NUM){1'b0}};

//set default value for seq_status
assign core_seq_status[MAX_CORE_NUM*2+MAX_CORE_NUM-1:MAX_CORE_NUM*2] = {MAX_CORE_NUM{1'b0}};

//set default value for npx group interfaces
assign arcsync_grp_pwr_down[2]  = {4{1'b`ARCSYNC_PMU_RESET_PMODE}};
assign arcsync_grp_isolate_n[2] = 4'b0;
assign arcsync_grp_isolate[2]   = 4'b0;
assign arcsync_grp_pd_mem[2]    = 4'b0;
assign arcsync_grp_pd_logic1[2] = 4'b0;
assign arcsync_grp_pd_logic2[2] = 4'b0;
assign arcsync_grp_pd_logic[2]  = 4'b0;
assign arcsync_grp_pu_rst[2]    = 4'b0;
assign group_seq_status[2]      = 4'b0;


///////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////

assign valid_ren_req  = mmio_ren && (     (|pu2iso_cnt_p0_en)
                                       || (|pu2rst_cnt_p0_en)
                                       || (|iso2pd_cnt_p0_en)
                                       || (|pu_core_lg1_cnt_p0_en)
                                       || (|pu_core_lg2_cnt_p0_en)
                                       || (|pu_grp_lg1_cnt_p0_en)
                                       || (|pu_grp_lg2_cnt_p0_en)
                                       || (|core_pmode_en)
                                       || (|grp0_pmode_en) 
                                       || (|grp1_pmode_en) 
                                       || (|grp2_pmode_en) 
                                       || (|grp3_pmode_en));

assign valid_wen_req  = mmio_wen && (     (|pu2iso_cnt_p0_wr)
                                       || (|pu2rst_cnt_p0_wr)
                                       || (|iso2pd_cnt_p0_wr)
                                       || (|pu_core_lg1_cnt_p0_wr)
                                       || (|pu_core_lg2_cnt_p0_wr)
                                       || (|pu_grp_lg1_cnt_p0_wr)
                                       || (|pu_grp_lg2_cnt_p0_wr)
                                       || (|core_pmode_wen)
                                       || (|grp0_pmode_wen) 
                                       || (|grp1_pmode_wen) 
                                       || (|grp2_pmode_wen) 
                                       || (|grp3_pmode_wen));

assign valid_req  = valid_ren_req || valid_wen_req;
assign mmio_resp  = {mmio_error,mmio_ack};
assign mmio_ack   =  mmio_sel | 1'b0;
assign mmio_error = (mmio_sel & !valid_req)
                     | 1'b0;

assign mmio_rdata  = arcsync_pmu_rd_data;


//-------------------------------------------------------------------------------------------------------
// Properties
//-------------------------------------------------------------------------------------------------------
`ifdef FORMAL_ASSERT_ON
  `include "prop_arcsync_pmu.sv"
`endif
endmodule
