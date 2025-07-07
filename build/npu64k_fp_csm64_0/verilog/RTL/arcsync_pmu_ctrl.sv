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
//
// Description:
//
// 1. generate UPF control signal to the related module
// 2. support the PDM interface from cores' PDM, vpx PDM, npx slice PDM or ...
//
// ===========================================================================
////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//`if ARCSYNC_PDM_HAS_FG ==1 
//  `let PD1_NUM = 3   //the number of pd1_sfx:pd1_pd,_pd1_fg,pd1_mem//
//`else
//  `let PD1_NUM =2
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////
`include "arcsync_defines.v"

module arcsync_pmu_ctrl #(
parameter PD1_NUM      = `ARCSYNC_PDM_HAS_FG + 2,        
parameter NUM     = 4              ,
parameter PUCNT_W      = 16             ,
parameter RSTCNT_W     = 8              ,
parameter PDCNT_W      = 8              ,
//TODO
parameter PUCNT_LOGIC1_W      = 16      ,
parameter PUCNT_LOGIC2_W      = 16      ,
parameter ACT_PUCNT_LOGIC1_W  = PUCNT_LOGIC1_W + 8   ,
parameter ACT_PUCNT_LOGIC2_W  = PUCNT_LOGIC2_W + 8   ,

parameter ACT_PUCNT_W  = PUCNT_W + 8   ,
parameter ACT_RSTCNT_W = RSTCNT_W + 3  ,
parameter ACT_PDCNT_W  = PDCNT_W + 8   
)
(
  // generate regular power interface
  output  logic  [NUM-1:0]      core_pwr_down,
  output  logic  [NUM-1:0]      core_isolate,
  output  logic  [NUM-1:0]      core_isolate_n,
  output  logic  [NUM-1:0]      core_pd_logic1,
  output  logic  [NUM-1:0]      core_pd_logic2,
  output  logic  [NUM-1:0]      core_pd_logic,
  output  logic  [NUM-1:0]      core_pd_mem,
  output  logic  [NUM-1:0]      core_pu_rst,
  output  logic  [NUM-1:0]      seq_status,     //indicates whether is in power up/down sequence

  input  logic   [NUM-1:0]      trigger_pu_req, 
  input  logic   [NUM-1:0]      trigger_pd_req,  

  input  logic     [PUCNT_W-1:0]  pu2iso_cnt,   // count from power-up to isolation release
  input  logic     [RSTCNT_W-1:0] pu2rst_cnt,   // count from power-up to reset release
  input  logic     [PDCNT_W-1:0]  iso2pd_cnt,   // count from isolation enabled to power-down
  input  logic     [PUCNT_LOGIC1_W-1:0] pu_lg1_cnt, // count from power-up logic1 to logic2. PMU_PU_LOGIC1
  input  logic     [PUCNT_LOGIC2_W-1:0] pu_lg2_cnt, // count from power-up logic2 to logic. PMU_PU_LOGIC2

  // global signal
  input  logic         iso_override,  // override iso control value in test_mode
  input  logic         test_mode,     // bypass pd/iso control signal
  input  logic         clk,           // gated unit clock
  input  logic         rst_a          // async reset
);

///////////////////////////////////////////////////////////////////////////////
//                                                                           //
//                    local parameters definition                            //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////
  parameter PM_IDLE    = 4'b0000;
  parameter PM_PD0     = 4'b0001;
  parameter PM_PD1     = 4'b0010;
  parameter PM_PD2     = 4'b0011;
  parameter PM_PU0     = 4'b0100;
  parameter PM_PU0_LOGIC1     = 4'b0101;
  parameter PM_PU0_LOGIC2     = 4'b0110;
  parameter PM_PU1     = 4'b0111;
  parameter PM_PU2     = 4'b1000;
  parameter PM_PU3     = 4'b1001;
  parameter PM_PU_LAST = 4'b1010;
///////////////////////////////////////////////////////////////////////////////
//                                                                           //
//                    local wires and regs declaration                       //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////

//UPF related signal
logic           core_pd_isolate_en[NUM];
logic           core_pd_isolate_dis[NUM];
logic           core_pd_isolate_r[NUM];
logic           core_pd_logic_en[NUM];
logic           core_pd_logic_dis[NUM];
logic           core_pd_logic_r[NUM];
logic           core_pd_mem_en[NUM];
logic           core_pd_mem_dis[NUM];
logic           core_pd_mem_r[NUM];
logic           core_pd_logic1_en[NUM];
logic           core_pd_logic1_dis[NUM];
logic           core_pd_logic1_r[NUM];
logic           core_pd_logic2_en[NUM];
logic           core_pd_logic2_dis[NUM];
logic           core_pd_logic2_r[NUM];

//UPF related signal
logic           core_pu_rst_r[NUM];
logic           core_pu_out_rst[NUM];
logic           core_pwr_down_en[NUM];
logic           core_pwr_down_dis[NUM];
logic           core_pwr_down_r[NUM];
//power up counter
logic    [ACT_PUCNT_W-1:0]   core_pu2iso_cnt_r[NUM];
logic    [ACT_PUCNT_W-1:0]   core_pu2iso_cnt_nxt[NUM];
logic                        core_pu2iso_cnt_dec[NUM];
logic                        core_pu2iso_cnt_load[NUM];  
//power up reset counter
logic    [ACT_RSTCNT_W-1:0]  core_pu2rst_cnt_r[NUM];
logic    [ACT_RSTCNT_W-1:0]  core_pu2rst_cnt_nxt[NUM];
logic                        core_pu2rst_cnt_dec[NUM];
logic                        core_pu2rst_cnt_load[NUM];  
//power down counter
logic    [ACT_PDCNT_W-1:0]   core_iso2pd_cnt_r[NUM];
logic    [ACT_PDCNT_W-1:0]   core_iso2pd_cnt_nxt[NUM];
logic                        core_iso2pd_cnt_dec[NUM];
logic                        core_iso2pd_cnt_load[NUM];
//power up logic-logic1 counter
logic    [ACT_PUCNT_LOGIC1_W-1:0]   core_pu_lg1_cnt_r[NUM];
logic    [ACT_PUCNT_LOGIC1_W-1:0]   core_pu_lg1_cnt_nxt[NUM];
logic                               core_pu_lg1_cnt_dec[NUM];
logic                               core_pu_lg1_cnt_load[NUM];
//power up logic-logic1 counter
logic    [ACT_PUCNT_LOGIC2_W-1:0]   core_pu_lg2_cnt_r[NUM];
logic    [ACT_PUCNT_LOGIC2_W-1:0]   core_pu_lg2_cnt_nxt[NUM];
logic                               core_pu_lg2_cnt_dec[NUM];
logic                               core_pu_lg2_cnt_load[NUM];


//add this signal compare to v2
logic       [1:0]    core_pdsq_cnt_nxt[NUM];
logic       [1:0]    core_pdsq_cnt_r[NUM];
//FSM
logic                core_trigger_req[NUM];
logic       [3:0]    core_power_sta_cur[NUM];
logic       [3:0]    core_power_sta_nxt[NUM];

///////////////////////////////////////////////////////////////////////////////
//                                                                           //
//                             main code                                     //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////
//If the PUCNT is set to N, the duration will apply (256*N+8) cycles after each domain is powered up.
logic [ACT_PUCNT_W-1:0]  eff_pu2iso_cnt ;
logic [ACT_RSTCNT_W-1:0] eff_pu2rst_cnt ;
logic [ACT_PDCNT_W-1:0]  eff_iso2pd_cnt ;
logic [ACT_PUCNT_LOGIC1_W-1:0]   eff_pu_lg1_cnt;
logic [ACT_PUCNT_LOGIC2_W-1:0]   eff_pu_lg2_cnt;


assign eff_pu2iso_cnt = {pu2iso_cnt, 8'b00000111};
assign eff_pu2rst_cnt = {pu2rst_cnt, 3'b111};
assign eff_iso2pd_cnt = {iso2pd_cnt, 8'b00000111};
assign eff_pu_lg1_cnt = {pu_lg1_cnt, 8'b00000111};
assign eff_pu_lg2_cnt = {pu_lg2_cnt, 8'b00000111};



logic core_pwr2iso_cnt_dec[NUM];
logic core_pwr2iso_cnt_load[NUM];
logic [2:0]core_pwr2iso_cnt;
logic [2:0]core_pwr2iso_cnt_nxt[NUM];
logic [2:0]core_pwr2iso_cnt_r[NUM];
assign  core_pwr2iso_cnt = 3'b100;

logic core_rescind_pu_rst_cnt_dec[NUM];
logic core_rescind_pu_rst_cnt_load[NUM];
logic [2:0]core_rescind_pu_rst_cnt;
logic [2:0]core_rescind_pu_rst_cnt_nxt[NUM];
logic [2:0]core_rescind_pu_rst_cnt_r[NUM];
assign  core_rescind_pu_rst_cnt = 3'b100;

for(genvar i = 0; i < NUM; i++)//{
begin
//////////////////////////////////////////////////////////////////
// power switch and clamp control generation for regular table
//////////////////////////////////////////////////////////////////
//power up reset counter
assign core_pu2iso_cnt_nxt[i] =( core_pu2iso_cnt_load[i] ? eff_pu2iso_cnt : 
                                 (core_pu2iso_cnt_dec[i] ? 
                                 (core_pu2iso_cnt_r[i] - {{ACT_PUCNT_W-1{1'b0}},1'b1}) : 
                                 core_pu2iso_cnt_r[i])
                               ) | {ACT_PUCNT_W{1'b0}};

assign core_pu2rst_cnt_nxt[i] =( core_pu2rst_cnt_load[i] ? eff_pu2rst_cnt : 
                                 (core_pu2rst_cnt_dec[i] ? 
                                 (core_pu2rst_cnt_r[i] - {{ACT_RSTCNT_W-1{1'b0}},1'b1}) : 
                                 core_pu2rst_cnt_r[i])
                               ) | {ACT_RSTCNT_W{1'b0}};

assign core_iso2pd_cnt_nxt[i] =( core_iso2pd_cnt_load[i] ? eff_iso2pd_cnt : 
                                 (core_iso2pd_cnt_dec[i] ? 
                                 (core_iso2pd_cnt_r[i] - {{ACT_PDCNT_W-1{1'b0}},1'b1}) : 
                                 core_iso2pd_cnt_r[i])
                               ) | {ACT_PDCNT_W{1'b0}};

assign core_pu_lg1_cnt_nxt[i] =( core_pu_lg1_cnt_load[i] ? eff_pu_lg1_cnt : 
                                 (core_pu_lg1_cnt_dec[i] ? 
                                 (core_pu_lg1_cnt_r[i] - {{ACT_PUCNT_LOGIC1_W{1'b0}},1'b1}) : 
                                 core_pu_lg1_cnt_r[i])
                               ) | {ACT_PUCNT_LOGIC1_W{1'b0}};

assign core_pu_lg2_cnt_nxt[i] =( core_pu_lg2_cnt_load[i] ? eff_pu_lg2_cnt : 
                                 (core_pu_lg2_cnt_dec[i] ? 
                                 (core_pu_lg2_cnt_r[i] - {{ACT_PUCNT_LOGIC2_W{1'b0}},1'b1}) : 
                                 core_pu_lg2_cnt_r[i])
                               ) | {ACT_PUCNT_LOGIC2_W{1'b0}};

assign core_pwr2iso_cnt_nxt[i] =( core_pwr2iso_cnt_load[i] ? core_pwr2iso_cnt:
                                   (core_pwr2iso_cnt_dec[i]?
                                   (core_pwr2iso_cnt_r[i] - 3'b001) :
                                   core_pwr2iso_cnt_r[i])
                                ) | 3'b0;

assign core_rescind_pu_rst_cnt_nxt[i] =( core_rescind_pu_rst_cnt_load[i] ? core_rescind_pu_rst_cnt:
                                   (core_rescind_pu_rst_cnt_dec[i]?
                                   (core_rescind_pu_rst_cnt_r[i] - 3'b001) :
                                   core_rescind_pu_rst_cnt_r[i])
                                ) | 3'b0;

always @(posedge clk or posedge rst_a)
begin:core_pu2iso_cnt_r_PROC
  if(rst_a == 1'b1)begin
      core_pu2iso_cnt_r[i] <= {ACT_PUCNT_W{1'b0}};
  end 
  else begin
      core_pu2iso_cnt_r[i] <= core_pu2iso_cnt_nxt[i];
  end
end

always @(posedge clk or posedge rst_a)
begin:core_pu2rst_cnt_r_PROC
  if(rst_a == 1'b1)begin
      core_pu2rst_cnt_r[i] <= {ACT_RSTCNT_W{1'b0}};
  end 
  else begin
      core_pu2rst_cnt_r[i] <= core_pu2rst_cnt_nxt[i];
  end
end

always @(posedge clk or posedge rst_a)
begin:core_iso2pd_cnt_r_PROC
  if(rst_a == 1'b1)begin
      core_iso2pd_cnt_r[i] <= {ACT_PDCNT_W{1'b0}};
  end 
  else begin
      core_iso2pd_cnt_r[i] <= core_iso2pd_cnt_nxt[i];
  end
end

always @(posedge clk or posedge rst_a)
begin:core_pu_lg1_cnt_r_PROC
  if(rst_a == 1'b1)begin
      core_pu_lg1_cnt_r[i] <= {ACT_PUCNT_LOGIC1_W{1'b0}};
  end 
  else begin
      core_pu_lg1_cnt_r[i] <= core_pu_lg1_cnt_nxt[i];
  end
end

always @(posedge clk or posedge rst_a)
begin:core_pu_lg2_cnt_r_PROC
  if(rst_a == 1'b1)begin
      core_pu_lg2_cnt_r[i] <= {ACT_PUCNT_LOGIC2_W{1'b0}};
  end 
  else begin
      core_pu_lg2_cnt_r[i] <= core_pu_lg2_cnt_nxt[i];
  end
end

always @(posedge clk or posedge rst_a)
begin:core_pdsq_cnt_r_PROC
  if(rst_a == 1'b1)begin
      core_pdsq_cnt_r[i] <= 2'b0;
  end 
  else begin
      core_pdsq_cnt_r[i] <= core_pdsq_cnt_nxt[i];
  end
end

always @(posedge clk or posedge rst_a)
begin:core_pwr2iso_cnt_r_PROC
  if(rst_a == 1'b1)begin
      core_pwr2iso_cnt_r[i] <= 3'b0;
  end 
  else begin
      core_pwr2iso_cnt_r[i] <= core_pwr2iso_cnt_nxt[i];
  end
end

always @(posedge clk or posedge rst_a)
begin:core_rescind_pu_rst_cnt_r_PROC
  if(rst_a == 1'b1)begin
      core_rescind_pu_rst_cnt_r[i] <= 3'b0;
  end 
  else begin
      core_rescind_pu_rst_cnt_r[i] <= core_rescind_pu_rst_cnt_nxt[i];
  end
end
//////////////////////////////////////////////////////////////
//////////////////FSM for power down/up management////////////
//////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin:core_power_sta_cur_PROC
  if(rst_a == 1'b1)begin
      core_power_sta_cur[i] <= 4'b0;
  end 
  else begin
      core_power_sta_cur[i] <= core_power_sta_nxt[i];
  end
end

assign core_trigger_req[i] = 1'b0 | trigger_pd_req[i] | trigger_pu_req[i] ;

always @*
begin:core_FSM_PROC
  core_power_sta_nxt[i]   = core_power_sta_cur[i];
  core_pd_isolate_dis[i]  = 1'b0;
  core_pd_isolate_en[i]   = 1'b0;
  core_pu_out_rst[i]      = 1'b0;
  core_pu2iso_cnt_load[i] = 1'b0;
  core_pu2iso_cnt_dec[i]  = 1'b0;
  core_pu2rst_cnt_load[i] = 1'b0;
  core_pu2rst_cnt_dec[i]  = 1'b0;
  core_iso2pd_cnt_load[i] = 1'b0;
  core_iso2pd_cnt_dec[i]  = 1'b0;
  core_pu_lg1_cnt_load[i] = 1'b0;
  core_pu_lg1_cnt_dec[i]  = 1'b0;
  core_pu_lg2_cnt_load[i] = 1'b0;
  core_pu_lg2_cnt_dec[i]  = 1'b0;
  core_pdsq_cnt_nxt[i]    = core_pdsq_cnt_r[i];
  core_pd_logic_en[i]     = 1'b0;
  core_pd_logic_dis[i]    = 1'b0;
  core_pd_logic1_en[i]    = 1'b0;
  core_pd_logic1_dis[i]   = 1'b0;
  core_pd_logic2_en[i]    = 1'b0;
  core_pd_logic2_dis[i]   = 1'b0;
  core_pd_mem_en[i]       = 1'b0;
  core_pd_mem_dis[i]      = 1'b0;
  core_pwr_down_en[i]     = 1'b0;
  core_pwr_down_dis[i]    = 1'b0;
  core_pwr2iso_cnt_load[i] =1'b0;
  core_pwr2iso_cnt_dec[i]  =1'b0; 
  core_rescind_pu_rst_cnt_load[i] =1'b0;
  core_rescind_pu_rst_cnt_dec[i]  =1'b0;

  case(core_power_sta_cur[i])
    PM_IDLE:
    begin
      if(trigger_pd_req[i])begin
          core_power_sta_nxt[i] = PM_PD0;
          core_pwr_down_en[i] = 1'b1; // to assert pwr_down
          core_pwr2iso_cnt_load[i] =1'b1;
      end
      if(trigger_pu_req[i])begin
          core_power_sta_nxt[i] = PM_PU0;
      end
    end
    PM_PD0:
    begin
	   core_pwr2iso_cnt_dec[i] = (|core_pwr2iso_cnt_r[i]);
	   if(~(|core_pwr2iso_cnt_r[i]))begin
       core_pd_isolate_en[i] = 1'b1;   //isolation pull up after pwr_down pull up
	   core_power_sta_nxt[i] = PM_PD1;
       core_iso2pd_cnt_load[i] = 1'b1;  //load cnt to count iso2mem
       core_pdsq_cnt_nxt[i] = 1; // power down sequence//indicates sequence from pd_mem to pd_pd//	   
	   end
    end
    PM_PD1:
    begin
      core_iso2pd_cnt_dec[i] = (|core_iso2pd_cnt_r[i]);
      if(~(|core_iso2pd_cnt_r[i]))begin
         core_power_sta_nxt[i] = PM_PD2;
         core_iso2pd_cnt_load[i] = 1'b1;
         core_pdsq_cnt_nxt[i] = core_pdsq_cnt_r[i] - 1;
         core_pd_mem_en[i] = 1'b1;
      end
    end
    PM_PD2:
    begin 
      core_iso2pd_cnt_dec[i] = (|core_iso2pd_cnt_r[i]);
       if(~(|core_iso2pd_cnt_r[i]) & ~(|core_pdsq_cnt_r[i]))begin
         core_power_sta_nxt[i] = PM_IDLE;
         core_pd_logic_en[i]  = 1'b1;
         core_pd_logic1_en[i] = 1'b1;
         core_pd_logic2_en[i] = 1'b1;
       end
    end
    PM_PU0:
    begin
      core_pu_out_rst[i] = 1'b1;
      //pd_logic de-asserted
      core_pd_logic1_dis[i] = 1'b1;
      core_pu_lg1_cnt_load[i]  = 1'b1;   
      core_power_sta_nxt[i] = PM_PU0_LOGIC1;
    end
    PM_PU0_LOGIC1:
    begin
      core_pu_out_rst[i] = 1'b1;
      core_pu_lg1_cnt_dec[i] = (|core_pu_lg1_cnt_r[i]); 
      //pd_logic1 de-asserted
      if(~(|core_pu_lg1_cnt_r[i]))begin                 
         core_power_sta_nxt[i] = PM_PU0_LOGIC2;
         core_pu_lg2_cnt_load[i]  = 1'b1;               
         core_pd_logic2_dis[i] = 1'b1;                  
      end
    end
    PM_PU0_LOGIC2:
    begin
      core_pu_out_rst[i] = 1'b1;
      core_pu_lg2_cnt_dec[i] = (|core_pu_lg2_cnt_r[i]);       
      //pd_logic2 de-asserted
      if(~(|core_pu_lg2_cnt_r[i]))begin                 
        core_pd_logic_dis[i] = 1'b1;                   
        core_pdsq_cnt_nxt[i] = 1;
        core_pu2iso_cnt_load[i]  = 1'b1;
        core_power_sta_nxt[i] = PM_PU1;
      end
    end
   PM_PU1:
    begin
      core_pu_out_rst[i] = 1'b1;
      core_pu2iso_cnt_dec[i] = (|core_pu2iso_cnt_r[i]);
      //pd_mem de-asserted
      if(~(|core_pu2iso_cnt_r[i]))begin
          core_power_sta_nxt[i] = PM_PU2;
          core_pu2iso_cnt_load[i]  = 1'b1;
          core_pdsq_cnt_nxt[i] = core_pdsq_cnt_r[i] - 1;
          core_pd_mem_dis[i] = 1'b1;
      end
    end 
    PM_PU2:
    begin
      core_pu_out_rst[i] = 1'b1;
      core_pu2iso_cnt_dec[i] = (|core_pu2iso_cnt_r[i]);
      if(~(|core_pu2iso_cnt_r[i]) & ~(|core_pdsq_cnt_r[i]))begin
          core_power_sta_nxt[i] = PM_PU3;
          core_pu2rst_cnt_load[i]  = 1'b1;
          core_pd_isolate_dis[i]   = 1'b1;
      end
    end
    PM_PU3:
    begin
      core_pu_out_rst[i] = 1'b1;
      core_pu2rst_cnt_dec[i] = (|core_pu2rst_cnt_r[i]);
      if(~(|core_pu2rst_cnt_r[i]))begin
          core_pwr_down_dis[i]  = 1'b1;
          core_rescind_pu_rst_cnt_load[i] =1'b1;
          core_power_sta_nxt[i] = PM_PU_LAST;
      end
    end
    PM_PU_LAST:
    begin
	  core_rescind_pu_rst_cnt_dec[i] = (|core_rescind_pu_rst_cnt_r[i]);
	  if((~(|core_rescind_pu_rst_cnt_r[i])) & (~core_trigger_req[i]))begin
      core_pu_out_rst[i] = 1'b0;
	  core_power_sta_nxt[i] = PM_IDLE;
	  end
	  else begin
	  core_pu_out_rst[i] = 1'b1;
	  end  
    end
    default:
    begin
      core_power_sta_nxt[i]   = core_power_sta_cur[i];
      core_pd_isolate_dis[i]  = 1'b0;
      core_pd_isolate_en[i]   = 1'b0;
      core_pu_out_rst[i]      = 1'b0;
      core_pu2iso_cnt_load[i] = 1'b0;
      core_pu2iso_cnt_dec[i]  = 1'b0;
      core_pu2rst_cnt_load[i] = 1'b0;
      core_pu2rst_cnt_dec[i]  = 1'b0;
      core_iso2pd_cnt_load[i] = 1'b0;
      core_iso2pd_cnt_dec[i]  = 1'b0;
      core_pu_lg1_cnt_load[i] = 1'b0;
      core_pu_lg1_cnt_dec[i]  = 1'b0;
      core_pu_lg2_cnt_load[i] = 1'b0;
      core_pu_lg2_cnt_dec[i]  = 1'b0;
      core_pdsq_cnt_nxt[i]    = core_pdsq_cnt_r[i];
      core_pd_logic_en[i]     = 1'b0;
      core_pd_logic_dis[i]    = 1'b0;
      core_pd_logic1_en[i]    = 1'b0;
      core_pd_logic1_dis[i]   = 1'b0;
      core_pd_logic2_en[i]    = 1'b0;
      core_pd_logic2_dis[i]   = 1'b0;
      core_pd_mem_en[i]       = 1'b0;
      core_pd_mem_dis[i]      = 1'b0;
      core_pwr_down_en[i]     = 1'b0;
      core_pwr_down_dis[i]    = 1'b0;
      core_pwr2iso_cnt_load[i] =1'b0;
      core_pwr2iso_cnt_dec[i]  =1'b0;
	  core_rescind_pu_rst_cnt_load[i] =1'b0;
      core_rescind_pu_rst_cnt_dec[i]  =1'b0;
    end
  endcase
end


/////////////////////////////////////////////////////////////////////////////////////////
//outputs
//
always @(posedge clk or posedge rst_a)
begin:core_pd_isolate_r_PROC
  if(rst_a == 1'b1)begin
      core_pd_isolate_r[i] <= 1'b`ARCSYNC_PMU_RESET_PMODE;
  end else if(core_pd_isolate_en[i] | core_pd_isolate_dis[i])begin
      core_pd_isolate_r[i] <= core_pd_isolate_en[i] | (~core_pd_isolate_dis[i]);
  end
end 

always @(posedge clk or posedge rst_a)
begin:core_pd_logic_r_PROC
  if(rst_a == 1'b1)begin
      core_pd_logic_r[i] <= 1'b`ARCSYNC_PMU_RESET_PMODE;
  end 
  else begin
     if(core_pd_logic_en[i] | core_pd_logic_dis[i])begin
      core_pd_logic_r[i] <= core_pd_logic_en[i] | (~core_pd_logic_dis[i]);
     end
  end   
end

always @(posedge clk or posedge rst_a)
begin:core_pd_logic1_r_PROC
  if(rst_a == 1'b1)begin
      core_pd_logic1_r[i] <= 1'b`ARCSYNC_PMU_RESET_PMODE;
  end 
  else begin
     if(core_pd_logic1_en[i] | core_pd_logic1_dis[i])begin
      core_pd_logic1_r[i] <= core_pd_logic1_en[i] | (~core_pd_logic1_dis[i]);
     end
  end   
end

always @(posedge clk or posedge rst_a)
begin:core_pd_logic2_r_PROC
  if(rst_a == 1'b1)begin
      core_pd_logic2_r[i] <= 1'b`ARCSYNC_PMU_RESET_PMODE;
  end 
  else begin
     if(core_pd_logic2_en[i] | core_pd_logic2_dis[i])begin
      core_pd_logic2_r[i] <= core_pd_logic2_en[i] | (~core_pd_logic2_dis[i]);
     end
  end   
end

always @(posedge clk or posedge rst_a)
begin:core_pd_mem_r_PROC
  if(rst_a == 1'b1)begin
      core_pd_mem_r[i] <= 1'b`ARCSYNC_PMU_RESET_PMODE;
  end 
  else begin
     if(core_pd_mem_en[i] | core_pd_mem_dis[i])begin
      core_pd_mem_r[i] <= core_pd_mem_en[i] | (~core_pd_mem_dis[i]);
     end
  end   
end

always @(posedge clk or posedge rst_a)
begin:core_pwr_down_req_r_PROC
  if(rst_a == 1'b1)begin
      core_pwr_down_r[i] <= 1'b`ARCSYNC_PMU_RESET_PMODE;
  end 
  else begin
     if(core_pwr_down_en[i] | core_pwr_down_dis[i])begin
      core_pwr_down_r[i] <= core_pwr_down_en[i] | (~core_pwr_down_dis[i]);
     end
  end   
end

assign core_isolate_n[i] = test_mode ? ~iso_override : ~core_pd_isolate_r[i];
assign core_isolate[i]   = test_mode ? iso_override : core_pd_isolate_r[i];
assign core_pd_logic1[i]        = test_mode ? 1'b0 : core_pd_logic1_r[i];
assign core_pd_logic2[i]        = test_mode ? 1'b0 : core_pd_logic2_r[i];
assign core_pd_logic[i]        = test_mode ? 1'b0 : core_pd_logic_r[i];
assign core_pd_mem[i]          = test_mode ? 1'b0 : core_pd_mem_r[i]; 

always @(posedge clk or posedge rst_a)
begin:core_pu_rst_r_PROC
  if(rst_a == 1'b1)begin
      core_pu_rst_r[i]  <= 1'b0;
  end else begin
      core_pu_rst_r[i]  <= core_pu_out_rst[i];
  end
end

assign core_pwr_down[i] = test_mode ? 1'b0 : core_pwr_down_r[i];
assign core_pu_rst[i] = test_mode ? rst_a : core_pu_rst_r[i];


//return the power up/down status
always_comb
begin //{
   seq_status[i] = 1'b0;
if(core_power_sta_cur[i] != PM_IDLE)
  begin
   seq_status[i] = 1'b1;
  end
end //}

end//}





//-------------------------------------------------------------------------------------------------------
// Properties
//-------------------------------------------------------------------------------------------------------
`ifdef FORMAL_ASSERT_ON
  `include "prop_arcsync_pmu_ctrl.sv"
`endif


endmodule
