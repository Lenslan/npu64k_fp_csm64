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

// ===========================================================================
//
// Description:
//
// 1. generate UPF control signal to the related module
// 2. support the PDM interface from vpx PDM
//
// ===========================================================================
////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//`if ARCSYNC_PDM_HAS_FG ==1 
//  `let PD1_NUM = 3   //the number of pd1_sfx:pd1_pd,_pd1_fg,pd1_mem//
//`else
//  `let PD1_NUM =2
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////
`include "arcsync_defines.v"

module arcsync_vpx_pmu_ctrl #(
parameter PD1_NUM      = `ARCSYNC_PDM_HAS_FG + 2,        
parameter CORE_NUM     = 4              ,
parameter PUCNT_W      = 16             ,
parameter RSTCNT_W     = 8              ,
parameter PDCNT_W      = 8              ,
parameter ACT_PUCNT_W  = PUCNT_W + 8   ,
parameter ACT_RSTCNT_W = RSTCNT_W + 3  ,
parameter ACT_PDCNT_W  = PDCNT_W + 8   
)
(
  // generate regular power interface
  input   logic  [CORE_NUM-1:0]      core_pd1_pd_req,
  input   logic  [CORE_NUM-1:0]      core_pd2_pd_req,
  output  logic  [CORE_NUM-1:0]      core_pd1_pd_ack,
  output  logic  [CORE_NUM-1:0]      core_pd2_pd_ack,
  output  logic  [CORE_NUM-1:0]      core_pd1_isolate_n,
  output  logic  [CORE_NUM-1:0]      core_pd2_isolate_n,
  output  logic  [CORE_NUM-1:0]      core_pd1_isolate,
  output  logic  [CORE_NUM-1:0]      core_pd2_isolate,
  output  logic  [CORE_NUM-1:0]      core_pd1_pd_mem,
  output  logic  [CORE_NUM-1:0]      core_pd1_pd,
  output  logic  [CORE_NUM-1:0]      core_pd1_pd_fg,
  output  logic  [CORE_NUM-1:0]      core_pd2_pd,

  input   logic  [CORE_NUM-1:0]      core_pu_req,  //core_arcsync_pu_req[CORE_NUM]
  output  logic  [CORE_NUM-1:0]      core_pu_ack,
  output  logic  [CORE_NUM-1:0]      core_pu_rst,
  output  logic  [CORE_NUM-1:0]      seq_status,     //indicates whether is in power up/down sequence

  input   logic    [PUCNT_W-1:0]  pu2iso_cnt,   // count from power-up to isolation release
  input   logic    [RSTCNT_W-1:0] pu2rst_cnt,   // count from power-up to reset release
  input   logic    [PDCNT_W-1:0]  iso2pd_cnt,   // count from isolation enabled to power-down

  // global signal
  input   logic        iso_override,  // override iso control value in test_mode
  input   logic        test_mode,     // bypass pd/iso control signal
  input   logic        clk,           // gated unit clock
  input   logic        rst_a          // async reset
);

///////////////////////////////////////////////////////////////////////////////
//                                                                           //
//                    local parameters definition                            //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////
  parameter PM_IDLE    = 3'b000;
  parameter PM_PD0     = 3'b001;
  parameter PM_PD1     = 3'b010;
  parameter PM_PU0     = 3'b011;
  parameter PM_PU1     = 3'b100;
  parameter PM_ACK     = 3'b101;

///////////////////////////////////////////////////////////////////////////////
//                                                                           //
//                    local wires and regs declaration                       //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////

//UPF related signal
reg             core_pd1_isolate_en[CORE_NUM];
reg             core_pd1_isolate_r[CORE_NUM];
reg             core_pd2_isolate_en[CORE_NUM];
reg             core_pd2_isolate_r[CORE_NUM];

reg   [PD1_NUM -1:0] core_pd1_pd_en[CORE_NUM];
reg   [PD1_NUM -1:0] core_pd1_pd_r[CORE_NUM];
reg                  core_pd2_pd_en[CORE_NUM];
reg                  core_pd2_pd_r[CORE_NUM];

reg                  core_pd1_out_ack[CORE_NUM];
reg                  core_pd1_ack_r[CORE_NUM];
reg                  core_pd2_out_ack[CORE_NUM];
reg                  core_pd2_ack_r[CORE_NUM];

//FSM
wire            core_pd_req_or[CORE_NUM];
reg    [2:0]    core_power_sta_cur[CORE_NUM];
reg    [2:0]    core_power_sta_nxt[CORE_NUM];
//UPF related signal
reg             core_pd_isolate_dis[CORE_NUM];
reg             core_pu_rst_r[CORE_NUM];

reg    [PD1_NUM -1 : 0]          core_pd1_pd_pd_dis[CORE_NUM];
reg                              core_pd2_pd_pd_dis[CORE_NUM];
reg             core_pu_out_rst[CORE_NUM];
reg             core_pu_out_ack[CORE_NUM];
reg             core_pu_ack_r[CORE_NUM];
//power up counter
reg    [ACT_PUCNT_W-1:0]   core_pu2iso_cnt_r[CORE_NUM];
wire   [ACT_PUCNT_W-1:0]   core_pu2iso_cnt_nxt[CORE_NUM];
reg             core_pu2iso_cnt_dec[CORE_NUM];
reg             core_pu2iso_cnt_load[CORE_NUM];  
//power up reset counter
reg    [ACT_RSTCNT_W-1:0]  core_pu2rst_cnt_r[CORE_NUM];
wire   [ACT_RSTCNT_W-1:0]  core_pu2rst_cnt_nxt[CORE_NUM];
reg             core_pu2rst_cnt_dec[CORE_NUM];
reg             core_pu2rst_cnt_load[CORE_NUM];  
//power down counter
reg    [ACT_PDCNT_W-1:0]   core_iso2pd_cnt_r[CORE_NUM];
wire   [ACT_PDCNT_W-1:0]   core_iso2pd_cnt_nxt[CORE_NUM];
reg             core_iso2pd_cnt_dec[CORE_NUM];
reg             core_iso2pd_cnt_load[CORE_NUM]; 
//add this signal compare to v2
reg       [1:0] core_pdsq_cnt_nxt[CORE_NUM];
reg       [1:0] core_pdsq_cnt_r[CORE_NUM];

///////////////////////////////////////////////////////////////////////////////
//                                                                           //
//                             main code                                     //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////

wire [ACT_PUCNT_W-1:0]  eff_pu2iso_cnt = {pu2iso_cnt, 8'b111};
wire [ACT_RSTCNT_W-1:0] eff_pu2rst_cnt = {pu2rst_cnt, 3'b111};
wire [ACT_PDCNT_W-1:0]  eff_iso2pd_cnt = {iso2pd_cnt, 8'b111};

for(genvar i = 0; i < CORE_NUM; i++)//{
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

always @(posedge clk or posedge rst_a)
begin:core_pu2iso_cnt_r_PROC
  if(rst_a == 1'b1)begin
      core_pu2iso_cnt_r[i] <= {ACT_PUCNT_W{1'b0}};
  end else begin
      core_pu2iso_cnt_r[i] <= core_pu2iso_cnt_nxt[i];
  end
end

always @(posedge clk or posedge rst_a)
begin:core_pu2rst_cnt_r_PROC
  if(rst_a == 1'b1)begin
      core_pu2rst_cnt_r[i] <= {ACT_RSTCNT_W{1'b0}};
  end else begin
      core_pu2rst_cnt_r[i] <= core_pu2rst_cnt_nxt[i];
  end
end

always @(posedge clk or posedge rst_a)
begin:core_iso2pd_cnt_r_PROC
  if(rst_a == 1'b1)begin
      core_iso2pd_cnt_r[i] <= {ACT_PDCNT_W{1'b0}};
  end else begin
      core_iso2pd_cnt_r[i] <= core_iso2pd_cnt_nxt[i];
  end
end

always @(posedge clk or posedge rst_a)
begin:core_pdsq_cnt_r_PROC
  if(rst_a == 1'b1)begin
      core_pdsq_cnt_r[i] <= 2'b0;
  end else begin
      core_pdsq_cnt_r[i] <= core_pdsq_cnt_nxt[i];
  end
end

//FSM for power down/up management
always @(posedge clk or posedge rst_a)
begin:core_power_sta_cur_PROC
  if(rst_a == 1'b1)begin
      core_power_sta_cur[i] <= 3'b0;
  end else begin
      core_power_sta_cur[i] <= core_power_sta_nxt[i];
  end
end

assign core_pd_req_or[i] = 1'b0 | core_pd1_pd_req[i] | core_pd2_pd_req[i] ;

always @*
begin:core_FSM_PROC
  core_power_sta_nxt[i]   = core_power_sta_cur[i];
  core_pd_isolate_dis[i]  = 1'b0;
  core_pu_out_rst[i]      = 1'b0;
  core_pu_out_ack[i]      = 1'b0;
  core_pu2iso_cnt_load[i] = 1'b0;
  core_pu2iso_cnt_dec[i]  = 1'b0;
  core_pu2rst_cnt_load[i] = 1'b0;
  core_pu2rst_cnt_dec[i]  = 1'b0;
  core_iso2pd_cnt_load[i] = 1'b0;
  core_iso2pd_cnt_dec[i]  = 1'b0;
  core_pdsq_cnt_nxt[i]    = core_pdsq_cnt_r[i];
  core_pd1_isolate_en[i] = 1'b0;
  core_pd2_isolate_en[i] = 1'b0;
  core_pd1_pd_en[i][PD1_NUM -1:0]      = {PD1_NUM{1'b0}};
  core_pd1_pd_pd_dis[i][PD1_NUM -1:0]  = {PD1_NUM{1'b0}};
  core_pd2_pd_en[i]      = 1'b0;
  core_pd2_pd_pd_dis[i]  = 1'b0;
  core_pd1_out_ack[i]    = 1'b0;
  core_pd2_out_ack[i]    = 1'b0;

  case(core_power_sta_cur[i])
    PM_IDLE:
    begin
      if(core_pd_req_or[i])begin
          core_power_sta_nxt[i] = PM_PD0;
          core_iso2pd_cnt_load[i] = 1'b1;
          core_pdsq_cnt_nxt[i] = 1; // power down sequence//indicates sequence from pd_mem to pd_pd//
      end
      if(core_pu_req[i])begin
          core_power_sta_nxt[i] = PM_PU0;
          core_pdsq_cnt_nxt[i] =  PD1_NUM; // power up sequence//////////////
      end
    end
    PM_PD0:
    begin
      core_pd1_isolate_en[i] = core_pd1_pd_req[i];
      core_pd2_isolate_en[i] = core_pd2_pd_req[i];
      core_iso2pd_cnt_dec[i] = (|core_iso2pd_cnt_r[i]);
      if(~(|core_iso2pd_cnt_r[i]))begin
         core_power_sta_nxt[i] = PM_PD1;
         core_iso2pd_cnt_load[i] = 1'b1;
         core_pdsq_cnt_nxt[i] = core_pdsq_cnt_r[i] - 1;
      end
    end
    PM_PD1:
    begin                                    
      core_iso2pd_cnt_dec[i] = (|core_iso2pd_cnt_r[i]);
            core_pd1_pd_en[i] [PD1_NUM -1] = core_pd1_pd_req[i];
            core_pd2_pd_en[i] = core_pd2_pd_req[i];

       if(~(|core_iso2pd_cnt_r[i]) & ~(|core_pdsq_cnt_r[i]))begin
         core_power_sta_nxt[i] = PM_ACK;
         //`if(`PD1_NUM == 3) vpp_2_sv
         core_pd1_pd_en[i][0] = core_pd1_pd_req[i];
         core_pd1_pd_en[i][1] = core_pd1_pd_req[i];
       end
    end
    PM_PU0:
    begin
      core_pu_out_rst[i] = 1'b1;
      core_pu2iso_cnt_dec[i] = (|core_pu2iso_cnt_r[i]);
      if(~(|core_pu2iso_cnt_r[i]))begin
        if (~(|core_pdsq_cnt_r[i])) begin
          core_pu2rst_cnt_load[i]  = 1'b1;
          core_power_sta_nxt[i] = PM_PU1;
        end
        else begin
          core_pdsq_cnt_nxt[i] = core_pdsq_cnt_r[i] - 1;
          core_pu2iso_cnt_load[i]  = 1'b1;
         //`if(`PD1_NUM == 3) vpp_2_sv
          if (core_pdsq_cnt_r[i] == 2'd3) begin
            core_pd1_pd_pd_dis[i][0] = 1'b1;
          end
          if (core_pdsq_cnt_r[i] == 2'd2) begin
            core_pd1_pd_pd_dis[i][1] = 1'b1;
          end
          if (core_pdsq_cnt_r[i] == 2'd1) begin
            core_pd1_pd_pd_dis[i][2] = 1'b1;
          end
//               `for(`n = 0; `n < `PD1_NUM; `n++)//{
//          if (`s_pref::`p_pref::pdsq_cnt_r == `PD1_NUM - `n) begin
//            `s_pref::`p_pref::pd1_pd_pd_dis[`n] = 1'b1;
//          end
//               `endfor//}
          if (core_pdsq_cnt_r[i] == 2'b1) begin
            core_pd2_pd_pd_dis[i] = 1'b1;
          end          
        end
      end
    end      
    PM_PU1:
    begin
      core_pd_isolate_dis[i] = 1'b1;
      core_pu_out_rst[i] = (|core_pu2rst_cnt_r[i]);
      core_pu2rst_cnt_dec[i] = (|core_pu2rst_cnt_r[i]);
      if(~(|core_pu2rst_cnt_r[i]))begin
          core_power_sta_nxt[i] = PM_ACK;
      end
    end
    PM_ACK:
    begin
      core_pd1_out_ack[i] = core_pd1_pd_req[i];
      core_pd2_out_ack[i] = core_pd2_pd_req[i];
      core_pu_out_ack[i] = core_pu_req[i];
      if(~(core_pd_req_or[i] | core_pu_req[i]))begin
          core_power_sta_nxt[i] = PM_IDLE;
      end    
    end
    default:
    begin
      core_power_sta_nxt[i]   = core_power_sta_cur[i];
      core_pd_isolate_dis[i]  = 1'b0;
      core_pu_out_rst[i]      = 1'b0;
      core_pu_out_ack[i]      = 1'b0;
      core_pu2iso_cnt_load[i] = 1'b0;
      core_pu2iso_cnt_dec[i]  = 1'b0;
      core_pu2rst_cnt_load[i] = 1'b0;
      core_pu2rst_cnt_dec[i]  = 1'b0;
      core_iso2pd_cnt_load[i] = 1'b0;
      core_iso2pd_cnt_dec[i]  = 1'b0;
      core_pdsq_cnt_nxt[i]    = core_pdsq_cnt_r[i];
      core_pd1_isolate_en[i] = 1'b0;
      core_pd2_isolate_en[i] = 1'b0;
      core_pd1_pd_en[i][PD1_NUM -1:0]      = {PD1_NUM{1'b0}};
      core_pd1_pd_pd_dis[i][PD1_NUM -1:0]  = {PD1_NUM{1'b0}};
      core_pd2_pd_en[i]      = 1'b0;
      core_pd2_pd_pd_dis[i]  = 1'b0;
      core_pd1_out_ack[i]    = 1'b0;
      core_pd2_out_ack[i]    = 1'b0;
    end
  endcase
end


//send UPF signal out
//pd1//
always @(posedge clk or posedge rst_a)
begin:core_pd1_isolate_r_PROC
  if(rst_a == 1'b1)begin
      core_pd1_isolate_r[i] <= 1'b0;
  end else if(core_pd1_isolate_en[i] | core_pd_isolate_dis[i])begin
      core_pd1_isolate_r[i] <= core_pd1_isolate_en[i] | (~core_pd_isolate_dis[i]);
  end
end 

always @(posedge clk or posedge rst_a)
begin:core_pd1_pd_r_PROC
  if(rst_a == 1'b1)begin
      core_pd1_pd_r[i] <= {PD1_NUM{1'b0}};
  end 
  else begin
  //`if(`PD1_NUM == 3) vpp_2_sv
     if(core_pd1_pd_en[i][0] | core_pd1_pd_pd_dis[i][0])begin
      core_pd1_pd_r[i][0] <= core_pd1_pd_en[i][0] | (~core_pd1_pd_pd_dis[i][0]);
     end
     if(core_pd1_pd_en[i][1] | core_pd1_pd_pd_dis[i][1])begin
      core_pd1_pd_r[i][1] <= core_pd1_pd_en[i][1] | (~core_pd1_pd_pd_dis[i][1]);
     end
     if(core_pd1_pd_en[i][PD1_NUM-1] | core_pd1_pd_pd_dis[i][PD1_NUM-1])begin
      core_pd1_pd_r[i][PD1_NUM-1] <= core_pd1_pd_en[i][PD1_NUM-1] | (~core_pd1_pd_pd_dis[i][PD1_NUM-1]);
     end
//         `for(`n = 0; `n < `PD1_NUM; `n++)
//     if(`s_pref::`p_pref::`d_pref::pd_en[`n] | `s_pref::`p_pref::`d_pref::pd_pd_dis[`n])begin
//      `s_pref::`p_pref::`d_pref::pd_r[`n] <= `s_pref::`p_pref::`d_pref::pd_en[`n] | (~`s_pref::`p_pref::`d_pref::pd_pd_dis[`n]);
//     end
//         `endfor
  end   
end

always @(posedge clk or posedge rst_a)
begin:core_pd1_ack_r_PROC
  if(rst_a == 1'b1)begin
      core_pd1_ack_r[i] <= 1'b0;
  end else begin
      core_pd1_ack_r[i] <= core_pd1_out_ack[i];
  end
end

assign core_pd1_isolate_n[i] = test_mode ? ~iso_override : ~core_pd1_isolate_r[i];
assign core_pd1_isolate[i]   = test_mode ? iso_override : core_pd1_isolate_r[i];
        // `if(`PD1_NUM == 3)
assign          core_pd1_pd[i]       = test_mode ? 1'b0 : core_pd1_pd_r[i][0];
assign          core_pd1_pd_fg[i]    = test_mode ? 1'b0 : core_pd1_pd_r[i][1];
assign          core_pd1_pd_mem[i]   = test_mode ? 1'b0 : core_pd1_pd_r[i][PD1_NUM-1];
assign core_pd1_pd_ack[i]  = core_pd1_ack_r[i];

//pd2//
always @(posedge clk or posedge rst_a)
begin:core_pd2_isolate_r_PROC
  if(rst_a == 1'b1)begin
      core_pd2_isolate_r[i] <= 1'b0;
  end else if(core_pd2_isolate_en[i] | core_pd_isolate_dis[i])begin
      core_pd2_isolate_r[i] <= core_pd2_isolate_en[i] | (~core_pd_isolate_dis[i]);
  end
end 

always @(posedge clk or posedge rst_a)
begin:core_pd2_pd_r_PROC
  if(rst_a == 1'b1)begin
      core_pd2_pd_r[i] <= 1'b0;
  end 
  else begin
     if(core_pd2_pd_en[i] | core_pd2_pd_pd_dis[i])begin
      core_pd2_pd_r[i] <= core_pd2_pd_en[i] | (~core_pd2_pd_pd_dis[i]);
     end
  end   
end

always @(posedge clk or posedge rst_a)
begin:core_pd2_ack_r_PROC
  if(rst_a == 1'b1)begin
      core_pd2_ack_r[i] <= 1'b0;
  end else begin
      core_pd2_ack_r[i] <= core_pd2_out_ack[i];
  end
end

assign core_pd2_isolate_n[i] = test_mode ? ~iso_override : ~core_pd2_isolate_r[i];
assign core_pd2_isolate[i]   = test_mode ? iso_override : core_pd2_isolate_r[i];
assign core_pd2_pd[i]        = test_mode ? 1'b0 : core_pd2_pd_r[i];       
assign core_pd2_pd_ack[i]  = core_pd2_ack_r[i];

always @(posedge clk or posedge rst_a)
begin:core_pu_ack_r_PROC
  if(rst_a == 1'b1)begin
      core_pu_rst_r[i]  <= 1'b0;
      core_pu_ack_r[i]  <= 1'b0;      
  end else begin
      core_pu_rst_r[i]  <= core_pu_out_rst[i];
      core_pu_ack_r[i]  <= core_pu_out_ack[i];      
  end
end

assign core_pu_ack[i] = core_pu_ack_r[i];
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

