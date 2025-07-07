// Library ARC_Trace-3.0.999999999


// Copyright (C) 2012-2013 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary
// work of Synopsys, Inc., and is fully protected under copyright and
// trade secret laws. You may not view, use, disclose, copy, or distribute
// this file or any information contained herein except pursuant to a
// valid written license from Synopsys, Inc.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
//   rtt_<prefix>_prdcr_regs
//
// ===========================================================================
//
// Description:
//  Contains the programming registers of producers
//  can support 1,2 or 4 core configurations
//
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o rtt_<prefix>_prdcr_reg.vpp
//
// ===========================================================================



`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"
module npuarc_rtt_small_prdcr_regs
( rtt_clk,
  rst_a, //active low reset
  rtt_addr,
  rtt_dataw ,
  rtt_write,
  rtt_read,
  freeze_status,
  pr0_rtt_datar,
  pr0_wp_val,
  pr0_wp_hit,
  pr0_src_en,
  pr0_dsm_en,
  pr0_filter_type,
  pr0_addr_filter0_start,
  pr0_addr_filter0_stop,
  pr0_addr_filter1_start,
  pr0_addr_filter1_stop,
  pr0_addr_filter2_start,
  pr0_addr_filter2_stop,
  pr0_addr_filter3_start,
  pr0_addr_filter3_stop,
  pr0_trigger_reg,
  pr0_cti_ctrl_en,
  pr0_atid,
  pr0_syncrfr,
  rtt_flush_command,
  flush_done,
//extras from common regs
  pr0_ds_en,
  rtt_pr_sel,
  rtt_time_stamp_en,
  rtt_dbgr_msgs_en,
  rtt_freeze_cntrl,
  pr0_bhth,
  pr0_csts_en,
//  pr0_evti_reg,
  pr0_vdswm_en,
  pr0_wp_enable,
  pr0_wp_status



  );

localparam BCR_OCMW_PP = !`npuarc_OCM ? 2'b00: ((`npuarc_b_d_w == 32) ? 2'b00 :
                                         (`npuarc_b_d_w == 64) ? 2'b01 :
                                         (`npuarc_b_d_w == 128)? 2'b10 : 2'b11);

  input                            rtt_clk; //RTT clock
  input                            rst_a;//Active Low Reset
  input  [`npuarc_RTT_ADDR8:0]            rtt_addr ;   // Producer Interface address connected to the aux if of
                                      // ARC
  input  [`npuarc_AUX_DATA-1:0]            rtt_dataw; // Register Write data
  input                             rtt_write;  // Register Write enable
  input  [`npuarc_FR_STATUS-1:0]           freeze_status;
  input                             rtt_read;   // Register Read Enable
  input  [`npuarc_PR_WP-1:0]               pr0_wp_val;
  input                             pr0_wp_hit;
  output [`npuarc_AUX_DATA-1:0]            pr0_rtt_datar;  // Register read data
  output [2-2:0]          pr0_src_en ;
  output                            pr0_dsm_en;
  output  [24-1:0]          pr0_filter_type;
  output  [`npuarc_RTT_ADDR-1:0]           pr0_addr_filter0_start;
  output  [`npuarc_RTT_ADDR-1:0]           pr0_addr_filter0_stop;
  output  [`npuarc_RTT_ADDR-1:0]           pr0_addr_filter1_start;
  output  [`npuarc_RTT_ADDR-1:0]           pr0_addr_filter1_stop;
  output  [`npuarc_RTT_ADDR-1:0]           pr0_addr_filter2_start;
  output  [`npuarc_RTT_ADDR-1:0]           pr0_addr_filter2_stop;
  output  [`npuarc_RTT_ADDR-1:0]           pr0_addr_filter3_start;
  output  [`npuarc_RTT_ADDR-1:0]           pr0_addr_filter3_stop;
  output  [`npuarc_RTT_TRG-1:0]            pr0_trigger_reg;
  output                            pr0_cti_ctrl_en;
  output  [`npuarc_ATID_WDT-1:0]           pr0_atid;
  output  [`npuarc_SYNCRFR_WDT-1:0]        pr0_syncrfr;
  output                            rtt_flush_command;
  input                             flush_done;
  output                            pr0_ds_en;
  output                            rtt_pr_sel;
  output                            rtt_time_stamp_en;
  output                            rtt_dbgr_msgs_en;
  output                            rtt_freeze_cntrl;
  output  [2:0]                     pr0_bhth;
  output                            pr0_csts_en;
  output                            pr0_vdswm_en;
  output  [`npuarc_PR_WP-1:0]              pr0_wp_enable;
  output  [`npuarc_PR_WP-1:0]              pr0_wp_status;
//nets declarations
  reg [`npuarc_AUX_DATA-1:0]               pr0_rtt_datar;
   //filters
   wire  prdcr0_bnk_en;
   //filter registers
   reg  [`npuarc_RTT_ADDR-1:0]             pr0_addr_filter0_start;
   reg  [`npuarc_RTT_ADDR-1:0]             pr0_addr_filter0_stop;
   reg  [`npuarc_RTT_ADDR-1:0]             pr0_addr_filter1_start;
   reg  [`npuarc_RTT_ADDR-1:0]             pr0_addr_filter1_stop;
   reg  [`npuarc_RTT_ADDR-1:0]             pr0_addr_filter2_start;
   reg  [`npuarc_RTT_ADDR-1:0]             pr0_addr_filter2_stop;
   reg  [`npuarc_RTT_ADDR-1:0]             pr0_addr_filter3_start;
   reg  [`npuarc_RTT_ADDR-1:0]             pr0_addr_filter3_stop;
   reg  [`npuarc_RTT_TRG-1:0]              pr0_trigger_reg;
   reg                              pr0_cti_ctrl_en;
   reg  [`npuarc_ATID_WDT-1:0]             pr0_atid;
   reg  [`npuarc_SYNCRFR_WDT-1:0]          pr0_syncrfr;
   wire [`npuarc_AUX_DATA-1:0]             rtt_syncrfr_pad;
   reg                              rtt_flush_command;
   reg                              pr0_ds_en;
   reg  [2:0]                       pr0_bhth;
   reg                              pr0_csts_en;
   reg                              pr0_vdswm_en;
   reg  [24-1:0]              pr0_filter_type; //Producer0 type register
   wire  [`npuarc_PR_TYPE-1:0]               pr0_type;        //Producer0 type register

  reg   [2-2:0]       pr0_src_en ;
  reg            pr0_dsm_en ;

  reg [`npuarc_FR_STATUS-1:0]  pr0_freeze_status;
  reg [`npuarc_PR_WP-1:0]      pr0_wp_status_r;
  wire [`npuarc_PR_WP-1:0]      pr0_wp_status;
  reg                   pr0_wp_hit_r;
  reg [`npuarc_PR_WP-1:0]      pr0_wp_enable;

reg rtt_freeze;
reg rtt_freeze_cntrl;
reg rtt_pr_sel;
reg rtt_dbgr_msgs_en;
reg rtt_time_stamp_en;
generate
if (`npuarc_SYNCRFR_WDT != 32) begin:_pad_1_SYNCRFR_REG_ADDR
 assign rtt_syncrfr_pad = {{(32-`npuarc_SYNCRFR_WDT){1'b0}},pr0_syncrfr};
end
else begin:_pad_0_SYNCRFR_REG_ADDR
 assign rtt_syncrfr_pad = pr0_syncrfr;
end
endgenerate


wire [`npuarc_BCR-1:0] rtt_bcr;
wire ctrl_bnk_en;
 assign ctrl_bnk_en =  ((rtt_addr[8:5] == 4'b0000) && (rtt_read || rtt_write )); //0x000 - 0x01F

 // producer bank enable 0
// spyglass disable_block SelfDeterminedExpr-ML

 assign prdcr0_bnk_en = ((rtt_addr[8:6] == 3'b001) && (rtt_read || rtt_write )); //0x040 - 0x07F
// spyglass enable_block SelfDeterminedExpr-ML

 assign rtt_bcr = {2'd0, 1'b0, BCR_OCMW_PP,2'd1,1'b0,1'b`npuarc_RTT_CORESIGHT_OPTION,1'b`npuarc_HAS_NEXUS_IF,`npuarc_NEXUS_MSEO_WDT,`npuarc_MDO_PORTS,`npuarc_OCM,`npuarc_INT_MEM,`npuarc_NUM_PRDCR,6'd`npuarc_RTT_VERSION};


// Producer Select Register
always @ (posedge rtt_clk or posedge rst_a)
begin : CTRL_RTT_PR_SEL_PROC
  if (rst_a == 1'b1) begin
    rtt_pr_sel <= 1'b0;
  end // end if of reset
  else if ((rtt_addr[4:0] == `npuarc_RTT_PR_SEL) && rtt_write && ctrl_bnk_en) begin
     rtt_pr_sel <= rtt_dataw[0] ;
  end
end // end of CTRL_RTT_PR_SEL

// RTT Freeze register
always @ (posedge rtt_clk or posedge rst_a)
begin : CTRL_RTT_FREEZE_PROC
  if (rst_a == 1'b1) begin
    rtt_freeze <= 1'b0;
  end // end if of reset
  else begin

    rtt_freeze <= rtt_freeze_cntrl && (|freeze_status[12:0]);

  end
end // end of CTRL_RTT_FREEZE

// RTT Freeze Control Register
always @ (posedge rtt_clk or posedge rst_a)
begin : CTRL_RTT_FREEZE_CNTRL_PROC
  if (rst_a == 1'b1) begin
    rtt_freeze_cntrl <= 1'b0;
  end // end if of reset
  else if ((rtt_addr[4:0] == `npuarc_RTT_FREEZE_CTRL) && rtt_write && ctrl_bnk_en) begin
    rtt_freeze_cntrl <= rtt_dataw[0];
  end //
end // end of CTRL_RTT_FREEZE_CNTRL


//RTT Time Stamp Register
always @ (posedge rtt_clk or posedge rst_a)
begin : CTRL_RTT_TIME_STAMP_PROC
  if (rst_a == 1'b1) begin
    rtt_time_stamp_en <= 1'b0;
  end // end if of reset
  else if ((rtt_addr[4:0] == `npuarc_RTT_TST) && rtt_write && ctrl_bnk_en) begin
     rtt_time_stamp_en <= rtt_dataw[0];
  end
end

//RTT Debugger messages enable register
always @ (posedge rtt_clk or posedge rst_a)
begin : CTRL_RTT_DBGR_MSGS_EN_PROC
  if (rst_a == 1'b1) begin
    rtt_dbgr_msgs_en <= 1'b0;
  end // end if of reset
  else if ((rtt_addr[4:0] == `npuarc_RTT_DBGR_MSGS_EN) && rtt_write && ctrl_bnk_en) begin
     rtt_dbgr_msgs_en <= rtt_dataw[0];
  end
end

// Flush register
always @ (posedge rtt_clk or posedge rst_a)
begin : CTRL_RTT_FLUSH_COMMAND_PROC
  if (rst_a == 1'b1) begin
    rtt_flush_command <= 1'b0;
  end  // end of reset
  else if (flush_done) begin
    rtt_flush_command <= 1'b0;
  end
  else if ((rtt_addr[4:0] == `npuarc_FLUSH_COMMAND) && rtt_write  && ctrl_bnk_en && (rtt_dataw[0] == 1'b1)) begin
    rtt_flush_command <= 1'b1;
  end // end of flush command write register
end // end of flush register

//Data filtets programming
//data filter0




//data filter1




wire [24-1:0] rtt_dataw_filter_type_pad;
assign rtt_dataw_filter_type_pad = {{((8-`npuarc_RTT_NUM_FILTERS)*3){1'b0}},rtt_dataw[`npuarc_RTT_NUM_FILTERS*3-1:0]};




// leda DFT_022 off
// LMD: Incomplete case statement
// LJ: the case statement is put under the sequential process and
//     will not make any harm for not putting the default statement.
//     A Default statement in this case will insert an extra 32 registers

//Filter Register

// leda W71 off

always @ (posedge rtt_clk or posedge rst_a)
begin : PRODUCER0_FILTER_PROC
  if (rst_a == 1'b1) begin
    pr0_addr_filter0_start <= 32'h00 ;
    pr0_addr_filter0_stop  <= 32'hFFFF_FFFF;
    pr0_addr_filter1_start <= 32'h00 ;
    pr0_addr_filter1_stop  <= 32'hFFFF_FFFF;
    pr0_addr_filter2_start <= 32'h00 ;
    pr0_addr_filter2_stop  <= 32'hFFFF_FFFF;
    pr0_addr_filter3_start <= 32'h00 ;
    pr0_addr_filter3_stop  <= 32'hFFFF_FFFF;
// leda B_3208 off
// leda W163 off
    pr0_filter_type        <= {24{1'b0}};
// leda W163 on
// leda B_3208 on
    pr0_trigger_reg        <= {`npuarc_RTT_TRG{1'b0}};
    pr0_cti_ctrl_en        <= 1'b0;
    pr0_atid               <= {{(`npuarc_ATID_WDT-1'b1){1'b0}},1'b1};
//`if(`APB_ATB_CLK_INTERFACE == 1)
//    atid_en_sync           <= 1'b0;
//`endif
    pr0_syncrfr            <= {`npuarc_SYNCRFR_WDT{1'b0}};
    pr0_ds_en              <= 1'b0;
    pr0_bhth               <= 3'b0;
    pr0_csts_en            <= 1'b0;
  end  // end of reset
else if ((prdcr0_bnk_en == 1'b1)  && (rtt_write == 1'b1)) begin
      if(rtt_addr[5:0] == `npuarc_ADDR_FILTER_START0) begin
         pr0_addr_filter0_start  <= rtt_dataw;
      end
      if(rtt_addr[5:0] == `npuarc_ADDR_FILTER_STOP0) begin
         pr0_addr_filter0_stop  <= rtt_dataw;
      end
      if(rtt_addr[5:0] == `npuarc_ADDR_FILTER_START1) begin
         pr0_addr_filter1_start  <= rtt_dataw;
      end
      if(rtt_addr[5:0] == `npuarc_ADDR_FILTER_STOP1) begin
         pr0_addr_filter1_stop  <= rtt_dataw;
      end
      if(rtt_addr[5:0] == `npuarc_ADDR_FILTER_START2) begin
         pr0_addr_filter2_start  <= rtt_dataw;
      end
      if(rtt_addr[5:0] == `npuarc_ADDR_FILTER_STOP2) begin
         pr0_addr_filter2_stop  <= rtt_dataw;
      end
      if(rtt_addr[5:0] == `npuarc_ADDR_FILTER_START3) begin
         pr0_addr_filter3_start  <= rtt_dataw;
      end
      if(rtt_addr[5:0] == `npuarc_ADDR_FILTER_STOP3) begin
         pr0_addr_filter3_stop  <= rtt_dataw;
      end
      if (rtt_addr[5:0] == `npuarc_FILTER_TYPE) begin
            pr0_filter_type         <= rtt_dataw_filter_type_pad;
      end
      if (rtt_addr[5:0] == `npuarc_TRIGGER_REG) begin
            pr0_trigger_reg         <= rtt_dataw[`npuarc_RTT_TRG-1:0];
      end
      if (rtt_addr[5:0] == `npuarc_CTIEN_REG_ADDR) begin
            pr0_cti_ctrl_en         <= rtt_dataw[0];
      end
      if (rtt_addr[5:0] == `npuarc_ATID_REG_ADDR) begin
            pr0_atid                <= rtt_dataw[`npuarc_ATID_WDT-1:0];
      end
      if (rtt_addr[5:0] == `npuarc_SYNCRFR_REG_ADDR) begin
            pr0_syncrfr             <= rtt_dataw[`npuarc_SYNCRFR_WDT-1:0];
      end
      if (rtt_addr[5:0] == `npuarc_DSEN_REG_ADDR) begin
        {pr0_bhth,pr0_ds_en}    <= {rtt_dataw[4:2],rtt_dataw[0]};
      end
      if (rtt_addr[5:0] == `npuarc_CSTSEN_REG_ADDR) begin
        pr0_csts_en             <= rtt_dataw[0];
      end
end // end of else-if statement
end // end of always
// leda W71 on

// leda DFT_022 on
// Producer Type Register

assign pr0_type =
                  2'b00;


//Producer Source Enable
always @ (posedge rtt_clk or posedge rst_a)
begin : PRODUCER0_SRC_ENABLE_PROC
  if (rst_a == 1'b1) begin
     pr0_src_en   <= 1'b1;
     pr0_dsm_en   <= 1'b1;
    pr0_vdswm_en  <= 1'b1;


  end
  else if ((prdcr0_bnk_en == 1'b1) && (rtt_addr[5:0] ==`npuarc_PR_SRC_EN)
           && (rtt_write == 1'b1)) begin
     pr0_src_en   <= rtt_dataw[0];
     pr0_dsm_en   <=  rtt_dataw[6];
     pr0_vdswm_en <=  rtt_dataw[7];
  end
end  //end of always
// producer0 Buffer status register
always @ (posedge rtt_clk or posedge rst_a)
begin : PRODUCER0_BUF_ENABLE_PROC
  if (rst_a == 1'b1) begin
    pr0_freeze_status <= 13'b00;
  end
  else begin
    pr0_freeze_status <= freeze_status;
  end
end // end of always PRODUCER0_BUF_ENABLE

// producer0  Watchpoint status register
always @ (posedge rtt_clk or posedge rst_a)
begin : PRODUCER0_WP_STATUS_PROC
  if (rst_a == 1'b1) begin
    pr0_wp_status_r <= 8'h00;
  end
  else if (pr0_wp_hit) begin
    pr0_wp_status_r <= pr0_wp_val;
  end
end // end of always PRODUCER0_WP_STATUS

always @ (posedge rtt_clk or posedge rst_a)
begin : PRODUCER0_WP_HIT_R_PROC
  if (rst_a == 1'b1) begin
   pr0_wp_hit_r  <= 1'b0;
  end
//  else if (pr0_wp_hit) begin
  else begin
   pr0_wp_hit_r  <= pr0_wp_hit;
  end
end // end of always PRODUCER0_WP_STATUS

assign pr0_wp_status = pr0_wp_hit_r ? pr0_wp_status_r : 8'b00;

// producer0  Watchpoint Enable staus register
always @ (posedge rtt_clk or posedge rst_a)
begin : PRODUCER0_WP_ENABLE_PROC
  if (rst_a == 1'b1) begin
    pr0_wp_enable <= 8'hFF;
  end
  else if  ((prdcr0_bnk_en == 1'b1) && (rtt_addr[5:0] ==`npuarc_PR_WP_ENABLE)
            && (rtt_write == 1'b1)) begin
    pr0_wp_enable <= rtt_dataw [7:0];
  end
end // end of always PRODUCER0_WP_ENABLE

wire [`npuarc_AUX_DATA-1:0] rtt_bcr_pad;
generate
if (`npuarc_BCR != 32) begin:_pad_1_RTT_BCR
       assign rtt_bcr_pad = {{(32-`npuarc_BCR){1'b0}},rtt_bcr} ;
end
else begin:_pad_0_RTT_BCR
       assign rtt_bcr_pad = rtt_bcr;
end
endgenerate

wire [`npuarc_AUX_DATA-1:0] pr0_filter_type_pad;
       assign pr0_filter_type_pad = {8'b0,{((8-`npuarc_RTT_NUM_FILTERS)*3){1'b0}},pr0_filter_type[`npuarc_RTT_NUM_FILTERS*3-1:0]};

// spyglass disable_block SelfDeterminedExpr-ML
//Producer0 register Reads
always @*
begin : PR0_REG_READ_PROC

  if (rtt_addr[8:5] == 4'b00)
  begin
    case (rtt_addr[4:0])
       `npuarc_RTT_BCR          :      pr0_rtt_datar = rtt_bcr_pad ;
       `npuarc_RTT_PR_SEL       :      pr0_rtt_datar = {31'b0,       rtt_pr_sel};
       `npuarc_RTT_FREEZE       :      pr0_rtt_datar = {31'b0,       rtt_freeze};
       `npuarc_RTT_FREEZE_CTRL  :      pr0_rtt_datar = {31'b0, rtt_freeze_cntrl};
       `npuarc_RTT_TST          :      pr0_rtt_datar = {31'b0,rtt_time_stamp_en};
       `npuarc_RTT_DBGR_MSGS_EN :      pr0_rtt_datar = {31'b0, rtt_dbgr_msgs_en};
       `npuarc_FLUSH_COMMAND    :      pr0_rtt_datar = {31'b0,rtt_flush_command};
       default : pr0_rtt_datar = 32'h0;
    endcase
  end
  else
  if (rtt_addr[8:6] == 3'b001) begin
      case (rtt_addr[5:0])
          `npuarc_ADDR_FILTER_START0      :   pr0_rtt_datar = pr0_addr_filter0_start ;
          `npuarc_ADDR_FILTER_STOP0       :   pr0_rtt_datar = pr0_addr_filter0_stop  ;
          `npuarc_ADDR_FILTER_START1      :   pr0_rtt_datar = pr0_addr_filter1_start ;
          `npuarc_ADDR_FILTER_STOP1       :   pr0_rtt_datar = pr0_addr_filter1_stop  ;
          `npuarc_ADDR_FILTER_START2      :   pr0_rtt_datar = pr0_addr_filter2_start ;
          `npuarc_ADDR_FILTER_STOP2       :   pr0_rtt_datar = pr0_addr_filter2_stop  ;
          `npuarc_ADDR_FILTER_START3      :   pr0_rtt_datar = pr0_addr_filter3_start ;
          `npuarc_ADDR_FILTER_STOP3       :   pr0_rtt_datar = pr0_addr_filter3_stop  ;
          `npuarc_TRIGGER_REG             :   pr0_rtt_datar = {{(32-`npuarc_RTT_TRG){1'b0}},pr0_trigger_reg};
          `npuarc_CTIEN_REG_ADDR          :   pr0_rtt_datar = {31'b0, pr0_cti_ctrl_en};
          `npuarc_ATID_REG_ADDR           :   pr0_rtt_datar = {{(32-`npuarc_ATID_WDT){1'b0}},pr0_atid};
          `npuarc_DSEN_REG_ADDR           :   pr0_rtt_datar = {27'b0, pr0_bhth,1'b0,pr0_ds_en};
          `npuarc_SYNCRFR_REG_ADDR        :   pr0_rtt_datar = rtt_syncrfr_pad;
          `npuarc_CSTSEN_REG_ADDR         :   pr0_rtt_datar = {31'b0, pr0_csts_en};

          `npuarc_PRDCTYPE                :   pr0_rtt_datar = {30'b0,pr0_type}; 
          `npuarc_FILTER_TYPE             :   pr0_rtt_datar = pr0_filter_type_pad  ;
          `npuarc_PR_SRC_EN               :   pr0_rtt_datar ={24'b0,pr0_vdswm_en,pr0_dsm_en,5'b0, pr0_src_en};
          `npuarc_PR_FREEZE_STATUS        :   pr0_rtt_datar = {19'b0,pr0_freeze_status};
          `npuarc_PR_WP_STATUS            :   pr0_rtt_datar = {24'b0,pr0_wp_status};
          `npuarc_PR_WP_ENABLE            :   pr0_rtt_datar =  {24'b0,pr0_wp_enable};
           default : pr0_rtt_datar = 32'h0;
      endcase
   end
   else  begin
     pr0_rtt_datar = 32'h0;
   end
end //end of always
// spyglass enable_block SelfDeterminedExpr-ML








endmodule // end of progamming interface module
