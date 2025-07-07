
////////////////////////////////////////////////////////////////////////////////
//
//                  (C) COPYRIGHT 2017 - 2022 SYNOPSYS, INC.
//                            ALL RIGHTS RESERVED
//
//  This software and the associated documentation are confidential and
//  proprietary to Synopsys, Inc.  Your use or disclosure of this
//  software is subject to the terms and conditions of a written
//  license agreement between you, or your company, and Synopsys, Inc.
//
//  The entire notice above must be reproduced on all authorized copies.
//
// Description : npu_DWbb_bcm22_atv.v Verilog module for DWbb
//
// DesignWare IP ID: f1518104
//
////////////////////////////////////////////////////////////////////////////////



module npu_DWbb_bcm22_atv (
             clk_s,
             rst_s_n,
             event_s,

             clk_d,
             rst_d_n,
             event_d
             );

 parameter integer REG_EVENT    = 1;    // RANGE 0 to 1
 parameter integer F_SYNC_TYPE  = 2;    // RANGE 0 to 4
 parameter integer VERIF_EN     = 1;    // RANGE 0 to 4
 parameter integer PULSE_MODE   = 0;    // RANGE 0 to 3
 parameter integer SVA_TYPE     = 0;
 parameter integer TMR_CDC      = 0;

 localparam TMR_CDC_CC = (TMR_CDC == 0) ? TMR_CDC : 2;
 localparam CC_WIDTH = (TMR_CDC == 0) ? 1 : 3;
 localparam SYNC_ATV_WIDTH = 1;
 localparam F_SYNC_TYPE_P8 = F_SYNC_TYPE + 8;
`ifndef SYNTHESIS
`ifdef DWC_BCM_MSG_VERBOSITY
  localparam BCM_MSG_VERBOSITY = `DWC_BCM_MSG_VERBOSITY;
`else
  localparam BCM_MSG_VERBOSITY_DEF = 32'hfffffff1;

  `ifndef DWC_DISABLE_CDC_METHOD_REPORTING
    localparam BCM_MSG_VERBOSITY_TMP2 = 32'h00000004;
  `else
    localparam BCM_MSG_VERBOSITY_TMP2 = 32'h0;
  `endif

  localparam BCM_MSG_VERBOSITY = BCM_MSG_VERBOSITY_DEF |
               BCM_MSG_VERBOSITY_TMP2;
`endif
`endif

input  clk_s;                   // clock input for source domain
input  rst_s_n;                 // active low async. reset in clk_s domain
input  event_s;                 // event pulse input (active high event)

input  clk_d;                   // clock input for destination domain
input  rst_d_n;                 // active low async. reset in clk_d domain
output event_d;                 // event pulse output (active high event)

wire   next_tgl_event_s;
// Source register wiring
wire [CC_WIDTH-1:0]  tgl_event_cc;
wire   tgl_event_s;
wire [CC_WIDTH-1:0]  tgl_s_nfb_cdc;
wire   dw_sync_data_d;
wire   sync_event_out;    // history for edge detect
wire   next_event_d_q;    // event seen via edge detect (before registered)



`ifndef SYNTHESIS
  initial begin
    if (((F_SYNC_TYPE > 0)&&(F_SYNC_TYPE < 8))&&(BCM_MSG_VERBOSITY[2]==1'b1))
       $display("Information: *** Instance %m module is using the <Toggle Type Event Sychronizer (2)> Clock Domain Crossing Method ***");
  end

`endif


generate
  if (PULSE_MODE == 0) begin : GEN_PM_EQ_0

    npu_DWbb_bcm95 #(TMR_CDC, 1, 0)
                        U_TMR_S
                        (.clk(clk_s),
                         .rst_n(rst_s_n),
                         .d_in (next_tgl_event_s),
                         .d_out(tgl_event_s));

    npu_DWbb_bcm95_ne #(TMR_CDC_CC, 1, 0)
                        U_TMR_S_CC
                        (.clk(clk_s),
                         .rst_n(rst_s_n),
                         .d_in (next_tgl_event_s),
                         .d_out(tgl_s_nfb_cdc));

    assign next_tgl_event_s = tgl_event_s ^ event_s;
  end

  if (PULSE_MODE > 0) begin : GEN_PM_NE_0
    wire [1:0] next_tmr_reg_s;
    wire [1:0] tmr_reg_s;

    wire   event_s_d;

    assign next_tmr_reg_s = {next_tgl_event_s, event_s};

    npu_DWbb_bcm95 #(TMR_CDC, 2, 0)
                        U_TMR_S
                        (.clk(clk_s),
                         .rst_n(rst_s_n),
                         .d_in (next_tmr_reg_s),
                         .d_out(tmr_reg_s));

    assign {tgl_event_s, event_s_d} = tmr_reg_s;

    npu_DWbb_bcm95_ne #(TMR_CDC_CC, 1, 0)
                        U_TMR_S_CC
                        (.clk(clk_s),
                         .rst_n(rst_s_n),
                         .d_in (next_tgl_event_s),
                         .d_out(tgl_s_nfb_cdc));


    if (PULSE_MODE == 1) begin : GEN_PLSMD1
      wire event_s_pet;

      assign event_s_pet = event_s & (! event_s_d);
      assign next_tgl_event_s = tgl_event_s ^ event_s_pet;
    end

    if (PULSE_MODE == 2) begin : GEN_PLSMD2
      wire event_s_net;

      assign event_s_net = !event_s &   event_s_d;
      assign next_tgl_event_s = tgl_event_s ^ event_s_net;
    end

    if (PULSE_MODE >= 3) begin : GEN_PLSMD3
      wire event_s_pet;
      wire event_s_net;

      assign event_s_pet = event_s & (! event_s_d);
      assign event_s_net = !event_s &   event_s_d;
      assign next_tgl_event_s = tgl_event_s ^ (event_s_net | event_s_pet);
    end
  end
endgenerate



   assign tgl_event_cc = tgl_s_nfb_cdc;

  npu_DWbb_bcm21_atv #(SYNC_ATV_WIDTH, F_SYNC_TYPE_P8, VERIF_EN, SVA_TYPE, TMR_CDC) U_SYNC(
        .clk_d(clk_d),
        .rst_d_n(rst_d_n),
        .data_s(tgl_event_cc),
        .data_d(dw_sync_data_d) );

  assign next_event_d_q = sync_event_out ^ dw_sync_data_d;

generate
  if (REG_EVENT == 0) begin : GEN_RE_EQ_0
    wire  next_tmr_reg_d;
    wire  tmr_reg_d;

    assign next_tmr_reg_d = dw_sync_data_d;

    npu_DWbb_bcm95 #(TMR_CDC, 1, 0)
                        U_TMR_D
                        (.clk(clk_d),
                         .rst_n(rst_d_n),
                         .d_in (next_tmr_reg_d),
                         .d_out(tmr_reg_d));

    assign sync_event_out = tmr_reg_d;

    assign event_d = next_event_d_q;
  end
  if (REG_EVENT != 0) begin : GEN_RE_NE_0
    wire [1:0]  next_tmr_reg_d;
    wire [1:0]  tmr_reg_d;

    wire  event_d_q;      // registered version of event seen

    assign next_tmr_reg_d = {dw_sync_data_d, next_event_d_q};

    npu_DWbb_bcm95 #(TMR_CDC, 2, 0)
                        U_TMR_D
                        (.clk(clk_d),
                         .rst_n(rst_d_n),
                         .d_in (next_tmr_reg_d),
                         .d_out(tmr_reg_d));

    assign {sync_event_out, event_d_q} = tmr_reg_d;

    assign event_d = event_d_q;
  end
endgenerate


`ifdef DWC_BCM_SNPS_ASSERT_ON
`ifndef SYNTHESIS
  generate
    if (SVA_TYPE == 1) begin : GEN_SVATP_EQ_1
      DWbb_sva02 #(
        .F_SYNC_TYPE    (F_SYNC_TYPE&7),
        .PULSE_MODE     (PULSE_MODE   )
      ) P_PULSE_SYNC_HS (
          .clk_s        (clk_s        )
        , .rst_s_n      (rst_s_n      )
        , .rst_d_n      (rst_d_n      )
        , .event_s      (event_s      )
        , .event_d      (event_d      )
      );
    end
  endgenerate

  generate
    if (F_SYNC_TYPE==0) begin : GEN_SINGLE_CLOCK_CANDIDATE
      DWbb_sva07 #(F_SYNC_TYPE, F_SYNC_TYPE) P_CDC_CLKCOH (.*);
    end
  endgenerate
`endif // SYNTHESIS
`endif // DWC_BCM_SNPS_ASSERT_ON

endmodule
