// Library ARC_Trace-3.0.999999999
`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"


module npuarc_rtt_atb_if (
  input has_rtt_iso_disable, 
input atclken,
input ug_rtt_clk,
  input              prdcr_clk_0,

  input wire         rtt_flush_command_0,
  input wire         para_done_0,
  input [`npuarc_SYNCRFR_WDT-1:0] atb_syncrfr_0,
  input              req_0,
  input [120-1:0]    data_0,
  output wire        ack_0,

  output wire        atb_done_0,
  output wire        atb_ctrl_busy_0,
  input [6:0]        i_atid_0,
  input              ds_en_0,
  input              atready_0,
  input              afvalid_0,
  input              syncreq_0,
  output wire        atvalid_0,
  output wire [`npuarc_ATDATA_WIDTH-1:0] atdata_0,
  output wire [6:0]  atid_0,
  output wire [`npuarc_ATBYTE_WIDTH-1:0]  atbytes_0,
  output wire        afready_0,
  output wire        dsuppress_0,
  output wire        rttsyncreq_0,

  input              prdcr_clk_1,

  input wire         rtt_flush_command_1,
  input wire         para_done_1,
  input [`npuarc_SYNCRFR_WDT-1:0] atb_syncrfr_1,
  input              req_1,
  input [120-1:0]    data_1,
  output wire        ack_1,

  output wire        atb_done_1,
  output wire        atb_ctrl_busy_1,
  input [6:0]        i_atid_1,
  input              ds_en_1,
  input              atready_1,
  input              afvalid_1,
  input              syncreq_1,
  output wire        atvalid_1,
  output wire [`npuarc_SWE_ATDATA_WIDTH-1:0] atdata_1,
  output wire [6:0]  atid_1,
  output wire [`npuarc_SWE_ATBYTE_WIDTH-1:0]  atbytes_1,
  output wire        afready_1,
  output wire        dsuppress_1,
  output wire        rttsyncreq_1,


  input atresetn,
  input rst_a
);

wire nfifo_full_0;
assign ack_0 = nfifo_full_0;
npuarc_rtt_atb_ctrl #(.ATWDTH(`npuarc_ATDATA_WIDTH)
               ) u_rtt_atb_ctrl_0 (
        .has_rtt_iso_disable(has_rtt_iso_disable),
        .rtt_clk(prdcr_clk_0),
        .rst_a(rst_a),
        .atid_in(i_atid_0),
        .ds_en(ds_en_0),
        .wr_data(data_0),
        .wr_en(req_0),
        .fifo_full(nfifo_full_0),
        .dsuppress(dsuppress_0),
        .rttsyncreq(rttsyncreq_0),
        .rtt_flush_command(rtt_flush_command_0),
        .para_done(para_done_0),
        .atb_done(atb_done_0),
        .atb_ctrl_busy(atb_ctrl_busy_0),
        .atb_syncrfr(atb_syncrfr_0),
.atclken(atclken),
.ug_rtt_clk(ug_rtt_clk),
        .atresetn(atresetn),
        .syncreq(syncreq_0),
        .atready(atready_0),
        .afvalid(afvalid_0),
        .atvalid(atvalid_0),
        .atdata(atdata_0),
        .atid(atid_0),
        .atbytes(atbytes_0),
        .afready(afready_0)
        );

wire nfifo_full_1;
assign ack_1 = nfifo_full_1;
npuarc_rtt_swe_atb_ctrl #(.ATWDTH(`npuarc_SWE_ATDATA_WIDTH)
               ) u_rtt_swe_atb_ctrl_1 (
        .has_rtt_iso_disable(has_rtt_iso_disable),
        .rtt_clk(prdcr_clk_1),
        .rst_a(rst_a),
        .atid_in(i_atid_1),
        .ds_en(ds_en_1),
        .wr_data(data_1),
        .wr_en(req_1),
        .fifo_full(nfifo_full_1),
        .dsuppress(dsuppress_1),
        .rttsyncreq(rttsyncreq_1),
        .rtt_flush_command(rtt_flush_command_1),
        .para_done(para_done_1),
        .atb_done(atb_done_1),
        .atb_ctrl_busy(atb_ctrl_busy_1),
        .atb_syncrfr(atb_syncrfr_1),
.atclken(atclken),
.ug_rtt_clk(ug_rtt_clk),
        .atresetn(atresetn),
        .syncreq(syncreq_1),
        .atready(atready_1),
        .afvalid(afvalid_1),
        .atvalid(atvalid_1),
        .atdata(atdata_1),
        .atid(atid_1),
        .atbytes(atbytes_1),
        .afready(afready_1)
        );


endmodule
