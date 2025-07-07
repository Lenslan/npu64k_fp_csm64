// Library ARC_Trace-3.0.999999999
`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"

module npuarc_rtt_glue (
  output wire[`npuarc_PRNUM_WDT-1:0] pr0_num,
  input  prdcr_busy_0,
  input  prdcr_sel_0,
  output wire ored_prdcr_sel_p,


  input swe_prdcr_busy,
  input [`npuarc_RTT_NUM_SWE_PORTS-1:0] swe_prdcr_sel,
  output wire ored_swe_prdcr_sel,
  output wire sl0_alt_rtt_swe_prdcr_en,
  output wire sl1_alt_rtt_swe_prdcr_en,
  output wire sl2_alt_rtt_swe_prdcr_en,
  output wire sl3_alt_rtt_swe_prdcr_en,
  output wire sl4_alt_rtt_swe_prdcr_en,
  output wire sl5_alt_rtt_swe_prdcr_en,
  output wire sl6_alt_rtt_swe_prdcr_en,
  output wire sl7_alt_rtt_swe_prdcr_en,
  output wire sl8_alt_rtt_swe_prdcr_en,
  output wire sl9_alt_rtt_swe_prdcr_en,
  output wire sl10_alt_rtt_swe_prdcr_en,
  output wire sl11_alt_rtt_swe_prdcr_en,
  output wire sl12_alt_rtt_swe_prdcr_en,
  output wire sl13_alt_rtt_swe_prdcr_en,
  output wire sl14_alt_rtt_swe_prdcr_en,
  output wire sl15_alt_rtt_swe_prdcr_en,
  output wire sl16_alt_rtt_swe_prdcr_en,

  output wire cu_clk,


  input rtt_clk,

  input rst_a,
  output wire tmp_rst_a,
  output wire prdcr_busy
);


assign ored_swe_prdcr_sel = |swe_prdcr_sel;
 assign sl0_alt_rtt_swe_prdcr_en = swe_prdcr_sel[0];
 assign sl1_alt_rtt_swe_prdcr_en = swe_prdcr_sel[1];
 assign sl2_alt_rtt_swe_prdcr_en = swe_prdcr_sel[2];
 assign sl3_alt_rtt_swe_prdcr_en = swe_prdcr_sel[3];
 assign sl4_alt_rtt_swe_prdcr_en = swe_prdcr_sel[4];
 assign sl5_alt_rtt_swe_prdcr_en = swe_prdcr_sel[5];
 assign sl6_alt_rtt_swe_prdcr_en = swe_prdcr_sel[6];
 assign sl7_alt_rtt_swe_prdcr_en = swe_prdcr_sel[7];
 assign sl8_alt_rtt_swe_prdcr_en = swe_prdcr_sel[8];
 assign sl9_alt_rtt_swe_prdcr_en = swe_prdcr_sel[9];
 assign sl10_alt_rtt_swe_prdcr_en = swe_prdcr_sel[10];
 assign sl11_alt_rtt_swe_prdcr_en = swe_prdcr_sel[11];
 assign sl12_alt_rtt_swe_prdcr_en = swe_prdcr_sel[12];
 assign sl13_alt_rtt_swe_prdcr_en = swe_prdcr_sel[13];
 assign sl14_alt_rtt_swe_prdcr_en = swe_prdcr_sel[14];
 assign sl15_alt_rtt_swe_prdcr_en = swe_prdcr_sel[15];
 assign sl16_alt_rtt_swe_prdcr_en = swe_prdcr_sel[16];

assign ored_prdcr_sel_p =
    prdcr_sel_0 |
    ored_swe_prdcr_sel |
    1'b0;

  assign pr0_num = `npuarc_PR0_NUM;


assign prdcr_busy = ( prdcr_busy_0
                      || swe_prdcr_busy
                     );

assign cu_clk = rtt_clk;


assign tmp_rst_a = rst_a
                   ;

endmodule
