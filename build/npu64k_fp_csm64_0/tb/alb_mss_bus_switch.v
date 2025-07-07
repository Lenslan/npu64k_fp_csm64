`include "alb_mss_bus_switch_defines.v"
module alb_mss_bus_switch (
  // master side

  input                                   npu_mst0_axi_bs_ibp_cmd_valid,
  output                                  npu_mst0_axi_bs_ibp_cmd_accept,
  input                                   npu_mst0_axi_bs_ibp_cmd_read,
  input   [49                -1:0]       npu_mst0_axi_bs_ibp_cmd_addr,
  input                                   npu_mst0_axi_bs_ibp_cmd_wrap,
  input   [3-1:0]       npu_mst0_axi_bs_ibp_cmd_data_size,
  input   [4-1:0]       npu_mst0_axi_bs_ibp_cmd_burst_size,
  input   [2-1:0]       npu_mst0_axi_bs_ibp_cmd_prot,
  input   [4-1:0]       npu_mst0_axi_bs_ibp_cmd_cache,
  input                                   npu_mst0_axi_bs_ibp_cmd_lock,
  input                                   npu_mst0_axi_bs_ibp_cmd_excl,

  output                                  npu_mst0_axi_bs_ibp_rd_valid,
  output                                  npu_mst0_axi_bs_ibp_rd_excl_ok,
  input                                   npu_mst0_axi_bs_ibp_rd_accept,
  output                                  npu_mst0_axi_bs_ibp_err_rd,
  output  [64               -1:0]        npu_mst0_axi_bs_ibp_rd_data,
  output                                  npu_mst0_axi_bs_ibp_rd_last,

  input                                   npu_mst0_axi_bs_ibp_wr_valid,
  output                                  npu_mst0_axi_bs_ibp_wr_accept,
  input   [64               -1:0]        npu_mst0_axi_bs_ibp_wr_data,
  input   [(64         /8)  -1:0]        npu_mst0_axi_bs_ibp_wr_mask,
  input                                   npu_mst0_axi_bs_ibp_wr_last,

  output                                  npu_mst0_axi_bs_ibp_wr_done,
  output                                  npu_mst0_axi_bs_ibp_wr_excl_done,
  output                                  npu_mst0_axi_bs_ibp_err_wr,
  input                                   npu_mst0_axi_bs_ibp_wr_resp_accept,


  input                                   npu_mst1_axi_bs_ibp_cmd_valid,
  output                                  npu_mst1_axi_bs_ibp_cmd_accept,
  input                                   npu_mst1_axi_bs_ibp_cmd_read,
  input   [49                -1:0]       npu_mst1_axi_bs_ibp_cmd_addr,
  input                                   npu_mst1_axi_bs_ibp_cmd_wrap,
  input   [3-1:0]       npu_mst1_axi_bs_ibp_cmd_data_size,
  input   [4-1:0]       npu_mst1_axi_bs_ibp_cmd_burst_size,
  input   [2-1:0]       npu_mst1_axi_bs_ibp_cmd_prot,
  input   [4-1:0]       npu_mst1_axi_bs_ibp_cmd_cache,
  input                                   npu_mst1_axi_bs_ibp_cmd_lock,
  input                                   npu_mst1_axi_bs_ibp_cmd_excl,

  output                                  npu_mst1_axi_bs_ibp_rd_valid,
  output                                  npu_mst1_axi_bs_ibp_rd_excl_ok,
  input                                   npu_mst1_axi_bs_ibp_rd_accept,
  output                                  npu_mst1_axi_bs_ibp_err_rd,
  output  [512               -1:0]        npu_mst1_axi_bs_ibp_rd_data,
  output                                  npu_mst1_axi_bs_ibp_rd_last,

  input                                   npu_mst1_axi_bs_ibp_wr_valid,
  output                                  npu_mst1_axi_bs_ibp_wr_accept,
  input   [512               -1:0]        npu_mst1_axi_bs_ibp_wr_data,
  input   [(512         /8)  -1:0]        npu_mst1_axi_bs_ibp_wr_mask,
  input                                   npu_mst1_axi_bs_ibp_wr_last,

  output                                  npu_mst1_axi_bs_ibp_wr_done,
  output                                  npu_mst1_axi_bs_ibp_wr_excl_done,
  output                                  npu_mst1_axi_bs_ibp_err_wr,
  input                                   npu_mst1_axi_bs_ibp_wr_resp_accept,


  input                                   npu_mst2_axi_bs_ibp_cmd_valid,
  output                                  npu_mst2_axi_bs_ibp_cmd_accept,
  input                                   npu_mst2_axi_bs_ibp_cmd_read,
  input   [49                -1:0]       npu_mst2_axi_bs_ibp_cmd_addr,
  input                                   npu_mst2_axi_bs_ibp_cmd_wrap,
  input   [3-1:0]       npu_mst2_axi_bs_ibp_cmd_data_size,
  input   [4-1:0]       npu_mst2_axi_bs_ibp_cmd_burst_size,
  input   [2-1:0]       npu_mst2_axi_bs_ibp_cmd_prot,
  input   [4-1:0]       npu_mst2_axi_bs_ibp_cmd_cache,
  input                                   npu_mst2_axi_bs_ibp_cmd_lock,
  input                                   npu_mst2_axi_bs_ibp_cmd_excl,

  output                                  npu_mst2_axi_bs_ibp_rd_valid,
  output                                  npu_mst2_axi_bs_ibp_rd_excl_ok,
  input                                   npu_mst2_axi_bs_ibp_rd_accept,
  output                                  npu_mst2_axi_bs_ibp_err_rd,
  output  [512               -1:0]        npu_mst2_axi_bs_ibp_rd_data,
  output                                  npu_mst2_axi_bs_ibp_rd_last,

  input                                   npu_mst2_axi_bs_ibp_wr_valid,
  output                                  npu_mst2_axi_bs_ibp_wr_accept,
  input   [512               -1:0]        npu_mst2_axi_bs_ibp_wr_data,
  input   [(512         /8)  -1:0]        npu_mst2_axi_bs_ibp_wr_mask,
  input                                   npu_mst2_axi_bs_ibp_wr_last,

  output                                  npu_mst2_axi_bs_ibp_wr_done,
  output                                  npu_mst2_axi_bs_ibp_wr_excl_done,
  output                                  npu_mst2_axi_bs_ibp_err_wr,
  input                                   npu_mst2_axi_bs_ibp_wr_resp_accept,


  input                                   npu_mst3_axi_bs_ibp_cmd_valid,
  output                                  npu_mst3_axi_bs_ibp_cmd_accept,
  input                                   npu_mst3_axi_bs_ibp_cmd_read,
  input   [49                -1:0]       npu_mst3_axi_bs_ibp_cmd_addr,
  input                                   npu_mst3_axi_bs_ibp_cmd_wrap,
  input   [3-1:0]       npu_mst3_axi_bs_ibp_cmd_data_size,
  input   [4-1:0]       npu_mst3_axi_bs_ibp_cmd_burst_size,
  input   [2-1:0]       npu_mst3_axi_bs_ibp_cmd_prot,
  input   [4-1:0]       npu_mst3_axi_bs_ibp_cmd_cache,
  input                                   npu_mst3_axi_bs_ibp_cmd_lock,
  input                                   npu_mst3_axi_bs_ibp_cmd_excl,

  output                                  npu_mst3_axi_bs_ibp_rd_valid,
  output                                  npu_mst3_axi_bs_ibp_rd_excl_ok,
  input                                   npu_mst3_axi_bs_ibp_rd_accept,
  output                                  npu_mst3_axi_bs_ibp_err_rd,
  output  [512               -1:0]        npu_mst3_axi_bs_ibp_rd_data,
  output                                  npu_mst3_axi_bs_ibp_rd_last,

  input                                   npu_mst3_axi_bs_ibp_wr_valid,
  output                                  npu_mst3_axi_bs_ibp_wr_accept,
  input   [512               -1:0]        npu_mst3_axi_bs_ibp_wr_data,
  input   [(512         /8)  -1:0]        npu_mst3_axi_bs_ibp_wr_mask,
  input                                   npu_mst3_axi_bs_ibp_wr_last,

  output                                  npu_mst3_axi_bs_ibp_wr_done,
  output                                  npu_mst3_axi_bs_ibp_wr_excl_done,
  output                                  npu_mst3_axi_bs_ibp_err_wr,
  input                                   npu_mst3_axi_bs_ibp_wr_resp_accept,


  input                                   npu_mst4_axi_bs_ibp_cmd_valid,
  output                                  npu_mst4_axi_bs_ibp_cmd_accept,
  input                                   npu_mst4_axi_bs_ibp_cmd_read,
  input   [49                -1:0]       npu_mst4_axi_bs_ibp_cmd_addr,
  input                                   npu_mst4_axi_bs_ibp_cmd_wrap,
  input   [3-1:0]       npu_mst4_axi_bs_ibp_cmd_data_size,
  input   [4-1:0]       npu_mst4_axi_bs_ibp_cmd_burst_size,
  input   [2-1:0]       npu_mst4_axi_bs_ibp_cmd_prot,
  input   [4-1:0]       npu_mst4_axi_bs_ibp_cmd_cache,
  input                                   npu_mst4_axi_bs_ibp_cmd_lock,
  input                                   npu_mst4_axi_bs_ibp_cmd_excl,

  output                                  npu_mst4_axi_bs_ibp_rd_valid,
  output                                  npu_mst4_axi_bs_ibp_rd_excl_ok,
  input                                   npu_mst4_axi_bs_ibp_rd_accept,
  output                                  npu_mst4_axi_bs_ibp_err_rd,
  output  [512               -1:0]        npu_mst4_axi_bs_ibp_rd_data,
  output                                  npu_mst4_axi_bs_ibp_rd_last,

  input                                   npu_mst4_axi_bs_ibp_wr_valid,
  output                                  npu_mst4_axi_bs_ibp_wr_accept,
  input   [512               -1:0]        npu_mst4_axi_bs_ibp_wr_data,
  input   [(512         /8)  -1:0]        npu_mst4_axi_bs_ibp_wr_mask,
  input                                   npu_mst4_axi_bs_ibp_wr_last,

  output                                  npu_mst4_axi_bs_ibp_wr_done,
  output                                  npu_mst4_axi_bs_ibp_wr_excl_done,
  output                                  npu_mst4_axi_bs_ibp_err_wr,
  input                                   npu_mst4_axi_bs_ibp_wr_resp_accept,


  input                                   host_axi_bs_ibp_cmd_valid,
  output                                  host_axi_bs_ibp_cmd_accept,
  input                                   host_axi_bs_ibp_cmd_read,
  input   [49                -1:0]       host_axi_bs_ibp_cmd_addr,
  input                                   host_axi_bs_ibp_cmd_wrap,
  input   [3-1:0]       host_axi_bs_ibp_cmd_data_size,
  input   [4-1:0]       host_axi_bs_ibp_cmd_burst_size,
  input   [2-1:0]       host_axi_bs_ibp_cmd_prot,
  input   [4-1:0]       host_axi_bs_ibp_cmd_cache,
  input                                   host_axi_bs_ibp_cmd_lock,
  input                                   host_axi_bs_ibp_cmd_excl,

  output                                  host_axi_bs_ibp_rd_valid,
  output                                  host_axi_bs_ibp_rd_excl_ok,
  input                                   host_axi_bs_ibp_rd_accept,
  output                                  host_axi_bs_ibp_err_rd,
  output  [64               -1:0]        host_axi_bs_ibp_rd_data,
  output                                  host_axi_bs_ibp_rd_last,

  input                                   host_axi_bs_ibp_wr_valid,
  output                                  host_axi_bs_ibp_wr_accept,
  input   [64               -1:0]        host_axi_bs_ibp_wr_data,
  input   [(64         /8)  -1:0]        host_axi_bs_ibp_wr_mask,
  input                                   host_axi_bs_ibp_wr_last,

  output                                  host_axi_bs_ibp_wr_done,
  output                                  host_axi_bs_ibp_wr_excl_done,
  output                                  host_axi_bs_ibp_err_wr,
  input                                   host_axi_bs_ibp_wr_resp_accept,


  input                                   bri4tb_bs_ibp_cmd_valid,
  output                                  bri4tb_bs_ibp_cmd_accept,
  input                                   bri4tb_bs_ibp_cmd_read,
  input   [49                -1:0]       bri4tb_bs_ibp_cmd_addr,
  input                                   bri4tb_bs_ibp_cmd_wrap,
  input   [3-1:0]       bri4tb_bs_ibp_cmd_data_size,
  input   [4-1:0]       bri4tb_bs_ibp_cmd_burst_size,
  input   [2-1:0]       bri4tb_bs_ibp_cmd_prot,
  input   [4-1:0]       bri4tb_bs_ibp_cmd_cache,
  input                                   bri4tb_bs_ibp_cmd_lock,
  input                                   bri4tb_bs_ibp_cmd_excl,

  output                                  bri4tb_bs_ibp_rd_valid,
  output                                  bri4tb_bs_ibp_rd_excl_ok,
  input                                   bri4tb_bs_ibp_rd_accept,
  output                                  bri4tb_bs_ibp_err_rd,
  output  [32               -1:0]        bri4tb_bs_ibp_rd_data,
  output                                  bri4tb_bs_ibp_rd_last,

  input                                   bri4tb_bs_ibp_wr_valid,
  output                                  bri4tb_bs_ibp_wr_accept,
  input   [32               -1:0]        bri4tb_bs_ibp_wr_data,
  input   [(32         /8)  -1:0]        bri4tb_bs_ibp_wr_mask,
  input                                   bri4tb_bs_ibp_wr_last,

  output                                  bri4tb_bs_ibp_wr_done,
  output                                  bri4tb_bs_ibp_wr_excl_done,
  output                                  bri4tb_bs_ibp_err_wr,
  input                                   bri4tb_bs_ibp_wr_resp_accept,

  // slave side


  output                                  npu_dmi0_axi_bs_ibp_cmd_valid,
  input                                   npu_dmi0_axi_bs_ibp_cmd_accept,
  output                                  npu_dmi0_axi_bs_ibp_cmd_read,
  output  [49                -1:0]       npu_dmi0_axi_bs_ibp_cmd_addr,
  output                                  npu_dmi0_axi_bs_ibp_cmd_wrap,
  output  [3-1:0]       npu_dmi0_axi_bs_ibp_cmd_data_size,
  output  [4-1:0]       npu_dmi0_axi_bs_ibp_cmd_burst_size,
  output  [2-1:0]       npu_dmi0_axi_bs_ibp_cmd_prot,
  output  [4-1:0]       npu_dmi0_axi_bs_ibp_cmd_cache,
  output                                  npu_dmi0_axi_bs_ibp_cmd_lock,
  output                                  npu_dmi0_axi_bs_ibp_cmd_excl,

  input                                   npu_dmi0_axi_bs_ibp_rd_valid,
  input                                   npu_dmi0_axi_bs_ibp_rd_excl_ok,
  output                                  npu_dmi0_axi_bs_ibp_rd_accept,
  input                                   npu_dmi0_axi_bs_ibp_err_rd,
  input   [512               -1:0]        npu_dmi0_axi_bs_ibp_rd_data,
  input                                   npu_dmi0_axi_bs_ibp_rd_last,

  output                                  npu_dmi0_axi_bs_ibp_wr_valid,
  input                                   npu_dmi0_axi_bs_ibp_wr_accept,
  output  [512               -1:0]        npu_dmi0_axi_bs_ibp_wr_data,
  output  [(512         /8)  -1:0]        npu_dmi0_axi_bs_ibp_wr_mask,
  output                                  npu_dmi0_axi_bs_ibp_wr_last,

  input                                   npu_dmi0_axi_bs_ibp_wr_done,
  input                                   npu_dmi0_axi_bs_ibp_wr_excl_done,
  input                                   npu_dmi0_axi_bs_ibp_err_wr,
  output                                  npu_dmi0_axi_bs_ibp_wr_resp_accept,
output [0-1:0] npu_dmi0_axi_bs_ibp_cmd_region,



  output                                  npu_cfg_axi_bs_ibp_cmd_valid,
  input                                   npu_cfg_axi_bs_ibp_cmd_accept,
  output                                  npu_cfg_axi_bs_ibp_cmd_read,
  output  [49                -1:0]       npu_cfg_axi_bs_ibp_cmd_addr,
  output                                  npu_cfg_axi_bs_ibp_cmd_wrap,
  output  [3-1:0]       npu_cfg_axi_bs_ibp_cmd_data_size,
  output  [4-1:0]       npu_cfg_axi_bs_ibp_cmd_burst_size,
  output  [2-1:0]       npu_cfg_axi_bs_ibp_cmd_prot,
  output  [4-1:0]       npu_cfg_axi_bs_ibp_cmd_cache,
  output                                  npu_cfg_axi_bs_ibp_cmd_lock,
  output                                  npu_cfg_axi_bs_ibp_cmd_excl,

  input                                   npu_cfg_axi_bs_ibp_rd_valid,
  input                                   npu_cfg_axi_bs_ibp_rd_excl_ok,
  output                                  npu_cfg_axi_bs_ibp_rd_accept,
  input                                   npu_cfg_axi_bs_ibp_err_rd,
  input   [32               -1:0]        npu_cfg_axi_bs_ibp_rd_data,
  input                                   npu_cfg_axi_bs_ibp_rd_last,

  output                                  npu_cfg_axi_bs_ibp_wr_valid,
  input                                   npu_cfg_axi_bs_ibp_wr_accept,
  output  [32               -1:0]        npu_cfg_axi_bs_ibp_wr_data,
  output  [(32         /8)  -1:0]        npu_cfg_axi_bs_ibp_wr_mask,
  output                                  npu_cfg_axi_bs_ibp_wr_last,

  input                                   npu_cfg_axi_bs_ibp_wr_done,
  input                                   npu_cfg_axi_bs_ibp_wr_excl_done,
  input                                   npu_cfg_axi_bs_ibp_err_wr,
  output                                  npu_cfg_axi_bs_ibp_wr_resp_accept,
output [0-1:0] npu_cfg_axi_bs_ibp_cmd_region,



  output                                  arcsync_axi_bs_ibp_cmd_valid,
  input                                   arcsync_axi_bs_ibp_cmd_accept,
  output                                  arcsync_axi_bs_ibp_cmd_read,
  output  [49                -1:0]       arcsync_axi_bs_ibp_cmd_addr,
  output                                  arcsync_axi_bs_ibp_cmd_wrap,
  output  [3-1:0]       arcsync_axi_bs_ibp_cmd_data_size,
  output  [4-1:0]       arcsync_axi_bs_ibp_cmd_burst_size,
  output  [2-1:0]       arcsync_axi_bs_ibp_cmd_prot,
  output  [4-1:0]       arcsync_axi_bs_ibp_cmd_cache,
  output                                  arcsync_axi_bs_ibp_cmd_lock,
  output                                  arcsync_axi_bs_ibp_cmd_excl,

  input                                   arcsync_axi_bs_ibp_rd_valid,
  input                                   arcsync_axi_bs_ibp_rd_excl_ok,
  output                                  arcsync_axi_bs_ibp_rd_accept,
  input                                   arcsync_axi_bs_ibp_err_rd,
  input   [64               -1:0]        arcsync_axi_bs_ibp_rd_data,
  input                                   arcsync_axi_bs_ibp_rd_last,

  output                                  arcsync_axi_bs_ibp_wr_valid,
  input                                   arcsync_axi_bs_ibp_wr_accept,
  output  [64               -1:0]        arcsync_axi_bs_ibp_wr_data,
  output  [(64         /8)  -1:0]        arcsync_axi_bs_ibp_wr_mask,
  output                                  arcsync_axi_bs_ibp_wr_last,

  input                                   arcsync_axi_bs_ibp_wr_done,
  input                                   arcsync_axi_bs_ibp_wr_excl_done,
  input                                   arcsync_axi_bs_ibp_err_wr,
  output                                  arcsync_axi_bs_ibp_wr_resp_accept,
output [0-1:0] arcsync_axi_bs_ibp_cmd_region,



  output                                  mss_mem_bs_ibp_cmd_valid,
  input                                   mss_mem_bs_ibp_cmd_accept,
  output                                  mss_mem_bs_ibp_cmd_read,
  output  [49                -1:0]       mss_mem_bs_ibp_cmd_addr,
  output                                  mss_mem_bs_ibp_cmd_wrap,
  output  [3-1:0]       mss_mem_bs_ibp_cmd_data_size,
  output  [4-1:0]       mss_mem_bs_ibp_cmd_burst_size,
  output  [2-1:0]       mss_mem_bs_ibp_cmd_prot,
  output  [4-1:0]       mss_mem_bs_ibp_cmd_cache,
  output                                  mss_mem_bs_ibp_cmd_lock,
  output                                  mss_mem_bs_ibp_cmd_excl,

  input                                   mss_mem_bs_ibp_rd_valid,
  input                                   mss_mem_bs_ibp_rd_excl_ok,
  output                                  mss_mem_bs_ibp_rd_accept,
  input                                   mss_mem_bs_ibp_err_rd,
  input   [128               -1:0]        mss_mem_bs_ibp_rd_data,
  input                                   mss_mem_bs_ibp_rd_last,

  output                                  mss_mem_bs_ibp_wr_valid,
  input                                   mss_mem_bs_ibp_wr_accept,
  output  [128               -1:0]        mss_mem_bs_ibp_wr_data,
  output  [(128         /8)  -1:0]        mss_mem_bs_ibp_wr_mask,
  output                                  mss_mem_bs_ibp_wr_last,

  input                                   mss_mem_bs_ibp_wr_done,
  input                                   mss_mem_bs_ibp_wr_excl_done,
  input                                   mss_mem_bs_ibp_err_wr,
  output                                  mss_mem_bs_ibp_wr_resp_accept,
output [1-1:0] mss_mem_bs_ibp_cmd_region,

  // clock and reset
  input                                   clk,
  input                                   rst_a
);



// Internal wires and regs

wire [4 : 0] npu_mst0_axi_bs_ibp_cmd_rgon;



 wire [1-1:0] in_0_out_0_ibp_cmd_chnl_valid;
 wire [1-1:0] in_0_out_0_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_0_out_0_ibp_cmd_chnl;

 wire [1-1:0] in_0_out_0_ibp_wd_chnl_valid;
 wire [1-1:0] in_0_out_0_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] in_0_out_0_ibp_wd_chnl;

 wire [1-1:0] in_0_out_0_ibp_rd_chnl_accept;
 wire [1-1:0] in_0_out_0_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] in_0_out_0_ibp_rd_chnl;

 wire [1-1:0] in_0_out_0_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_0_out_0_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_0_out_0_ibp_wrsp_chnl;





 wire [1-1:0] in_0_out_1_ibp_cmd_chnl_valid;
 wire [1-1:0] in_0_out_1_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_0_out_1_ibp_cmd_chnl;

 wire [1-1:0] in_0_out_1_ibp_wd_chnl_valid;
 wire [1-1:0] in_0_out_1_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] in_0_out_1_ibp_wd_chnl;

 wire [1-1:0] in_0_out_1_ibp_rd_chnl_accept;
 wire [1-1:0] in_0_out_1_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] in_0_out_1_ibp_rd_chnl;

 wire [1-1:0] in_0_out_1_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_0_out_1_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_0_out_1_ibp_wrsp_chnl;





 wire [1-1:0] in_0_out_2_ibp_cmd_chnl_valid;
 wire [1-1:0] in_0_out_2_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_0_out_2_ibp_cmd_chnl;

 wire [1-1:0] in_0_out_2_ibp_wd_chnl_valid;
 wire [1-1:0] in_0_out_2_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] in_0_out_2_ibp_wd_chnl;

 wire [1-1:0] in_0_out_2_ibp_rd_chnl_accept;
 wire [1-1:0] in_0_out_2_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] in_0_out_2_ibp_rd_chnl;

 wire [1-1:0] in_0_out_2_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_0_out_2_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_0_out_2_ibp_wrsp_chnl;





 wire [1-1:0] in_0_out_3_ibp_cmd_chnl_valid;
 wire [1-1:0] in_0_out_3_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_0_out_3_ibp_cmd_chnl;

 wire [1-1:0] in_0_out_3_ibp_wd_chnl_valid;
 wire [1-1:0] in_0_out_3_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] in_0_out_3_ibp_wd_chnl;

 wire [1-1:0] in_0_out_3_ibp_rd_chnl_accept;
 wire [1-1:0] in_0_out_3_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] in_0_out_3_ibp_rd_chnl;

 wire [1-1:0] in_0_out_3_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_0_out_3_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_0_out_3_ibp_wrsp_chnl;





 wire [1-1:0] in_0_out_4_ibp_cmd_chnl_valid;
 wire [1-1:0] in_0_out_4_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_0_out_4_ibp_cmd_chnl;

 wire [1-1:0] in_0_out_4_ibp_wd_chnl_valid;
 wire [1-1:0] in_0_out_4_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] in_0_out_4_ibp_wd_chnl;

 wire [1-1:0] in_0_out_4_ibp_rd_chnl_accept;
 wire [1-1:0] in_0_out_4_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] in_0_out_4_ibp_rd_chnl;

 wire [1-1:0] in_0_out_4_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_0_out_4_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_0_out_4_ibp_wrsp_chnl;



wire [4 : 0] npu_mst1_axi_bs_ibp_cmd_rgon;



 wire [1-1:0] in_1_out_0_ibp_cmd_chnl_valid;
 wire [1-1:0] in_1_out_0_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_1_out_0_ibp_cmd_chnl;

 wire [1-1:0] in_1_out_0_ibp_wd_chnl_valid;
 wire [1-1:0] in_1_out_0_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] in_1_out_0_ibp_wd_chnl;

 wire [1-1:0] in_1_out_0_ibp_rd_chnl_accept;
 wire [1-1:0] in_1_out_0_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] in_1_out_0_ibp_rd_chnl;

 wire [1-1:0] in_1_out_0_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_1_out_0_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_1_out_0_ibp_wrsp_chnl;





 wire [1-1:0] in_1_out_1_ibp_cmd_chnl_valid;
 wire [1-1:0] in_1_out_1_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_1_out_1_ibp_cmd_chnl;

 wire [1-1:0] in_1_out_1_ibp_wd_chnl_valid;
 wire [1-1:0] in_1_out_1_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] in_1_out_1_ibp_wd_chnl;

 wire [1-1:0] in_1_out_1_ibp_rd_chnl_accept;
 wire [1-1:0] in_1_out_1_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] in_1_out_1_ibp_rd_chnl;

 wire [1-1:0] in_1_out_1_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_1_out_1_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_1_out_1_ibp_wrsp_chnl;





 wire [1-1:0] in_1_out_2_ibp_cmd_chnl_valid;
 wire [1-1:0] in_1_out_2_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_1_out_2_ibp_cmd_chnl;

 wire [1-1:0] in_1_out_2_ibp_wd_chnl_valid;
 wire [1-1:0] in_1_out_2_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] in_1_out_2_ibp_wd_chnl;

 wire [1-1:0] in_1_out_2_ibp_rd_chnl_accept;
 wire [1-1:0] in_1_out_2_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] in_1_out_2_ibp_rd_chnl;

 wire [1-1:0] in_1_out_2_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_1_out_2_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_1_out_2_ibp_wrsp_chnl;





 wire [1-1:0] in_1_out_3_ibp_cmd_chnl_valid;
 wire [1-1:0] in_1_out_3_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_1_out_3_ibp_cmd_chnl;

 wire [1-1:0] in_1_out_3_ibp_wd_chnl_valid;
 wire [1-1:0] in_1_out_3_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] in_1_out_3_ibp_wd_chnl;

 wire [1-1:0] in_1_out_3_ibp_rd_chnl_accept;
 wire [1-1:0] in_1_out_3_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] in_1_out_3_ibp_rd_chnl;

 wire [1-1:0] in_1_out_3_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_1_out_3_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_1_out_3_ibp_wrsp_chnl;





 wire [1-1:0] in_1_out_4_ibp_cmd_chnl_valid;
 wire [1-1:0] in_1_out_4_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_1_out_4_ibp_cmd_chnl;

 wire [1-1:0] in_1_out_4_ibp_wd_chnl_valid;
 wire [1-1:0] in_1_out_4_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] in_1_out_4_ibp_wd_chnl;

 wire [1-1:0] in_1_out_4_ibp_rd_chnl_accept;
 wire [1-1:0] in_1_out_4_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] in_1_out_4_ibp_rd_chnl;

 wire [1-1:0] in_1_out_4_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_1_out_4_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_1_out_4_ibp_wrsp_chnl;



wire [4 : 0] npu_mst2_axi_bs_ibp_cmd_rgon;



 wire [1-1:0] in_2_out_0_ibp_cmd_chnl_valid;
 wire [1-1:0] in_2_out_0_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_2_out_0_ibp_cmd_chnl;

 wire [1-1:0] in_2_out_0_ibp_wd_chnl_valid;
 wire [1-1:0] in_2_out_0_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] in_2_out_0_ibp_wd_chnl;

 wire [1-1:0] in_2_out_0_ibp_rd_chnl_accept;
 wire [1-1:0] in_2_out_0_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] in_2_out_0_ibp_rd_chnl;

 wire [1-1:0] in_2_out_0_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_2_out_0_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_2_out_0_ibp_wrsp_chnl;





 wire [1-1:0] in_2_out_1_ibp_cmd_chnl_valid;
 wire [1-1:0] in_2_out_1_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_2_out_1_ibp_cmd_chnl;

 wire [1-1:0] in_2_out_1_ibp_wd_chnl_valid;
 wire [1-1:0] in_2_out_1_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] in_2_out_1_ibp_wd_chnl;

 wire [1-1:0] in_2_out_1_ibp_rd_chnl_accept;
 wire [1-1:0] in_2_out_1_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] in_2_out_1_ibp_rd_chnl;

 wire [1-1:0] in_2_out_1_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_2_out_1_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_2_out_1_ibp_wrsp_chnl;





 wire [1-1:0] in_2_out_2_ibp_cmd_chnl_valid;
 wire [1-1:0] in_2_out_2_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_2_out_2_ibp_cmd_chnl;

 wire [1-1:0] in_2_out_2_ibp_wd_chnl_valid;
 wire [1-1:0] in_2_out_2_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] in_2_out_2_ibp_wd_chnl;

 wire [1-1:0] in_2_out_2_ibp_rd_chnl_accept;
 wire [1-1:0] in_2_out_2_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] in_2_out_2_ibp_rd_chnl;

 wire [1-1:0] in_2_out_2_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_2_out_2_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_2_out_2_ibp_wrsp_chnl;





 wire [1-1:0] in_2_out_3_ibp_cmd_chnl_valid;
 wire [1-1:0] in_2_out_3_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_2_out_3_ibp_cmd_chnl;

 wire [1-1:0] in_2_out_3_ibp_wd_chnl_valid;
 wire [1-1:0] in_2_out_3_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] in_2_out_3_ibp_wd_chnl;

 wire [1-1:0] in_2_out_3_ibp_rd_chnl_accept;
 wire [1-1:0] in_2_out_3_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] in_2_out_3_ibp_rd_chnl;

 wire [1-1:0] in_2_out_3_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_2_out_3_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_2_out_3_ibp_wrsp_chnl;





 wire [1-1:0] in_2_out_4_ibp_cmd_chnl_valid;
 wire [1-1:0] in_2_out_4_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_2_out_4_ibp_cmd_chnl;

 wire [1-1:0] in_2_out_4_ibp_wd_chnl_valid;
 wire [1-1:0] in_2_out_4_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] in_2_out_4_ibp_wd_chnl;

 wire [1-1:0] in_2_out_4_ibp_rd_chnl_accept;
 wire [1-1:0] in_2_out_4_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] in_2_out_4_ibp_rd_chnl;

 wire [1-1:0] in_2_out_4_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_2_out_4_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_2_out_4_ibp_wrsp_chnl;



wire [4 : 0] npu_mst3_axi_bs_ibp_cmd_rgon;



 wire [1-1:0] in_3_out_0_ibp_cmd_chnl_valid;
 wire [1-1:0] in_3_out_0_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_3_out_0_ibp_cmd_chnl;

 wire [1-1:0] in_3_out_0_ibp_wd_chnl_valid;
 wire [1-1:0] in_3_out_0_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] in_3_out_0_ibp_wd_chnl;

 wire [1-1:0] in_3_out_0_ibp_rd_chnl_accept;
 wire [1-1:0] in_3_out_0_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] in_3_out_0_ibp_rd_chnl;

 wire [1-1:0] in_3_out_0_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_3_out_0_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_3_out_0_ibp_wrsp_chnl;





 wire [1-1:0] in_3_out_1_ibp_cmd_chnl_valid;
 wire [1-1:0] in_3_out_1_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_3_out_1_ibp_cmd_chnl;

 wire [1-1:0] in_3_out_1_ibp_wd_chnl_valid;
 wire [1-1:0] in_3_out_1_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] in_3_out_1_ibp_wd_chnl;

 wire [1-1:0] in_3_out_1_ibp_rd_chnl_accept;
 wire [1-1:0] in_3_out_1_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] in_3_out_1_ibp_rd_chnl;

 wire [1-1:0] in_3_out_1_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_3_out_1_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_3_out_1_ibp_wrsp_chnl;





 wire [1-1:0] in_3_out_2_ibp_cmd_chnl_valid;
 wire [1-1:0] in_3_out_2_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_3_out_2_ibp_cmd_chnl;

 wire [1-1:0] in_3_out_2_ibp_wd_chnl_valid;
 wire [1-1:0] in_3_out_2_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] in_3_out_2_ibp_wd_chnl;

 wire [1-1:0] in_3_out_2_ibp_rd_chnl_accept;
 wire [1-1:0] in_3_out_2_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] in_3_out_2_ibp_rd_chnl;

 wire [1-1:0] in_3_out_2_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_3_out_2_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_3_out_2_ibp_wrsp_chnl;





 wire [1-1:0] in_3_out_3_ibp_cmd_chnl_valid;
 wire [1-1:0] in_3_out_3_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_3_out_3_ibp_cmd_chnl;

 wire [1-1:0] in_3_out_3_ibp_wd_chnl_valid;
 wire [1-1:0] in_3_out_3_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] in_3_out_3_ibp_wd_chnl;

 wire [1-1:0] in_3_out_3_ibp_rd_chnl_accept;
 wire [1-1:0] in_3_out_3_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] in_3_out_3_ibp_rd_chnl;

 wire [1-1:0] in_3_out_3_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_3_out_3_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_3_out_3_ibp_wrsp_chnl;





 wire [1-1:0] in_3_out_4_ibp_cmd_chnl_valid;
 wire [1-1:0] in_3_out_4_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_3_out_4_ibp_cmd_chnl;

 wire [1-1:0] in_3_out_4_ibp_wd_chnl_valid;
 wire [1-1:0] in_3_out_4_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] in_3_out_4_ibp_wd_chnl;

 wire [1-1:0] in_3_out_4_ibp_rd_chnl_accept;
 wire [1-1:0] in_3_out_4_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] in_3_out_4_ibp_rd_chnl;

 wire [1-1:0] in_3_out_4_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_3_out_4_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_3_out_4_ibp_wrsp_chnl;



wire [4 : 0] npu_mst4_axi_bs_ibp_cmd_rgon;



 wire [1-1:0] in_4_out_0_ibp_cmd_chnl_valid;
 wire [1-1:0] in_4_out_0_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_4_out_0_ibp_cmd_chnl;

 wire [1-1:0] in_4_out_0_ibp_wd_chnl_valid;
 wire [1-1:0] in_4_out_0_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] in_4_out_0_ibp_wd_chnl;

 wire [1-1:0] in_4_out_0_ibp_rd_chnl_accept;
 wire [1-1:0] in_4_out_0_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] in_4_out_0_ibp_rd_chnl;

 wire [1-1:0] in_4_out_0_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_4_out_0_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_4_out_0_ibp_wrsp_chnl;





 wire [1-1:0] in_4_out_1_ibp_cmd_chnl_valid;
 wire [1-1:0] in_4_out_1_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_4_out_1_ibp_cmd_chnl;

 wire [1-1:0] in_4_out_1_ibp_wd_chnl_valid;
 wire [1-1:0] in_4_out_1_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] in_4_out_1_ibp_wd_chnl;

 wire [1-1:0] in_4_out_1_ibp_rd_chnl_accept;
 wire [1-1:0] in_4_out_1_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] in_4_out_1_ibp_rd_chnl;

 wire [1-1:0] in_4_out_1_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_4_out_1_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_4_out_1_ibp_wrsp_chnl;





 wire [1-1:0] in_4_out_2_ibp_cmd_chnl_valid;
 wire [1-1:0] in_4_out_2_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_4_out_2_ibp_cmd_chnl;

 wire [1-1:0] in_4_out_2_ibp_wd_chnl_valid;
 wire [1-1:0] in_4_out_2_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] in_4_out_2_ibp_wd_chnl;

 wire [1-1:0] in_4_out_2_ibp_rd_chnl_accept;
 wire [1-1:0] in_4_out_2_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] in_4_out_2_ibp_rd_chnl;

 wire [1-1:0] in_4_out_2_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_4_out_2_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_4_out_2_ibp_wrsp_chnl;





 wire [1-1:0] in_4_out_3_ibp_cmd_chnl_valid;
 wire [1-1:0] in_4_out_3_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_4_out_3_ibp_cmd_chnl;

 wire [1-1:0] in_4_out_3_ibp_wd_chnl_valid;
 wire [1-1:0] in_4_out_3_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] in_4_out_3_ibp_wd_chnl;

 wire [1-1:0] in_4_out_3_ibp_rd_chnl_accept;
 wire [1-1:0] in_4_out_3_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] in_4_out_3_ibp_rd_chnl;

 wire [1-1:0] in_4_out_3_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_4_out_3_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_4_out_3_ibp_wrsp_chnl;





 wire [1-1:0] in_4_out_4_ibp_cmd_chnl_valid;
 wire [1-1:0] in_4_out_4_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_4_out_4_ibp_cmd_chnl;

 wire [1-1:0] in_4_out_4_ibp_wd_chnl_valid;
 wire [1-1:0] in_4_out_4_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] in_4_out_4_ibp_wd_chnl;

 wire [1-1:0] in_4_out_4_ibp_rd_chnl_accept;
 wire [1-1:0] in_4_out_4_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] in_4_out_4_ibp_rd_chnl;

 wire [1-1:0] in_4_out_4_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_4_out_4_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_4_out_4_ibp_wrsp_chnl;



wire [4 : 0] host_axi_bs_ibp_cmd_rgon;



 wire [1-1:0] in_5_out_0_ibp_cmd_chnl_valid;
 wire [1-1:0] in_5_out_0_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_5_out_0_ibp_cmd_chnl;

 wire [1-1:0] in_5_out_0_ibp_wd_chnl_valid;
 wire [1-1:0] in_5_out_0_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] in_5_out_0_ibp_wd_chnl;

 wire [1-1:0] in_5_out_0_ibp_rd_chnl_accept;
 wire [1-1:0] in_5_out_0_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] in_5_out_0_ibp_rd_chnl;

 wire [1-1:0] in_5_out_0_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_5_out_0_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_5_out_0_ibp_wrsp_chnl;





 wire [1-1:0] in_5_out_1_ibp_cmd_chnl_valid;
 wire [1-1:0] in_5_out_1_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_5_out_1_ibp_cmd_chnl;

 wire [1-1:0] in_5_out_1_ibp_wd_chnl_valid;
 wire [1-1:0] in_5_out_1_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] in_5_out_1_ibp_wd_chnl;

 wire [1-1:0] in_5_out_1_ibp_rd_chnl_accept;
 wire [1-1:0] in_5_out_1_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] in_5_out_1_ibp_rd_chnl;

 wire [1-1:0] in_5_out_1_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_5_out_1_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_5_out_1_ibp_wrsp_chnl;





 wire [1-1:0] in_5_out_2_ibp_cmd_chnl_valid;
 wire [1-1:0] in_5_out_2_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_5_out_2_ibp_cmd_chnl;

 wire [1-1:0] in_5_out_2_ibp_wd_chnl_valid;
 wire [1-1:0] in_5_out_2_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] in_5_out_2_ibp_wd_chnl;

 wire [1-1:0] in_5_out_2_ibp_rd_chnl_accept;
 wire [1-1:0] in_5_out_2_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] in_5_out_2_ibp_rd_chnl;

 wire [1-1:0] in_5_out_2_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_5_out_2_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_5_out_2_ibp_wrsp_chnl;





 wire [1-1:0] in_5_out_3_ibp_cmd_chnl_valid;
 wire [1-1:0] in_5_out_3_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_5_out_3_ibp_cmd_chnl;

 wire [1-1:0] in_5_out_3_ibp_wd_chnl_valid;
 wire [1-1:0] in_5_out_3_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] in_5_out_3_ibp_wd_chnl;

 wire [1-1:0] in_5_out_3_ibp_rd_chnl_accept;
 wire [1-1:0] in_5_out_3_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] in_5_out_3_ibp_rd_chnl;

 wire [1-1:0] in_5_out_3_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_5_out_3_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_5_out_3_ibp_wrsp_chnl;





 wire [1-1:0] in_5_out_4_ibp_cmd_chnl_valid;
 wire [1-1:0] in_5_out_4_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_5_out_4_ibp_cmd_chnl;

 wire [1-1:0] in_5_out_4_ibp_wd_chnl_valid;
 wire [1-1:0] in_5_out_4_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] in_5_out_4_ibp_wd_chnl;

 wire [1-1:0] in_5_out_4_ibp_rd_chnl_accept;
 wire [1-1:0] in_5_out_4_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] in_5_out_4_ibp_rd_chnl;

 wire [1-1:0] in_5_out_4_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_5_out_4_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_5_out_4_ibp_wrsp_chnl;



wire [4 : 0] bri4tb_bs_ibp_cmd_rgon;



 wire [1-1:0] in_6_out_0_ibp_cmd_chnl_valid;
 wire [1-1:0] in_6_out_0_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_6_out_0_ibp_cmd_chnl;

 wire [1-1:0] in_6_out_0_ibp_wd_chnl_valid;
 wire [1-1:0] in_6_out_0_ibp_wd_chnl_accept;
 wire [37 * 1 -1:0] in_6_out_0_ibp_wd_chnl;

 wire [1-1:0] in_6_out_0_ibp_rd_chnl_accept;
 wire [1-1:0] in_6_out_0_ibp_rd_chnl_valid;
 wire [35 * 1 -1:0] in_6_out_0_ibp_rd_chnl;

 wire [1-1:0] in_6_out_0_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_6_out_0_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_6_out_0_ibp_wrsp_chnl;





 wire [1-1:0] in_6_out_1_ibp_cmd_chnl_valid;
 wire [1-1:0] in_6_out_1_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_6_out_1_ibp_cmd_chnl;

 wire [1-1:0] in_6_out_1_ibp_wd_chnl_valid;
 wire [1-1:0] in_6_out_1_ibp_wd_chnl_accept;
 wire [37 * 1 -1:0] in_6_out_1_ibp_wd_chnl;

 wire [1-1:0] in_6_out_1_ibp_rd_chnl_accept;
 wire [1-1:0] in_6_out_1_ibp_rd_chnl_valid;
 wire [35 * 1 -1:0] in_6_out_1_ibp_rd_chnl;

 wire [1-1:0] in_6_out_1_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_6_out_1_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_6_out_1_ibp_wrsp_chnl;





 wire [1-1:0] in_6_out_2_ibp_cmd_chnl_valid;
 wire [1-1:0] in_6_out_2_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_6_out_2_ibp_cmd_chnl;

 wire [1-1:0] in_6_out_2_ibp_wd_chnl_valid;
 wire [1-1:0] in_6_out_2_ibp_wd_chnl_accept;
 wire [37 * 1 -1:0] in_6_out_2_ibp_wd_chnl;

 wire [1-1:0] in_6_out_2_ibp_rd_chnl_accept;
 wire [1-1:0] in_6_out_2_ibp_rd_chnl_valid;
 wire [35 * 1 -1:0] in_6_out_2_ibp_rd_chnl;

 wire [1-1:0] in_6_out_2_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_6_out_2_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_6_out_2_ibp_wrsp_chnl;





 wire [1-1:0] in_6_out_3_ibp_cmd_chnl_valid;
 wire [1-1:0] in_6_out_3_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_6_out_3_ibp_cmd_chnl;

 wire [1-1:0] in_6_out_3_ibp_wd_chnl_valid;
 wire [1-1:0] in_6_out_3_ibp_wd_chnl_accept;
 wire [37 * 1 -1:0] in_6_out_3_ibp_wd_chnl;

 wire [1-1:0] in_6_out_3_ibp_rd_chnl_accept;
 wire [1-1:0] in_6_out_3_ibp_rd_chnl_valid;
 wire [35 * 1 -1:0] in_6_out_3_ibp_rd_chnl;

 wire [1-1:0] in_6_out_3_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_6_out_3_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_6_out_3_ibp_wrsp_chnl;





 wire [1-1:0] in_6_out_4_ibp_cmd_chnl_valid;
 wire [1-1:0] in_6_out_4_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] in_6_out_4_ibp_cmd_chnl;

 wire [1-1:0] in_6_out_4_ibp_wd_chnl_valid;
 wire [1-1:0] in_6_out_4_ibp_wd_chnl_accept;
 wire [37 * 1 -1:0] in_6_out_4_ibp_wd_chnl;

 wire [1-1:0] in_6_out_4_ibp_rd_chnl_accept;
 wire [1-1:0] in_6_out_4_ibp_rd_chnl_valid;
 wire [35 * 1 -1:0] in_6_out_4_ibp_rd_chnl;

 wire [1-1:0] in_6_out_4_ibp_wrsp_chnl_valid;
 wire [1-1:0] in_6_out_4_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] in_6_out_4_ibp_wrsp_chnl;



//
// Instantiation for each master port
//
mss_bus_switch_dw64_slv u_mss_bs_slv_0 (























    .dw64_in_ibp_cmd_rgon (npu_mst0_axi_bs_ibp_cmd_rgon),

  .dw64_in_ibp_cmd_valid             (npu_mst0_axi_bs_ibp_cmd_valid),
  .dw64_in_ibp_cmd_accept            (npu_mst0_axi_bs_ibp_cmd_accept),
  .dw64_in_ibp_cmd_read              (npu_mst0_axi_bs_ibp_cmd_read),
  .dw64_in_ibp_cmd_addr              (npu_mst0_axi_bs_ibp_cmd_addr),
  .dw64_in_ibp_cmd_wrap              (npu_mst0_axi_bs_ibp_cmd_wrap),
  .dw64_in_ibp_cmd_data_size         (npu_mst0_axi_bs_ibp_cmd_data_size),
  .dw64_in_ibp_cmd_burst_size        (npu_mst0_axi_bs_ibp_cmd_burst_size),
  .dw64_in_ibp_cmd_prot              (npu_mst0_axi_bs_ibp_cmd_prot),
  .dw64_in_ibp_cmd_cache             (npu_mst0_axi_bs_ibp_cmd_cache),
  .dw64_in_ibp_cmd_lock              (npu_mst0_axi_bs_ibp_cmd_lock),
  .dw64_in_ibp_cmd_excl              (npu_mst0_axi_bs_ibp_cmd_excl),

  .dw64_in_ibp_rd_valid              (npu_mst0_axi_bs_ibp_rd_valid),
  .dw64_in_ibp_rd_excl_ok            (npu_mst0_axi_bs_ibp_rd_excl_ok),
  .dw64_in_ibp_rd_accept             (npu_mst0_axi_bs_ibp_rd_accept),
  .dw64_in_ibp_err_rd                (npu_mst0_axi_bs_ibp_err_rd),
  .dw64_in_ibp_rd_data               (npu_mst0_axi_bs_ibp_rd_data),
  .dw64_in_ibp_rd_last               (npu_mst0_axi_bs_ibp_rd_last),

  .dw64_in_ibp_wr_valid              (npu_mst0_axi_bs_ibp_wr_valid),
  .dw64_in_ibp_wr_accept             (npu_mst0_axi_bs_ibp_wr_accept),
  .dw64_in_ibp_wr_data               (npu_mst0_axi_bs_ibp_wr_data),
  .dw64_in_ibp_wr_mask               (npu_mst0_axi_bs_ibp_wr_mask),
  .dw64_in_ibp_wr_last               (npu_mst0_axi_bs_ibp_wr_last),

  .dw64_in_ibp_wr_done               (npu_mst0_axi_bs_ibp_wr_done),
  .dw64_in_ibp_wr_excl_done          (npu_mst0_axi_bs_ibp_wr_excl_done),
  .dw64_in_ibp_err_wr                (npu_mst0_axi_bs_ibp_err_wr),
  .dw64_in_ibp_wr_resp_accept        (npu_mst0_axi_bs_ibp_wr_resp_accept),




    .dw64_out_0_ibp_cmd_chnl_valid  (in_0_out_0_ibp_cmd_chnl_valid),
    .dw64_out_0_ibp_cmd_chnl_accept (in_0_out_0_ibp_cmd_chnl_accept),
    .dw64_out_0_ibp_cmd_chnl        (in_0_out_0_ibp_cmd_chnl),

    .dw64_out_0_ibp_rd_chnl_valid   (in_0_out_0_ibp_rd_chnl_valid),
    .dw64_out_0_ibp_rd_chnl_accept  (in_0_out_0_ibp_rd_chnl_accept),
    .dw64_out_0_ibp_rd_chnl         (in_0_out_0_ibp_rd_chnl),

    .dw64_out_0_ibp_wd_chnl_valid   (in_0_out_0_ibp_wd_chnl_valid),
    .dw64_out_0_ibp_wd_chnl_accept  (in_0_out_0_ibp_wd_chnl_accept),
    .dw64_out_0_ibp_wd_chnl         (in_0_out_0_ibp_wd_chnl),

    .dw64_out_0_ibp_wrsp_chnl_valid (in_0_out_0_ibp_wrsp_chnl_valid),
    .dw64_out_0_ibp_wrsp_chnl_accept(in_0_out_0_ibp_wrsp_chnl_accept),
    .dw64_out_0_ibp_wrsp_chnl       (in_0_out_0_ibp_wrsp_chnl),





    .dw64_out_1_ibp_cmd_chnl_valid  (in_0_out_1_ibp_cmd_chnl_valid),
    .dw64_out_1_ibp_cmd_chnl_accept (in_0_out_1_ibp_cmd_chnl_accept),
    .dw64_out_1_ibp_cmd_chnl        (in_0_out_1_ibp_cmd_chnl),

    .dw64_out_1_ibp_rd_chnl_valid   (in_0_out_1_ibp_rd_chnl_valid),
    .dw64_out_1_ibp_rd_chnl_accept  (in_0_out_1_ibp_rd_chnl_accept),
    .dw64_out_1_ibp_rd_chnl         (in_0_out_1_ibp_rd_chnl),

    .dw64_out_1_ibp_wd_chnl_valid   (in_0_out_1_ibp_wd_chnl_valid),
    .dw64_out_1_ibp_wd_chnl_accept  (in_0_out_1_ibp_wd_chnl_accept),
    .dw64_out_1_ibp_wd_chnl         (in_0_out_1_ibp_wd_chnl),

    .dw64_out_1_ibp_wrsp_chnl_valid (in_0_out_1_ibp_wrsp_chnl_valid),
    .dw64_out_1_ibp_wrsp_chnl_accept(in_0_out_1_ibp_wrsp_chnl_accept),
    .dw64_out_1_ibp_wrsp_chnl       (in_0_out_1_ibp_wrsp_chnl),





    .dw64_out_2_ibp_cmd_chnl_valid  (in_0_out_2_ibp_cmd_chnl_valid),
    .dw64_out_2_ibp_cmd_chnl_accept (in_0_out_2_ibp_cmd_chnl_accept),
    .dw64_out_2_ibp_cmd_chnl        (in_0_out_2_ibp_cmd_chnl),

    .dw64_out_2_ibp_rd_chnl_valid   (in_0_out_2_ibp_rd_chnl_valid),
    .dw64_out_2_ibp_rd_chnl_accept  (in_0_out_2_ibp_rd_chnl_accept),
    .dw64_out_2_ibp_rd_chnl         (in_0_out_2_ibp_rd_chnl),

    .dw64_out_2_ibp_wd_chnl_valid   (in_0_out_2_ibp_wd_chnl_valid),
    .dw64_out_2_ibp_wd_chnl_accept  (in_0_out_2_ibp_wd_chnl_accept),
    .dw64_out_2_ibp_wd_chnl         (in_0_out_2_ibp_wd_chnl),

    .dw64_out_2_ibp_wrsp_chnl_valid (in_0_out_2_ibp_wrsp_chnl_valid),
    .dw64_out_2_ibp_wrsp_chnl_accept(in_0_out_2_ibp_wrsp_chnl_accept),
    .dw64_out_2_ibp_wrsp_chnl       (in_0_out_2_ibp_wrsp_chnl),





    .dw64_out_3_ibp_cmd_chnl_valid  (in_0_out_3_ibp_cmd_chnl_valid),
    .dw64_out_3_ibp_cmd_chnl_accept (in_0_out_3_ibp_cmd_chnl_accept),
    .dw64_out_3_ibp_cmd_chnl        (in_0_out_3_ibp_cmd_chnl),

    .dw64_out_3_ibp_rd_chnl_valid   (in_0_out_3_ibp_rd_chnl_valid),
    .dw64_out_3_ibp_rd_chnl_accept  (in_0_out_3_ibp_rd_chnl_accept),
    .dw64_out_3_ibp_rd_chnl         (in_0_out_3_ibp_rd_chnl),

    .dw64_out_3_ibp_wd_chnl_valid   (in_0_out_3_ibp_wd_chnl_valid),
    .dw64_out_3_ibp_wd_chnl_accept  (in_0_out_3_ibp_wd_chnl_accept),
    .dw64_out_3_ibp_wd_chnl         (in_0_out_3_ibp_wd_chnl),

    .dw64_out_3_ibp_wrsp_chnl_valid (in_0_out_3_ibp_wrsp_chnl_valid),
    .dw64_out_3_ibp_wrsp_chnl_accept(in_0_out_3_ibp_wrsp_chnl_accept),
    .dw64_out_3_ibp_wrsp_chnl       (in_0_out_3_ibp_wrsp_chnl),





    .dw64_out_4_ibp_cmd_chnl_valid  (in_0_out_4_ibp_cmd_chnl_valid),
    .dw64_out_4_ibp_cmd_chnl_accept (in_0_out_4_ibp_cmd_chnl_accept),
    .dw64_out_4_ibp_cmd_chnl        (in_0_out_4_ibp_cmd_chnl),

    .dw64_out_4_ibp_rd_chnl_valid   (in_0_out_4_ibp_rd_chnl_valid),
    .dw64_out_4_ibp_rd_chnl_accept  (in_0_out_4_ibp_rd_chnl_accept),
    .dw64_out_4_ibp_rd_chnl         (in_0_out_4_ibp_rd_chnl),

    .dw64_out_4_ibp_wd_chnl_valid   (in_0_out_4_ibp_wd_chnl_valid),
    .dw64_out_4_ibp_wd_chnl_accept  (in_0_out_4_ibp_wd_chnl_accept),
    .dw64_out_4_ibp_wd_chnl         (in_0_out_4_ibp_wd_chnl),

    .dw64_out_4_ibp_wrsp_chnl_valid (in_0_out_4_ibp_wrsp_chnl_valid),
    .dw64_out_4_ibp_wrsp_chnl_accept(in_0_out_4_ibp_wrsp_chnl_accept),
    .dw64_out_4_ibp_wrsp_chnl       (in_0_out_4_ibp_wrsp_chnl),



.clk         (clk),
.sync_rst_r  (rst_a),
.async_rst   (rst_a),
.rst_a       (rst_a)
);
mss_bus_switch_dw512_slv u_mss_bs_slv_1 (























    .dw512_in_ibp_cmd_rgon (npu_mst1_axi_bs_ibp_cmd_rgon),

  .dw512_in_ibp_cmd_valid             (npu_mst1_axi_bs_ibp_cmd_valid),
  .dw512_in_ibp_cmd_accept            (npu_mst1_axi_bs_ibp_cmd_accept),
  .dw512_in_ibp_cmd_read              (npu_mst1_axi_bs_ibp_cmd_read),
  .dw512_in_ibp_cmd_addr              (npu_mst1_axi_bs_ibp_cmd_addr),
  .dw512_in_ibp_cmd_wrap              (npu_mst1_axi_bs_ibp_cmd_wrap),
  .dw512_in_ibp_cmd_data_size         (npu_mst1_axi_bs_ibp_cmd_data_size),
  .dw512_in_ibp_cmd_burst_size        (npu_mst1_axi_bs_ibp_cmd_burst_size),
  .dw512_in_ibp_cmd_prot              (npu_mst1_axi_bs_ibp_cmd_prot),
  .dw512_in_ibp_cmd_cache             (npu_mst1_axi_bs_ibp_cmd_cache),
  .dw512_in_ibp_cmd_lock              (npu_mst1_axi_bs_ibp_cmd_lock),
  .dw512_in_ibp_cmd_excl              (npu_mst1_axi_bs_ibp_cmd_excl),

  .dw512_in_ibp_rd_valid              (npu_mst1_axi_bs_ibp_rd_valid),
  .dw512_in_ibp_rd_excl_ok            (npu_mst1_axi_bs_ibp_rd_excl_ok),
  .dw512_in_ibp_rd_accept             (npu_mst1_axi_bs_ibp_rd_accept),
  .dw512_in_ibp_err_rd                (npu_mst1_axi_bs_ibp_err_rd),
  .dw512_in_ibp_rd_data               (npu_mst1_axi_bs_ibp_rd_data),
  .dw512_in_ibp_rd_last               (npu_mst1_axi_bs_ibp_rd_last),

  .dw512_in_ibp_wr_valid              (npu_mst1_axi_bs_ibp_wr_valid),
  .dw512_in_ibp_wr_accept             (npu_mst1_axi_bs_ibp_wr_accept),
  .dw512_in_ibp_wr_data               (npu_mst1_axi_bs_ibp_wr_data),
  .dw512_in_ibp_wr_mask               (npu_mst1_axi_bs_ibp_wr_mask),
  .dw512_in_ibp_wr_last               (npu_mst1_axi_bs_ibp_wr_last),

  .dw512_in_ibp_wr_done               (npu_mst1_axi_bs_ibp_wr_done),
  .dw512_in_ibp_wr_excl_done          (npu_mst1_axi_bs_ibp_wr_excl_done),
  .dw512_in_ibp_err_wr                (npu_mst1_axi_bs_ibp_err_wr),
  .dw512_in_ibp_wr_resp_accept        (npu_mst1_axi_bs_ibp_wr_resp_accept),




    .dw512_out_0_ibp_cmd_chnl_valid  (in_1_out_0_ibp_cmd_chnl_valid),
    .dw512_out_0_ibp_cmd_chnl_accept (in_1_out_0_ibp_cmd_chnl_accept),
    .dw512_out_0_ibp_cmd_chnl        (in_1_out_0_ibp_cmd_chnl),

    .dw512_out_0_ibp_rd_chnl_valid   (in_1_out_0_ibp_rd_chnl_valid),
    .dw512_out_0_ibp_rd_chnl_accept  (in_1_out_0_ibp_rd_chnl_accept),
    .dw512_out_0_ibp_rd_chnl         (in_1_out_0_ibp_rd_chnl),

    .dw512_out_0_ibp_wd_chnl_valid   (in_1_out_0_ibp_wd_chnl_valid),
    .dw512_out_0_ibp_wd_chnl_accept  (in_1_out_0_ibp_wd_chnl_accept),
    .dw512_out_0_ibp_wd_chnl         (in_1_out_0_ibp_wd_chnl),

    .dw512_out_0_ibp_wrsp_chnl_valid (in_1_out_0_ibp_wrsp_chnl_valid),
    .dw512_out_0_ibp_wrsp_chnl_accept(in_1_out_0_ibp_wrsp_chnl_accept),
    .dw512_out_0_ibp_wrsp_chnl       (in_1_out_0_ibp_wrsp_chnl),





    .dw512_out_1_ibp_cmd_chnl_valid  (in_1_out_1_ibp_cmd_chnl_valid),
    .dw512_out_1_ibp_cmd_chnl_accept (in_1_out_1_ibp_cmd_chnl_accept),
    .dw512_out_1_ibp_cmd_chnl        (in_1_out_1_ibp_cmd_chnl),

    .dw512_out_1_ibp_rd_chnl_valid   (in_1_out_1_ibp_rd_chnl_valid),
    .dw512_out_1_ibp_rd_chnl_accept  (in_1_out_1_ibp_rd_chnl_accept),
    .dw512_out_1_ibp_rd_chnl         (in_1_out_1_ibp_rd_chnl),

    .dw512_out_1_ibp_wd_chnl_valid   (in_1_out_1_ibp_wd_chnl_valid),
    .dw512_out_1_ibp_wd_chnl_accept  (in_1_out_1_ibp_wd_chnl_accept),
    .dw512_out_1_ibp_wd_chnl         (in_1_out_1_ibp_wd_chnl),

    .dw512_out_1_ibp_wrsp_chnl_valid (in_1_out_1_ibp_wrsp_chnl_valid),
    .dw512_out_1_ibp_wrsp_chnl_accept(in_1_out_1_ibp_wrsp_chnl_accept),
    .dw512_out_1_ibp_wrsp_chnl       (in_1_out_1_ibp_wrsp_chnl),





    .dw512_out_2_ibp_cmd_chnl_valid  (in_1_out_2_ibp_cmd_chnl_valid),
    .dw512_out_2_ibp_cmd_chnl_accept (in_1_out_2_ibp_cmd_chnl_accept),
    .dw512_out_2_ibp_cmd_chnl        (in_1_out_2_ibp_cmd_chnl),

    .dw512_out_2_ibp_rd_chnl_valid   (in_1_out_2_ibp_rd_chnl_valid),
    .dw512_out_2_ibp_rd_chnl_accept  (in_1_out_2_ibp_rd_chnl_accept),
    .dw512_out_2_ibp_rd_chnl         (in_1_out_2_ibp_rd_chnl),

    .dw512_out_2_ibp_wd_chnl_valid   (in_1_out_2_ibp_wd_chnl_valid),
    .dw512_out_2_ibp_wd_chnl_accept  (in_1_out_2_ibp_wd_chnl_accept),
    .dw512_out_2_ibp_wd_chnl         (in_1_out_2_ibp_wd_chnl),

    .dw512_out_2_ibp_wrsp_chnl_valid (in_1_out_2_ibp_wrsp_chnl_valid),
    .dw512_out_2_ibp_wrsp_chnl_accept(in_1_out_2_ibp_wrsp_chnl_accept),
    .dw512_out_2_ibp_wrsp_chnl       (in_1_out_2_ibp_wrsp_chnl),





    .dw512_out_3_ibp_cmd_chnl_valid  (in_1_out_3_ibp_cmd_chnl_valid),
    .dw512_out_3_ibp_cmd_chnl_accept (in_1_out_3_ibp_cmd_chnl_accept),
    .dw512_out_3_ibp_cmd_chnl        (in_1_out_3_ibp_cmd_chnl),

    .dw512_out_3_ibp_rd_chnl_valid   (in_1_out_3_ibp_rd_chnl_valid),
    .dw512_out_3_ibp_rd_chnl_accept  (in_1_out_3_ibp_rd_chnl_accept),
    .dw512_out_3_ibp_rd_chnl         (in_1_out_3_ibp_rd_chnl),

    .dw512_out_3_ibp_wd_chnl_valid   (in_1_out_3_ibp_wd_chnl_valid),
    .dw512_out_3_ibp_wd_chnl_accept  (in_1_out_3_ibp_wd_chnl_accept),
    .dw512_out_3_ibp_wd_chnl         (in_1_out_3_ibp_wd_chnl),

    .dw512_out_3_ibp_wrsp_chnl_valid (in_1_out_3_ibp_wrsp_chnl_valid),
    .dw512_out_3_ibp_wrsp_chnl_accept(in_1_out_3_ibp_wrsp_chnl_accept),
    .dw512_out_3_ibp_wrsp_chnl       (in_1_out_3_ibp_wrsp_chnl),





    .dw512_out_4_ibp_cmd_chnl_valid  (in_1_out_4_ibp_cmd_chnl_valid),
    .dw512_out_4_ibp_cmd_chnl_accept (in_1_out_4_ibp_cmd_chnl_accept),
    .dw512_out_4_ibp_cmd_chnl        (in_1_out_4_ibp_cmd_chnl),

    .dw512_out_4_ibp_rd_chnl_valid   (in_1_out_4_ibp_rd_chnl_valid),
    .dw512_out_4_ibp_rd_chnl_accept  (in_1_out_4_ibp_rd_chnl_accept),
    .dw512_out_4_ibp_rd_chnl         (in_1_out_4_ibp_rd_chnl),

    .dw512_out_4_ibp_wd_chnl_valid   (in_1_out_4_ibp_wd_chnl_valid),
    .dw512_out_4_ibp_wd_chnl_accept  (in_1_out_4_ibp_wd_chnl_accept),
    .dw512_out_4_ibp_wd_chnl         (in_1_out_4_ibp_wd_chnl),

    .dw512_out_4_ibp_wrsp_chnl_valid (in_1_out_4_ibp_wrsp_chnl_valid),
    .dw512_out_4_ibp_wrsp_chnl_accept(in_1_out_4_ibp_wrsp_chnl_accept),
    .dw512_out_4_ibp_wrsp_chnl       (in_1_out_4_ibp_wrsp_chnl),



.clk         (clk),
.sync_rst_r  (rst_a),
.async_rst   (rst_a),
.rst_a       (rst_a)
);
mss_bus_switch_dw512_slv u_mss_bs_slv_2 (























    .dw512_in_ibp_cmd_rgon (npu_mst2_axi_bs_ibp_cmd_rgon),

  .dw512_in_ibp_cmd_valid             (npu_mst2_axi_bs_ibp_cmd_valid),
  .dw512_in_ibp_cmd_accept            (npu_mst2_axi_bs_ibp_cmd_accept),
  .dw512_in_ibp_cmd_read              (npu_mst2_axi_bs_ibp_cmd_read),
  .dw512_in_ibp_cmd_addr              (npu_mst2_axi_bs_ibp_cmd_addr),
  .dw512_in_ibp_cmd_wrap              (npu_mst2_axi_bs_ibp_cmd_wrap),
  .dw512_in_ibp_cmd_data_size         (npu_mst2_axi_bs_ibp_cmd_data_size),
  .dw512_in_ibp_cmd_burst_size        (npu_mst2_axi_bs_ibp_cmd_burst_size),
  .dw512_in_ibp_cmd_prot              (npu_mst2_axi_bs_ibp_cmd_prot),
  .dw512_in_ibp_cmd_cache             (npu_mst2_axi_bs_ibp_cmd_cache),
  .dw512_in_ibp_cmd_lock              (npu_mst2_axi_bs_ibp_cmd_lock),
  .dw512_in_ibp_cmd_excl              (npu_mst2_axi_bs_ibp_cmd_excl),

  .dw512_in_ibp_rd_valid              (npu_mst2_axi_bs_ibp_rd_valid),
  .dw512_in_ibp_rd_excl_ok            (npu_mst2_axi_bs_ibp_rd_excl_ok),
  .dw512_in_ibp_rd_accept             (npu_mst2_axi_bs_ibp_rd_accept),
  .dw512_in_ibp_err_rd                (npu_mst2_axi_bs_ibp_err_rd),
  .dw512_in_ibp_rd_data               (npu_mst2_axi_bs_ibp_rd_data),
  .dw512_in_ibp_rd_last               (npu_mst2_axi_bs_ibp_rd_last),

  .dw512_in_ibp_wr_valid              (npu_mst2_axi_bs_ibp_wr_valid),
  .dw512_in_ibp_wr_accept             (npu_mst2_axi_bs_ibp_wr_accept),
  .dw512_in_ibp_wr_data               (npu_mst2_axi_bs_ibp_wr_data),
  .dw512_in_ibp_wr_mask               (npu_mst2_axi_bs_ibp_wr_mask),
  .dw512_in_ibp_wr_last               (npu_mst2_axi_bs_ibp_wr_last),

  .dw512_in_ibp_wr_done               (npu_mst2_axi_bs_ibp_wr_done),
  .dw512_in_ibp_wr_excl_done          (npu_mst2_axi_bs_ibp_wr_excl_done),
  .dw512_in_ibp_err_wr                (npu_mst2_axi_bs_ibp_err_wr),
  .dw512_in_ibp_wr_resp_accept        (npu_mst2_axi_bs_ibp_wr_resp_accept),




    .dw512_out_0_ibp_cmd_chnl_valid  (in_2_out_0_ibp_cmd_chnl_valid),
    .dw512_out_0_ibp_cmd_chnl_accept (in_2_out_0_ibp_cmd_chnl_accept),
    .dw512_out_0_ibp_cmd_chnl        (in_2_out_0_ibp_cmd_chnl),

    .dw512_out_0_ibp_rd_chnl_valid   (in_2_out_0_ibp_rd_chnl_valid),
    .dw512_out_0_ibp_rd_chnl_accept  (in_2_out_0_ibp_rd_chnl_accept),
    .dw512_out_0_ibp_rd_chnl         (in_2_out_0_ibp_rd_chnl),

    .dw512_out_0_ibp_wd_chnl_valid   (in_2_out_0_ibp_wd_chnl_valid),
    .dw512_out_0_ibp_wd_chnl_accept  (in_2_out_0_ibp_wd_chnl_accept),
    .dw512_out_0_ibp_wd_chnl         (in_2_out_0_ibp_wd_chnl),

    .dw512_out_0_ibp_wrsp_chnl_valid (in_2_out_0_ibp_wrsp_chnl_valid),
    .dw512_out_0_ibp_wrsp_chnl_accept(in_2_out_0_ibp_wrsp_chnl_accept),
    .dw512_out_0_ibp_wrsp_chnl       (in_2_out_0_ibp_wrsp_chnl),





    .dw512_out_1_ibp_cmd_chnl_valid  (in_2_out_1_ibp_cmd_chnl_valid),
    .dw512_out_1_ibp_cmd_chnl_accept (in_2_out_1_ibp_cmd_chnl_accept),
    .dw512_out_1_ibp_cmd_chnl        (in_2_out_1_ibp_cmd_chnl),

    .dw512_out_1_ibp_rd_chnl_valid   (in_2_out_1_ibp_rd_chnl_valid),
    .dw512_out_1_ibp_rd_chnl_accept  (in_2_out_1_ibp_rd_chnl_accept),
    .dw512_out_1_ibp_rd_chnl         (in_2_out_1_ibp_rd_chnl),

    .dw512_out_1_ibp_wd_chnl_valid   (in_2_out_1_ibp_wd_chnl_valid),
    .dw512_out_1_ibp_wd_chnl_accept  (in_2_out_1_ibp_wd_chnl_accept),
    .dw512_out_1_ibp_wd_chnl         (in_2_out_1_ibp_wd_chnl),

    .dw512_out_1_ibp_wrsp_chnl_valid (in_2_out_1_ibp_wrsp_chnl_valid),
    .dw512_out_1_ibp_wrsp_chnl_accept(in_2_out_1_ibp_wrsp_chnl_accept),
    .dw512_out_1_ibp_wrsp_chnl       (in_2_out_1_ibp_wrsp_chnl),





    .dw512_out_2_ibp_cmd_chnl_valid  (in_2_out_2_ibp_cmd_chnl_valid),
    .dw512_out_2_ibp_cmd_chnl_accept (in_2_out_2_ibp_cmd_chnl_accept),
    .dw512_out_2_ibp_cmd_chnl        (in_2_out_2_ibp_cmd_chnl),

    .dw512_out_2_ibp_rd_chnl_valid   (in_2_out_2_ibp_rd_chnl_valid),
    .dw512_out_2_ibp_rd_chnl_accept  (in_2_out_2_ibp_rd_chnl_accept),
    .dw512_out_2_ibp_rd_chnl         (in_2_out_2_ibp_rd_chnl),

    .dw512_out_2_ibp_wd_chnl_valid   (in_2_out_2_ibp_wd_chnl_valid),
    .dw512_out_2_ibp_wd_chnl_accept  (in_2_out_2_ibp_wd_chnl_accept),
    .dw512_out_2_ibp_wd_chnl         (in_2_out_2_ibp_wd_chnl),

    .dw512_out_2_ibp_wrsp_chnl_valid (in_2_out_2_ibp_wrsp_chnl_valid),
    .dw512_out_2_ibp_wrsp_chnl_accept(in_2_out_2_ibp_wrsp_chnl_accept),
    .dw512_out_2_ibp_wrsp_chnl       (in_2_out_2_ibp_wrsp_chnl),





    .dw512_out_3_ibp_cmd_chnl_valid  (in_2_out_3_ibp_cmd_chnl_valid),
    .dw512_out_3_ibp_cmd_chnl_accept (in_2_out_3_ibp_cmd_chnl_accept),
    .dw512_out_3_ibp_cmd_chnl        (in_2_out_3_ibp_cmd_chnl),

    .dw512_out_3_ibp_rd_chnl_valid   (in_2_out_3_ibp_rd_chnl_valid),
    .dw512_out_3_ibp_rd_chnl_accept  (in_2_out_3_ibp_rd_chnl_accept),
    .dw512_out_3_ibp_rd_chnl         (in_2_out_3_ibp_rd_chnl),

    .dw512_out_3_ibp_wd_chnl_valid   (in_2_out_3_ibp_wd_chnl_valid),
    .dw512_out_3_ibp_wd_chnl_accept  (in_2_out_3_ibp_wd_chnl_accept),
    .dw512_out_3_ibp_wd_chnl         (in_2_out_3_ibp_wd_chnl),

    .dw512_out_3_ibp_wrsp_chnl_valid (in_2_out_3_ibp_wrsp_chnl_valid),
    .dw512_out_3_ibp_wrsp_chnl_accept(in_2_out_3_ibp_wrsp_chnl_accept),
    .dw512_out_3_ibp_wrsp_chnl       (in_2_out_3_ibp_wrsp_chnl),





    .dw512_out_4_ibp_cmd_chnl_valid  (in_2_out_4_ibp_cmd_chnl_valid),
    .dw512_out_4_ibp_cmd_chnl_accept (in_2_out_4_ibp_cmd_chnl_accept),
    .dw512_out_4_ibp_cmd_chnl        (in_2_out_4_ibp_cmd_chnl),

    .dw512_out_4_ibp_rd_chnl_valid   (in_2_out_4_ibp_rd_chnl_valid),
    .dw512_out_4_ibp_rd_chnl_accept  (in_2_out_4_ibp_rd_chnl_accept),
    .dw512_out_4_ibp_rd_chnl         (in_2_out_4_ibp_rd_chnl),

    .dw512_out_4_ibp_wd_chnl_valid   (in_2_out_4_ibp_wd_chnl_valid),
    .dw512_out_4_ibp_wd_chnl_accept  (in_2_out_4_ibp_wd_chnl_accept),
    .dw512_out_4_ibp_wd_chnl         (in_2_out_4_ibp_wd_chnl),

    .dw512_out_4_ibp_wrsp_chnl_valid (in_2_out_4_ibp_wrsp_chnl_valid),
    .dw512_out_4_ibp_wrsp_chnl_accept(in_2_out_4_ibp_wrsp_chnl_accept),
    .dw512_out_4_ibp_wrsp_chnl       (in_2_out_4_ibp_wrsp_chnl),



.clk         (clk),
.sync_rst_r  (rst_a),
.async_rst   (rst_a),
.rst_a       (rst_a)
);
mss_bus_switch_dw512_slv u_mss_bs_slv_3 (























    .dw512_in_ibp_cmd_rgon (npu_mst3_axi_bs_ibp_cmd_rgon),

  .dw512_in_ibp_cmd_valid             (npu_mst3_axi_bs_ibp_cmd_valid),
  .dw512_in_ibp_cmd_accept            (npu_mst3_axi_bs_ibp_cmd_accept),
  .dw512_in_ibp_cmd_read              (npu_mst3_axi_bs_ibp_cmd_read),
  .dw512_in_ibp_cmd_addr              (npu_mst3_axi_bs_ibp_cmd_addr),
  .dw512_in_ibp_cmd_wrap              (npu_mst3_axi_bs_ibp_cmd_wrap),
  .dw512_in_ibp_cmd_data_size         (npu_mst3_axi_bs_ibp_cmd_data_size),
  .dw512_in_ibp_cmd_burst_size        (npu_mst3_axi_bs_ibp_cmd_burst_size),
  .dw512_in_ibp_cmd_prot              (npu_mst3_axi_bs_ibp_cmd_prot),
  .dw512_in_ibp_cmd_cache             (npu_mst3_axi_bs_ibp_cmd_cache),
  .dw512_in_ibp_cmd_lock              (npu_mst3_axi_bs_ibp_cmd_lock),
  .dw512_in_ibp_cmd_excl              (npu_mst3_axi_bs_ibp_cmd_excl),

  .dw512_in_ibp_rd_valid              (npu_mst3_axi_bs_ibp_rd_valid),
  .dw512_in_ibp_rd_excl_ok            (npu_mst3_axi_bs_ibp_rd_excl_ok),
  .dw512_in_ibp_rd_accept             (npu_mst3_axi_bs_ibp_rd_accept),
  .dw512_in_ibp_err_rd                (npu_mst3_axi_bs_ibp_err_rd),
  .dw512_in_ibp_rd_data               (npu_mst3_axi_bs_ibp_rd_data),
  .dw512_in_ibp_rd_last               (npu_mst3_axi_bs_ibp_rd_last),

  .dw512_in_ibp_wr_valid              (npu_mst3_axi_bs_ibp_wr_valid),
  .dw512_in_ibp_wr_accept             (npu_mst3_axi_bs_ibp_wr_accept),
  .dw512_in_ibp_wr_data               (npu_mst3_axi_bs_ibp_wr_data),
  .dw512_in_ibp_wr_mask               (npu_mst3_axi_bs_ibp_wr_mask),
  .dw512_in_ibp_wr_last               (npu_mst3_axi_bs_ibp_wr_last),

  .dw512_in_ibp_wr_done               (npu_mst3_axi_bs_ibp_wr_done),
  .dw512_in_ibp_wr_excl_done          (npu_mst3_axi_bs_ibp_wr_excl_done),
  .dw512_in_ibp_err_wr                (npu_mst3_axi_bs_ibp_err_wr),
  .dw512_in_ibp_wr_resp_accept        (npu_mst3_axi_bs_ibp_wr_resp_accept),




    .dw512_out_0_ibp_cmd_chnl_valid  (in_3_out_0_ibp_cmd_chnl_valid),
    .dw512_out_0_ibp_cmd_chnl_accept (in_3_out_0_ibp_cmd_chnl_accept),
    .dw512_out_0_ibp_cmd_chnl        (in_3_out_0_ibp_cmd_chnl),

    .dw512_out_0_ibp_rd_chnl_valid   (in_3_out_0_ibp_rd_chnl_valid),
    .dw512_out_0_ibp_rd_chnl_accept  (in_3_out_0_ibp_rd_chnl_accept),
    .dw512_out_0_ibp_rd_chnl         (in_3_out_0_ibp_rd_chnl),

    .dw512_out_0_ibp_wd_chnl_valid   (in_3_out_0_ibp_wd_chnl_valid),
    .dw512_out_0_ibp_wd_chnl_accept  (in_3_out_0_ibp_wd_chnl_accept),
    .dw512_out_0_ibp_wd_chnl         (in_3_out_0_ibp_wd_chnl),

    .dw512_out_0_ibp_wrsp_chnl_valid (in_3_out_0_ibp_wrsp_chnl_valid),
    .dw512_out_0_ibp_wrsp_chnl_accept(in_3_out_0_ibp_wrsp_chnl_accept),
    .dw512_out_0_ibp_wrsp_chnl       (in_3_out_0_ibp_wrsp_chnl),





    .dw512_out_1_ibp_cmd_chnl_valid  (in_3_out_1_ibp_cmd_chnl_valid),
    .dw512_out_1_ibp_cmd_chnl_accept (in_3_out_1_ibp_cmd_chnl_accept),
    .dw512_out_1_ibp_cmd_chnl        (in_3_out_1_ibp_cmd_chnl),

    .dw512_out_1_ibp_rd_chnl_valid   (in_3_out_1_ibp_rd_chnl_valid),
    .dw512_out_1_ibp_rd_chnl_accept  (in_3_out_1_ibp_rd_chnl_accept),
    .dw512_out_1_ibp_rd_chnl         (in_3_out_1_ibp_rd_chnl),

    .dw512_out_1_ibp_wd_chnl_valid   (in_3_out_1_ibp_wd_chnl_valid),
    .dw512_out_1_ibp_wd_chnl_accept  (in_3_out_1_ibp_wd_chnl_accept),
    .dw512_out_1_ibp_wd_chnl         (in_3_out_1_ibp_wd_chnl),

    .dw512_out_1_ibp_wrsp_chnl_valid (in_3_out_1_ibp_wrsp_chnl_valid),
    .dw512_out_1_ibp_wrsp_chnl_accept(in_3_out_1_ibp_wrsp_chnl_accept),
    .dw512_out_1_ibp_wrsp_chnl       (in_3_out_1_ibp_wrsp_chnl),





    .dw512_out_2_ibp_cmd_chnl_valid  (in_3_out_2_ibp_cmd_chnl_valid),
    .dw512_out_2_ibp_cmd_chnl_accept (in_3_out_2_ibp_cmd_chnl_accept),
    .dw512_out_2_ibp_cmd_chnl        (in_3_out_2_ibp_cmd_chnl),

    .dw512_out_2_ibp_rd_chnl_valid   (in_3_out_2_ibp_rd_chnl_valid),
    .dw512_out_2_ibp_rd_chnl_accept  (in_3_out_2_ibp_rd_chnl_accept),
    .dw512_out_2_ibp_rd_chnl         (in_3_out_2_ibp_rd_chnl),

    .dw512_out_2_ibp_wd_chnl_valid   (in_3_out_2_ibp_wd_chnl_valid),
    .dw512_out_2_ibp_wd_chnl_accept  (in_3_out_2_ibp_wd_chnl_accept),
    .dw512_out_2_ibp_wd_chnl         (in_3_out_2_ibp_wd_chnl),

    .dw512_out_2_ibp_wrsp_chnl_valid (in_3_out_2_ibp_wrsp_chnl_valid),
    .dw512_out_2_ibp_wrsp_chnl_accept(in_3_out_2_ibp_wrsp_chnl_accept),
    .dw512_out_2_ibp_wrsp_chnl       (in_3_out_2_ibp_wrsp_chnl),





    .dw512_out_3_ibp_cmd_chnl_valid  (in_3_out_3_ibp_cmd_chnl_valid),
    .dw512_out_3_ibp_cmd_chnl_accept (in_3_out_3_ibp_cmd_chnl_accept),
    .dw512_out_3_ibp_cmd_chnl        (in_3_out_3_ibp_cmd_chnl),

    .dw512_out_3_ibp_rd_chnl_valid   (in_3_out_3_ibp_rd_chnl_valid),
    .dw512_out_3_ibp_rd_chnl_accept  (in_3_out_3_ibp_rd_chnl_accept),
    .dw512_out_3_ibp_rd_chnl         (in_3_out_3_ibp_rd_chnl),

    .dw512_out_3_ibp_wd_chnl_valid   (in_3_out_3_ibp_wd_chnl_valid),
    .dw512_out_3_ibp_wd_chnl_accept  (in_3_out_3_ibp_wd_chnl_accept),
    .dw512_out_3_ibp_wd_chnl         (in_3_out_3_ibp_wd_chnl),

    .dw512_out_3_ibp_wrsp_chnl_valid (in_3_out_3_ibp_wrsp_chnl_valid),
    .dw512_out_3_ibp_wrsp_chnl_accept(in_3_out_3_ibp_wrsp_chnl_accept),
    .dw512_out_3_ibp_wrsp_chnl       (in_3_out_3_ibp_wrsp_chnl),





    .dw512_out_4_ibp_cmd_chnl_valid  (in_3_out_4_ibp_cmd_chnl_valid),
    .dw512_out_4_ibp_cmd_chnl_accept (in_3_out_4_ibp_cmd_chnl_accept),
    .dw512_out_4_ibp_cmd_chnl        (in_3_out_4_ibp_cmd_chnl),

    .dw512_out_4_ibp_rd_chnl_valid   (in_3_out_4_ibp_rd_chnl_valid),
    .dw512_out_4_ibp_rd_chnl_accept  (in_3_out_4_ibp_rd_chnl_accept),
    .dw512_out_4_ibp_rd_chnl         (in_3_out_4_ibp_rd_chnl),

    .dw512_out_4_ibp_wd_chnl_valid   (in_3_out_4_ibp_wd_chnl_valid),
    .dw512_out_4_ibp_wd_chnl_accept  (in_3_out_4_ibp_wd_chnl_accept),
    .dw512_out_4_ibp_wd_chnl         (in_3_out_4_ibp_wd_chnl),

    .dw512_out_4_ibp_wrsp_chnl_valid (in_3_out_4_ibp_wrsp_chnl_valid),
    .dw512_out_4_ibp_wrsp_chnl_accept(in_3_out_4_ibp_wrsp_chnl_accept),
    .dw512_out_4_ibp_wrsp_chnl       (in_3_out_4_ibp_wrsp_chnl),



.clk         (clk),
.sync_rst_r  (rst_a),
.async_rst   (rst_a),
.rst_a       (rst_a)
);
mss_bus_switch_dw512_slv u_mss_bs_slv_4 (























    .dw512_in_ibp_cmd_rgon (npu_mst4_axi_bs_ibp_cmd_rgon),

  .dw512_in_ibp_cmd_valid             (npu_mst4_axi_bs_ibp_cmd_valid),
  .dw512_in_ibp_cmd_accept            (npu_mst4_axi_bs_ibp_cmd_accept),
  .dw512_in_ibp_cmd_read              (npu_mst4_axi_bs_ibp_cmd_read),
  .dw512_in_ibp_cmd_addr              (npu_mst4_axi_bs_ibp_cmd_addr),
  .dw512_in_ibp_cmd_wrap              (npu_mst4_axi_bs_ibp_cmd_wrap),
  .dw512_in_ibp_cmd_data_size         (npu_mst4_axi_bs_ibp_cmd_data_size),
  .dw512_in_ibp_cmd_burst_size        (npu_mst4_axi_bs_ibp_cmd_burst_size),
  .dw512_in_ibp_cmd_prot              (npu_mst4_axi_bs_ibp_cmd_prot),
  .dw512_in_ibp_cmd_cache             (npu_mst4_axi_bs_ibp_cmd_cache),
  .dw512_in_ibp_cmd_lock              (npu_mst4_axi_bs_ibp_cmd_lock),
  .dw512_in_ibp_cmd_excl              (npu_mst4_axi_bs_ibp_cmd_excl),

  .dw512_in_ibp_rd_valid              (npu_mst4_axi_bs_ibp_rd_valid),
  .dw512_in_ibp_rd_excl_ok            (npu_mst4_axi_bs_ibp_rd_excl_ok),
  .dw512_in_ibp_rd_accept             (npu_mst4_axi_bs_ibp_rd_accept),
  .dw512_in_ibp_err_rd                (npu_mst4_axi_bs_ibp_err_rd),
  .dw512_in_ibp_rd_data               (npu_mst4_axi_bs_ibp_rd_data),
  .dw512_in_ibp_rd_last               (npu_mst4_axi_bs_ibp_rd_last),

  .dw512_in_ibp_wr_valid              (npu_mst4_axi_bs_ibp_wr_valid),
  .dw512_in_ibp_wr_accept             (npu_mst4_axi_bs_ibp_wr_accept),
  .dw512_in_ibp_wr_data               (npu_mst4_axi_bs_ibp_wr_data),
  .dw512_in_ibp_wr_mask               (npu_mst4_axi_bs_ibp_wr_mask),
  .dw512_in_ibp_wr_last               (npu_mst4_axi_bs_ibp_wr_last),

  .dw512_in_ibp_wr_done               (npu_mst4_axi_bs_ibp_wr_done),
  .dw512_in_ibp_wr_excl_done          (npu_mst4_axi_bs_ibp_wr_excl_done),
  .dw512_in_ibp_err_wr                (npu_mst4_axi_bs_ibp_err_wr),
  .dw512_in_ibp_wr_resp_accept        (npu_mst4_axi_bs_ibp_wr_resp_accept),




    .dw512_out_0_ibp_cmd_chnl_valid  (in_4_out_0_ibp_cmd_chnl_valid),
    .dw512_out_0_ibp_cmd_chnl_accept (in_4_out_0_ibp_cmd_chnl_accept),
    .dw512_out_0_ibp_cmd_chnl        (in_4_out_0_ibp_cmd_chnl),

    .dw512_out_0_ibp_rd_chnl_valid   (in_4_out_0_ibp_rd_chnl_valid),
    .dw512_out_0_ibp_rd_chnl_accept  (in_4_out_0_ibp_rd_chnl_accept),
    .dw512_out_0_ibp_rd_chnl         (in_4_out_0_ibp_rd_chnl),

    .dw512_out_0_ibp_wd_chnl_valid   (in_4_out_0_ibp_wd_chnl_valid),
    .dw512_out_0_ibp_wd_chnl_accept  (in_4_out_0_ibp_wd_chnl_accept),
    .dw512_out_0_ibp_wd_chnl         (in_4_out_0_ibp_wd_chnl),

    .dw512_out_0_ibp_wrsp_chnl_valid (in_4_out_0_ibp_wrsp_chnl_valid),
    .dw512_out_0_ibp_wrsp_chnl_accept(in_4_out_0_ibp_wrsp_chnl_accept),
    .dw512_out_0_ibp_wrsp_chnl       (in_4_out_0_ibp_wrsp_chnl),





    .dw512_out_1_ibp_cmd_chnl_valid  (in_4_out_1_ibp_cmd_chnl_valid),
    .dw512_out_1_ibp_cmd_chnl_accept (in_4_out_1_ibp_cmd_chnl_accept),
    .dw512_out_1_ibp_cmd_chnl        (in_4_out_1_ibp_cmd_chnl),

    .dw512_out_1_ibp_rd_chnl_valid   (in_4_out_1_ibp_rd_chnl_valid),
    .dw512_out_1_ibp_rd_chnl_accept  (in_4_out_1_ibp_rd_chnl_accept),
    .dw512_out_1_ibp_rd_chnl         (in_4_out_1_ibp_rd_chnl),

    .dw512_out_1_ibp_wd_chnl_valid   (in_4_out_1_ibp_wd_chnl_valid),
    .dw512_out_1_ibp_wd_chnl_accept  (in_4_out_1_ibp_wd_chnl_accept),
    .dw512_out_1_ibp_wd_chnl         (in_4_out_1_ibp_wd_chnl),

    .dw512_out_1_ibp_wrsp_chnl_valid (in_4_out_1_ibp_wrsp_chnl_valid),
    .dw512_out_1_ibp_wrsp_chnl_accept(in_4_out_1_ibp_wrsp_chnl_accept),
    .dw512_out_1_ibp_wrsp_chnl       (in_4_out_1_ibp_wrsp_chnl),





    .dw512_out_2_ibp_cmd_chnl_valid  (in_4_out_2_ibp_cmd_chnl_valid),
    .dw512_out_2_ibp_cmd_chnl_accept (in_4_out_2_ibp_cmd_chnl_accept),
    .dw512_out_2_ibp_cmd_chnl        (in_4_out_2_ibp_cmd_chnl),

    .dw512_out_2_ibp_rd_chnl_valid   (in_4_out_2_ibp_rd_chnl_valid),
    .dw512_out_2_ibp_rd_chnl_accept  (in_4_out_2_ibp_rd_chnl_accept),
    .dw512_out_2_ibp_rd_chnl         (in_4_out_2_ibp_rd_chnl),

    .dw512_out_2_ibp_wd_chnl_valid   (in_4_out_2_ibp_wd_chnl_valid),
    .dw512_out_2_ibp_wd_chnl_accept  (in_4_out_2_ibp_wd_chnl_accept),
    .dw512_out_2_ibp_wd_chnl         (in_4_out_2_ibp_wd_chnl),

    .dw512_out_2_ibp_wrsp_chnl_valid (in_4_out_2_ibp_wrsp_chnl_valid),
    .dw512_out_2_ibp_wrsp_chnl_accept(in_4_out_2_ibp_wrsp_chnl_accept),
    .dw512_out_2_ibp_wrsp_chnl       (in_4_out_2_ibp_wrsp_chnl),





    .dw512_out_3_ibp_cmd_chnl_valid  (in_4_out_3_ibp_cmd_chnl_valid),
    .dw512_out_3_ibp_cmd_chnl_accept (in_4_out_3_ibp_cmd_chnl_accept),
    .dw512_out_3_ibp_cmd_chnl        (in_4_out_3_ibp_cmd_chnl),

    .dw512_out_3_ibp_rd_chnl_valid   (in_4_out_3_ibp_rd_chnl_valid),
    .dw512_out_3_ibp_rd_chnl_accept  (in_4_out_3_ibp_rd_chnl_accept),
    .dw512_out_3_ibp_rd_chnl         (in_4_out_3_ibp_rd_chnl),

    .dw512_out_3_ibp_wd_chnl_valid   (in_4_out_3_ibp_wd_chnl_valid),
    .dw512_out_3_ibp_wd_chnl_accept  (in_4_out_3_ibp_wd_chnl_accept),
    .dw512_out_3_ibp_wd_chnl         (in_4_out_3_ibp_wd_chnl),

    .dw512_out_3_ibp_wrsp_chnl_valid (in_4_out_3_ibp_wrsp_chnl_valid),
    .dw512_out_3_ibp_wrsp_chnl_accept(in_4_out_3_ibp_wrsp_chnl_accept),
    .dw512_out_3_ibp_wrsp_chnl       (in_4_out_3_ibp_wrsp_chnl),





    .dw512_out_4_ibp_cmd_chnl_valid  (in_4_out_4_ibp_cmd_chnl_valid),
    .dw512_out_4_ibp_cmd_chnl_accept (in_4_out_4_ibp_cmd_chnl_accept),
    .dw512_out_4_ibp_cmd_chnl        (in_4_out_4_ibp_cmd_chnl),

    .dw512_out_4_ibp_rd_chnl_valid   (in_4_out_4_ibp_rd_chnl_valid),
    .dw512_out_4_ibp_rd_chnl_accept  (in_4_out_4_ibp_rd_chnl_accept),
    .dw512_out_4_ibp_rd_chnl         (in_4_out_4_ibp_rd_chnl),

    .dw512_out_4_ibp_wd_chnl_valid   (in_4_out_4_ibp_wd_chnl_valid),
    .dw512_out_4_ibp_wd_chnl_accept  (in_4_out_4_ibp_wd_chnl_accept),
    .dw512_out_4_ibp_wd_chnl         (in_4_out_4_ibp_wd_chnl),

    .dw512_out_4_ibp_wrsp_chnl_valid (in_4_out_4_ibp_wrsp_chnl_valid),
    .dw512_out_4_ibp_wrsp_chnl_accept(in_4_out_4_ibp_wrsp_chnl_accept),
    .dw512_out_4_ibp_wrsp_chnl       (in_4_out_4_ibp_wrsp_chnl),



.clk         (clk),
.sync_rst_r  (rst_a),
.async_rst   (rst_a),
.rst_a       (rst_a)
);
mss_bus_switch_dw64_slv u_mss_bs_slv_5 (























    .dw64_in_ibp_cmd_rgon (host_axi_bs_ibp_cmd_rgon),

  .dw64_in_ibp_cmd_valid             (host_axi_bs_ibp_cmd_valid),
  .dw64_in_ibp_cmd_accept            (host_axi_bs_ibp_cmd_accept),
  .dw64_in_ibp_cmd_read              (host_axi_bs_ibp_cmd_read),
  .dw64_in_ibp_cmd_addr              (host_axi_bs_ibp_cmd_addr),
  .dw64_in_ibp_cmd_wrap              (host_axi_bs_ibp_cmd_wrap),
  .dw64_in_ibp_cmd_data_size         (host_axi_bs_ibp_cmd_data_size),
  .dw64_in_ibp_cmd_burst_size        (host_axi_bs_ibp_cmd_burst_size),
  .dw64_in_ibp_cmd_prot              (host_axi_bs_ibp_cmd_prot),
  .dw64_in_ibp_cmd_cache             (host_axi_bs_ibp_cmd_cache),
  .dw64_in_ibp_cmd_lock              (host_axi_bs_ibp_cmd_lock),
  .dw64_in_ibp_cmd_excl              (host_axi_bs_ibp_cmd_excl),

  .dw64_in_ibp_rd_valid              (host_axi_bs_ibp_rd_valid),
  .dw64_in_ibp_rd_excl_ok            (host_axi_bs_ibp_rd_excl_ok),
  .dw64_in_ibp_rd_accept             (host_axi_bs_ibp_rd_accept),
  .dw64_in_ibp_err_rd                (host_axi_bs_ibp_err_rd),
  .dw64_in_ibp_rd_data               (host_axi_bs_ibp_rd_data),
  .dw64_in_ibp_rd_last               (host_axi_bs_ibp_rd_last),

  .dw64_in_ibp_wr_valid              (host_axi_bs_ibp_wr_valid),
  .dw64_in_ibp_wr_accept             (host_axi_bs_ibp_wr_accept),
  .dw64_in_ibp_wr_data               (host_axi_bs_ibp_wr_data),
  .dw64_in_ibp_wr_mask               (host_axi_bs_ibp_wr_mask),
  .dw64_in_ibp_wr_last               (host_axi_bs_ibp_wr_last),

  .dw64_in_ibp_wr_done               (host_axi_bs_ibp_wr_done),
  .dw64_in_ibp_wr_excl_done          (host_axi_bs_ibp_wr_excl_done),
  .dw64_in_ibp_err_wr                (host_axi_bs_ibp_err_wr),
  .dw64_in_ibp_wr_resp_accept        (host_axi_bs_ibp_wr_resp_accept),




    .dw64_out_0_ibp_cmd_chnl_valid  (in_5_out_0_ibp_cmd_chnl_valid),
    .dw64_out_0_ibp_cmd_chnl_accept (in_5_out_0_ibp_cmd_chnl_accept),
    .dw64_out_0_ibp_cmd_chnl        (in_5_out_0_ibp_cmd_chnl),

    .dw64_out_0_ibp_rd_chnl_valid   (in_5_out_0_ibp_rd_chnl_valid),
    .dw64_out_0_ibp_rd_chnl_accept  (in_5_out_0_ibp_rd_chnl_accept),
    .dw64_out_0_ibp_rd_chnl         (in_5_out_0_ibp_rd_chnl),

    .dw64_out_0_ibp_wd_chnl_valid   (in_5_out_0_ibp_wd_chnl_valid),
    .dw64_out_0_ibp_wd_chnl_accept  (in_5_out_0_ibp_wd_chnl_accept),
    .dw64_out_0_ibp_wd_chnl         (in_5_out_0_ibp_wd_chnl),

    .dw64_out_0_ibp_wrsp_chnl_valid (in_5_out_0_ibp_wrsp_chnl_valid),
    .dw64_out_0_ibp_wrsp_chnl_accept(in_5_out_0_ibp_wrsp_chnl_accept),
    .dw64_out_0_ibp_wrsp_chnl       (in_5_out_0_ibp_wrsp_chnl),





    .dw64_out_1_ibp_cmd_chnl_valid  (in_5_out_1_ibp_cmd_chnl_valid),
    .dw64_out_1_ibp_cmd_chnl_accept (in_5_out_1_ibp_cmd_chnl_accept),
    .dw64_out_1_ibp_cmd_chnl        (in_5_out_1_ibp_cmd_chnl),

    .dw64_out_1_ibp_rd_chnl_valid   (in_5_out_1_ibp_rd_chnl_valid),
    .dw64_out_1_ibp_rd_chnl_accept  (in_5_out_1_ibp_rd_chnl_accept),
    .dw64_out_1_ibp_rd_chnl         (in_5_out_1_ibp_rd_chnl),

    .dw64_out_1_ibp_wd_chnl_valid   (in_5_out_1_ibp_wd_chnl_valid),
    .dw64_out_1_ibp_wd_chnl_accept  (in_5_out_1_ibp_wd_chnl_accept),
    .dw64_out_1_ibp_wd_chnl         (in_5_out_1_ibp_wd_chnl),

    .dw64_out_1_ibp_wrsp_chnl_valid (in_5_out_1_ibp_wrsp_chnl_valid),
    .dw64_out_1_ibp_wrsp_chnl_accept(in_5_out_1_ibp_wrsp_chnl_accept),
    .dw64_out_1_ibp_wrsp_chnl       (in_5_out_1_ibp_wrsp_chnl),





    .dw64_out_2_ibp_cmd_chnl_valid  (in_5_out_2_ibp_cmd_chnl_valid),
    .dw64_out_2_ibp_cmd_chnl_accept (in_5_out_2_ibp_cmd_chnl_accept),
    .dw64_out_2_ibp_cmd_chnl        (in_5_out_2_ibp_cmd_chnl),

    .dw64_out_2_ibp_rd_chnl_valid   (in_5_out_2_ibp_rd_chnl_valid),
    .dw64_out_2_ibp_rd_chnl_accept  (in_5_out_2_ibp_rd_chnl_accept),
    .dw64_out_2_ibp_rd_chnl         (in_5_out_2_ibp_rd_chnl),

    .dw64_out_2_ibp_wd_chnl_valid   (in_5_out_2_ibp_wd_chnl_valid),
    .dw64_out_2_ibp_wd_chnl_accept  (in_5_out_2_ibp_wd_chnl_accept),
    .dw64_out_2_ibp_wd_chnl         (in_5_out_2_ibp_wd_chnl),

    .dw64_out_2_ibp_wrsp_chnl_valid (in_5_out_2_ibp_wrsp_chnl_valid),
    .dw64_out_2_ibp_wrsp_chnl_accept(in_5_out_2_ibp_wrsp_chnl_accept),
    .dw64_out_2_ibp_wrsp_chnl       (in_5_out_2_ibp_wrsp_chnl),





    .dw64_out_3_ibp_cmd_chnl_valid  (in_5_out_3_ibp_cmd_chnl_valid),
    .dw64_out_3_ibp_cmd_chnl_accept (in_5_out_3_ibp_cmd_chnl_accept),
    .dw64_out_3_ibp_cmd_chnl        (in_5_out_3_ibp_cmd_chnl),

    .dw64_out_3_ibp_rd_chnl_valid   (in_5_out_3_ibp_rd_chnl_valid),
    .dw64_out_3_ibp_rd_chnl_accept  (in_5_out_3_ibp_rd_chnl_accept),
    .dw64_out_3_ibp_rd_chnl         (in_5_out_3_ibp_rd_chnl),

    .dw64_out_3_ibp_wd_chnl_valid   (in_5_out_3_ibp_wd_chnl_valid),
    .dw64_out_3_ibp_wd_chnl_accept  (in_5_out_3_ibp_wd_chnl_accept),
    .dw64_out_3_ibp_wd_chnl         (in_5_out_3_ibp_wd_chnl),

    .dw64_out_3_ibp_wrsp_chnl_valid (in_5_out_3_ibp_wrsp_chnl_valid),
    .dw64_out_3_ibp_wrsp_chnl_accept(in_5_out_3_ibp_wrsp_chnl_accept),
    .dw64_out_3_ibp_wrsp_chnl       (in_5_out_3_ibp_wrsp_chnl),





    .dw64_out_4_ibp_cmd_chnl_valid  (in_5_out_4_ibp_cmd_chnl_valid),
    .dw64_out_4_ibp_cmd_chnl_accept (in_5_out_4_ibp_cmd_chnl_accept),
    .dw64_out_4_ibp_cmd_chnl        (in_5_out_4_ibp_cmd_chnl),

    .dw64_out_4_ibp_rd_chnl_valid   (in_5_out_4_ibp_rd_chnl_valid),
    .dw64_out_4_ibp_rd_chnl_accept  (in_5_out_4_ibp_rd_chnl_accept),
    .dw64_out_4_ibp_rd_chnl         (in_5_out_4_ibp_rd_chnl),

    .dw64_out_4_ibp_wd_chnl_valid   (in_5_out_4_ibp_wd_chnl_valid),
    .dw64_out_4_ibp_wd_chnl_accept  (in_5_out_4_ibp_wd_chnl_accept),
    .dw64_out_4_ibp_wd_chnl         (in_5_out_4_ibp_wd_chnl),

    .dw64_out_4_ibp_wrsp_chnl_valid (in_5_out_4_ibp_wrsp_chnl_valid),
    .dw64_out_4_ibp_wrsp_chnl_accept(in_5_out_4_ibp_wrsp_chnl_accept),
    .dw64_out_4_ibp_wrsp_chnl       (in_5_out_4_ibp_wrsp_chnl),



.clk         (clk),
.sync_rst_r  (rst_a),
.async_rst   (rst_a),
.rst_a       (rst_a)
);
mss_bus_switch_dw32_slv u_mss_bs_slv_6 (























    .dw32_in_ibp_cmd_rgon (bri4tb_bs_ibp_cmd_rgon),

  .dw32_in_ibp_cmd_valid             (bri4tb_bs_ibp_cmd_valid),
  .dw32_in_ibp_cmd_accept            (bri4tb_bs_ibp_cmd_accept),
  .dw32_in_ibp_cmd_read              (bri4tb_bs_ibp_cmd_read),
  .dw32_in_ibp_cmd_addr              (bri4tb_bs_ibp_cmd_addr),
  .dw32_in_ibp_cmd_wrap              (bri4tb_bs_ibp_cmd_wrap),
  .dw32_in_ibp_cmd_data_size         (bri4tb_bs_ibp_cmd_data_size),
  .dw32_in_ibp_cmd_burst_size        (bri4tb_bs_ibp_cmd_burst_size),
  .dw32_in_ibp_cmd_prot              (bri4tb_bs_ibp_cmd_prot),
  .dw32_in_ibp_cmd_cache             (bri4tb_bs_ibp_cmd_cache),
  .dw32_in_ibp_cmd_lock              (bri4tb_bs_ibp_cmd_lock),
  .dw32_in_ibp_cmd_excl              (bri4tb_bs_ibp_cmd_excl),

  .dw32_in_ibp_rd_valid              (bri4tb_bs_ibp_rd_valid),
  .dw32_in_ibp_rd_excl_ok            (bri4tb_bs_ibp_rd_excl_ok),
  .dw32_in_ibp_rd_accept             (bri4tb_bs_ibp_rd_accept),
  .dw32_in_ibp_err_rd                (bri4tb_bs_ibp_err_rd),
  .dw32_in_ibp_rd_data               (bri4tb_bs_ibp_rd_data),
  .dw32_in_ibp_rd_last               (bri4tb_bs_ibp_rd_last),

  .dw32_in_ibp_wr_valid              (bri4tb_bs_ibp_wr_valid),
  .dw32_in_ibp_wr_accept             (bri4tb_bs_ibp_wr_accept),
  .dw32_in_ibp_wr_data               (bri4tb_bs_ibp_wr_data),
  .dw32_in_ibp_wr_mask               (bri4tb_bs_ibp_wr_mask),
  .dw32_in_ibp_wr_last               (bri4tb_bs_ibp_wr_last),

  .dw32_in_ibp_wr_done               (bri4tb_bs_ibp_wr_done),
  .dw32_in_ibp_wr_excl_done          (bri4tb_bs_ibp_wr_excl_done),
  .dw32_in_ibp_err_wr                (bri4tb_bs_ibp_err_wr),
  .dw32_in_ibp_wr_resp_accept        (bri4tb_bs_ibp_wr_resp_accept),




    .dw32_out_0_ibp_cmd_chnl_valid  (in_6_out_0_ibp_cmd_chnl_valid),
    .dw32_out_0_ibp_cmd_chnl_accept (in_6_out_0_ibp_cmd_chnl_accept),
    .dw32_out_0_ibp_cmd_chnl        (in_6_out_0_ibp_cmd_chnl),

    .dw32_out_0_ibp_rd_chnl_valid   (in_6_out_0_ibp_rd_chnl_valid),
    .dw32_out_0_ibp_rd_chnl_accept  (in_6_out_0_ibp_rd_chnl_accept),
    .dw32_out_0_ibp_rd_chnl         (in_6_out_0_ibp_rd_chnl),

    .dw32_out_0_ibp_wd_chnl_valid   (in_6_out_0_ibp_wd_chnl_valid),
    .dw32_out_0_ibp_wd_chnl_accept  (in_6_out_0_ibp_wd_chnl_accept),
    .dw32_out_0_ibp_wd_chnl         (in_6_out_0_ibp_wd_chnl),

    .dw32_out_0_ibp_wrsp_chnl_valid (in_6_out_0_ibp_wrsp_chnl_valid),
    .dw32_out_0_ibp_wrsp_chnl_accept(in_6_out_0_ibp_wrsp_chnl_accept),
    .dw32_out_0_ibp_wrsp_chnl       (in_6_out_0_ibp_wrsp_chnl),





    .dw32_out_1_ibp_cmd_chnl_valid  (in_6_out_1_ibp_cmd_chnl_valid),
    .dw32_out_1_ibp_cmd_chnl_accept (in_6_out_1_ibp_cmd_chnl_accept),
    .dw32_out_1_ibp_cmd_chnl        (in_6_out_1_ibp_cmd_chnl),

    .dw32_out_1_ibp_rd_chnl_valid   (in_6_out_1_ibp_rd_chnl_valid),
    .dw32_out_1_ibp_rd_chnl_accept  (in_6_out_1_ibp_rd_chnl_accept),
    .dw32_out_1_ibp_rd_chnl         (in_6_out_1_ibp_rd_chnl),

    .dw32_out_1_ibp_wd_chnl_valid   (in_6_out_1_ibp_wd_chnl_valid),
    .dw32_out_1_ibp_wd_chnl_accept  (in_6_out_1_ibp_wd_chnl_accept),
    .dw32_out_1_ibp_wd_chnl         (in_6_out_1_ibp_wd_chnl),

    .dw32_out_1_ibp_wrsp_chnl_valid (in_6_out_1_ibp_wrsp_chnl_valid),
    .dw32_out_1_ibp_wrsp_chnl_accept(in_6_out_1_ibp_wrsp_chnl_accept),
    .dw32_out_1_ibp_wrsp_chnl       (in_6_out_1_ibp_wrsp_chnl),





    .dw32_out_2_ibp_cmd_chnl_valid  (in_6_out_2_ibp_cmd_chnl_valid),
    .dw32_out_2_ibp_cmd_chnl_accept (in_6_out_2_ibp_cmd_chnl_accept),
    .dw32_out_2_ibp_cmd_chnl        (in_6_out_2_ibp_cmd_chnl),

    .dw32_out_2_ibp_rd_chnl_valid   (in_6_out_2_ibp_rd_chnl_valid),
    .dw32_out_2_ibp_rd_chnl_accept  (in_6_out_2_ibp_rd_chnl_accept),
    .dw32_out_2_ibp_rd_chnl         (in_6_out_2_ibp_rd_chnl),

    .dw32_out_2_ibp_wd_chnl_valid   (in_6_out_2_ibp_wd_chnl_valid),
    .dw32_out_2_ibp_wd_chnl_accept  (in_6_out_2_ibp_wd_chnl_accept),
    .dw32_out_2_ibp_wd_chnl         (in_6_out_2_ibp_wd_chnl),

    .dw32_out_2_ibp_wrsp_chnl_valid (in_6_out_2_ibp_wrsp_chnl_valid),
    .dw32_out_2_ibp_wrsp_chnl_accept(in_6_out_2_ibp_wrsp_chnl_accept),
    .dw32_out_2_ibp_wrsp_chnl       (in_6_out_2_ibp_wrsp_chnl),





    .dw32_out_3_ibp_cmd_chnl_valid  (in_6_out_3_ibp_cmd_chnl_valid),
    .dw32_out_3_ibp_cmd_chnl_accept (in_6_out_3_ibp_cmd_chnl_accept),
    .dw32_out_3_ibp_cmd_chnl        (in_6_out_3_ibp_cmd_chnl),

    .dw32_out_3_ibp_rd_chnl_valid   (in_6_out_3_ibp_rd_chnl_valid),
    .dw32_out_3_ibp_rd_chnl_accept  (in_6_out_3_ibp_rd_chnl_accept),
    .dw32_out_3_ibp_rd_chnl         (in_6_out_3_ibp_rd_chnl),

    .dw32_out_3_ibp_wd_chnl_valid   (in_6_out_3_ibp_wd_chnl_valid),
    .dw32_out_3_ibp_wd_chnl_accept  (in_6_out_3_ibp_wd_chnl_accept),
    .dw32_out_3_ibp_wd_chnl         (in_6_out_3_ibp_wd_chnl),

    .dw32_out_3_ibp_wrsp_chnl_valid (in_6_out_3_ibp_wrsp_chnl_valid),
    .dw32_out_3_ibp_wrsp_chnl_accept(in_6_out_3_ibp_wrsp_chnl_accept),
    .dw32_out_3_ibp_wrsp_chnl       (in_6_out_3_ibp_wrsp_chnl),





    .dw32_out_4_ibp_cmd_chnl_valid  (in_6_out_4_ibp_cmd_chnl_valid),
    .dw32_out_4_ibp_cmd_chnl_accept (in_6_out_4_ibp_cmd_chnl_accept),
    .dw32_out_4_ibp_cmd_chnl        (in_6_out_4_ibp_cmd_chnl),

    .dw32_out_4_ibp_rd_chnl_valid   (in_6_out_4_ibp_rd_chnl_valid),
    .dw32_out_4_ibp_rd_chnl_accept  (in_6_out_4_ibp_rd_chnl_accept),
    .dw32_out_4_ibp_rd_chnl         (in_6_out_4_ibp_rd_chnl),

    .dw32_out_4_ibp_wd_chnl_valid   (in_6_out_4_ibp_wd_chnl_valid),
    .dw32_out_4_ibp_wd_chnl_accept  (in_6_out_4_ibp_wd_chnl_accept),
    .dw32_out_4_ibp_wd_chnl         (in_6_out_4_ibp_wd_chnl),

    .dw32_out_4_ibp_wrsp_chnl_valid (in_6_out_4_ibp_wrsp_chnl_valid),
    .dw32_out_4_ibp_wrsp_chnl_accept(in_6_out_4_ibp_wrsp_chnl_accept),
    .dw32_out_4_ibp_wrsp_chnl       (in_6_out_4_ibp_wrsp_chnl),



.clk         (clk),
.sync_rst_r  (rst_a),
.async_rst   (rst_a),
.rst_a       (rst_a)
);

//
// Instantiation for each slave port
//
mss_bus_switch_ibp_dw512_mst u_mss_bs_mst_0 (



    .ibp_dw512_in_0_ibp_cmd_chnl_valid  (in_0_out_0_ibp_cmd_chnl_valid),
    .ibp_dw512_in_0_ibp_cmd_chnl_accept (in_0_out_0_ibp_cmd_chnl_accept),
    .ibp_dw512_in_0_ibp_cmd_chnl        (in_0_out_0_ibp_cmd_chnl),

    .ibp_dw512_in_0_ibp_rd_chnl_valid   (in_0_out_0_ibp_rd_chnl_valid),
    .ibp_dw512_in_0_ibp_rd_chnl_accept  (in_0_out_0_ibp_rd_chnl_accept),
    .ibp_dw512_in_0_ibp_rd_chnl         (in_0_out_0_ibp_rd_chnl),

    .ibp_dw512_in_0_ibp_wd_chnl_valid   (in_0_out_0_ibp_wd_chnl_valid),
    .ibp_dw512_in_0_ibp_wd_chnl_accept  (in_0_out_0_ibp_wd_chnl_accept),
    .ibp_dw512_in_0_ibp_wd_chnl         (in_0_out_0_ibp_wd_chnl),

    .ibp_dw512_in_0_ibp_wrsp_chnl_valid (in_0_out_0_ibp_wrsp_chnl_valid),
    .ibp_dw512_in_0_ibp_wrsp_chnl_accept(in_0_out_0_ibp_wrsp_chnl_accept),
    .ibp_dw512_in_0_ibp_wrsp_chnl       (in_0_out_0_ibp_wrsp_chnl),





    .ibp_dw512_in_1_ibp_cmd_chnl_valid  (in_1_out_0_ibp_cmd_chnl_valid),
    .ibp_dw512_in_1_ibp_cmd_chnl_accept (in_1_out_0_ibp_cmd_chnl_accept),
    .ibp_dw512_in_1_ibp_cmd_chnl        (in_1_out_0_ibp_cmd_chnl),

    .ibp_dw512_in_1_ibp_rd_chnl_valid   (in_1_out_0_ibp_rd_chnl_valid),
    .ibp_dw512_in_1_ibp_rd_chnl_accept  (in_1_out_0_ibp_rd_chnl_accept),
    .ibp_dw512_in_1_ibp_rd_chnl         (in_1_out_0_ibp_rd_chnl),

    .ibp_dw512_in_1_ibp_wd_chnl_valid   (in_1_out_0_ibp_wd_chnl_valid),
    .ibp_dw512_in_1_ibp_wd_chnl_accept  (in_1_out_0_ibp_wd_chnl_accept),
    .ibp_dw512_in_1_ibp_wd_chnl         (in_1_out_0_ibp_wd_chnl),

    .ibp_dw512_in_1_ibp_wrsp_chnl_valid (in_1_out_0_ibp_wrsp_chnl_valid),
    .ibp_dw512_in_1_ibp_wrsp_chnl_accept(in_1_out_0_ibp_wrsp_chnl_accept),
    .ibp_dw512_in_1_ibp_wrsp_chnl       (in_1_out_0_ibp_wrsp_chnl),





    .ibp_dw512_in_2_ibp_cmd_chnl_valid  (in_2_out_0_ibp_cmd_chnl_valid),
    .ibp_dw512_in_2_ibp_cmd_chnl_accept (in_2_out_0_ibp_cmd_chnl_accept),
    .ibp_dw512_in_2_ibp_cmd_chnl        (in_2_out_0_ibp_cmd_chnl),

    .ibp_dw512_in_2_ibp_rd_chnl_valid   (in_2_out_0_ibp_rd_chnl_valid),
    .ibp_dw512_in_2_ibp_rd_chnl_accept  (in_2_out_0_ibp_rd_chnl_accept),
    .ibp_dw512_in_2_ibp_rd_chnl         (in_2_out_0_ibp_rd_chnl),

    .ibp_dw512_in_2_ibp_wd_chnl_valid   (in_2_out_0_ibp_wd_chnl_valid),
    .ibp_dw512_in_2_ibp_wd_chnl_accept  (in_2_out_0_ibp_wd_chnl_accept),
    .ibp_dw512_in_2_ibp_wd_chnl         (in_2_out_0_ibp_wd_chnl),

    .ibp_dw512_in_2_ibp_wrsp_chnl_valid (in_2_out_0_ibp_wrsp_chnl_valid),
    .ibp_dw512_in_2_ibp_wrsp_chnl_accept(in_2_out_0_ibp_wrsp_chnl_accept),
    .ibp_dw512_in_2_ibp_wrsp_chnl       (in_2_out_0_ibp_wrsp_chnl),





    .ibp_dw512_in_3_ibp_cmd_chnl_valid  (in_3_out_0_ibp_cmd_chnl_valid),
    .ibp_dw512_in_3_ibp_cmd_chnl_accept (in_3_out_0_ibp_cmd_chnl_accept),
    .ibp_dw512_in_3_ibp_cmd_chnl        (in_3_out_0_ibp_cmd_chnl),

    .ibp_dw512_in_3_ibp_rd_chnl_valid   (in_3_out_0_ibp_rd_chnl_valid),
    .ibp_dw512_in_3_ibp_rd_chnl_accept  (in_3_out_0_ibp_rd_chnl_accept),
    .ibp_dw512_in_3_ibp_rd_chnl         (in_3_out_0_ibp_rd_chnl),

    .ibp_dw512_in_3_ibp_wd_chnl_valid   (in_3_out_0_ibp_wd_chnl_valid),
    .ibp_dw512_in_3_ibp_wd_chnl_accept  (in_3_out_0_ibp_wd_chnl_accept),
    .ibp_dw512_in_3_ibp_wd_chnl         (in_3_out_0_ibp_wd_chnl),

    .ibp_dw512_in_3_ibp_wrsp_chnl_valid (in_3_out_0_ibp_wrsp_chnl_valid),
    .ibp_dw512_in_3_ibp_wrsp_chnl_accept(in_3_out_0_ibp_wrsp_chnl_accept),
    .ibp_dw512_in_3_ibp_wrsp_chnl       (in_3_out_0_ibp_wrsp_chnl),





    .ibp_dw512_in_4_ibp_cmd_chnl_valid  (in_4_out_0_ibp_cmd_chnl_valid),
    .ibp_dw512_in_4_ibp_cmd_chnl_accept (in_4_out_0_ibp_cmd_chnl_accept),
    .ibp_dw512_in_4_ibp_cmd_chnl        (in_4_out_0_ibp_cmd_chnl),

    .ibp_dw512_in_4_ibp_rd_chnl_valid   (in_4_out_0_ibp_rd_chnl_valid),
    .ibp_dw512_in_4_ibp_rd_chnl_accept  (in_4_out_0_ibp_rd_chnl_accept),
    .ibp_dw512_in_4_ibp_rd_chnl         (in_4_out_0_ibp_rd_chnl),

    .ibp_dw512_in_4_ibp_wd_chnl_valid   (in_4_out_0_ibp_wd_chnl_valid),
    .ibp_dw512_in_4_ibp_wd_chnl_accept  (in_4_out_0_ibp_wd_chnl_accept),
    .ibp_dw512_in_4_ibp_wd_chnl         (in_4_out_0_ibp_wd_chnl),

    .ibp_dw512_in_4_ibp_wrsp_chnl_valid (in_4_out_0_ibp_wrsp_chnl_valid),
    .ibp_dw512_in_4_ibp_wrsp_chnl_accept(in_4_out_0_ibp_wrsp_chnl_accept),
    .ibp_dw512_in_4_ibp_wrsp_chnl       (in_4_out_0_ibp_wrsp_chnl),





    .ibp_dw512_in_5_ibp_cmd_chnl_valid  (in_5_out_0_ibp_cmd_chnl_valid),
    .ibp_dw512_in_5_ibp_cmd_chnl_accept (in_5_out_0_ibp_cmd_chnl_accept),
    .ibp_dw512_in_5_ibp_cmd_chnl        (in_5_out_0_ibp_cmd_chnl),

    .ibp_dw512_in_5_ibp_rd_chnl_valid   (in_5_out_0_ibp_rd_chnl_valid),
    .ibp_dw512_in_5_ibp_rd_chnl_accept  (in_5_out_0_ibp_rd_chnl_accept),
    .ibp_dw512_in_5_ibp_rd_chnl         (in_5_out_0_ibp_rd_chnl),

    .ibp_dw512_in_5_ibp_wd_chnl_valid   (in_5_out_0_ibp_wd_chnl_valid),
    .ibp_dw512_in_5_ibp_wd_chnl_accept  (in_5_out_0_ibp_wd_chnl_accept),
    .ibp_dw512_in_5_ibp_wd_chnl         (in_5_out_0_ibp_wd_chnl),

    .ibp_dw512_in_5_ibp_wrsp_chnl_valid (in_5_out_0_ibp_wrsp_chnl_valid),
    .ibp_dw512_in_5_ibp_wrsp_chnl_accept(in_5_out_0_ibp_wrsp_chnl_accept),
    .ibp_dw512_in_5_ibp_wrsp_chnl       (in_5_out_0_ibp_wrsp_chnl),





    .ibp_dw512_in_6_ibp_cmd_chnl_valid  (in_6_out_0_ibp_cmd_chnl_valid),
    .ibp_dw512_in_6_ibp_cmd_chnl_accept (in_6_out_0_ibp_cmd_chnl_accept),
    .ibp_dw512_in_6_ibp_cmd_chnl        (in_6_out_0_ibp_cmd_chnl),

    .ibp_dw512_in_6_ibp_rd_chnl_valid   (in_6_out_0_ibp_rd_chnl_valid),
    .ibp_dw512_in_6_ibp_rd_chnl_accept  (in_6_out_0_ibp_rd_chnl_accept),
    .ibp_dw512_in_6_ibp_rd_chnl         (in_6_out_0_ibp_rd_chnl),

    .ibp_dw512_in_6_ibp_wd_chnl_valid   (in_6_out_0_ibp_wd_chnl_valid),
    .ibp_dw512_in_6_ibp_wd_chnl_accept  (in_6_out_0_ibp_wd_chnl_accept),
    .ibp_dw512_in_6_ibp_wd_chnl         (in_6_out_0_ibp_wd_chnl),

    .ibp_dw512_in_6_ibp_wrsp_chnl_valid (in_6_out_0_ibp_wrsp_chnl_valid),
    .ibp_dw512_in_6_ibp_wrsp_chnl_accept(in_6_out_0_ibp_wrsp_chnl_accept),
    .ibp_dw512_in_6_ibp_wrsp_chnl       (in_6_out_0_ibp_wrsp_chnl),



  .ibp_dw512_out_ibp_cmd_valid             (npu_dmi0_axi_bs_ibp_cmd_valid),
  .ibp_dw512_out_ibp_cmd_accept            (npu_dmi0_axi_bs_ibp_cmd_accept),
  .ibp_dw512_out_ibp_cmd_read              (npu_dmi0_axi_bs_ibp_cmd_read),
  .ibp_dw512_out_ibp_cmd_addr              (npu_dmi0_axi_bs_ibp_cmd_addr),
  .ibp_dw512_out_ibp_cmd_wrap              (npu_dmi0_axi_bs_ibp_cmd_wrap),
  .ibp_dw512_out_ibp_cmd_data_size         (npu_dmi0_axi_bs_ibp_cmd_data_size),
  .ibp_dw512_out_ibp_cmd_burst_size        (npu_dmi0_axi_bs_ibp_cmd_burst_size),
  .ibp_dw512_out_ibp_cmd_prot              (npu_dmi0_axi_bs_ibp_cmd_prot),
  .ibp_dw512_out_ibp_cmd_cache             (npu_dmi0_axi_bs_ibp_cmd_cache),
  .ibp_dw512_out_ibp_cmd_lock              (npu_dmi0_axi_bs_ibp_cmd_lock),
  .ibp_dw512_out_ibp_cmd_excl              (npu_dmi0_axi_bs_ibp_cmd_excl),

  .ibp_dw512_out_ibp_rd_valid              (npu_dmi0_axi_bs_ibp_rd_valid),
  .ibp_dw512_out_ibp_rd_excl_ok            (npu_dmi0_axi_bs_ibp_rd_excl_ok),
  .ibp_dw512_out_ibp_rd_accept             (npu_dmi0_axi_bs_ibp_rd_accept),
  .ibp_dw512_out_ibp_err_rd                (npu_dmi0_axi_bs_ibp_err_rd),
  .ibp_dw512_out_ibp_rd_data               (npu_dmi0_axi_bs_ibp_rd_data),
  .ibp_dw512_out_ibp_rd_last               (npu_dmi0_axi_bs_ibp_rd_last),

  .ibp_dw512_out_ibp_wr_valid              (npu_dmi0_axi_bs_ibp_wr_valid),
  .ibp_dw512_out_ibp_wr_accept             (npu_dmi0_axi_bs_ibp_wr_accept),
  .ibp_dw512_out_ibp_wr_data               (npu_dmi0_axi_bs_ibp_wr_data),
  .ibp_dw512_out_ibp_wr_mask               (npu_dmi0_axi_bs_ibp_wr_mask),
  .ibp_dw512_out_ibp_wr_last               (npu_dmi0_axi_bs_ibp_wr_last),

  .ibp_dw512_out_ibp_wr_done               (npu_dmi0_axi_bs_ibp_wr_done),
  .ibp_dw512_out_ibp_wr_excl_done          (npu_dmi0_axi_bs_ibp_wr_excl_done),
  .ibp_dw512_out_ibp_err_wr                (npu_dmi0_axi_bs_ibp_err_wr),
  .ibp_dw512_out_ibp_wr_resp_accept        (npu_dmi0_axi_bs_ibp_wr_resp_accept),
.clk         (clk),
.rst_a       (rst_a)
);
mss_bus_switch_ibp_dw32_mst u_mss_bs_mst_1 (



    .ibp_dw32_in_0_ibp_cmd_chnl_valid  (in_0_out_1_ibp_cmd_chnl_valid),
    .ibp_dw32_in_0_ibp_cmd_chnl_accept (in_0_out_1_ibp_cmd_chnl_accept),
    .ibp_dw32_in_0_ibp_cmd_chnl        (in_0_out_1_ibp_cmd_chnl),

    .ibp_dw32_in_0_ibp_rd_chnl_valid   (in_0_out_1_ibp_rd_chnl_valid),
    .ibp_dw32_in_0_ibp_rd_chnl_accept  (in_0_out_1_ibp_rd_chnl_accept),
    .ibp_dw32_in_0_ibp_rd_chnl         (in_0_out_1_ibp_rd_chnl),

    .ibp_dw32_in_0_ibp_wd_chnl_valid   (in_0_out_1_ibp_wd_chnl_valid),
    .ibp_dw32_in_0_ibp_wd_chnl_accept  (in_0_out_1_ibp_wd_chnl_accept),
    .ibp_dw32_in_0_ibp_wd_chnl         (in_0_out_1_ibp_wd_chnl),

    .ibp_dw32_in_0_ibp_wrsp_chnl_valid (in_0_out_1_ibp_wrsp_chnl_valid),
    .ibp_dw32_in_0_ibp_wrsp_chnl_accept(in_0_out_1_ibp_wrsp_chnl_accept),
    .ibp_dw32_in_0_ibp_wrsp_chnl       (in_0_out_1_ibp_wrsp_chnl),





    .ibp_dw32_in_1_ibp_cmd_chnl_valid  (in_1_out_1_ibp_cmd_chnl_valid),
    .ibp_dw32_in_1_ibp_cmd_chnl_accept (in_1_out_1_ibp_cmd_chnl_accept),
    .ibp_dw32_in_1_ibp_cmd_chnl        (in_1_out_1_ibp_cmd_chnl),

    .ibp_dw32_in_1_ibp_rd_chnl_valid   (in_1_out_1_ibp_rd_chnl_valid),
    .ibp_dw32_in_1_ibp_rd_chnl_accept  (in_1_out_1_ibp_rd_chnl_accept),
    .ibp_dw32_in_1_ibp_rd_chnl         (in_1_out_1_ibp_rd_chnl),

    .ibp_dw32_in_1_ibp_wd_chnl_valid   (in_1_out_1_ibp_wd_chnl_valid),
    .ibp_dw32_in_1_ibp_wd_chnl_accept  (in_1_out_1_ibp_wd_chnl_accept),
    .ibp_dw32_in_1_ibp_wd_chnl         (in_1_out_1_ibp_wd_chnl),

    .ibp_dw32_in_1_ibp_wrsp_chnl_valid (in_1_out_1_ibp_wrsp_chnl_valid),
    .ibp_dw32_in_1_ibp_wrsp_chnl_accept(in_1_out_1_ibp_wrsp_chnl_accept),
    .ibp_dw32_in_1_ibp_wrsp_chnl       (in_1_out_1_ibp_wrsp_chnl),





    .ibp_dw32_in_2_ibp_cmd_chnl_valid  (in_2_out_1_ibp_cmd_chnl_valid),
    .ibp_dw32_in_2_ibp_cmd_chnl_accept (in_2_out_1_ibp_cmd_chnl_accept),
    .ibp_dw32_in_2_ibp_cmd_chnl        (in_2_out_1_ibp_cmd_chnl),

    .ibp_dw32_in_2_ibp_rd_chnl_valid   (in_2_out_1_ibp_rd_chnl_valid),
    .ibp_dw32_in_2_ibp_rd_chnl_accept  (in_2_out_1_ibp_rd_chnl_accept),
    .ibp_dw32_in_2_ibp_rd_chnl         (in_2_out_1_ibp_rd_chnl),

    .ibp_dw32_in_2_ibp_wd_chnl_valid   (in_2_out_1_ibp_wd_chnl_valid),
    .ibp_dw32_in_2_ibp_wd_chnl_accept  (in_2_out_1_ibp_wd_chnl_accept),
    .ibp_dw32_in_2_ibp_wd_chnl         (in_2_out_1_ibp_wd_chnl),

    .ibp_dw32_in_2_ibp_wrsp_chnl_valid (in_2_out_1_ibp_wrsp_chnl_valid),
    .ibp_dw32_in_2_ibp_wrsp_chnl_accept(in_2_out_1_ibp_wrsp_chnl_accept),
    .ibp_dw32_in_2_ibp_wrsp_chnl       (in_2_out_1_ibp_wrsp_chnl),





    .ibp_dw32_in_3_ibp_cmd_chnl_valid  (in_3_out_1_ibp_cmd_chnl_valid),
    .ibp_dw32_in_3_ibp_cmd_chnl_accept (in_3_out_1_ibp_cmd_chnl_accept),
    .ibp_dw32_in_3_ibp_cmd_chnl        (in_3_out_1_ibp_cmd_chnl),

    .ibp_dw32_in_3_ibp_rd_chnl_valid   (in_3_out_1_ibp_rd_chnl_valid),
    .ibp_dw32_in_3_ibp_rd_chnl_accept  (in_3_out_1_ibp_rd_chnl_accept),
    .ibp_dw32_in_3_ibp_rd_chnl         (in_3_out_1_ibp_rd_chnl),

    .ibp_dw32_in_3_ibp_wd_chnl_valid   (in_3_out_1_ibp_wd_chnl_valid),
    .ibp_dw32_in_3_ibp_wd_chnl_accept  (in_3_out_1_ibp_wd_chnl_accept),
    .ibp_dw32_in_3_ibp_wd_chnl         (in_3_out_1_ibp_wd_chnl),

    .ibp_dw32_in_3_ibp_wrsp_chnl_valid (in_3_out_1_ibp_wrsp_chnl_valid),
    .ibp_dw32_in_3_ibp_wrsp_chnl_accept(in_3_out_1_ibp_wrsp_chnl_accept),
    .ibp_dw32_in_3_ibp_wrsp_chnl       (in_3_out_1_ibp_wrsp_chnl),





    .ibp_dw32_in_4_ibp_cmd_chnl_valid  (in_4_out_1_ibp_cmd_chnl_valid),
    .ibp_dw32_in_4_ibp_cmd_chnl_accept (in_4_out_1_ibp_cmd_chnl_accept),
    .ibp_dw32_in_4_ibp_cmd_chnl        (in_4_out_1_ibp_cmd_chnl),

    .ibp_dw32_in_4_ibp_rd_chnl_valid   (in_4_out_1_ibp_rd_chnl_valid),
    .ibp_dw32_in_4_ibp_rd_chnl_accept  (in_4_out_1_ibp_rd_chnl_accept),
    .ibp_dw32_in_4_ibp_rd_chnl         (in_4_out_1_ibp_rd_chnl),

    .ibp_dw32_in_4_ibp_wd_chnl_valid   (in_4_out_1_ibp_wd_chnl_valid),
    .ibp_dw32_in_4_ibp_wd_chnl_accept  (in_4_out_1_ibp_wd_chnl_accept),
    .ibp_dw32_in_4_ibp_wd_chnl         (in_4_out_1_ibp_wd_chnl),

    .ibp_dw32_in_4_ibp_wrsp_chnl_valid (in_4_out_1_ibp_wrsp_chnl_valid),
    .ibp_dw32_in_4_ibp_wrsp_chnl_accept(in_4_out_1_ibp_wrsp_chnl_accept),
    .ibp_dw32_in_4_ibp_wrsp_chnl       (in_4_out_1_ibp_wrsp_chnl),





    .ibp_dw32_in_5_ibp_cmd_chnl_valid  (in_5_out_1_ibp_cmd_chnl_valid),
    .ibp_dw32_in_5_ibp_cmd_chnl_accept (in_5_out_1_ibp_cmd_chnl_accept),
    .ibp_dw32_in_5_ibp_cmd_chnl        (in_5_out_1_ibp_cmd_chnl),

    .ibp_dw32_in_5_ibp_rd_chnl_valid   (in_5_out_1_ibp_rd_chnl_valid),
    .ibp_dw32_in_5_ibp_rd_chnl_accept  (in_5_out_1_ibp_rd_chnl_accept),
    .ibp_dw32_in_5_ibp_rd_chnl         (in_5_out_1_ibp_rd_chnl),

    .ibp_dw32_in_5_ibp_wd_chnl_valid   (in_5_out_1_ibp_wd_chnl_valid),
    .ibp_dw32_in_5_ibp_wd_chnl_accept  (in_5_out_1_ibp_wd_chnl_accept),
    .ibp_dw32_in_5_ibp_wd_chnl         (in_5_out_1_ibp_wd_chnl),

    .ibp_dw32_in_5_ibp_wrsp_chnl_valid (in_5_out_1_ibp_wrsp_chnl_valid),
    .ibp_dw32_in_5_ibp_wrsp_chnl_accept(in_5_out_1_ibp_wrsp_chnl_accept),
    .ibp_dw32_in_5_ibp_wrsp_chnl       (in_5_out_1_ibp_wrsp_chnl),





    .ibp_dw32_in_6_ibp_cmd_chnl_valid  (in_6_out_1_ibp_cmd_chnl_valid),
    .ibp_dw32_in_6_ibp_cmd_chnl_accept (in_6_out_1_ibp_cmd_chnl_accept),
    .ibp_dw32_in_6_ibp_cmd_chnl        (in_6_out_1_ibp_cmd_chnl),

    .ibp_dw32_in_6_ibp_rd_chnl_valid   (in_6_out_1_ibp_rd_chnl_valid),
    .ibp_dw32_in_6_ibp_rd_chnl_accept  (in_6_out_1_ibp_rd_chnl_accept),
    .ibp_dw32_in_6_ibp_rd_chnl         (in_6_out_1_ibp_rd_chnl),

    .ibp_dw32_in_6_ibp_wd_chnl_valid   (in_6_out_1_ibp_wd_chnl_valid),
    .ibp_dw32_in_6_ibp_wd_chnl_accept  (in_6_out_1_ibp_wd_chnl_accept),
    .ibp_dw32_in_6_ibp_wd_chnl         (in_6_out_1_ibp_wd_chnl),

    .ibp_dw32_in_6_ibp_wrsp_chnl_valid (in_6_out_1_ibp_wrsp_chnl_valid),
    .ibp_dw32_in_6_ibp_wrsp_chnl_accept(in_6_out_1_ibp_wrsp_chnl_accept),
    .ibp_dw32_in_6_ibp_wrsp_chnl       (in_6_out_1_ibp_wrsp_chnl),



  .ibp_dw32_out_ibp_cmd_valid             (npu_cfg_axi_bs_ibp_cmd_valid),
  .ibp_dw32_out_ibp_cmd_accept            (npu_cfg_axi_bs_ibp_cmd_accept),
  .ibp_dw32_out_ibp_cmd_read              (npu_cfg_axi_bs_ibp_cmd_read),
  .ibp_dw32_out_ibp_cmd_addr              (npu_cfg_axi_bs_ibp_cmd_addr),
  .ibp_dw32_out_ibp_cmd_wrap              (npu_cfg_axi_bs_ibp_cmd_wrap),
  .ibp_dw32_out_ibp_cmd_data_size         (npu_cfg_axi_bs_ibp_cmd_data_size),
  .ibp_dw32_out_ibp_cmd_burst_size        (npu_cfg_axi_bs_ibp_cmd_burst_size),
  .ibp_dw32_out_ibp_cmd_prot              (npu_cfg_axi_bs_ibp_cmd_prot),
  .ibp_dw32_out_ibp_cmd_cache             (npu_cfg_axi_bs_ibp_cmd_cache),
  .ibp_dw32_out_ibp_cmd_lock              (npu_cfg_axi_bs_ibp_cmd_lock),
  .ibp_dw32_out_ibp_cmd_excl              (npu_cfg_axi_bs_ibp_cmd_excl),

  .ibp_dw32_out_ibp_rd_valid              (npu_cfg_axi_bs_ibp_rd_valid),
  .ibp_dw32_out_ibp_rd_excl_ok            (npu_cfg_axi_bs_ibp_rd_excl_ok),
  .ibp_dw32_out_ibp_rd_accept             (npu_cfg_axi_bs_ibp_rd_accept),
  .ibp_dw32_out_ibp_err_rd                (npu_cfg_axi_bs_ibp_err_rd),
  .ibp_dw32_out_ibp_rd_data               (npu_cfg_axi_bs_ibp_rd_data),
  .ibp_dw32_out_ibp_rd_last               (npu_cfg_axi_bs_ibp_rd_last),

  .ibp_dw32_out_ibp_wr_valid              (npu_cfg_axi_bs_ibp_wr_valid),
  .ibp_dw32_out_ibp_wr_accept             (npu_cfg_axi_bs_ibp_wr_accept),
  .ibp_dw32_out_ibp_wr_data               (npu_cfg_axi_bs_ibp_wr_data),
  .ibp_dw32_out_ibp_wr_mask               (npu_cfg_axi_bs_ibp_wr_mask),
  .ibp_dw32_out_ibp_wr_last               (npu_cfg_axi_bs_ibp_wr_last),

  .ibp_dw32_out_ibp_wr_done               (npu_cfg_axi_bs_ibp_wr_done),
  .ibp_dw32_out_ibp_wr_excl_done          (npu_cfg_axi_bs_ibp_wr_excl_done),
  .ibp_dw32_out_ibp_err_wr                (npu_cfg_axi_bs_ibp_err_wr),
  .ibp_dw32_out_ibp_wr_resp_accept        (npu_cfg_axi_bs_ibp_wr_resp_accept),
.clk         (clk),
.rst_a       (rst_a)
);
mss_bus_switch_ibp_dw64_mst u_mss_bs_mst_2 (



    .ibp_dw64_in_0_ibp_cmd_chnl_valid  (in_0_out_2_ibp_cmd_chnl_valid),
    .ibp_dw64_in_0_ibp_cmd_chnl_accept (in_0_out_2_ibp_cmd_chnl_accept),
    .ibp_dw64_in_0_ibp_cmd_chnl        (in_0_out_2_ibp_cmd_chnl),

    .ibp_dw64_in_0_ibp_rd_chnl_valid   (in_0_out_2_ibp_rd_chnl_valid),
    .ibp_dw64_in_0_ibp_rd_chnl_accept  (in_0_out_2_ibp_rd_chnl_accept),
    .ibp_dw64_in_0_ibp_rd_chnl         (in_0_out_2_ibp_rd_chnl),

    .ibp_dw64_in_0_ibp_wd_chnl_valid   (in_0_out_2_ibp_wd_chnl_valid),
    .ibp_dw64_in_0_ibp_wd_chnl_accept  (in_0_out_2_ibp_wd_chnl_accept),
    .ibp_dw64_in_0_ibp_wd_chnl         (in_0_out_2_ibp_wd_chnl),

    .ibp_dw64_in_0_ibp_wrsp_chnl_valid (in_0_out_2_ibp_wrsp_chnl_valid),
    .ibp_dw64_in_0_ibp_wrsp_chnl_accept(in_0_out_2_ibp_wrsp_chnl_accept),
    .ibp_dw64_in_0_ibp_wrsp_chnl       (in_0_out_2_ibp_wrsp_chnl),





    .ibp_dw64_in_1_ibp_cmd_chnl_valid  (in_1_out_2_ibp_cmd_chnl_valid),
    .ibp_dw64_in_1_ibp_cmd_chnl_accept (in_1_out_2_ibp_cmd_chnl_accept),
    .ibp_dw64_in_1_ibp_cmd_chnl        (in_1_out_2_ibp_cmd_chnl),

    .ibp_dw64_in_1_ibp_rd_chnl_valid   (in_1_out_2_ibp_rd_chnl_valid),
    .ibp_dw64_in_1_ibp_rd_chnl_accept  (in_1_out_2_ibp_rd_chnl_accept),
    .ibp_dw64_in_1_ibp_rd_chnl         (in_1_out_2_ibp_rd_chnl),

    .ibp_dw64_in_1_ibp_wd_chnl_valid   (in_1_out_2_ibp_wd_chnl_valid),
    .ibp_dw64_in_1_ibp_wd_chnl_accept  (in_1_out_2_ibp_wd_chnl_accept),
    .ibp_dw64_in_1_ibp_wd_chnl         (in_1_out_2_ibp_wd_chnl),

    .ibp_dw64_in_1_ibp_wrsp_chnl_valid (in_1_out_2_ibp_wrsp_chnl_valid),
    .ibp_dw64_in_1_ibp_wrsp_chnl_accept(in_1_out_2_ibp_wrsp_chnl_accept),
    .ibp_dw64_in_1_ibp_wrsp_chnl       (in_1_out_2_ibp_wrsp_chnl),





    .ibp_dw64_in_2_ibp_cmd_chnl_valid  (in_2_out_2_ibp_cmd_chnl_valid),
    .ibp_dw64_in_2_ibp_cmd_chnl_accept (in_2_out_2_ibp_cmd_chnl_accept),
    .ibp_dw64_in_2_ibp_cmd_chnl        (in_2_out_2_ibp_cmd_chnl),

    .ibp_dw64_in_2_ibp_rd_chnl_valid   (in_2_out_2_ibp_rd_chnl_valid),
    .ibp_dw64_in_2_ibp_rd_chnl_accept  (in_2_out_2_ibp_rd_chnl_accept),
    .ibp_dw64_in_2_ibp_rd_chnl         (in_2_out_2_ibp_rd_chnl),

    .ibp_dw64_in_2_ibp_wd_chnl_valid   (in_2_out_2_ibp_wd_chnl_valid),
    .ibp_dw64_in_2_ibp_wd_chnl_accept  (in_2_out_2_ibp_wd_chnl_accept),
    .ibp_dw64_in_2_ibp_wd_chnl         (in_2_out_2_ibp_wd_chnl),

    .ibp_dw64_in_2_ibp_wrsp_chnl_valid (in_2_out_2_ibp_wrsp_chnl_valid),
    .ibp_dw64_in_2_ibp_wrsp_chnl_accept(in_2_out_2_ibp_wrsp_chnl_accept),
    .ibp_dw64_in_2_ibp_wrsp_chnl       (in_2_out_2_ibp_wrsp_chnl),





    .ibp_dw64_in_3_ibp_cmd_chnl_valid  (in_3_out_2_ibp_cmd_chnl_valid),
    .ibp_dw64_in_3_ibp_cmd_chnl_accept (in_3_out_2_ibp_cmd_chnl_accept),
    .ibp_dw64_in_3_ibp_cmd_chnl        (in_3_out_2_ibp_cmd_chnl),

    .ibp_dw64_in_3_ibp_rd_chnl_valid   (in_3_out_2_ibp_rd_chnl_valid),
    .ibp_dw64_in_3_ibp_rd_chnl_accept  (in_3_out_2_ibp_rd_chnl_accept),
    .ibp_dw64_in_3_ibp_rd_chnl         (in_3_out_2_ibp_rd_chnl),

    .ibp_dw64_in_3_ibp_wd_chnl_valid   (in_3_out_2_ibp_wd_chnl_valid),
    .ibp_dw64_in_3_ibp_wd_chnl_accept  (in_3_out_2_ibp_wd_chnl_accept),
    .ibp_dw64_in_3_ibp_wd_chnl         (in_3_out_2_ibp_wd_chnl),

    .ibp_dw64_in_3_ibp_wrsp_chnl_valid (in_3_out_2_ibp_wrsp_chnl_valid),
    .ibp_dw64_in_3_ibp_wrsp_chnl_accept(in_3_out_2_ibp_wrsp_chnl_accept),
    .ibp_dw64_in_3_ibp_wrsp_chnl       (in_3_out_2_ibp_wrsp_chnl),





    .ibp_dw64_in_4_ibp_cmd_chnl_valid  (in_4_out_2_ibp_cmd_chnl_valid),
    .ibp_dw64_in_4_ibp_cmd_chnl_accept (in_4_out_2_ibp_cmd_chnl_accept),
    .ibp_dw64_in_4_ibp_cmd_chnl        (in_4_out_2_ibp_cmd_chnl),

    .ibp_dw64_in_4_ibp_rd_chnl_valid   (in_4_out_2_ibp_rd_chnl_valid),
    .ibp_dw64_in_4_ibp_rd_chnl_accept  (in_4_out_2_ibp_rd_chnl_accept),
    .ibp_dw64_in_4_ibp_rd_chnl         (in_4_out_2_ibp_rd_chnl),

    .ibp_dw64_in_4_ibp_wd_chnl_valid   (in_4_out_2_ibp_wd_chnl_valid),
    .ibp_dw64_in_4_ibp_wd_chnl_accept  (in_4_out_2_ibp_wd_chnl_accept),
    .ibp_dw64_in_4_ibp_wd_chnl         (in_4_out_2_ibp_wd_chnl),

    .ibp_dw64_in_4_ibp_wrsp_chnl_valid (in_4_out_2_ibp_wrsp_chnl_valid),
    .ibp_dw64_in_4_ibp_wrsp_chnl_accept(in_4_out_2_ibp_wrsp_chnl_accept),
    .ibp_dw64_in_4_ibp_wrsp_chnl       (in_4_out_2_ibp_wrsp_chnl),





    .ibp_dw64_in_5_ibp_cmd_chnl_valid  (in_5_out_2_ibp_cmd_chnl_valid),
    .ibp_dw64_in_5_ibp_cmd_chnl_accept (in_5_out_2_ibp_cmd_chnl_accept),
    .ibp_dw64_in_5_ibp_cmd_chnl        (in_5_out_2_ibp_cmd_chnl),

    .ibp_dw64_in_5_ibp_rd_chnl_valid   (in_5_out_2_ibp_rd_chnl_valid),
    .ibp_dw64_in_5_ibp_rd_chnl_accept  (in_5_out_2_ibp_rd_chnl_accept),
    .ibp_dw64_in_5_ibp_rd_chnl         (in_5_out_2_ibp_rd_chnl),

    .ibp_dw64_in_5_ibp_wd_chnl_valid   (in_5_out_2_ibp_wd_chnl_valid),
    .ibp_dw64_in_5_ibp_wd_chnl_accept  (in_5_out_2_ibp_wd_chnl_accept),
    .ibp_dw64_in_5_ibp_wd_chnl         (in_5_out_2_ibp_wd_chnl),

    .ibp_dw64_in_5_ibp_wrsp_chnl_valid (in_5_out_2_ibp_wrsp_chnl_valid),
    .ibp_dw64_in_5_ibp_wrsp_chnl_accept(in_5_out_2_ibp_wrsp_chnl_accept),
    .ibp_dw64_in_5_ibp_wrsp_chnl       (in_5_out_2_ibp_wrsp_chnl),





    .ibp_dw64_in_6_ibp_cmd_chnl_valid  (in_6_out_2_ibp_cmd_chnl_valid),
    .ibp_dw64_in_6_ibp_cmd_chnl_accept (in_6_out_2_ibp_cmd_chnl_accept),
    .ibp_dw64_in_6_ibp_cmd_chnl        (in_6_out_2_ibp_cmd_chnl),

    .ibp_dw64_in_6_ibp_rd_chnl_valid   (in_6_out_2_ibp_rd_chnl_valid),
    .ibp_dw64_in_6_ibp_rd_chnl_accept  (in_6_out_2_ibp_rd_chnl_accept),
    .ibp_dw64_in_6_ibp_rd_chnl         (in_6_out_2_ibp_rd_chnl),

    .ibp_dw64_in_6_ibp_wd_chnl_valid   (in_6_out_2_ibp_wd_chnl_valid),
    .ibp_dw64_in_6_ibp_wd_chnl_accept  (in_6_out_2_ibp_wd_chnl_accept),
    .ibp_dw64_in_6_ibp_wd_chnl         (in_6_out_2_ibp_wd_chnl),

    .ibp_dw64_in_6_ibp_wrsp_chnl_valid (in_6_out_2_ibp_wrsp_chnl_valid),
    .ibp_dw64_in_6_ibp_wrsp_chnl_accept(in_6_out_2_ibp_wrsp_chnl_accept),
    .ibp_dw64_in_6_ibp_wrsp_chnl       (in_6_out_2_ibp_wrsp_chnl),



  .ibp_dw64_out_ibp_cmd_valid             (arcsync_axi_bs_ibp_cmd_valid),
  .ibp_dw64_out_ibp_cmd_accept            (arcsync_axi_bs_ibp_cmd_accept),
  .ibp_dw64_out_ibp_cmd_read              (arcsync_axi_bs_ibp_cmd_read),
  .ibp_dw64_out_ibp_cmd_addr              (arcsync_axi_bs_ibp_cmd_addr),
  .ibp_dw64_out_ibp_cmd_wrap              (arcsync_axi_bs_ibp_cmd_wrap),
  .ibp_dw64_out_ibp_cmd_data_size         (arcsync_axi_bs_ibp_cmd_data_size),
  .ibp_dw64_out_ibp_cmd_burst_size        (arcsync_axi_bs_ibp_cmd_burst_size),
  .ibp_dw64_out_ibp_cmd_prot              (arcsync_axi_bs_ibp_cmd_prot),
  .ibp_dw64_out_ibp_cmd_cache             (arcsync_axi_bs_ibp_cmd_cache),
  .ibp_dw64_out_ibp_cmd_lock              (arcsync_axi_bs_ibp_cmd_lock),
  .ibp_dw64_out_ibp_cmd_excl              (arcsync_axi_bs_ibp_cmd_excl),

  .ibp_dw64_out_ibp_rd_valid              (arcsync_axi_bs_ibp_rd_valid),
  .ibp_dw64_out_ibp_rd_excl_ok            (arcsync_axi_bs_ibp_rd_excl_ok),
  .ibp_dw64_out_ibp_rd_accept             (arcsync_axi_bs_ibp_rd_accept),
  .ibp_dw64_out_ibp_err_rd                (arcsync_axi_bs_ibp_err_rd),
  .ibp_dw64_out_ibp_rd_data               (arcsync_axi_bs_ibp_rd_data),
  .ibp_dw64_out_ibp_rd_last               (arcsync_axi_bs_ibp_rd_last),

  .ibp_dw64_out_ibp_wr_valid              (arcsync_axi_bs_ibp_wr_valid),
  .ibp_dw64_out_ibp_wr_accept             (arcsync_axi_bs_ibp_wr_accept),
  .ibp_dw64_out_ibp_wr_data               (arcsync_axi_bs_ibp_wr_data),
  .ibp_dw64_out_ibp_wr_mask               (arcsync_axi_bs_ibp_wr_mask),
  .ibp_dw64_out_ibp_wr_last               (arcsync_axi_bs_ibp_wr_last),

  .ibp_dw64_out_ibp_wr_done               (arcsync_axi_bs_ibp_wr_done),
  .ibp_dw64_out_ibp_wr_excl_done          (arcsync_axi_bs_ibp_wr_excl_done),
  .ibp_dw64_out_ibp_err_wr                (arcsync_axi_bs_ibp_err_wr),
  .ibp_dw64_out_ibp_wr_resp_accept        (arcsync_axi_bs_ibp_wr_resp_accept),
.clk         (clk),
.rst_a       (rst_a)
);
mss_bus_switch_ibp_dw128_mst u_mss_bs_mst_3 (



    .ibp_dw128_in_0_ibp_cmd_chnl_valid  (in_0_out_3_ibp_cmd_chnl_valid),
    .ibp_dw128_in_0_ibp_cmd_chnl_accept (in_0_out_3_ibp_cmd_chnl_accept),
    .ibp_dw128_in_0_ibp_cmd_chnl        (in_0_out_3_ibp_cmd_chnl),

    .ibp_dw128_in_0_ibp_rd_chnl_valid   (in_0_out_3_ibp_rd_chnl_valid),
    .ibp_dw128_in_0_ibp_rd_chnl_accept  (in_0_out_3_ibp_rd_chnl_accept),
    .ibp_dw128_in_0_ibp_rd_chnl         (in_0_out_3_ibp_rd_chnl),

    .ibp_dw128_in_0_ibp_wd_chnl_valid   (in_0_out_3_ibp_wd_chnl_valid),
    .ibp_dw128_in_0_ibp_wd_chnl_accept  (in_0_out_3_ibp_wd_chnl_accept),
    .ibp_dw128_in_0_ibp_wd_chnl         (in_0_out_3_ibp_wd_chnl),

    .ibp_dw128_in_0_ibp_wrsp_chnl_valid (in_0_out_3_ibp_wrsp_chnl_valid),
    .ibp_dw128_in_0_ibp_wrsp_chnl_accept(in_0_out_3_ibp_wrsp_chnl_accept),
    .ibp_dw128_in_0_ibp_wrsp_chnl       (in_0_out_3_ibp_wrsp_chnl),





    .ibp_dw128_in_1_ibp_cmd_chnl_valid  (in_1_out_3_ibp_cmd_chnl_valid),
    .ibp_dw128_in_1_ibp_cmd_chnl_accept (in_1_out_3_ibp_cmd_chnl_accept),
    .ibp_dw128_in_1_ibp_cmd_chnl        (in_1_out_3_ibp_cmd_chnl),

    .ibp_dw128_in_1_ibp_rd_chnl_valid   (in_1_out_3_ibp_rd_chnl_valid),
    .ibp_dw128_in_1_ibp_rd_chnl_accept  (in_1_out_3_ibp_rd_chnl_accept),
    .ibp_dw128_in_1_ibp_rd_chnl         (in_1_out_3_ibp_rd_chnl),

    .ibp_dw128_in_1_ibp_wd_chnl_valid   (in_1_out_3_ibp_wd_chnl_valid),
    .ibp_dw128_in_1_ibp_wd_chnl_accept  (in_1_out_3_ibp_wd_chnl_accept),
    .ibp_dw128_in_1_ibp_wd_chnl         (in_1_out_3_ibp_wd_chnl),

    .ibp_dw128_in_1_ibp_wrsp_chnl_valid (in_1_out_3_ibp_wrsp_chnl_valid),
    .ibp_dw128_in_1_ibp_wrsp_chnl_accept(in_1_out_3_ibp_wrsp_chnl_accept),
    .ibp_dw128_in_1_ibp_wrsp_chnl       (in_1_out_3_ibp_wrsp_chnl),





    .ibp_dw128_in_2_ibp_cmd_chnl_valid  (in_2_out_3_ibp_cmd_chnl_valid),
    .ibp_dw128_in_2_ibp_cmd_chnl_accept (in_2_out_3_ibp_cmd_chnl_accept),
    .ibp_dw128_in_2_ibp_cmd_chnl        (in_2_out_3_ibp_cmd_chnl),

    .ibp_dw128_in_2_ibp_rd_chnl_valid   (in_2_out_3_ibp_rd_chnl_valid),
    .ibp_dw128_in_2_ibp_rd_chnl_accept  (in_2_out_3_ibp_rd_chnl_accept),
    .ibp_dw128_in_2_ibp_rd_chnl         (in_2_out_3_ibp_rd_chnl),

    .ibp_dw128_in_2_ibp_wd_chnl_valid   (in_2_out_3_ibp_wd_chnl_valid),
    .ibp_dw128_in_2_ibp_wd_chnl_accept  (in_2_out_3_ibp_wd_chnl_accept),
    .ibp_dw128_in_2_ibp_wd_chnl         (in_2_out_3_ibp_wd_chnl),

    .ibp_dw128_in_2_ibp_wrsp_chnl_valid (in_2_out_3_ibp_wrsp_chnl_valid),
    .ibp_dw128_in_2_ibp_wrsp_chnl_accept(in_2_out_3_ibp_wrsp_chnl_accept),
    .ibp_dw128_in_2_ibp_wrsp_chnl       (in_2_out_3_ibp_wrsp_chnl),





    .ibp_dw128_in_3_ibp_cmd_chnl_valid  (in_3_out_3_ibp_cmd_chnl_valid),
    .ibp_dw128_in_3_ibp_cmd_chnl_accept (in_3_out_3_ibp_cmd_chnl_accept),
    .ibp_dw128_in_3_ibp_cmd_chnl        (in_3_out_3_ibp_cmd_chnl),

    .ibp_dw128_in_3_ibp_rd_chnl_valid   (in_3_out_3_ibp_rd_chnl_valid),
    .ibp_dw128_in_3_ibp_rd_chnl_accept  (in_3_out_3_ibp_rd_chnl_accept),
    .ibp_dw128_in_3_ibp_rd_chnl         (in_3_out_3_ibp_rd_chnl),

    .ibp_dw128_in_3_ibp_wd_chnl_valid   (in_3_out_3_ibp_wd_chnl_valid),
    .ibp_dw128_in_3_ibp_wd_chnl_accept  (in_3_out_3_ibp_wd_chnl_accept),
    .ibp_dw128_in_3_ibp_wd_chnl         (in_3_out_3_ibp_wd_chnl),

    .ibp_dw128_in_3_ibp_wrsp_chnl_valid (in_3_out_3_ibp_wrsp_chnl_valid),
    .ibp_dw128_in_3_ibp_wrsp_chnl_accept(in_3_out_3_ibp_wrsp_chnl_accept),
    .ibp_dw128_in_3_ibp_wrsp_chnl       (in_3_out_3_ibp_wrsp_chnl),





    .ibp_dw128_in_4_ibp_cmd_chnl_valid  (in_4_out_3_ibp_cmd_chnl_valid),
    .ibp_dw128_in_4_ibp_cmd_chnl_accept (in_4_out_3_ibp_cmd_chnl_accept),
    .ibp_dw128_in_4_ibp_cmd_chnl        (in_4_out_3_ibp_cmd_chnl),

    .ibp_dw128_in_4_ibp_rd_chnl_valid   (in_4_out_3_ibp_rd_chnl_valid),
    .ibp_dw128_in_4_ibp_rd_chnl_accept  (in_4_out_3_ibp_rd_chnl_accept),
    .ibp_dw128_in_4_ibp_rd_chnl         (in_4_out_3_ibp_rd_chnl),

    .ibp_dw128_in_4_ibp_wd_chnl_valid   (in_4_out_3_ibp_wd_chnl_valid),
    .ibp_dw128_in_4_ibp_wd_chnl_accept  (in_4_out_3_ibp_wd_chnl_accept),
    .ibp_dw128_in_4_ibp_wd_chnl         (in_4_out_3_ibp_wd_chnl),

    .ibp_dw128_in_4_ibp_wrsp_chnl_valid (in_4_out_3_ibp_wrsp_chnl_valid),
    .ibp_dw128_in_4_ibp_wrsp_chnl_accept(in_4_out_3_ibp_wrsp_chnl_accept),
    .ibp_dw128_in_4_ibp_wrsp_chnl       (in_4_out_3_ibp_wrsp_chnl),





    .ibp_dw128_in_5_ibp_cmd_chnl_valid  (in_5_out_3_ibp_cmd_chnl_valid),
    .ibp_dw128_in_5_ibp_cmd_chnl_accept (in_5_out_3_ibp_cmd_chnl_accept),
    .ibp_dw128_in_5_ibp_cmd_chnl        (in_5_out_3_ibp_cmd_chnl),

    .ibp_dw128_in_5_ibp_rd_chnl_valid   (in_5_out_3_ibp_rd_chnl_valid),
    .ibp_dw128_in_5_ibp_rd_chnl_accept  (in_5_out_3_ibp_rd_chnl_accept),
    .ibp_dw128_in_5_ibp_rd_chnl         (in_5_out_3_ibp_rd_chnl),

    .ibp_dw128_in_5_ibp_wd_chnl_valid   (in_5_out_3_ibp_wd_chnl_valid),
    .ibp_dw128_in_5_ibp_wd_chnl_accept  (in_5_out_3_ibp_wd_chnl_accept),
    .ibp_dw128_in_5_ibp_wd_chnl         (in_5_out_3_ibp_wd_chnl),

    .ibp_dw128_in_5_ibp_wrsp_chnl_valid (in_5_out_3_ibp_wrsp_chnl_valid),
    .ibp_dw128_in_5_ibp_wrsp_chnl_accept(in_5_out_3_ibp_wrsp_chnl_accept),
    .ibp_dw128_in_5_ibp_wrsp_chnl       (in_5_out_3_ibp_wrsp_chnl),





    .ibp_dw128_in_6_ibp_cmd_chnl_valid  (in_6_out_3_ibp_cmd_chnl_valid),
    .ibp_dw128_in_6_ibp_cmd_chnl_accept (in_6_out_3_ibp_cmd_chnl_accept),
    .ibp_dw128_in_6_ibp_cmd_chnl        (in_6_out_3_ibp_cmd_chnl),

    .ibp_dw128_in_6_ibp_rd_chnl_valid   (in_6_out_3_ibp_rd_chnl_valid),
    .ibp_dw128_in_6_ibp_rd_chnl_accept  (in_6_out_3_ibp_rd_chnl_accept),
    .ibp_dw128_in_6_ibp_rd_chnl         (in_6_out_3_ibp_rd_chnl),

    .ibp_dw128_in_6_ibp_wd_chnl_valid   (in_6_out_3_ibp_wd_chnl_valid),
    .ibp_dw128_in_6_ibp_wd_chnl_accept  (in_6_out_3_ibp_wd_chnl_accept),
    .ibp_dw128_in_6_ibp_wd_chnl         (in_6_out_3_ibp_wd_chnl),

    .ibp_dw128_in_6_ibp_wrsp_chnl_valid (in_6_out_3_ibp_wrsp_chnl_valid),
    .ibp_dw128_in_6_ibp_wrsp_chnl_accept(in_6_out_3_ibp_wrsp_chnl_accept),
    .ibp_dw128_in_6_ibp_wrsp_chnl       (in_6_out_3_ibp_wrsp_chnl),



  .ibp_dw128_out_ibp_cmd_valid             (mss_mem_bs_ibp_cmd_valid),
  .ibp_dw128_out_ibp_cmd_accept            (mss_mem_bs_ibp_cmd_accept),
  .ibp_dw128_out_ibp_cmd_read              (mss_mem_bs_ibp_cmd_read),
  .ibp_dw128_out_ibp_cmd_addr              (mss_mem_bs_ibp_cmd_addr),
  .ibp_dw128_out_ibp_cmd_wrap              (mss_mem_bs_ibp_cmd_wrap),
  .ibp_dw128_out_ibp_cmd_data_size         (mss_mem_bs_ibp_cmd_data_size),
  .ibp_dw128_out_ibp_cmd_burst_size        (mss_mem_bs_ibp_cmd_burst_size),
  .ibp_dw128_out_ibp_cmd_prot              (mss_mem_bs_ibp_cmd_prot),
  .ibp_dw128_out_ibp_cmd_cache             (mss_mem_bs_ibp_cmd_cache),
  .ibp_dw128_out_ibp_cmd_lock              (mss_mem_bs_ibp_cmd_lock),
  .ibp_dw128_out_ibp_cmd_excl              (mss_mem_bs_ibp_cmd_excl),

  .ibp_dw128_out_ibp_rd_valid              (mss_mem_bs_ibp_rd_valid),
  .ibp_dw128_out_ibp_rd_excl_ok            (mss_mem_bs_ibp_rd_excl_ok),
  .ibp_dw128_out_ibp_rd_accept             (mss_mem_bs_ibp_rd_accept),
  .ibp_dw128_out_ibp_err_rd                (mss_mem_bs_ibp_err_rd),
  .ibp_dw128_out_ibp_rd_data               (mss_mem_bs_ibp_rd_data),
  .ibp_dw128_out_ibp_rd_last               (mss_mem_bs_ibp_rd_last),

  .ibp_dw128_out_ibp_wr_valid              (mss_mem_bs_ibp_wr_valid),
  .ibp_dw128_out_ibp_wr_accept             (mss_mem_bs_ibp_wr_accept),
  .ibp_dw128_out_ibp_wr_data               (mss_mem_bs_ibp_wr_data),
  .ibp_dw128_out_ibp_wr_mask               (mss_mem_bs_ibp_wr_mask),
  .ibp_dw128_out_ibp_wr_last               (mss_mem_bs_ibp_wr_last),

  .ibp_dw128_out_ibp_wr_done               (mss_mem_bs_ibp_wr_done),
  .ibp_dw128_out_ibp_wr_excl_done          (mss_mem_bs_ibp_wr_excl_done),
  .ibp_dw128_out_ibp_err_wr                (mss_mem_bs_ibp_err_wr),
  .ibp_dw128_out_ibp_wr_resp_accept        (mss_mem_bs_ibp_wr_resp_accept),
.clk         (clk),
.rst_a       (rst_a)
);

//
// default slave
//

  wire                                  bus_switch_def_slv_ibp_cmd_valid;
  wire                                  bus_switch_def_slv_ibp_cmd_accept;
  wire                                  bus_switch_def_slv_ibp_cmd_read;
  wire  [49                -1:0]       bus_switch_def_slv_ibp_cmd_addr;
  wire                                  bus_switch_def_slv_ibp_cmd_wrap;
  wire  [3-1:0]       bus_switch_def_slv_ibp_cmd_data_size;
  wire  [4-1:0]       bus_switch_def_slv_ibp_cmd_burst_size;
  wire  [2-1:0]       bus_switch_def_slv_ibp_cmd_prot;
  wire  [4-1:0]       bus_switch_def_slv_ibp_cmd_cache;
  wire                                  bus_switch_def_slv_ibp_cmd_lock;
  wire                                  bus_switch_def_slv_ibp_cmd_excl;

  wire                                  bus_switch_def_slv_ibp_rd_valid;
  wire                                  bus_switch_def_slv_ibp_rd_excl_ok;
  wire                                  bus_switch_def_slv_ibp_rd_accept;
  wire                                  bus_switch_def_slv_ibp_err_rd;
  wire  [32               -1:0]        bus_switch_def_slv_ibp_rd_data;
  wire                                  bus_switch_def_slv_ibp_rd_last;

  wire                                  bus_switch_def_slv_ibp_wr_valid;
  wire                                  bus_switch_def_slv_ibp_wr_accept;
  wire  [32               -1:0]        bus_switch_def_slv_ibp_wr_data;
  wire  [(32         /8)  -1:0]        bus_switch_def_slv_ibp_wr_mask;
  wire                                  bus_switch_def_slv_ibp_wr_last;

  wire                                  bus_switch_def_slv_ibp_wr_done;
  wire                                  bus_switch_def_slv_ibp_wr_excl_done;
  wire                                  bus_switch_def_slv_ibp_err_wr;
  wire                                  bus_switch_def_slv_ibp_wr_resp_accept;


mss_bus_switch_ibp_dw32_mst u_mss_bs_mst_4 (



    .ibp_dw32_in_0_ibp_cmd_chnl_valid  (in_0_out_4_ibp_cmd_chnl_valid),
    .ibp_dw32_in_0_ibp_cmd_chnl_accept (in_0_out_4_ibp_cmd_chnl_accept),
    .ibp_dw32_in_0_ibp_cmd_chnl        (in_0_out_4_ibp_cmd_chnl),

    .ibp_dw32_in_0_ibp_rd_chnl_valid   (in_0_out_4_ibp_rd_chnl_valid),
    .ibp_dw32_in_0_ibp_rd_chnl_accept  (in_0_out_4_ibp_rd_chnl_accept),
    .ibp_dw32_in_0_ibp_rd_chnl         (in_0_out_4_ibp_rd_chnl),

    .ibp_dw32_in_0_ibp_wd_chnl_valid   (in_0_out_4_ibp_wd_chnl_valid),
    .ibp_dw32_in_0_ibp_wd_chnl_accept  (in_0_out_4_ibp_wd_chnl_accept),
    .ibp_dw32_in_0_ibp_wd_chnl         (in_0_out_4_ibp_wd_chnl),

    .ibp_dw32_in_0_ibp_wrsp_chnl_valid (in_0_out_4_ibp_wrsp_chnl_valid),
    .ibp_dw32_in_0_ibp_wrsp_chnl_accept(in_0_out_4_ibp_wrsp_chnl_accept),
    .ibp_dw32_in_0_ibp_wrsp_chnl       (in_0_out_4_ibp_wrsp_chnl),





    .ibp_dw32_in_1_ibp_cmd_chnl_valid  (in_1_out_4_ibp_cmd_chnl_valid),
    .ibp_dw32_in_1_ibp_cmd_chnl_accept (in_1_out_4_ibp_cmd_chnl_accept),
    .ibp_dw32_in_1_ibp_cmd_chnl        (in_1_out_4_ibp_cmd_chnl),

    .ibp_dw32_in_1_ibp_rd_chnl_valid   (in_1_out_4_ibp_rd_chnl_valid),
    .ibp_dw32_in_1_ibp_rd_chnl_accept  (in_1_out_4_ibp_rd_chnl_accept),
    .ibp_dw32_in_1_ibp_rd_chnl         (in_1_out_4_ibp_rd_chnl),

    .ibp_dw32_in_1_ibp_wd_chnl_valid   (in_1_out_4_ibp_wd_chnl_valid),
    .ibp_dw32_in_1_ibp_wd_chnl_accept  (in_1_out_4_ibp_wd_chnl_accept),
    .ibp_dw32_in_1_ibp_wd_chnl         (in_1_out_4_ibp_wd_chnl),

    .ibp_dw32_in_1_ibp_wrsp_chnl_valid (in_1_out_4_ibp_wrsp_chnl_valid),
    .ibp_dw32_in_1_ibp_wrsp_chnl_accept(in_1_out_4_ibp_wrsp_chnl_accept),
    .ibp_dw32_in_1_ibp_wrsp_chnl       (in_1_out_4_ibp_wrsp_chnl),





    .ibp_dw32_in_2_ibp_cmd_chnl_valid  (in_2_out_4_ibp_cmd_chnl_valid),
    .ibp_dw32_in_2_ibp_cmd_chnl_accept (in_2_out_4_ibp_cmd_chnl_accept),
    .ibp_dw32_in_2_ibp_cmd_chnl        (in_2_out_4_ibp_cmd_chnl),

    .ibp_dw32_in_2_ibp_rd_chnl_valid   (in_2_out_4_ibp_rd_chnl_valid),
    .ibp_dw32_in_2_ibp_rd_chnl_accept  (in_2_out_4_ibp_rd_chnl_accept),
    .ibp_dw32_in_2_ibp_rd_chnl         (in_2_out_4_ibp_rd_chnl),

    .ibp_dw32_in_2_ibp_wd_chnl_valid   (in_2_out_4_ibp_wd_chnl_valid),
    .ibp_dw32_in_2_ibp_wd_chnl_accept  (in_2_out_4_ibp_wd_chnl_accept),
    .ibp_dw32_in_2_ibp_wd_chnl         (in_2_out_4_ibp_wd_chnl),

    .ibp_dw32_in_2_ibp_wrsp_chnl_valid (in_2_out_4_ibp_wrsp_chnl_valid),
    .ibp_dw32_in_2_ibp_wrsp_chnl_accept(in_2_out_4_ibp_wrsp_chnl_accept),
    .ibp_dw32_in_2_ibp_wrsp_chnl       (in_2_out_4_ibp_wrsp_chnl),





    .ibp_dw32_in_3_ibp_cmd_chnl_valid  (in_3_out_4_ibp_cmd_chnl_valid),
    .ibp_dw32_in_3_ibp_cmd_chnl_accept (in_3_out_4_ibp_cmd_chnl_accept),
    .ibp_dw32_in_3_ibp_cmd_chnl        (in_3_out_4_ibp_cmd_chnl),

    .ibp_dw32_in_3_ibp_rd_chnl_valid   (in_3_out_4_ibp_rd_chnl_valid),
    .ibp_dw32_in_3_ibp_rd_chnl_accept  (in_3_out_4_ibp_rd_chnl_accept),
    .ibp_dw32_in_3_ibp_rd_chnl         (in_3_out_4_ibp_rd_chnl),

    .ibp_dw32_in_3_ibp_wd_chnl_valid   (in_3_out_4_ibp_wd_chnl_valid),
    .ibp_dw32_in_3_ibp_wd_chnl_accept  (in_3_out_4_ibp_wd_chnl_accept),
    .ibp_dw32_in_3_ibp_wd_chnl         (in_3_out_4_ibp_wd_chnl),

    .ibp_dw32_in_3_ibp_wrsp_chnl_valid (in_3_out_4_ibp_wrsp_chnl_valid),
    .ibp_dw32_in_3_ibp_wrsp_chnl_accept(in_3_out_4_ibp_wrsp_chnl_accept),
    .ibp_dw32_in_3_ibp_wrsp_chnl       (in_3_out_4_ibp_wrsp_chnl),





    .ibp_dw32_in_4_ibp_cmd_chnl_valid  (in_4_out_4_ibp_cmd_chnl_valid),
    .ibp_dw32_in_4_ibp_cmd_chnl_accept (in_4_out_4_ibp_cmd_chnl_accept),
    .ibp_dw32_in_4_ibp_cmd_chnl        (in_4_out_4_ibp_cmd_chnl),

    .ibp_dw32_in_4_ibp_rd_chnl_valid   (in_4_out_4_ibp_rd_chnl_valid),
    .ibp_dw32_in_4_ibp_rd_chnl_accept  (in_4_out_4_ibp_rd_chnl_accept),
    .ibp_dw32_in_4_ibp_rd_chnl         (in_4_out_4_ibp_rd_chnl),

    .ibp_dw32_in_4_ibp_wd_chnl_valid   (in_4_out_4_ibp_wd_chnl_valid),
    .ibp_dw32_in_4_ibp_wd_chnl_accept  (in_4_out_4_ibp_wd_chnl_accept),
    .ibp_dw32_in_4_ibp_wd_chnl         (in_4_out_4_ibp_wd_chnl),

    .ibp_dw32_in_4_ibp_wrsp_chnl_valid (in_4_out_4_ibp_wrsp_chnl_valid),
    .ibp_dw32_in_4_ibp_wrsp_chnl_accept(in_4_out_4_ibp_wrsp_chnl_accept),
    .ibp_dw32_in_4_ibp_wrsp_chnl       (in_4_out_4_ibp_wrsp_chnl),





    .ibp_dw32_in_5_ibp_cmd_chnl_valid  (in_5_out_4_ibp_cmd_chnl_valid),
    .ibp_dw32_in_5_ibp_cmd_chnl_accept (in_5_out_4_ibp_cmd_chnl_accept),
    .ibp_dw32_in_5_ibp_cmd_chnl        (in_5_out_4_ibp_cmd_chnl),

    .ibp_dw32_in_5_ibp_rd_chnl_valid   (in_5_out_4_ibp_rd_chnl_valid),
    .ibp_dw32_in_5_ibp_rd_chnl_accept  (in_5_out_4_ibp_rd_chnl_accept),
    .ibp_dw32_in_5_ibp_rd_chnl         (in_5_out_4_ibp_rd_chnl),

    .ibp_dw32_in_5_ibp_wd_chnl_valid   (in_5_out_4_ibp_wd_chnl_valid),
    .ibp_dw32_in_5_ibp_wd_chnl_accept  (in_5_out_4_ibp_wd_chnl_accept),
    .ibp_dw32_in_5_ibp_wd_chnl         (in_5_out_4_ibp_wd_chnl),

    .ibp_dw32_in_5_ibp_wrsp_chnl_valid (in_5_out_4_ibp_wrsp_chnl_valid),
    .ibp_dw32_in_5_ibp_wrsp_chnl_accept(in_5_out_4_ibp_wrsp_chnl_accept),
    .ibp_dw32_in_5_ibp_wrsp_chnl       (in_5_out_4_ibp_wrsp_chnl),





    .ibp_dw32_in_6_ibp_cmd_chnl_valid  (in_6_out_4_ibp_cmd_chnl_valid),
    .ibp_dw32_in_6_ibp_cmd_chnl_accept (in_6_out_4_ibp_cmd_chnl_accept),
    .ibp_dw32_in_6_ibp_cmd_chnl        (in_6_out_4_ibp_cmd_chnl),

    .ibp_dw32_in_6_ibp_rd_chnl_valid   (in_6_out_4_ibp_rd_chnl_valid),
    .ibp_dw32_in_6_ibp_rd_chnl_accept  (in_6_out_4_ibp_rd_chnl_accept),
    .ibp_dw32_in_6_ibp_rd_chnl         (in_6_out_4_ibp_rd_chnl),

    .ibp_dw32_in_6_ibp_wd_chnl_valid   (in_6_out_4_ibp_wd_chnl_valid),
    .ibp_dw32_in_6_ibp_wd_chnl_accept  (in_6_out_4_ibp_wd_chnl_accept),
    .ibp_dw32_in_6_ibp_wd_chnl         (in_6_out_4_ibp_wd_chnl),

    .ibp_dw32_in_6_ibp_wrsp_chnl_valid (in_6_out_4_ibp_wrsp_chnl_valid),
    .ibp_dw32_in_6_ibp_wrsp_chnl_accept(in_6_out_4_ibp_wrsp_chnl_accept),
    .ibp_dw32_in_6_ibp_wrsp_chnl       (in_6_out_4_ibp_wrsp_chnl),



  .ibp_dw32_out_ibp_cmd_valid             (bus_switch_def_slv_ibp_cmd_valid),
  .ibp_dw32_out_ibp_cmd_accept            (bus_switch_def_slv_ibp_cmd_accept),
  .ibp_dw32_out_ibp_cmd_read              (bus_switch_def_slv_ibp_cmd_read),
  .ibp_dw32_out_ibp_cmd_addr              (bus_switch_def_slv_ibp_cmd_addr),
  .ibp_dw32_out_ibp_cmd_wrap              (bus_switch_def_slv_ibp_cmd_wrap),
  .ibp_dw32_out_ibp_cmd_data_size         (bus_switch_def_slv_ibp_cmd_data_size),
  .ibp_dw32_out_ibp_cmd_burst_size        (bus_switch_def_slv_ibp_cmd_burst_size),
  .ibp_dw32_out_ibp_cmd_prot              (bus_switch_def_slv_ibp_cmd_prot),
  .ibp_dw32_out_ibp_cmd_cache             (bus_switch_def_slv_ibp_cmd_cache),
  .ibp_dw32_out_ibp_cmd_lock              (bus_switch_def_slv_ibp_cmd_lock),
  .ibp_dw32_out_ibp_cmd_excl              (bus_switch_def_slv_ibp_cmd_excl),

  .ibp_dw32_out_ibp_rd_valid              (bus_switch_def_slv_ibp_rd_valid),
  .ibp_dw32_out_ibp_rd_excl_ok            (bus_switch_def_slv_ibp_rd_excl_ok),
  .ibp_dw32_out_ibp_rd_accept             (bus_switch_def_slv_ibp_rd_accept),
  .ibp_dw32_out_ibp_err_rd                (bus_switch_def_slv_ibp_err_rd),
  .ibp_dw32_out_ibp_rd_data               (bus_switch_def_slv_ibp_rd_data),
  .ibp_dw32_out_ibp_rd_last               (bus_switch_def_slv_ibp_rd_last),

  .ibp_dw32_out_ibp_wr_valid              (bus_switch_def_slv_ibp_wr_valid),
  .ibp_dw32_out_ibp_wr_accept             (bus_switch_def_slv_ibp_wr_accept),
  .ibp_dw32_out_ibp_wr_data               (bus_switch_def_slv_ibp_wr_data),
  .ibp_dw32_out_ibp_wr_mask               (bus_switch_def_slv_ibp_wr_mask),
  .ibp_dw32_out_ibp_wr_last               (bus_switch_def_slv_ibp_wr_last),

  .ibp_dw32_out_ibp_wr_done               (bus_switch_def_slv_ibp_wr_done),
  .ibp_dw32_out_ibp_wr_excl_done          (bus_switch_def_slv_ibp_wr_excl_done),
  .ibp_dw32_out_ibp_err_wr                (bus_switch_def_slv_ibp_err_wr),
  .ibp_dw32_out_ibp_wr_resp_accept        (bus_switch_def_slv_ibp_wr_resp_accept),
.clk         (clk),
.rst_a       (rst_a)
);


mss_bus_switch_default_slv #(49, 32, `BUS_SWITCH_SLV_HOLE_RESP_ERR) u_default_slv(

  .bus_switch_def_slv_ibp_cmd_valid             (bus_switch_def_slv_ibp_cmd_valid),
  .bus_switch_def_slv_ibp_cmd_accept            (bus_switch_def_slv_ibp_cmd_accept),
  .bus_switch_def_slv_ibp_cmd_read              (bus_switch_def_slv_ibp_cmd_read),
  .bus_switch_def_slv_ibp_cmd_addr              (bus_switch_def_slv_ibp_cmd_addr),
  .bus_switch_def_slv_ibp_cmd_wrap              (bus_switch_def_slv_ibp_cmd_wrap),
  .bus_switch_def_slv_ibp_cmd_data_size         (bus_switch_def_slv_ibp_cmd_data_size),
  .bus_switch_def_slv_ibp_cmd_burst_size        (bus_switch_def_slv_ibp_cmd_burst_size),
  .bus_switch_def_slv_ibp_cmd_prot              (bus_switch_def_slv_ibp_cmd_prot),
  .bus_switch_def_slv_ibp_cmd_cache             (bus_switch_def_slv_ibp_cmd_cache),
  .bus_switch_def_slv_ibp_cmd_lock              (bus_switch_def_slv_ibp_cmd_lock),
  .bus_switch_def_slv_ibp_cmd_excl              (bus_switch_def_slv_ibp_cmd_excl),

  .bus_switch_def_slv_ibp_rd_valid              (bus_switch_def_slv_ibp_rd_valid),
  .bus_switch_def_slv_ibp_rd_excl_ok            (bus_switch_def_slv_ibp_rd_excl_ok),
  .bus_switch_def_slv_ibp_rd_accept             (bus_switch_def_slv_ibp_rd_accept),
  .bus_switch_def_slv_ibp_err_rd                (bus_switch_def_slv_ibp_err_rd),
  .bus_switch_def_slv_ibp_rd_data               (bus_switch_def_slv_ibp_rd_data),
  .bus_switch_def_slv_ibp_rd_last               (bus_switch_def_slv_ibp_rd_last),

  .bus_switch_def_slv_ibp_wr_valid              (bus_switch_def_slv_ibp_wr_valid),
  .bus_switch_def_slv_ibp_wr_accept             (bus_switch_def_slv_ibp_wr_accept),
  .bus_switch_def_slv_ibp_wr_data               (bus_switch_def_slv_ibp_wr_data),
  .bus_switch_def_slv_ibp_wr_mask               (bus_switch_def_slv_ibp_wr_mask),
  .bus_switch_def_slv_ibp_wr_last               (bus_switch_def_slv_ibp_wr_last),

  .bus_switch_def_slv_ibp_wr_done               (bus_switch_def_slv_ibp_wr_done),
  .bus_switch_def_slv_ibp_wr_excl_done          (bus_switch_def_slv_ibp_wr_excl_done),
  .bus_switch_def_slv_ibp_err_wr                (bus_switch_def_slv_ibp_err_wr),
  .bus_switch_def_slv_ibp_wr_resp_accept        (bus_switch_def_slv_ibp_wr_resp_accept),
.clk         (clk),
.rst_a       (rst_a)
);



/////////////////////////master region compute////////////////////////////////////////////



assign npu_mst0_axi_bs_ibp_cmd_rgon =
                                0 ? (1 << `BUS_SWITCH_SLV_NUM) :
                                addr_in_rgn(917504, 983039, npu_mst0_axi_bs_ibp_cmd_addr[`BUS_SWITCH_ADDR_RANGE]) ? (1 << 0) :
                                addr_in_rgn(983040, 983295, npu_mst0_axi_bs_ibp_cmd_addr[`BUS_SWITCH_ADDR_RANGE]) ? (1 << 1) :
                                addr_in_rgn(868352, 872447, npu_mst0_axi_bs_ibp_cmd_addr[`BUS_SWITCH_ADDR_RANGE]) ? (1 << 2) :
                                addr_in_rgn(0, 1048575, npu_mst0_axi_bs_ibp_cmd_addr[`BUS_SWITCH_ADDR_RANGE]) ? (1 << 3) :
                                (1 << `BUS_SWITCH_SLV_NUM);


assign npu_mst1_axi_bs_ibp_cmd_rgon =
                                0 ? (1 << `BUS_SWITCH_SLV_NUM) :
                                addr_in_rgn(917504, 983039, npu_mst1_axi_bs_ibp_cmd_addr[`BUS_SWITCH_ADDR_RANGE]) ? (1 << 0) :
                                addr_in_rgn(983040, 983295, npu_mst1_axi_bs_ibp_cmd_addr[`BUS_SWITCH_ADDR_RANGE]) ? (1 << 1) :
                                addr_in_rgn(868352, 872447, npu_mst1_axi_bs_ibp_cmd_addr[`BUS_SWITCH_ADDR_RANGE]) ? (1 << 2) :
                                addr_in_rgn(0, 1048575, npu_mst1_axi_bs_ibp_cmd_addr[`BUS_SWITCH_ADDR_RANGE]) ? (1 << 3) :
                                (1 << `BUS_SWITCH_SLV_NUM);


assign npu_mst2_axi_bs_ibp_cmd_rgon =
                                0 ? (1 << `BUS_SWITCH_SLV_NUM) :
                                addr_in_rgn(917504, 983039, npu_mst2_axi_bs_ibp_cmd_addr[`BUS_SWITCH_ADDR_RANGE]) ? (1 << 0) :
                                addr_in_rgn(983040, 983295, npu_mst2_axi_bs_ibp_cmd_addr[`BUS_SWITCH_ADDR_RANGE]) ? (1 << 1) :
                                addr_in_rgn(868352, 872447, npu_mst2_axi_bs_ibp_cmd_addr[`BUS_SWITCH_ADDR_RANGE]) ? (1 << 2) :
                                addr_in_rgn(0, 1048575, npu_mst2_axi_bs_ibp_cmd_addr[`BUS_SWITCH_ADDR_RANGE]) ? (1 << 3) :
                                (1 << `BUS_SWITCH_SLV_NUM);


assign npu_mst3_axi_bs_ibp_cmd_rgon =
                                0 ? (1 << `BUS_SWITCH_SLV_NUM) :
                                addr_in_rgn(917504, 983039, npu_mst3_axi_bs_ibp_cmd_addr[`BUS_SWITCH_ADDR_RANGE]) ? (1 << 0) :
                                addr_in_rgn(983040, 983295, npu_mst3_axi_bs_ibp_cmd_addr[`BUS_SWITCH_ADDR_RANGE]) ? (1 << 1) :
                                addr_in_rgn(868352, 872447, npu_mst3_axi_bs_ibp_cmd_addr[`BUS_SWITCH_ADDR_RANGE]) ? (1 << 2) :
                                addr_in_rgn(0, 1048575, npu_mst3_axi_bs_ibp_cmd_addr[`BUS_SWITCH_ADDR_RANGE]) ? (1 << 3) :
                                (1 << `BUS_SWITCH_SLV_NUM);


assign npu_mst4_axi_bs_ibp_cmd_rgon =
                                0 ? (1 << `BUS_SWITCH_SLV_NUM) :
                                addr_in_rgn(917504, 983039, npu_mst4_axi_bs_ibp_cmd_addr[`BUS_SWITCH_ADDR_RANGE]) ? (1 << 0) :
                                addr_in_rgn(983040, 983295, npu_mst4_axi_bs_ibp_cmd_addr[`BUS_SWITCH_ADDR_RANGE]) ? (1 << 1) :
                                addr_in_rgn(868352, 872447, npu_mst4_axi_bs_ibp_cmd_addr[`BUS_SWITCH_ADDR_RANGE]) ? (1 << 2) :
                                addr_in_rgn(0, 1048575, npu_mst4_axi_bs_ibp_cmd_addr[`BUS_SWITCH_ADDR_RANGE]) ? (1 << 3) :
                                (1 << `BUS_SWITCH_SLV_NUM);


assign host_axi_bs_ibp_cmd_rgon =
                                0 ? (1 << `BUS_SWITCH_SLV_NUM) :
                                addr_in_rgn(917504, 983039, host_axi_bs_ibp_cmd_addr[`BUS_SWITCH_ADDR_RANGE]) ? (1 << 0) :
                                addr_in_rgn(983040, 983295, host_axi_bs_ibp_cmd_addr[`BUS_SWITCH_ADDR_RANGE]) ? (1 << 1) :
                                addr_in_rgn(868352, 872447, host_axi_bs_ibp_cmd_addr[`BUS_SWITCH_ADDR_RANGE]) ? (1 << 2) :
                                addr_in_rgn(0, 1048575, host_axi_bs_ibp_cmd_addr[`BUS_SWITCH_ADDR_RANGE]) ? (1 << 3) :
                                (1 << `BUS_SWITCH_SLV_NUM);


assign bri4tb_bs_ibp_cmd_rgon =
                                0 ? (1 << `BUS_SWITCH_SLV_NUM) :
                                addr_in_rgn(917504, 983039, bri4tb_bs_ibp_cmd_addr[`BUS_SWITCH_ADDR_RANGE]) ? (1 << 0) :
                                addr_in_rgn(983040, 983295, bri4tb_bs_ibp_cmd_addr[`BUS_SWITCH_ADDR_RANGE]) ? (1 << 1) :
                                addr_in_rgn(868352, 872447, bri4tb_bs_ibp_cmd_addr[`BUS_SWITCH_ADDR_RANGE]) ? (1 << 2) :
                                addr_in_rgn(0, 1048575, bri4tb_bs_ibp_cmd_addr[`BUS_SWITCH_ADDR_RANGE]) ? (1 << 3) :
                                (1 << `BUS_SWITCH_SLV_NUM);


/////////////////////////base addr and addr apeature calcu////////////////////////
function addr_in_rgn;
input [27 : 0] low_addr, up_addr, addr;
    if((addr >= low_addr) & (addr <= up_addr))
        addr_in_rgn = 1;
    else
        addr_in_rgn = 0;
endfunction
// 4KB aligned



/////////////////////slv region compute////////////////////////////////////////


    assign npu_dmi0_axi_bs_ibp_cmd_region =
                                      ((npu_dmi0_axi_bs_ibp_cmd_addr[`BUS_SWITCH_SLV_RGN_MATCH_RANGE] &  base_size_mask(28)) ==
                                      ((917504) & base_size_mask(28)) ) ? 0 :
                                      0;



    assign npu_cfg_axi_bs_ibp_cmd_region =
                                      ((npu_cfg_axi_bs_ibp_cmd_addr[`BUS_SWITCH_SLV_RGN_MATCH_RANGE] &  base_size_mask(20)) ==
                                      ((983040) & base_size_mask(20)) ) ? 0 :
                                      0;



    assign arcsync_axi_bs_ibp_cmd_region =
                                      ((arcsync_axi_bs_ibp_cmd_addr[`BUS_SWITCH_SLV_RGN_MATCH_RANGE] &  base_size_mask(24)) ==
                                      ((868352) & base_size_mask(24)) ) ? 0 :
                                      0;



    assign mss_mem_bs_ibp_cmd_region =
                                      ((mss_mem_bs_ibp_cmd_addr[`BUS_SWITCH_SLV_RGN_MATCH_RANGE] &  base_size_mask(32)) ==
                                      ((0) & base_size_mask(32)) ) ? 0 :
                                      0;



function [`BUS_SWITCH_SLV_RGN_BASE_RANGE] base_size_mask;
input [`BUS_SWITCH_SLV_RGN_SIZE_RANGE] base_size;
begin
    case (base_size -12)
    `BUS_SWITCH_SLV_RGN_SIZE_BITS'd0: base_size_mask = ~`BUS_SWITCH_SLV_RGN_BASE_BITS'd0;
    `BUS_SWITCH_SLV_RGN_SIZE_BITS'd1: base_size_mask = ~`BUS_SWITCH_SLV_RGN_BASE_BITS'd1;
    `BUS_SWITCH_SLV_RGN_SIZE_BITS'd2: base_size_mask = ~`BUS_SWITCH_SLV_RGN_BASE_BITS'd3;
    `BUS_SWITCH_SLV_RGN_SIZE_BITS'd3: base_size_mask = ~`BUS_SWITCH_SLV_RGN_BASE_BITS'd7;
    `BUS_SWITCH_SLV_RGN_SIZE_BITS'd4: base_size_mask = ~`BUS_SWITCH_SLV_RGN_BASE_BITS'd15;
    `BUS_SWITCH_SLV_RGN_SIZE_BITS'd5: base_size_mask = ~`BUS_SWITCH_SLV_RGN_BASE_BITS'd31;
    `BUS_SWITCH_SLV_RGN_SIZE_BITS'd6: base_size_mask = ~`BUS_SWITCH_SLV_RGN_BASE_BITS'd63;
    `BUS_SWITCH_SLV_RGN_SIZE_BITS'd7: base_size_mask = ~`BUS_SWITCH_SLV_RGN_BASE_BITS'd127;
    `BUS_SWITCH_SLV_RGN_SIZE_BITS'd8: base_size_mask = ~`BUS_SWITCH_SLV_RGN_BASE_BITS'd255;
    `BUS_SWITCH_SLV_RGN_SIZE_BITS'd9: base_size_mask = ~`BUS_SWITCH_SLV_RGN_BASE_BITS'd511;
    `BUS_SWITCH_SLV_RGN_SIZE_BITS'd10: base_size_mask = ~`BUS_SWITCH_SLV_RGN_BASE_BITS'd1023;
    `BUS_SWITCH_SLV_RGN_SIZE_BITS'd11: base_size_mask = ~`BUS_SWITCH_SLV_RGN_BASE_BITS'd2047;
    `BUS_SWITCH_SLV_RGN_SIZE_BITS'd12: base_size_mask = ~`BUS_SWITCH_SLV_RGN_BASE_BITS'd4095;
    `BUS_SWITCH_SLV_RGN_SIZE_BITS'd13: base_size_mask = ~`BUS_SWITCH_SLV_RGN_BASE_BITS'd8191;
    `BUS_SWITCH_SLV_RGN_SIZE_BITS'd14: base_size_mask = ~`BUS_SWITCH_SLV_RGN_BASE_BITS'd16383;
    `BUS_SWITCH_SLV_RGN_SIZE_BITS'd15: base_size_mask = ~`BUS_SWITCH_SLV_RGN_BASE_BITS'd32767;
    `BUS_SWITCH_SLV_RGN_SIZE_BITS'd16: base_size_mask = ~`BUS_SWITCH_SLV_RGN_BASE_BITS'd65535;
    `BUS_SWITCH_SLV_RGN_SIZE_BITS'd17: base_size_mask = ~`BUS_SWITCH_SLV_RGN_BASE_BITS'd131071;
    `BUS_SWITCH_SLV_RGN_SIZE_BITS'd18: base_size_mask = ~`BUS_SWITCH_SLV_RGN_BASE_BITS'd262143;
    `BUS_SWITCH_SLV_RGN_SIZE_BITS'd19: base_size_mask = ~`BUS_SWITCH_SLV_RGN_BASE_BITS'd524287;
    `BUS_SWITCH_SLV_RGN_SIZE_BITS'd20: base_size_mask = ~`BUS_SWITCH_SLV_RGN_BASE_BITS'd1048575;
    `BUS_SWITCH_SLV_RGN_SIZE_BITS'd21: base_size_mask = ~`BUS_SWITCH_SLV_RGN_BASE_BITS'd2097151;
    `BUS_SWITCH_SLV_RGN_SIZE_BITS'd22: base_size_mask = ~`BUS_SWITCH_SLV_RGN_BASE_BITS'd4194303;
    `BUS_SWITCH_SLV_RGN_SIZE_BITS'd23: base_size_mask = ~`BUS_SWITCH_SLV_RGN_BASE_BITS'd8388607;
    `BUS_SWITCH_SLV_RGN_SIZE_BITS'd24: base_size_mask = ~`BUS_SWITCH_SLV_RGN_BASE_BITS'd16777215;
    `BUS_SWITCH_SLV_RGN_SIZE_BITS'd25: base_size_mask = ~`BUS_SWITCH_SLV_RGN_BASE_BITS'd33554431;
    `BUS_SWITCH_SLV_RGN_SIZE_BITS'd26: base_size_mask = ~`BUS_SWITCH_SLV_RGN_BASE_BITS'd67108863;
    `BUS_SWITCH_SLV_RGN_SIZE_BITS'd27: base_size_mask = ~`BUS_SWITCH_SLV_RGN_BASE_BITS'd134217727;
    `BUS_SWITCH_SLV_RGN_SIZE_BITS'd28: base_size_mask = ~`BUS_SWITCH_SLV_RGN_BASE_BITS'd268435455;
    default: base_size_mask = ~`BUS_SWITCH_SLV_RGN_BASE_BITS'd268435455;
    endcase
end
endfunction

endmodule
