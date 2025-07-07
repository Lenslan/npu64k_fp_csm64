
/// Parameter definition

//`let configure = "`define"
`define BUS_SWITCH_AW              49
`define BUS_SWITCH_IDW             9
`define BUS_SWITCH_SLV_HOLE_RESP_ERR 1
`define BUS_SWITCH_MST_NUM         7
`define BUS_SWITCH_SLV_NUM         4
`define BUS_SWITCH_SRAM_MEM_IDX    3
`define BUS_SWITCH_DDR_MEM_IDX     -1

`define BUS_SWITCH_ADDR_RANGE 39:12


//below for adress base and adress size related defines
//4KB aligned and smallest aperature is 4KB
//TODO

//masters

`define BUS_SWITCH_MST0_PFX      npu_mst0_axi_bs_
`define BUS_SWITCH_MST0_AW       49
`define BUS_SWITCH_MST0_DW       64
`define BUS_SWITCH_MST0_LOCK     1


`define BUS_SWITCH_MST1_PFX      npu_mst1_axi_bs_
`define BUS_SWITCH_MST1_AW       49
`define BUS_SWITCH_MST1_DW       512
`define BUS_SWITCH_MST1_LOCK     1


`define BUS_SWITCH_MST2_PFX      npu_mst2_axi_bs_
`define BUS_SWITCH_MST2_AW       49
`define BUS_SWITCH_MST2_DW       512
`define BUS_SWITCH_MST2_LOCK     1


`define BUS_SWITCH_MST3_PFX      npu_mst3_axi_bs_
`define BUS_SWITCH_MST3_AW       49
`define BUS_SWITCH_MST3_DW       512
`define BUS_SWITCH_MST3_LOCK     1


`define BUS_SWITCH_MST4_PFX      npu_mst4_axi_bs_
`define BUS_SWITCH_MST4_AW       49
`define BUS_SWITCH_MST4_DW       512
`define BUS_SWITCH_MST4_LOCK     1


`define BUS_SWITCH_MST5_PFX      host_axi_bs_
`define BUS_SWITCH_MST5_AW       49
`define BUS_SWITCH_MST5_DW       64
`define BUS_SWITCH_MST5_LOCK     1


`define BUS_SWITCH_MST6_PFX      bri4tb_bs_
`define BUS_SWITCH_MST6_AW       49
`define BUS_SWITCH_MST6_DW       32
`define BUS_SWITCH_MST6_LOCK     0

//slaves

`define BUS_SWITCH_SLV0_PFX                  npu_dmi0_axi_bs_
`define BUS_SWITCH_SLV0_AW                   49
`define BUS_SWITCH_SLV0_DW                   512
`define BUS_SWITCH_SLV0_CONFLICT_FREE        0
`define BUS_SWITCH_SLV0_REGION_WIDTH         0
`define BUS_SWITCH_SLV0_REGION_NUM           1
`define BUS_SWITCH_SLV0_BASE_ADDR             917504 // 0xe0000
`define BUS_SWITCH_SLV0_UP_ADDR               983039 // 0xeffff

`define BUS_SWITCH_SLV0_REG0_BASE_ADDR  917504 // 0xe0000
`define BUS_SWITCH_SLV0_REG0_APER_WIDTH 28



`define BUS_SWITCH_SLV1_PFX                  npu_cfg_axi_bs_
`define BUS_SWITCH_SLV1_AW                   49
`define BUS_SWITCH_SLV1_DW                   32
`define BUS_SWITCH_SLV1_CONFLICT_FREE        0
`define BUS_SWITCH_SLV1_REGION_WIDTH         0
`define BUS_SWITCH_SLV1_REGION_NUM           1
`define BUS_SWITCH_SLV1_BASE_ADDR             983040 // 0xf0000
`define BUS_SWITCH_SLV1_UP_ADDR               983295 // 0xf00ff

`define BUS_SWITCH_SLV1_REG0_BASE_ADDR  983040 // 0xf0000
`define BUS_SWITCH_SLV1_REG0_APER_WIDTH 20



`define BUS_SWITCH_SLV2_PFX                  arcsync_axi_bs_
`define BUS_SWITCH_SLV2_AW                   49
`define BUS_SWITCH_SLV2_DW                   64
`define BUS_SWITCH_SLV2_CONFLICT_FREE        0
`define BUS_SWITCH_SLV2_REGION_WIDTH         0
`define BUS_SWITCH_SLV2_REGION_NUM           1
`define BUS_SWITCH_SLV2_BASE_ADDR             868352 // 0xd4000
`define BUS_SWITCH_SLV2_UP_ADDR               872447 // 0xd4fff

`define BUS_SWITCH_SLV2_REG0_BASE_ADDR  868352 // 0xd4000
`define BUS_SWITCH_SLV2_REG0_APER_WIDTH 24



`define BUS_SWITCH_SLV3_PFX                  mss_mem_bs_
`define BUS_SWITCH_SLV3_AW                   49
`define BUS_SWITCH_SLV3_DW                   128
`define BUS_SWITCH_SLV3_CONFLICT_FREE        0
`define BUS_SWITCH_SLV3_REGION_WIDTH         1
`define BUS_SWITCH_SLV3_REGION_NUM           1
`define BUS_SWITCH_SLV3_BASE_ADDR             0 // 0x0
`define BUS_SWITCH_SLV3_UP_ADDR               1048575 // 0xfffff

`define BUS_SWITCH_SLV3_REG0_BASE_ADDR  0 // 0x0
`define BUS_SWITCH_SLV3_REG0_APER_WIDTH 32



//unused memory space
`define BUS_SWITCH_UNUSED_REGION_NUM      0


//TODO

`define BUS_SWITCH_SLV_RGN_BASE_BITS     28
`define BUS_SWITCH_SLV_RGN_SIZE_BITS     6
`define BUS_SWITCH_SLV_RGN_MATCH_RANGE   39:12
`define BUS_SWITCH_SLV_RGN_BASE_RANGE    27:0
`define BUS_SWITCH_SLV_RGN_SIZE_RANGE    5:0

//--------------------------------------------------------------//
//                         genral master/slave
//--------------------------------------------------------------//
//---------------general slave 32 bits---------------------------

`define MSS_BUS_SWITCH_DW32_SLV_AW                      49
`define MSS_BUS_SWITCH_DW32_SLV_RGON_W                  5
`define MSS_BUS_SWITCH_DW32_SLV_HSEL_W                  1
`define MSS_BUS_SWITCH_DW32_SLV_IDW                     4
`define MSS_BUS_SWITCH_DW32_SLV_I_IBP_ENPACK            0
`define MSS_BUS_SWITCH_DW32_SLV_I_IBP_W2N_MAY_OVF       1
`define MSS_BUS_SWITCH_DW32_SLV_I_BUS_ENDIAN            0
`define MSS_BUS_SWITCH_DW32_SLV_I_BUS_DW                32

`define MSS_BUS_SWITCH_DW32_SLV_I_BUS_OUT_NUM           64 // need to confirm
`define MSS_BUS_SWITCH_DW32_SLV_I_HAS_CLK_EN            0
//TODO
`define MSS_BUS_SWITCH_DW32_SLV_I_BUS_CLK_EN_NAME       mss_bs_in_clk_en
`define MSS_BUS_SWITCH_DW32_SLV_I_IBP_SPLT4IBPW2N       0

`define MSS_BUS_SWITCH_DW32_SLV_I_BUS_TYPE              ibp
`define MSS_BUS_SWITCH_DW32_SLV_I_BUS_PFX               dw32_in_
`define MSS_BUS_SWITCH_DW32_0_SLV_I_BUS_INST_PFX     npu_mst0_axi_bs_
//TODO
`define MSS_BUS_SWITCH_DW32_0_SLV_I_BUS_INST_CLK_EN_NAME       npu_mst0_axi_bs_clk_en
`define MSS_BUS_SWITCH_DW32_1_SLV_I_BUS_INST_PFX     npu_mst1_axi_bs_
//TODO
`define MSS_BUS_SWITCH_DW32_1_SLV_I_BUS_INST_CLK_EN_NAME       npu_mst1_axi_bs_clk_en
`define MSS_BUS_SWITCH_DW32_2_SLV_I_BUS_INST_PFX     npu_mst2_axi_bs_
//TODO
`define MSS_BUS_SWITCH_DW32_2_SLV_I_BUS_INST_CLK_EN_NAME       npu_mst2_axi_bs_clk_en
`define MSS_BUS_SWITCH_DW32_3_SLV_I_BUS_INST_PFX     npu_mst3_axi_bs_
//TODO
`define MSS_BUS_SWITCH_DW32_3_SLV_I_BUS_INST_CLK_EN_NAME       npu_mst3_axi_bs_clk_en
`define MSS_BUS_SWITCH_DW32_4_SLV_I_BUS_INST_PFX     npu_mst4_axi_bs_
//TODO
`define MSS_BUS_SWITCH_DW32_4_SLV_I_BUS_INST_CLK_EN_NAME       npu_mst4_axi_bs_clk_en
`define MSS_BUS_SWITCH_DW32_5_SLV_I_BUS_INST_PFX     host_axi_bs_
//TODO
`define MSS_BUS_SWITCH_DW32_5_SLV_I_BUS_INST_CLK_EN_NAME       host_axi_bs_clk_en
`define MSS_BUS_SWITCH_DW32_6_SLV_I_BUS_INST_PFX     bri4tb_bs_
//TODO
`define MSS_BUS_SWITCH_DW32_6_SLV_I_BUS_INST_CLK_EN_NAME       bri4tb_bs_clk_en
`define MSS_BUS_SWITCH_DW32_SLV_I_BUS_BUF_ENTRIES       0
`define MSS_BUS_SWITCH_DW32_SLV_MID_BUF_CMD_ENTRIES     0
`define MSS_BUS_SWITCH_DW32_SLV_MID_BUF_WD_ENTRIES      0
`define MSS_BUS_SWITCH_DW32_SLV_MID_BUF_RD_ENTRIES      0
`define MSS_BUS_SWITCH_DW32_SLV_MID_BUF_WRSP_ENTRIES    0
`define MSS_BUS_SWITCH_DW32_SLV_ALL_O_BUS_DW            32
`define MSS_BUS_SWITCH_DW32_SLV_O_BUS_NUM               5
`define MSS_BUS_SWITCH_DW32_SLV_ALL_O_NEED_SPLT         0 // need to confirm
`define MSS_BUS_SWITCH_DW32_SLV_O_ALLOW_DIFF_BRANCH     0

`define MSS_BUS_SWITCH_DW32_SLV_O_BUS0_RGON          1
`define MSS_BUS_SWITCH_DW32_SLV_O_BUS0_PFX           dw32_out_0_
`define MSS_BUS_SWITCH_DW32_0_SLV_O_BUS0_INST_PFX     in_0_out_0_
`define MSS_BUS_SWITCH_DW32_1_SLV_O_BUS0_INST_PFX     in_1_out_0_
`define MSS_BUS_SWITCH_DW32_2_SLV_O_BUS0_INST_PFX     in_2_out_0_
`define MSS_BUS_SWITCH_DW32_3_SLV_O_BUS0_INST_PFX     in_3_out_0_
`define MSS_BUS_SWITCH_DW32_4_SLV_O_BUS0_INST_PFX     in_4_out_0_
`define MSS_BUS_SWITCH_DW32_5_SLV_O_BUS0_INST_PFX     in_5_out_0_
`define MSS_BUS_SWITCH_DW32_6_SLV_O_BUS0_INST_PFX     in_6_out_0_

`define MSS_BUS_SWITCH_DW32_SLV_O_BUS0_ENPACK        1
`define MSS_BUS_SWITCH_DW32_SLV_O_BUS0_NEED_REQ      0 // need to confirm
`define MSS_BUS_SWITCH_DW32_SLV_O_BUS1_RGON          2
`define MSS_BUS_SWITCH_DW32_SLV_O_BUS1_PFX           dw32_out_1_
`define MSS_BUS_SWITCH_DW32_0_SLV_O_BUS1_INST_PFX     in_0_out_1_
`define MSS_BUS_SWITCH_DW32_1_SLV_O_BUS1_INST_PFX     in_1_out_1_
`define MSS_BUS_SWITCH_DW32_2_SLV_O_BUS1_INST_PFX     in_2_out_1_
`define MSS_BUS_SWITCH_DW32_3_SLV_O_BUS1_INST_PFX     in_3_out_1_
`define MSS_BUS_SWITCH_DW32_4_SLV_O_BUS1_INST_PFX     in_4_out_1_
`define MSS_BUS_SWITCH_DW32_5_SLV_O_BUS1_INST_PFX     in_5_out_1_
`define MSS_BUS_SWITCH_DW32_6_SLV_O_BUS1_INST_PFX     in_6_out_1_

`define MSS_BUS_SWITCH_DW32_SLV_O_BUS1_ENPACK        1
`define MSS_BUS_SWITCH_DW32_SLV_O_BUS1_NEED_REQ      0 // need to confirm
`define MSS_BUS_SWITCH_DW32_SLV_O_BUS2_RGON          4
`define MSS_BUS_SWITCH_DW32_SLV_O_BUS2_PFX           dw32_out_2_
`define MSS_BUS_SWITCH_DW32_0_SLV_O_BUS2_INST_PFX     in_0_out_2_
`define MSS_BUS_SWITCH_DW32_1_SLV_O_BUS2_INST_PFX     in_1_out_2_
`define MSS_BUS_SWITCH_DW32_2_SLV_O_BUS2_INST_PFX     in_2_out_2_
`define MSS_BUS_SWITCH_DW32_3_SLV_O_BUS2_INST_PFX     in_3_out_2_
`define MSS_BUS_SWITCH_DW32_4_SLV_O_BUS2_INST_PFX     in_4_out_2_
`define MSS_BUS_SWITCH_DW32_5_SLV_O_BUS2_INST_PFX     in_5_out_2_
`define MSS_BUS_SWITCH_DW32_6_SLV_O_BUS2_INST_PFX     in_6_out_2_

`define MSS_BUS_SWITCH_DW32_SLV_O_BUS2_ENPACK        1
`define MSS_BUS_SWITCH_DW32_SLV_O_BUS2_NEED_REQ      0 // need to confirm
`define MSS_BUS_SWITCH_DW32_SLV_O_BUS3_RGON          8
`define MSS_BUS_SWITCH_DW32_SLV_O_BUS3_PFX           dw32_out_3_
`define MSS_BUS_SWITCH_DW32_0_SLV_O_BUS3_INST_PFX     in_0_out_3_
`define MSS_BUS_SWITCH_DW32_1_SLV_O_BUS3_INST_PFX     in_1_out_3_
`define MSS_BUS_SWITCH_DW32_2_SLV_O_BUS3_INST_PFX     in_2_out_3_
`define MSS_BUS_SWITCH_DW32_3_SLV_O_BUS3_INST_PFX     in_3_out_3_
`define MSS_BUS_SWITCH_DW32_4_SLV_O_BUS3_INST_PFX     in_4_out_3_
`define MSS_BUS_SWITCH_DW32_5_SLV_O_BUS3_INST_PFX     in_5_out_3_
`define MSS_BUS_SWITCH_DW32_6_SLV_O_BUS3_INST_PFX     in_6_out_3_

`define MSS_BUS_SWITCH_DW32_SLV_O_BUS3_ENPACK        1
`define MSS_BUS_SWITCH_DW32_SLV_O_BUS3_NEED_REQ      0 // need to confirm
`define MSS_BUS_SWITCH_DW32_SLV_O_BUS4_RGON          16
`define MSS_BUS_SWITCH_DW32_SLV_O_BUS4_PFX           dw32_out_4_
`define MSS_BUS_SWITCH_DW32_0_SLV_O_BUS4_INST_PFX     in_0_out_4_
`define MSS_BUS_SWITCH_DW32_1_SLV_O_BUS4_INST_PFX     in_1_out_4_
`define MSS_BUS_SWITCH_DW32_2_SLV_O_BUS4_INST_PFX     in_2_out_4_
`define MSS_BUS_SWITCH_DW32_3_SLV_O_BUS4_INST_PFX     in_3_out_4_
`define MSS_BUS_SWITCH_DW32_4_SLV_O_BUS4_INST_PFX     in_4_out_4_
`define MSS_BUS_SWITCH_DW32_5_SLV_O_BUS4_INST_PFX     in_5_out_4_
`define MSS_BUS_SWITCH_DW32_6_SLV_O_BUS4_INST_PFX     in_6_out_4_

`define MSS_BUS_SWITCH_DW32_SLV_O_BUS4_ENPACK        1
`define MSS_BUS_SWITCH_DW32_SLV_O_BUS4_NEED_REQ      0 // need to confirm

//---------------slave 64 bits---------------------------------
`define MSS_BUS_SWITCH_DW64_SLV_AW                      49
`define MSS_BUS_SWITCH_DW64_SLV_RGON_W                  5
`define MSS_BUS_SWITCH_DW64_SLV_HSEL_W                  1
`define MSS_BUS_SWITCH_DW64_SLV_IDW                     4
`define MSS_BUS_SWITCH_DW64_SLV_I_IBP_ENPACK            0
`define MSS_BUS_SWITCH_DW64_SLV_I_IBP_W2N_MAY_OVF       1
`define MSS_BUS_SWITCH_DW64_SLV_I_BUS_ENDIAN            0
`define MSS_BUS_SWITCH_DW64_SLV_I_BUS_DW                64

`define MSS_BUS_SWITCH_DW64_SLV_I_BUS_OUT_NUM           64
`define MSS_BUS_SWITCH_DW64_SLV_I_HAS_CLK_EN            0
`define MSS_BUS_SWITCH_DW64_SLV_I_BUS_CLK_EN_NAME       mss_bs_in_clk_en
`define MSS_BUS_SWITCH_DW64_SLV_I_IBP_SPLT4IBPW2N       0

`define MSS_BUS_SWITCH_DW64_SLV_I_BUS_TYPE              ibp
`define MSS_BUS_SWITCH_DW64_SLV_I_BUS_PFX               dw64_in_
`define MSS_BUS_SWITCH_DW64_0_SLV_I_BUS_INST_PFX     npu_mst0_axi_bs_
`define MSS_BUS_SWITCH_DW64_0_SLV_I_BUS_INST_CLK_EN_NAME       npu_mst0_axi_bs_clk_en
`define MSS_BUS_SWITCH_DW64_1_SLV_I_BUS_INST_PFX     npu_mst1_axi_bs_
`define MSS_BUS_SWITCH_DW64_1_SLV_I_BUS_INST_CLK_EN_NAME       npu_mst1_axi_bs_clk_en
`define MSS_BUS_SWITCH_DW64_2_SLV_I_BUS_INST_PFX     npu_mst2_axi_bs_
`define MSS_BUS_SWITCH_DW64_2_SLV_I_BUS_INST_CLK_EN_NAME       npu_mst2_axi_bs_clk_en
`define MSS_BUS_SWITCH_DW64_3_SLV_I_BUS_INST_PFX     npu_mst3_axi_bs_
`define MSS_BUS_SWITCH_DW64_3_SLV_I_BUS_INST_CLK_EN_NAME       npu_mst3_axi_bs_clk_en
`define MSS_BUS_SWITCH_DW64_4_SLV_I_BUS_INST_PFX     npu_mst4_axi_bs_
`define MSS_BUS_SWITCH_DW64_4_SLV_I_BUS_INST_CLK_EN_NAME       npu_mst4_axi_bs_clk_en
`define MSS_BUS_SWITCH_DW64_5_SLV_I_BUS_INST_PFX     host_axi_bs_
`define MSS_BUS_SWITCH_DW64_5_SLV_I_BUS_INST_CLK_EN_NAME       host_axi_bs_clk_en
`define MSS_BUS_SWITCH_DW64_6_SLV_I_BUS_INST_PFX     bri4tb_bs_
`define MSS_BUS_SWITCH_DW64_6_SLV_I_BUS_INST_CLK_EN_NAME       bri4tb_bs_clk_en
`define MSS_BUS_SWITCH_DW64_SLV_I_BUS_BUF_ENTRIES       0

`define MSS_BUS_SWITCH_DW64_SLV_MID_BUF_CMD_ENTRIES     0
`define MSS_BUS_SWITCH_DW64_SLV_MID_BUF_WD_ENTRIES      0
`define MSS_BUS_SWITCH_DW64_SLV_MID_BUF_RD_ENTRIES      0
`define MSS_BUS_SWITCH_DW64_SLV_MID_BUF_WRSP_ENTRIES    0
`define MSS_BUS_SWITCH_DW64_SLV_ALL_O_BUS_DW            64
`define MSS_BUS_SWITCH_DW64_SLV_O_BUS_NUM               5
`define MSS_BUS_SWITCH_DW64_SLV_ALL_O_NEED_SPLT         0
`define MSS_BUS_SWITCH_DW64_SLV_O_ALLOW_DIFF_BRANCH     0

`define MSS_BUS_SWITCH_DW64_SLV_O_BUS0_RGON          1
`define MSS_BUS_SWITCH_DW64_SLV_O_BUS0_PFX           dw64_out_0_
`define MSS_BUS_SWITCH_DW64_0_SLV_O_BUS0_INST_PFX     in_0_out_0_
`define MSS_BUS_SWITCH_DW64_1_SLV_O_BUS0_INST_PFX     in_1_out_0_
`define MSS_BUS_SWITCH_DW64_2_SLV_O_BUS0_INST_PFX     in_2_out_0_
`define MSS_BUS_SWITCH_DW64_3_SLV_O_BUS0_INST_PFX     in_3_out_0_
`define MSS_BUS_SWITCH_DW64_4_SLV_O_BUS0_INST_PFX     in_4_out_0_
`define MSS_BUS_SWITCH_DW64_5_SLV_O_BUS0_INST_PFX     in_5_out_0_
`define MSS_BUS_SWITCH_DW64_6_SLV_O_BUS0_INST_PFX     in_6_out_0_
`define MSS_BUS_SWITCH_DW64_SLV_O_BUS0_ENPACK        1
`define MSS_BUS_SWITCH_DW64_SLV_O_BUS0_NEED_REQ      0
`define MSS_BUS_SWITCH_DW64_SLV_O_BUS1_RGON          2
`define MSS_BUS_SWITCH_DW64_SLV_O_BUS1_PFX           dw64_out_1_
`define MSS_BUS_SWITCH_DW64_0_SLV_O_BUS1_INST_PFX     in_0_out_1_
`define MSS_BUS_SWITCH_DW64_1_SLV_O_BUS1_INST_PFX     in_1_out_1_
`define MSS_BUS_SWITCH_DW64_2_SLV_O_BUS1_INST_PFX     in_2_out_1_
`define MSS_BUS_SWITCH_DW64_3_SLV_O_BUS1_INST_PFX     in_3_out_1_
`define MSS_BUS_SWITCH_DW64_4_SLV_O_BUS1_INST_PFX     in_4_out_1_
`define MSS_BUS_SWITCH_DW64_5_SLV_O_BUS1_INST_PFX     in_5_out_1_
`define MSS_BUS_SWITCH_DW64_6_SLV_O_BUS1_INST_PFX     in_6_out_1_
`define MSS_BUS_SWITCH_DW64_SLV_O_BUS1_ENPACK        1
`define MSS_BUS_SWITCH_DW64_SLV_O_BUS1_NEED_REQ      0
`define MSS_BUS_SWITCH_DW64_SLV_O_BUS2_RGON          4
`define MSS_BUS_SWITCH_DW64_SLV_O_BUS2_PFX           dw64_out_2_
`define MSS_BUS_SWITCH_DW64_0_SLV_O_BUS2_INST_PFX     in_0_out_2_
`define MSS_BUS_SWITCH_DW64_1_SLV_O_BUS2_INST_PFX     in_1_out_2_
`define MSS_BUS_SWITCH_DW64_2_SLV_O_BUS2_INST_PFX     in_2_out_2_
`define MSS_BUS_SWITCH_DW64_3_SLV_O_BUS2_INST_PFX     in_3_out_2_
`define MSS_BUS_SWITCH_DW64_4_SLV_O_BUS2_INST_PFX     in_4_out_2_
`define MSS_BUS_SWITCH_DW64_5_SLV_O_BUS2_INST_PFX     in_5_out_2_
`define MSS_BUS_SWITCH_DW64_6_SLV_O_BUS2_INST_PFX     in_6_out_2_
`define MSS_BUS_SWITCH_DW64_SLV_O_BUS2_ENPACK        1
`define MSS_BUS_SWITCH_DW64_SLV_O_BUS2_NEED_REQ      0
`define MSS_BUS_SWITCH_DW64_SLV_O_BUS3_RGON          8
`define MSS_BUS_SWITCH_DW64_SLV_O_BUS3_PFX           dw64_out_3_
`define MSS_BUS_SWITCH_DW64_0_SLV_O_BUS3_INST_PFX     in_0_out_3_
`define MSS_BUS_SWITCH_DW64_1_SLV_O_BUS3_INST_PFX     in_1_out_3_
`define MSS_BUS_SWITCH_DW64_2_SLV_O_BUS3_INST_PFX     in_2_out_3_
`define MSS_BUS_SWITCH_DW64_3_SLV_O_BUS3_INST_PFX     in_3_out_3_
`define MSS_BUS_SWITCH_DW64_4_SLV_O_BUS3_INST_PFX     in_4_out_3_
`define MSS_BUS_SWITCH_DW64_5_SLV_O_BUS3_INST_PFX     in_5_out_3_
`define MSS_BUS_SWITCH_DW64_6_SLV_O_BUS3_INST_PFX     in_6_out_3_
`define MSS_BUS_SWITCH_DW64_SLV_O_BUS3_ENPACK        1
`define MSS_BUS_SWITCH_DW64_SLV_O_BUS3_NEED_REQ      0
`define MSS_BUS_SWITCH_DW64_SLV_O_BUS4_RGON          16
`define MSS_BUS_SWITCH_DW64_SLV_O_BUS4_PFX           dw64_out_4_
`define MSS_BUS_SWITCH_DW64_0_SLV_O_BUS4_INST_PFX     in_0_out_4_
`define MSS_BUS_SWITCH_DW64_1_SLV_O_BUS4_INST_PFX     in_1_out_4_
`define MSS_BUS_SWITCH_DW64_2_SLV_O_BUS4_INST_PFX     in_2_out_4_
`define MSS_BUS_SWITCH_DW64_3_SLV_O_BUS4_INST_PFX     in_3_out_4_
`define MSS_BUS_SWITCH_DW64_4_SLV_O_BUS4_INST_PFX     in_4_out_4_
`define MSS_BUS_SWITCH_DW64_5_SLV_O_BUS4_INST_PFX     in_5_out_4_
`define MSS_BUS_SWITCH_DW64_6_SLV_O_BUS4_INST_PFX     in_6_out_4_
`define MSS_BUS_SWITCH_DW64_SLV_O_BUS4_ENPACK        1
`define MSS_BUS_SWITCH_DW64_SLV_O_BUS4_NEED_REQ      0


//---------------slave 128 bits---------------------------------
`define MSS_BUS_SWITCH_DW128_SLV_AW                      49
`define MSS_BUS_SWITCH_DW128_SLV_RGON_W                  5
`define MSS_BUS_SWITCH_DW128_SLV_HSEL_W                  1
`define MSS_BUS_SWITCH_DW128_SLV_IDW                     4
`define MSS_BUS_SWITCH_DW128_SLV_I_IBP_ENPACK            0
`define MSS_BUS_SWITCH_DW128_SLV_I_IBP_W2N_MAY_OVF       1
`define MSS_BUS_SWITCH_DW128_SLV_I_BUS_ENDIAN            0
`define MSS_BUS_SWITCH_DW128_SLV_I_BUS_DW                128

`define MSS_BUS_SWITCH_DW128_SLV_I_BUS_OUT_NUM           64
`define MSS_BUS_SWITCH_DW128_SLV_I_HAS_CLK_EN            0
`define MSS_BUS_SWITCH_DW128_SLV_I_BUS_CLK_EN_NAME       mss_bs_in_clk_en
`define MSS_BUS_SWITCH_DW128_SLV_I_IBP_SPLT4IBPW2N       0

`define MSS_BUS_SWITCH_DW128_SLV_I_BUS_TYPE              ibp
`define MSS_BUS_SWITCH_DW128_SLV_I_BUS_PFX               dw128_in_
`define MSS_BUS_SWITCH_DW128_0_SLV_I_BUS_INST_PFX     npu_mst0_axi_bs_
`define MSS_BUS_SWITCH_DW128_0_SLV_I_BUS_INST_CLK_EN_NAME       npu_mst0_axi_bs_clk_en
`define MSS_BUS_SWITCH_DW128_1_SLV_I_BUS_INST_PFX     npu_mst1_axi_bs_
`define MSS_BUS_SWITCH_DW128_1_SLV_I_BUS_INST_CLK_EN_NAME       npu_mst1_axi_bs_clk_en
`define MSS_BUS_SWITCH_DW128_2_SLV_I_BUS_INST_PFX     npu_mst2_axi_bs_
`define MSS_BUS_SWITCH_DW128_2_SLV_I_BUS_INST_CLK_EN_NAME       npu_mst2_axi_bs_clk_en
`define MSS_BUS_SWITCH_DW128_3_SLV_I_BUS_INST_PFX     npu_mst3_axi_bs_
`define MSS_BUS_SWITCH_DW128_3_SLV_I_BUS_INST_CLK_EN_NAME       npu_mst3_axi_bs_clk_en
`define MSS_BUS_SWITCH_DW128_4_SLV_I_BUS_INST_PFX     npu_mst4_axi_bs_
`define MSS_BUS_SWITCH_DW128_4_SLV_I_BUS_INST_CLK_EN_NAME       npu_mst4_axi_bs_clk_en
`define MSS_BUS_SWITCH_DW128_5_SLV_I_BUS_INST_PFX     host_axi_bs_
`define MSS_BUS_SWITCH_DW128_5_SLV_I_BUS_INST_CLK_EN_NAME       host_axi_bs_clk_en
`define MSS_BUS_SWITCH_DW128_6_SLV_I_BUS_INST_PFX     bri4tb_bs_
`define MSS_BUS_SWITCH_DW128_6_SLV_I_BUS_INST_CLK_EN_NAME       bri4tb_bs_clk_en
`define MSS_BUS_SWITCH_DW128_SLV_I_BUS_BUF_ENTRIES       0

`define MSS_BUS_SWITCH_DW128_SLV_MID_BUF_CMD_ENTRIES     0
`define MSS_BUS_SWITCH_DW128_SLV_MID_BUF_WD_ENTRIES      0
`define MSS_BUS_SWITCH_DW128_SLV_MID_BUF_RD_ENTRIES      0
`define MSS_BUS_SWITCH_DW128_SLV_MID_BUF_WRSP_ENTRIES    0
`define MSS_BUS_SWITCH_DW128_SLV_ALL_O_BUS_DW            128
`define MSS_BUS_SWITCH_DW128_SLV_O_BUS_NUM               5
`define MSS_BUS_SWITCH_DW128_SLV_ALL_O_NEED_SPLT         0
`define MSS_BUS_SWITCH_DW128_SLV_O_ALLOW_DIFF_BRANCH     0

`define MSS_BUS_SWITCH_DW128_SLV_O_BUS0_RGON          1
`define MSS_BUS_SWITCH_DW128_SLV_O_BUS0_PFX           dw128_out_0_
`define MSS_BUS_SWITCH_DW128_0_SLV_O_BUS0_INST_PFX   in_0_out_0_
`define MSS_BUS_SWITCH_DW128_1_SLV_O_BUS0_INST_PFX   in_1_out_0_
`define MSS_BUS_SWITCH_DW128_2_SLV_O_BUS0_INST_PFX   in_2_out_0_
`define MSS_BUS_SWITCH_DW128_3_SLV_O_BUS0_INST_PFX   in_3_out_0_
`define MSS_BUS_SWITCH_DW128_4_SLV_O_BUS0_INST_PFX   in_4_out_0_
`define MSS_BUS_SWITCH_DW128_5_SLV_O_BUS0_INST_PFX   in_5_out_0_
`define MSS_BUS_SWITCH_DW128_6_SLV_O_BUS0_INST_PFX   in_6_out_0_
`define MSS_BUS_SWITCH_DW128_SLV_O_BUS0_ENPACK        1
`define MSS_BUS_SWITCH_DW128_SLV_O_BUS0_NEED_REQ      0
`define MSS_BUS_SWITCH_DW128_SLV_O_BUS1_RGON          2
`define MSS_BUS_SWITCH_DW128_SLV_O_BUS1_PFX           dw128_out_1_
`define MSS_BUS_SWITCH_DW128_0_SLV_O_BUS1_INST_PFX   in_0_out_1_
`define MSS_BUS_SWITCH_DW128_1_SLV_O_BUS1_INST_PFX   in_1_out_1_
`define MSS_BUS_SWITCH_DW128_2_SLV_O_BUS1_INST_PFX   in_2_out_1_
`define MSS_BUS_SWITCH_DW128_3_SLV_O_BUS1_INST_PFX   in_3_out_1_
`define MSS_BUS_SWITCH_DW128_4_SLV_O_BUS1_INST_PFX   in_4_out_1_
`define MSS_BUS_SWITCH_DW128_5_SLV_O_BUS1_INST_PFX   in_5_out_1_
`define MSS_BUS_SWITCH_DW128_6_SLV_O_BUS1_INST_PFX   in_6_out_1_
`define MSS_BUS_SWITCH_DW128_SLV_O_BUS1_ENPACK        1
`define MSS_BUS_SWITCH_DW128_SLV_O_BUS1_NEED_REQ      0
`define MSS_BUS_SWITCH_DW128_SLV_O_BUS2_RGON          4
`define MSS_BUS_SWITCH_DW128_SLV_O_BUS2_PFX           dw128_out_2_
`define MSS_BUS_SWITCH_DW128_0_SLV_O_BUS2_INST_PFX   in_0_out_2_
`define MSS_BUS_SWITCH_DW128_1_SLV_O_BUS2_INST_PFX   in_1_out_2_
`define MSS_BUS_SWITCH_DW128_2_SLV_O_BUS2_INST_PFX   in_2_out_2_
`define MSS_BUS_SWITCH_DW128_3_SLV_O_BUS2_INST_PFX   in_3_out_2_
`define MSS_BUS_SWITCH_DW128_4_SLV_O_BUS2_INST_PFX   in_4_out_2_
`define MSS_BUS_SWITCH_DW128_5_SLV_O_BUS2_INST_PFX   in_5_out_2_
`define MSS_BUS_SWITCH_DW128_6_SLV_O_BUS2_INST_PFX   in_6_out_2_
`define MSS_BUS_SWITCH_DW128_SLV_O_BUS2_ENPACK        1
`define MSS_BUS_SWITCH_DW128_SLV_O_BUS2_NEED_REQ      0
`define MSS_BUS_SWITCH_DW128_SLV_O_BUS3_RGON          8
`define MSS_BUS_SWITCH_DW128_SLV_O_BUS3_PFX           dw128_out_3_
`define MSS_BUS_SWITCH_DW128_0_SLV_O_BUS3_INST_PFX   in_0_out_3_
`define MSS_BUS_SWITCH_DW128_1_SLV_O_BUS3_INST_PFX   in_1_out_3_
`define MSS_BUS_SWITCH_DW128_2_SLV_O_BUS3_INST_PFX   in_2_out_3_
`define MSS_BUS_SWITCH_DW128_3_SLV_O_BUS3_INST_PFX   in_3_out_3_
`define MSS_BUS_SWITCH_DW128_4_SLV_O_BUS3_INST_PFX   in_4_out_3_
`define MSS_BUS_SWITCH_DW128_5_SLV_O_BUS3_INST_PFX   in_5_out_3_
`define MSS_BUS_SWITCH_DW128_6_SLV_O_BUS3_INST_PFX   in_6_out_3_
`define MSS_BUS_SWITCH_DW128_SLV_O_BUS3_ENPACK        1
`define MSS_BUS_SWITCH_DW128_SLV_O_BUS3_NEED_REQ      0
`define MSS_BUS_SWITCH_DW128_SLV_O_BUS4_RGON          16
`define MSS_BUS_SWITCH_DW128_SLV_O_BUS4_PFX           dw128_out_4_
`define MSS_BUS_SWITCH_DW128_0_SLV_O_BUS4_INST_PFX   in_0_out_4_
`define MSS_BUS_SWITCH_DW128_1_SLV_O_BUS4_INST_PFX   in_1_out_4_
`define MSS_BUS_SWITCH_DW128_2_SLV_O_BUS4_INST_PFX   in_2_out_4_
`define MSS_BUS_SWITCH_DW128_3_SLV_O_BUS4_INST_PFX   in_3_out_4_
`define MSS_BUS_SWITCH_DW128_4_SLV_O_BUS4_INST_PFX   in_4_out_4_
`define MSS_BUS_SWITCH_DW128_5_SLV_O_BUS4_INST_PFX   in_5_out_4_
`define MSS_BUS_SWITCH_DW128_6_SLV_O_BUS4_INST_PFX   in_6_out_4_
`define MSS_BUS_SWITCH_DW128_SLV_O_BUS4_ENPACK        1
`define MSS_BUS_SWITCH_DW128_SLV_O_BUS4_NEED_REQ      0


//---------------slave 256 bits---------------------------------
`define MSS_BUS_SWITCH_DW256_SLV_AW                      49
`define MSS_BUS_SWITCH_DW256_SLV_RGON_W                  5
`define MSS_BUS_SWITCH_DW256_SLV_HSEL_W                  1
`define MSS_BUS_SWITCH_DW256_SLV_IDW                     4
`define MSS_BUS_SWITCH_DW256_SLV_I_IBP_ENPACK            0
`define MSS_BUS_SWITCH_DW256_SLV_I_IBP_W2N_MAY_OVF       1
`define MSS_BUS_SWITCH_DW256_SLV_I_BUS_ENDIAN            0
`define MSS_BUS_SWITCH_DW256_SLV_I_BUS_DW                256

`define MSS_BUS_SWITCH_DW256_SLV_I_BUS_OUT_NUM           64
`define MSS_BUS_SWITCH_DW256_SLV_I_HAS_CLK_EN            0
`define MSS_BUS_SWITCH_DW256_SLV_I_BUS_CLK_EN_NAME       mss_bs_in_clk_en
`define MSS_BUS_SWITCH_DW256_SLV_I_IBP_SPLT4IBPW2N       0

`define MSS_BUS_SWITCH_DW256_SLV_I_BUS_TYPE              ibp
`define MSS_BUS_SWITCH_DW256_SLV_I_BUS_PFX               dw256_in_
`define MSS_BUS_SWITCH_DW256_0_SLV_I_BUS_INST_PFX     npu_mst0_axi_bs_
`define MSS_BUS_SWITCH_DW256_0_SLV_I_BUS_INST_CLK_EN_NAME       npu_mst0_axi_bs_clk_en
`define MSS_BUS_SWITCH_DW256_1_SLV_I_BUS_INST_PFX     npu_mst1_axi_bs_
`define MSS_BUS_SWITCH_DW256_1_SLV_I_BUS_INST_CLK_EN_NAME       npu_mst1_axi_bs_clk_en
`define MSS_BUS_SWITCH_DW256_2_SLV_I_BUS_INST_PFX     npu_mst2_axi_bs_
`define MSS_BUS_SWITCH_DW256_2_SLV_I_BUS_INST_CLK_EN_NAME       npu_mst2_axi_bs_clk_en
`define MSS_BUS_SWITCH_DW256_3_SLV_I_BUS_INST_PFX     npu_mst3_axi_bs_
`define MSS_BUS_SWITCH_DW256_3_SLV_I_BUS_INST_CLK_EN_NAME       npu_mst3_axi_bs_clk_en
`define MSS_BUS_SWITCH_DW256_4_SLV_I_BUS_INST_PFX     npu_mst4_axi_bs_
`define MSS_BUS_SWITCH_DW256_4_SLV_I_BUS_INST_CLK_EN_NAME       npu_mst4_axi_bs_clk_en
`define MSS_BUS_SWITCH_DW256_5_SLV_I_BUS_INST_PFX     host_axi_bs_
`define MSS_BUS_SWITCH_DW256_5_SLV_I_BUS_INST_CLK_EN_NAME       host_axi_bs_clk_en
`define MSS_BUS_SWITCH_DW256_6_SLV_I_BUS_INST_PFX     bri4tb_bs_
`define MSS_BUS_SWITCH_DW256_6_SLV_I_BUS_INST_CLK_EN_NAME       bri4tb_bs_clk_en
`define MSS_BUS_SWITCH_DW256_SLV_I_BUS_BUF_ENTRIES       0

`define MSS_BUS_SWITCH_DW256_SLV_MID_BUF_CMD_ENTRIES     0
`define MSS_BUS_SWITCH_DW256_SLV_MID_BUF_WD_ENTRIES      0
`define MSS_BUS_SWITCH_DW256_SLV_MID_BUF_RD_ENTRIES      0
`define MSS_BUS_SWITCH_DW256_SLV_MID_BUF_WRSP_ENTRIES    0
`define MSS_BUS_SWITCH_DW256_SLV_ALL_O_BUS_DW            256
`define MSS_BUS_SWITCH_DW256_SLV_O_BUS_NUM               5
`define MSS_BUS_SWITCH_DW256_SLV_ALL_O_NEED_SPLT         0
`define MSS_BUS_SWITCH_DW256_SLV_O_ALLOW_DIFF_BRANCH     0

`define MSS_BUS_SWITCH_DW256_SLV_O_BUS0_RGON          1
`define MSS_BUS_SWITCH_DW256_SLV_O_BUS0_PFX           dw256_out_0_
`define MSS_BUS_SWITCH_DW256_0_SLV_O_BUS0_INST_PFX   in_0_out_0_
`define MSS_BUS_SWITCH_DW256_1_SLV_O_BUS0_INST_PFX   in_1_out_0_
`define MSS_BUS_SWITCH_DW256_2_SLV_O_BUS0_INST_PFX   in_2_out_0_
`define MSS_BUS_SWITCH_DW256_3_SLV_O_BUS0_INST_PFX   in_3_out_0_
`define MSS_BUS_SWITCH_DW256_4_SLV_O_BUS0_INST_PFX   in_4_out_0_
`define MSS_BUS_SWITCH_DW256_5_SLV_O_BUS0_INST_PFX   in_5_out_0_
`define MSS_BUS_SWITCH_DW256_6_SLV_O_BUS0_INST_PFX   in_6_out_0_
`define MSS_BUS_SWITCH_DW256_SLV_O_BUS0_ENPACK        1
`define MSS_BUS_SWITCH_DW256_SLV_O_BUS0_NEED_REQ      0
`define MSS_BUS_SWITCH_DW256_SLV_O_BUS1_RGON          2
`define MSS_BUS_SWITCH_DW256_SLV_O_BUS1_PFX           dw256_out_1_
`define MSS_BUS_SWITCH_DW256_0_SLV_O_BUS1_INST_PFX   in_0_out_1_
`define MSS_BUS_SWITCH_DW256_1_SLV_O_BUS1_INST_PFX   in_1_out_1_
`define MSS_BUS_SWITCH_DW256_2_SLV_O_BUS1_INST_PFX   in_2_out_1_
`define MSS_BUS_SWITCH_DW256_3_SLV_O_BUS1_INST_PFX   in_3_out_1_
`define MSS_BUS_SWITCH_DW256_4_SLV_O_BUS1_INST_PFX   in_4_out_1_
`define MSS_BUS_SWITCH_DW256_5_SLV_O_BUS1_INST_PFX   in_5_out_1_
`define MSS_BUS_SWITCH_DW256_6_SLV_O_BUS1_INST_PFX   in_6_out_1_
`define MSS_BUS_SWITCH_DW256_SLV_O_BUS1_ENPACK        1
`define MSS_BUS_SWITCH_DW256_SLV_O_BUS1_NEED_REQ      0
`define MSS_BUS_SWITCH_DW256_SLV_O_BUS2_RGON          4
`define MSS_BUS_SWITCH_DW256_SLV_O_BUS2_PFX           dw256_out_2_
`define MSS_BUS_SWITCH_DW256_0_SLV_O_BUS2_INST_PFX   in_0_out_2_
`define MSS_BUS_SWITCH_DW256_1_SLV_O_BUS2_INST_PFX   in_1_out_2_
`define MSS_BUS_SWITCH_DW256_2_SLV_O_BUS2_INST_PFX   in_2_out_2_
`define MSS_BUS_SWITCH_DW256_3_SLV_O_BUS2_INST_PFX   in_3_out_2_
`define MSS_BUS_SWITCH_DW256_4_SLV_O_BUS2_INST_PFX   in_4_out_2_
`define MSS_BUS_SWITCH_DW256_5_SLV_O_BUS2_INST_PFX   in_5_out_2_
`define MSS_BUS_SWITCH_DW256_6_SLV_O_BUS2_INST_PFX   in_6_out_2_
`define MSS_BUS_SWITCH_DW256_SLV_O_BUS2_ENPACK        1
`define MSS_BUS_SWITCH_DW256_SLV_O_BUS2_NEED_REQ      0
`define MSS_BUS_SWITCH_DW256_SLV_O_BUS3_RGON          8
`define MSS_BUS_SWITCH_DW256_SLV_O_BUS3_PFX           dw256_out_3_
`define MSS_BUS_SWITCH_DW256_0_SLV_O_BUS3_INST_PFX   in_0_out_3_
`define MSS_BUS_SWITCH_DW256_1_SLV_O_BUS3_INST_PFX   in_1_out_3_
`define MSS_BUS_SWITCH_DW256_2_SLV_O_BUS3_INST_PFX   in_2_out_3_
`define MSS_BUS_SWITCH_DW256_3_SLV_O_BUS3_INST_PFX   in_3_out_3_
`define MSS_BUS_SWITCH_DW256_4_SLV_O_BUS3_INST_PFX   in_4_out_3_
`define MSS_BUS_SWITCH_DW256_5_SLV_O_BUS3_INST_PFX   in_5_out_3_
`define MSS_BUS_SWITCH_DW256_6_SLV_O_BUS3_INST_PFX   in_6_out_3_
`define MSS_BUS_SWITCH_DW256_SLV_O_BUS3_ENPACK        1
`define MSS_BUS_SWITCH_DW256_SLV_O_BUS3_NEED_REQ      0
`define MSS_BUS_SWITCH_DW256_SLV_O_BUS4_RGON          16
`define MSS_BUS_SWITCH_DW256_SLV_O_BUS4_PFX           dw256_out_4_
`define MSS_BUS_SWITCH_DW256_0_SLV_O_BUS4_INST_PFX   in_0_out_4_
`define MSS_BUS_SWITCH_DW256_1_SLV_O_BUS4_INST_PFX   in_1_out_4_
`define MSS_BUS_SWITCH_DW256_2_SLV_O_BUS4_INST_PFX   in_2_out_4_
`define MSS_BUS_SWITCH_DW256_3_SLV_O_BUS4_INST_PFX   in_3_out_4_
`define MSS_BUS_SWITCH_DW256_4_SLV_O_BUS4_INST_PFX   in_4_out_4_
`define MSS_BUS_SWITCH_DW256_5_SLV_O_BUS4_INST_PFX   in_5_out_4_
`define MSS_BUS_SWITCH_DW256_6_SLV_O_BUS4_INST_PFX   in_6_out_4_
`define MSS_BUS_SWITCH_DW256_SLV_O_BUS4_ENPACK        1
`define MSS_BUS_SWITCH_DW256_SLV_O_BUS4_NEED_REQ      0


//---------------slave 512 bits---------------------------------
`define MSS_BUS_SWITCH_DW512_SLV_AW                      49
`define MSS_BUS_SWITCH_DW512_SLV_RGON_W                  5
`define MSS_BUS_SWITCH_DW512_SLV_HSEL_W                  1
`define MSS_BUS_SWITCH_DW512_SLV_IDW                     4
`define MSS_BUS_SWITCH_DW512_SLV_I_IBP_ENPACK            0
`define MSS_BUS_SWITCH_DW512_SLV_I_IBP_W2N_MAY_OVF       1
`define MSS_BUS_SWITCH_DW512_SLV_I_BUS_ENDIAN            0
`define MSS_BUS_SWITCH_DW512_SLV_I_BUS_DW                512

`define MSS_BUS_SWITCH_DW512_SLV_I_BUS_OUT_NUM           64
`define MSS_BUS_SWITCH_DW512_SLV_I_HAS_CLK_EN            0
`define MSS_BUS_SWITCH_DW512_SLV_I_BUS_CLK_EN_NAME       mss_bs_in_clk_en
`define MSS_BUS_SWITCH_DW512_SLV_I_IBP_SPLT4IBPW2N       0

`define MSS_BUS_SWITCH_DW512_SLV_I_BUS_TYPE              ibp
`define MSS_BUS_SWITCH_DW512_SLV_I_BUS_PFX               dw512_in_
`define MSS_BUS_SWITCH_DW512_0_SLV_I_BUS_INST_PFX     npu_mst0_axi_bs_
`define MSS_BUS_SWITCH_DW512_0_SLV_I_BUS_INST_CLK_EN_NAME       npu_mst0_axi_bs_clk_en
`define MSS_BUS_SWITCH_DW512_1_SLV_I_BUS_INST_PFX     npu_mst1_axi_bs_
`define MSS_BUS_SWITCH_DW512_1_SLV_I_BUS_INST_CLK_EN_NAME       npu_mst1_axi_bs_clk_en
`define MSS_BUS_SWITCH_DW512_2_SLV_I_BUS_INST_PFX     npu_mst2_axi_bs_
`define MSS_BUS_SWITCH_DW512_2_SLV_I_BUS_INST_CLK_EN_NAME       npu_mst2_axi_bs_clk_en
`define MSS_BUS_SWITCH_DW512_3_SLV_I_BUS_INST_PFX     npu_mst3_axi_bs_
`define MSS_BUS_SWITCH_DW512_3_SLV_I_BUS_INST_CLK_EN_NAME       npu_mst3_axi_bs_clk_en
`define MSS_BUS_SWITCH_DW512_4_SLV_I_BUS_INST_PFX     npu_mst4_axi_bs_
`define MSS_BUS_SWITCH_DW512_4_SLV_I_BUS_INST_CLK_EN_NAME       npu_mst4_axi_bs_clk_en
`define MSS_BUS_SWITCH_DW512_5_SLV_I_BUS_INST_PFX     host_axi_bs_
`define MSS_BUS_SWITCH_DW512_5_SLV_I_BUS_INST_CLK_EN_NAME       host_axi_bs_clk_en
`define MSS_BUS_SWITCH_DW512_6_SLV_I_BUS_INST_PFX     bri4tb_bs_
`define MSS_BUS_SWITCH_DW512_6_SLV_I_BUS_INST_CLK_EN_NAME       bri4tb_bs_clk_en
`define MSS_BUS_SWITCH_DW512_SLV_I_BUS_BUF_ENTRIES       0

`define MSS_BUS_SWITCH_DW512_SLV_MID_BUF_CMD_ENTRIES     0
`define MSS_BUS_SWITCH_DW512_SLV_MID_BUF_WD_ENTRIES      0
`define MSS_BUS_SWITCH_DW512_SLV_MID_BUF_RD_ENTRIES      0
`define MSS_BUS_SWITCH_DW512_SLV_MID_BUF_WRSP_ENTRIES    0
`define MSS_BUS_SWITCH_DW512_SLV_ALL_O_BUS_DW            512
`define MSS_BUS_SWITCH_DW512_SLV_O_BUS_NUM               5
`define MSS_BUS_SWITCH_DW512_SLV_ALL_O_NEED_SPLT         0
`define MSS_BUS_SWITCH_DW512_SLV_O_ALLOW_DIFF_BRANCH     0

`define MSS_BUS_SWITCH_DW512_SLV_O_BUS0_RGON          1
`define MSS_BUS_SWITCH_DW512_SLV_O_BUS0_PFX           dw512_out_0_
`define MSS_BUS_SWITCH_DW512_0_SLV_O_BUS0_INST_PFX   in_0_out_0_
`define MSS_BUS_SWITCH_DW512_1_SLV_O_BUS0_INST_PFX   in_1_out_0_
`define MSS_BUS_SWITCH_DW512_2_SLV_O_BUS0_INST_PFX   in_2_out_0_
`define MSS_BUS_SWITCH_DW512_3_SLV_O_BUS0_INST_PFX   in_3_out_0_
`define MSS_BUS_SWITCH_DW512_4_SLV_O_BUS0_INST_PFX   in_4_out_0_
`define MSS_BUS_SWITCH_DW512_5_SLV_O_BUS0_INST_PFX   in_5_out_0_
`define MSS_BUS_SWITCH_DW512_6_SLV_O_BUS0_INST_PFX   in_6_out_0_
`define MSS_BUS_SWITCH_DW512_SLV_O_BUS0_ENPACK        1
`define MSS_BUS_SWITCH_DW512_SLV_O_BUS0_NEED_REQ      0
`define MSS_BUS_SWITCH_DW512_SLV_O_BUS1_RGON          2
`define MSS_BUS_SWITCH_DW512_SLV_O_BUS1_PFX           dw512_out_1_
`define MSS_BUS_SWITCH_DW512_0_SLV_O_BUS1_INST_PFX   in_0_out_1_
`define MSS_BUS_SWITCH_DW512_1_SLV_O_BUS1_INST_PFX   in_1_out_1_
`define MSS_BUS_SWITCH_DW512_2_SLV_O_BUS1_INST_PFX   in_2_out_1_
`define MSS_BUS_SWITCH_DW512_3_SLV_O_BUS1_INST_PFX   in_3_out_1_
`define MSS_BUS_SWITCH_DW512_4_SLV_O_BUS1_INST_PFX   in_4_out_1_
`define MSS_BUS_SWITCH_DW512_5_SLV_O_BUS1_INST_PFX   in_5_out_1_
`define MSS_BUS_SWITCH_DW512_6_SLV_O_BUS1_INST_PFX   in_6_out_1_
`define MSS_BUS_SWITCH_DW512_SLV_O_BUS1_ENPACK        1
`define MSS_BUS_SWITCH_DW512_SLV_O_BUS1_NEED_REQ      0
`define MSS_BUS_SWITCH_DW512_SLV_O_BUS2_RGON          4
`define MSS_BUS_SWITCH_DW512_SLV_O_BUS2_PFX           dw512_out_2_
`define MSS_BUS_SWITCH_DW512_0_SLV_O_BUS2_INST_PFX   in_0_out_2_
`define MSS_BUS_SWITCH_DW512_1_SLV_O_BUS2_INST_PFX   in_1_out_2_
`define MSS_BUS_SWITCH_DW512_2_SLV_O_BUS2_INST_PFX   in_2_out_2_
`define MSS_BUS_SWITCH_DW512_3_SLV_O_BUS2_INST_PFX   in_3_out_2_
`define MSS_BUS_SWITCH_DW512_4_SLV_O_BUS2_INST_PFX   in_4_out_2_
`define MSS_BUS_SWITCH_DW512_5_SLV_O_BUS2_INST_PFX   in_5_out_2_
`define MSS_BUS_SWITCH_DW512_6_SLV_O_BUS2_INST_PFX   in_6_out_2_
`define MSS_BUS_SWITCH_DW512_SLV_O_BUS2_ENPACK        1
`define MSS_BUS_SWITCH_DW512_SLV_O_BUS2_NEED_REQ      0
`define MSS_BUS_SWITCH_DW512_SLV_O_BUS3_RGON          8
`define MSS_BUS_SWITCH_DW512_SLV_O_BUS3_PFX           dw512_out_3_
`define MSS_BUS_SWITCH_DW512_0_SLV_O_BUS3_INST_PFX   in_0_out_3_
`define MSS_BUS_SWITCH_DW512_1_SLV_O_BUS3_INST_PFX   in_1_out_3_
`define MSS_BUS_SWITCH_DW512_2_SLV_O_BUS3_INST_PFX   in_2_out_3_
`define MSS_BUS_SWITCH_DW512_3_SLV_O_BUS3_INST_PFX   in_3_out_3_
`define MSS_BUS_SWITCH_DW512_4_SLV_O_BUS3_INST_PFX   in_4_out_3_
`define MSS_BUS_SWITCH_DW512_5_SLV_O_BUS3_INST_PFX   in_5_out_3_
`define MSS_BUS_SWITCH_DW512_6_SLV_O_BUS3_INST_PFX   in_6_out_3_
`define MSS_BUS_SWITCH_DW512_SLV_O_BUS3_ENPACK        1
`define MSS_BUS_SWITCH_DW512_SLV_O_BUS3_NEED_REQ      0
`define MSS_BUS_SWITCH_DW512_SLV_O_BUS4_RGON          16
`define MSS_BUS_SWITCH_DW512_SLV_O_BUS4_PFX           dw512_out_4_
`define MSS_BUS_SWITCH_DW512_0_SLV_O_BUS4_INST_PFX   in_0_out_4_
`define MSS_BUS_SWITCH_DW512_1_SLV_O_BUS4_INST_PFX   in_1_out_4_
`define MSS_BUS_SWITCH_DW512_2_SLV_O_BUS4_INST_PFX   in_2_out_4_
`define MSS_BUS_SWITCH_DW512_3_SLV_O_BUS4_INST_PFX   in_3_out_4_
`define MSS_BUS_SWITCH_DW512_4_SLV_O_BUS4_INST_PFX   in_4_out_4_
`define MSS_BUS_SWITCH_DW512_5_SLV_O_BUS4_INST_PFX   in_5_out_4_
`define MSS_BUS_SWITCH_DW512_6_SLV_O_BUS4_INST_PFX   in_6_out_4_
`define MSS_BUS_SWITCH_DW512_SLV_O_BUS4_ENPACK        1
`define MSS_BUS_SWITCH_DW512_SLV_O_BUS4_NEED_REQ      0


//----------------------master ibp 32 bits-----------------------------------------

`define MSS_BUS_SWITCH_IBP_DW32_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_DW32_MST_IDW                4
`define MSS_BUS_SWITCH_IBP_DW32_MST_INUM               7

`define MSS_BUS_SWITCH_IBP_DW32_MST_I0_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW32_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_DW32_MST_I0_PFX             ibp_dw32_in_0_
`define MSS_BUS_SWITCH_IBP_DW32_0_MST_I0_INST_PFX    in_0_out_0_
`define MSS_BUS_SWITCH_IBP_DW32_0_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_1_MST_I0_INST_PFX    in_0_out_1_
`define MSS_BUS_SWITCH_IBP_DW32_1_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_2_MST_I0_INST_PFX    in_0_out_2_
`define MSS_BUS_SWITCH_IBP_DW32_2_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_3_MST_I0_INST_PFX    in_0_out_3_
`define MSS_BUS_SWITCH_IBP_DW32_3_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_4_MST_I0_INST_PFX    in_0_out_4_
`define MSS_BUS_SWITCH_IBP_DW32_4_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_MST_I0_DW              64
`define MSS_BUS_SWITCH_IBP_DW32_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW32_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW32_MST_I0_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW32_MST_I1_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW32_MST_I1_UNIQ_ID         1
`define MSS_BUS_SWITCH_IBP_DW32_MST_I1_PFX             ibp_dw32_in_1_
`define MSS_BUS_SWITCH_IBP_DW32_0_MST_I1_INST_PFX    in_1_out_0_
`define MSS_BUS_SWITCH_IBP_DW32_0_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_1_MST_I1_INST_PFX    in_1_out_1_
`define MSS_BUS_SWITCH_IBP_DW32_1_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_2_MST_I1_INST_PFX    in_1_out_2_
`define MSS_BUS_SWITCH_IBP_DW32_2_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_3_MST_I1_INST_PFX    in_1_out_3_
`define MSS_BUS_SWITCH_IBP_DW32_3_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_4_MST_I1_INST_PFX    in_1_out_4_
`define MSS_BUS_SWITCH_IBP_DW32_4_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_MST_I1_DW              512
`define MSS_BUS_SWITCH_IBP_DW32_MST_I1_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW32_MST_I1_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW32_MST_I1_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW32_MST_I2_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW32_MST_I2_UNIQ_ID         2
`define MSS_BUS_SWITCH_IBP_DW32_MST_I2_PFX             ibp_dw32_in_2_
`define MSS_BUS_SWITCH_IBP_DW32_0_MST_I2_INST_PFX    in_2_out_0_
`define MSS_BUS_SWITCH_IBP_DW32_0_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_1_MST_I2_INST_PFX    in_2_out_1_
`define MSS_BUS_SWITCH_IBP_DW32_1_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_2_MST_I2_INST_PFX    in_2_out_2_
`define MSS_BUS_SWITCH_IBP_DW32_2_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_3_MST_I2_INST_PFX    in_2_out_3_
`define MSS_BUS_SWITCH_IBP_DW32_3_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_4_MST_I2_INST_PFX    in_2_out_4_
`define MSS_BUS_SWITCH_IBP_DW32_4_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_MST_I2_DW              512
`define MSS_BUS_SWITCH_IBP_DW32_MST_I2_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW32_MST_I2_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW32_MST_I2_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW32_MST_I3_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW32_MST_I3_UNIQ_ID         3
`define MSS_BUS_SWITCH_IBP_DW32_MST_I3_PFX             ibp_dw32_in_3_
`define MSS_BUS_SWITCH_IBP_DW32_0_MST_I3_INST_PFX    in_3_out_0_
`define MSS_BUS_SWITCH_IBP_DW32_0_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_1_MST_I3_INST_PFX    in_3_out_1_
`define MSS_BUS_SWITCH_IBP_DW32_1_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_2_MST_I3_INST_PFX    in_3_out_2_
`define MSS_BUS_SWITCH_IBP_DW32_2_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_3_MST_I3_INST_PFX    in_3_out_3_
`define MSS_BUS_SWITCH_IBP_DW32_3_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_4_MST_I3_INST_PFX    in_3_out_4_
`define MSS_BUS_SWITCH_IBP_DW32_4_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_MST_I3_DW              512
`define MSS_BUS_SWITCH_IBP_DW32_MST_I3_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW32_MST_I3_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW32_MST_I3_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW32_MST_I4_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW32_MST_I4_UNIQ_ID         4
`define MSS_BUS_SWITCH_IBP_DW32_MST_I4_PFX             ibp_dw32_in_4_
`define MSS_BUS_SWITCH_IBP_DW32_0_MST_I4_INST_PFX    in_4_out_0_
`define MSS_BUS_SWITCH_IBP_DW32_0_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_1_MST_I4_INST_PFX    in_4_out_1_
`define MSS_BUS_SWITCH_IBP_DW32_1_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_2_MST_I4_INST_PFX    in_4_out_2_
`define MSS_BUS_SWITCH_IBP_DW32_2_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_3_MST_I4_INST_PFX    in_4_out_3_
`define MSS_BUS_SWITCH_IBP_DW32_3_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_4_MST_I4_INST_PFX    in_4_out_4_
`define MSS_BUS_SWITCH_IBP_DW32_4_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_MST_I4_DW              512
`define MSS_BUS_SWITCH_IBP_DW32_MST_I4_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW32_MST_I4_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW32_MST_I4_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW32_MST_I5_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW32_MST_I5_UNIQ_ID         5
`define MSS_BUS_SWITCH_IBP_DW32_MST_I5_PFX             ibp_dw32_in_5_
`define MSS_BUS_SWITCH_IBP_DW32_0_MST_I5_INST_PFX    in_5_out_0_
`define MSS_BUS_SWITCH_IBP_DW32_0_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_1_MST_I5_INST_PFX    in_5_out_1_
`define MSS_BUS_SWITCH_IBP_DW32_1_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_2_MST_I5_INST_PFX    in_5_out_2_
`define MSS_BUS_SWITCH_IBP_DW32_2_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_3_MST_I5_INST_PFX    in_5_out_3_
`define MSS_BUS_SWITCH_IBP_DW32_3_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_4_MST_I5_INST_PFX    in_5_out_4_
`define MSS_BUS_SWITCH_IBP_DW32_4_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_MST_I5_DW              64
`define MSS_BUS_SWITCH_IBP_DW32_MST_I5_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW32_MST_I5_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW32_MST_I5_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW32_MST_I6_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW32_MST_I6_UNIQ_ID         6
`define MSS_BUS_SWITCH_IBP_DW32_MST_I6_PFX             ibp_dw32_in_6_
`define MSS_BUS_SWITCH_IBP_DW32_0_MST_I6_INST_PFX    in_6_out_0_
`define MSS_BUS_SWITCH_IBP_DW32_0_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_1_MST_I6_INST_PFX    in_6_out_1_
`define MSS_BUS_SWITCH_IBP_DW32_1_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_2_MST_I6_INST_PFX    in_6_out_2_
`define MSS_BUS_SWITCH_IBP_DW32_2_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_3_MST_I6_INST_PFX    in_6_out_3_
`define MSS_BUS_SWITCH_IBP_DW32_3_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_4_MST_I6_INST_PFX    in_6_out_4_
`define MSS_BUS_SWITCH_IBP_DW32_4_MST_O_BUS_INST_CLK_EN_NAME  `mst_inst_pfx::clk_en
`define MSS_BUS_SWITCH_IBP_DW32_MST_I6_DW              32
`define MSS_BUS_SWITCH_IBP_DW32_MST_I6_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW32_MST_I6_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW32_MST_I6_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_DW32_0_MST_O_BUS_INST_PFX    npu_dmi0_axi_bs_
`define MSS_BUS_SWITCH_IBP_DW32_1_MST_O_BUS_INST_PFX    npu_cfg_axi_bs_
`define MSS_BUS_SWITCH_IBP_DW32_2_MST_O_BUS_INST_PFX    arcsync_axi_bs_
`define MSS_BUS_SWITCH_IBP_DW32_3_MST_O_BUS_INST_PFX    mss_mem_bs_

`define MSS_BUS_SWITCH_IBP_DW32_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_DW32_MST_O_BUS_DW           32
`define MSS_BUS_SWITCH_IBP_DW32_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_DW32_MST_O_BUS_PFX          ibp_dw32_out_
`define MSS_BUS_SWITCH_IBP_DW32_MST_O_ENPACK            0

`define MSS_BUS_SWITCH_IBP_DW32_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_DW32_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_DW32_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_DW32_MST_O_BUS_SPLT_IBP     0


//---------------------master ibp 64 bits------------------------------------------
`define MSS_BUS_SWITCH_IBP_DW64_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_DW64_MST_IDW                 4
`define MSS_BUS_SWITCH_IBP_DW64_MST_INUM               7

`define MSS_BUS_SWITCH_IBP_DW64_MST_I0_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW64_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_DW64_MST_I0_PFX             ibp_dw64_in_0_
`define MSS_BUS_SWITCH_IBP_DW64_0_MST_I0_INST_PFX     in_0_out_0_
`define MSS_BUS_SWITCH_IBP_DW64_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW64_1_MST_I0_INST_PFX     in_0_out_1_
`define MSS_BUS_SWITCH_IBP_DW64_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW64_2_MST_I0_INST_PFX     in_0_out_2_
`define MSS_BUS_SWITCH_IBP_DW64_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW64_3_MST_I0_INST_PFX     in_0_out_3_
`define MSS_BUS_SWITCH_IBP_DW64_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW64_MST_I0_DW              64
`define MSS_BUS_SWITCH_IBP_DW64_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW64_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW64_MST_I0_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW64_MST_I1_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW64_MST_I1_UNIQ_ID         1
`define MSS_BUS_SWITCH_IBP_DW64_MST_I1_PFX             ibp_dw64_in_1_
`define MSS_BUS_SWITCH_IBP_DW64_0_MST_I1_INST_PFX     in_1_out_0_
`define MSS_BUS_SWITCH_IBP_DW64_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW64_1_MST_I1_INST_PFX     in_1_out_1_
`define MSS_BUS_SWITCH_IBP_DW64_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW64_2_MST_I1_INST_PFX     in_1_out_2_
`define MSS_BUS_SWITCH_IBP_DW64_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW64_3_MST_I1_INST_PFX     in_1_out_3_
`define MSS_BUS_SWITCH_IBP_DW64_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW64_MST_I1_DW              512
`define MSS_BUS_SWITCH_IBP_DW64_MST_I1_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW64_MST_I1_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW64_MST_I1_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW64_MST_I2_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW64_MST_I2_UNIQ_ID         2
`define MSS_BUS_SWITCH_IBP_DW64_MST_I2_PFX             ibp_dw64_in_2_
`define MSS_BUS_SWITCH_IBP_DW64_0_MST_I2_INST_PFX     in_2_out_0_
`define MSS_BUS_SWITCH_IBP_DW64_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW64_1_MST_I2_INST_PFX     in_2_out_1_
`define MSS_BUS_SWITCH_IBP_DW64_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW64_2_MST_I2_INST_PFX     in_2_out_2_
`define MSS_BUS_SWITCH_IBP_DW64_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW64_3_MST_I2_INST_PFX     in_2_out_3_
`define MSS_BUS_SWITCH_IBP_DW64_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW64_MST_I2_DW              512
`define MSS_BUS_SWITCH_IBP_DW64_MST_I2_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW64_MST_I2_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW64_MST_I2_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW64_MST_I3_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW64_MST_I3_UNIQ_ID         3
`define MSS_BUS_SWITCH_IBP_DW64_MST_I3_PFX             ibp_dw64_in_3_
`define MSS_BUS_SWITCH_IBP_DW64_0_MST_I3_INST_PFX     in_3_out_0_
`define MSS_BUS_SWITCH_IBP_DW64_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW64_1_MST_I3_INST_PFX     in_3_out_1_
`define MSS_BUS_SWITCH_IBP_DW64_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW64_2_MST_I3_INST_PFX     in_3_out_2_
`define MSS_BUS_SWITCH_IBP_DW64_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW64_3_MST_I3_INST_PFX     in_3_out_3_
`define MSS_BUS_SWITCH_IBP_DW64_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW64_MST_I3_DW              512
`define MSS_BUS_SWITCH_IBP_DW64_MST_I3_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW64_MST_I3_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW64_MST_I3_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW64_MST_I4_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW64_MST_I4_UNIQ_ID         4
`define MSS_BUS_SWITCH_IBP_DW64_MST_I4_PFX             ibp_dw64_in_4_
`define MSS_BUS_SWITCH_IBP_DW64_0_MST_I4_INST_PFX     in_4_out_0_
`define MSS_BUS_SWITCH_IBP_DW64_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW64_1_MST_I4_INST_PFX     in_4_out_1_
`define MSS_BUS_SWITCH_IBP_DW64_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW64_2_MST_I4_INST_PFX     in_4_out_2_
`define MSS_BUS_SWITCH_IBP_DW64_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW64_3_MST_I4_INST_PFX     in_4_out_3_
`define MSS_BUS_SWITCH_IBP_DW64_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW64_MST_I4_DW              512
`define MSS_BUS_SWITCH_IBP_DW64_MST_I4_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW64_MST_I4_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW64_MST_I4_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW64_MST_I5_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW64_MST_I5_UNIQ_ID         5
`define MSS_BUS_SWITCH_IBP_DW64_MST_I5_PFX             ibp_dw64_in_5_
`define MSS_BUS_SWITCH_IBP_DW64_0_MST_I5_INST_PFX     in_5_out_0_
`define MSS_BUS_SWITCH_IBP_DW64_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW64_1_MST_I5_INST_PFX     in_5_out_1_
`define MSS_BUS_SWITCH_IBP_DW64_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW64_2_MST_I5_INST_PFX     in_5_out_2_
`define MSS_BUS_SWITCH_IBP_DW64_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW64_3_MST_I5_INST_PFX     in_5_out_3_
`define MSS_BUS_SWITCH_IBP_DW64_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW64_MST_I5_DW              64
`define MSS_BUS_SWITCH_IBP_DW64_MST_I5_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW64_MST_I5_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW64_MST_I5_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW64_MST_I6_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW64_MST_I6_UNIQ_ID         6
`define MSS_BUS_SWITCH_IBP_DW64_MST_I6_PFX             ibp_dw64_in_6_
`define MSS_BUS_SWITCH_IBP_DW64_0_MST_I6_INST_PFX     in_6_out_0_
`define MSS_BUS_SWITCH_IBP_DW64_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW64_1_MST_I6_INST_PFX     in_6_out_1_
`define MSS_BUS_SWITCH_IBP_DW64_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW64_2_MST_I6_INST_PFX     in_6_out_2_
`define MSS_BUS_SWITCH_IBP_DW64_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW64_3_MST_I6_INST_PFX     in_6_out_3_
`define MSS_BUS_SWITCH_IBP_DW64_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW64_MST_I6_DW              32
`define MSS_BUS_SWITCH_IBP_DW64_MST_I6_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW64_MST_I6_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW64_MST_I6_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_DW64_0_MST_O_BUS_INST_PFX    npu_dmi0_axi_bs_
`define MSS_BUS_SWITCH_IBP_DW64_1_MST_O_BUS_INST_PFX    npu_cfg_axi_bs_
`define MSS_BUS_SWITCH_IBP_DW64_2_MST_O_BUS_INST_PFX    arcsync_axi_bs_
`define MSS_BUS_SWITCH_IBP_DW64_3_MST_O_BUS_INST_PFX    mss_mem_bs_

`define MSS_BUS_SWITCH_IBP_DW64_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_DW64_MST_O_BUS_DW           64
`define MSS_BUS_SWITCH_IBP_DW64_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_DW64_MST_O_BUS_PFX          ibp_dw64_out_
`define MSS_BUS_SWITCH_IBP_DW64_MST_O_ENPACK            0

`define MSS_BUS_SWITCH_IBP_DW64_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_DW64_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_DW64_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_DW64_MST_O_BUS_SPLT_IBP     0

//---------------------master ibp 128 bits------------------------------------------
`define MSS_BUS_SWITCH_IBP_DW128_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_DW128_MST_IDW                 4
`define MSS_BUS_SWITCH_IBP_DW128_MST_INUM               7

`define MSS_BUS_SWITCH_IBP_DW128_MST_I0_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW128_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_DW128_MST_I0_PFX             ibp_dw128_in_0_
`define MSS_BUS_SWITCH_IBP_DW128_0_MST_I0_INST_PFX     in_0_out_0_
`define MSS_BUS_SWITCH_IBP_DW128_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW128_1_MST_I0_INST_PFX     in_0_out_1_
`define MSS_BUS_SWITCH_IBP_DW128_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW128_2_MST_I0_INST_PFX     in_0_out_2_
`define MSS_BUS_SWITCH_IBP_DW128_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW128_3_MST_I0_INST_PFX     in_0_out_3_
`define MSS_BUS_SWITCH_IBP_DW128_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW128_MST_I0_DW              64
`define MSS_BUS_SWITCH_IBP_DW128_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW128_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW128_MST_I0_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW128_MST_I1_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW128_MST_I1_UNIQ_ID         1
`define MSS_BUS_SWITCH_IBP_DW128_MST_I1_PFX             ibp_dw128_in_1_
`define MSS_BUS_SWITCH_IBP_DW128_0_MST_I1_INST_PFX     in_1_out_0_
`define MSS_BUS_SWITCH_IBP_DW128_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW128_1_MST_I1_INST_PFX     in_1_out_1_
`define MSS_BUS_SWITCH_IBP_DW128_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW128_2_MST_I1_INST_PFX     in_1_out_2_
`define MSS_BUS_SWITCH_IBP_DW128_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW128_3_MST_I1_INST_PFX     in_1_out_3_
`define MSS_BUS_SWITCH_IBP_DW128_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW128_MST_I1_DW              512
`define MSS_BUS_SWITCH_IBP_DW128_MST_I1_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW128_MST_I1_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW128_MST_I1_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW128_MST_I2_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW128_MST_I2_UNIQ_ID         2
`define MSS_BUS_SWITCH_IBP_DW128_MST_I2_PFX             ibp_dw128_in_2_
`define MSS_BUS_SWITCH_IBP_DW128_0_MST_I2_INST_PFX     in_2_out_0_
`define MSS_BUS_SWITCH_IBP_DW128_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW128_1_MST_I2_INST_PFX     in_2_out_1_
`define MSS_BUS_SWITCH_IBP_DW128_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW128_2_MST_I2_INST_PFX     in_2_out_2_
`define MSS_BUS_SWITCH_IBP_DW128_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW128_3_MST_I2_INST_PFX     in_2_out_3_
`define MSS_BUS_SWITCH_IBP_DW128_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW128_MST_I2_DW              512
`define MSS_BUS_SWITCH_IBP_DW128_MST_I2_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW128_MST_I2_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW128_MST_I2_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW128_MST_I3_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW128_MST_I3_UNIQ_ID         3
`define MSS_BUS_SWITCH_IBP_DW128_MST_I3_PFX             ibp_dw128_in_3_
`define MSS_BUS_SWITCH_IBP_DW128_0_MST_I3_INST_PFX     in_3_out_0_
`define MSS_BUS_SWITCH_IBP_DW128_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW128_1_MST_I3_INST_PFX     in_3_out_1_
`define MSS_BUS_SWITCH_IBP_DW128_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW128_2_MST_I3_INST_PFX     in_3_out_2_
`define MSS_BUS_SWITCH_IBP_DW128_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW128_3_MST_I3_INST_PFX     in_3_out_3_
`define MSS_BUS_SWITCH_IBP_DW128_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW128_MST_I3_DW              512
`define MSS_BUS_SWITCH_IBP_DW128_MST_I3_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW128_MST_I3_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW128_MST_I3_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW128_MST_I4_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW128_MST_I4_UNIQ_ID         4
`define MSS_BUS_SWITCH_IBP_DW128_MST_I4_PFX             ibp_dw128_in_4_
`define MSS_BUS_SWITCH_IBP_DW128_0_MST_I4_INST_PFX     in_4_out_0_
`define MSS_BUS_SWITCH_IBP_DW128_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW128_1_MST_I4_INST_PFX     in_4_out_1_
`define MSS_BUS_SWITCH_IBP_DW128_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW128_2_MST_I4_INST_PFX     in_4_out_2_
`define MSS_BUS_SWITCH_IBP_DW128_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW128_3_MST_I4_INST_PFX     in_4_out_3_
`define MSS_BUS_SWITCH_IBP_DW128_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW128_MST_I4_DW              512
`define MSS_BUS_SWITCH_IBP_DW128_MST_I4_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW128_MST_I4_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW128_MST_I4_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW128_MST_I5_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW128_MST_I5_UNIQ_ID         5
`define MSS_BUS_SWITCH_IBP_DW128_MST_I5_PFX             ibp_dw128_in_5_
`define MSS_BUS_SWITCH_IBP_DW128_0_MST_I5_INST_PFX     in_5_out_0_
`define MSS_BUS_SWITCH_IBP_DW128_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW128_1_MST_I5_INST_PFX     in_5_out_1_
`define MSS_BUS_SWITCH_IBP_DW128_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW128_2_MST_I5_INST_PFX     in_5_out_2_
`define MSS_BUS_SWITCH_IBP_DW128_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW128_3_MST_I5_INST_PFX     in_5_out_3_
`define MSS_BUS_SWITCH_IBP_DW128_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW128_MST_I5_DW              64
`define MSS_BUS_SWITCH_IBP_DW128_MST_I5_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW128_MST_I5_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW128_MST_I5_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW128_MST_I6_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW128_MST_I6_UNIQ_ID         6
`define MSS_BUS_SWITCH_IBP_DW128_MST_I6_PFX             ibp_dw128_in_6_
`define MSS_BUS_SWITCH_IBP_DW128_0_MST_I6_INST_PFX     in_6_out_0_
`define MSS_BUS_SWITCH_IBP_DW128_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW128_1_MST_I6_INST_PFX     in_6_out_1_
`define MSS_BUS_SWITCH_IBP_DW128_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW128_2_MST_I6_INST_PFX     in_6_out_2_
`define MSS_BUS_SWITCH_IBP_DW128_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW128_3_MST_I6_INST_PFX     in_6_out_3_
`define MSS_BUS_SWITCH_IBP_DW128_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW128_MST_I6_DW              32
`define MSS_BUS_SWITCH_IBP_DW128_MST_I6_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW128_MST_I6_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW128_MST_I6_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_DW128_0_MST_O_BUS_INST_PFX    npu_dmi0_axi_bs_
`define MSS_BUS_SWITCH_IBP_DW128_1_MST_O_BUS_INST_PFX    npu_cfg_axi_bs_
`define MSS_BUS_SWITCH_IBP_DW128_2_MST_O_BUS_INST_PFX    arcsync_axi_bs_
`define MSS_BUS_SWITCH_IBP_DW128_3_MST_O_BUS_INST_PFX    mss_mem_bs_

`define MSS_BUS_SWITCH_IBP_DW128_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_DW128_MST_O_BUS_DW           128
`define MSS_BUS_SWITCH_IBP_DW128_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_DW128_MST_O_BUS_PFX          ibp_dw128_out_
`define MSS_BUS_SWITCH_IBP_DW128_MST_O_ENPACK           0

`define MSS_BUS_SWITCH_IBP_DW128_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_DW128_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_DW128_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_DW128_MST_O_BUS_SPLT_IBP     0


//---------------------master ibp 256 bits------------------------------------------
`define MSS_BUS_SWITCH_IBP_DW256_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_DW256_MST_IDW                 4
`define MSS_BUS_SWITCH_IBP_DW256_MST_INUM               7

`define MSS_BUS_SWITCH_IBP_DW256_MST_I0_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW256_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_DW256_MST_I0_PFX             ibp_dw256_in_0_
`define MSS_BUS_SWITCH_IBP_DW256_0_MST_I0_INST_PFX     in_0_out_0_
`define MSS_BUS_SWITCH_IBP_DW256_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_1_MST_I0_INST_PFX     in_0_out_1_
`define MSS_BUS_SWITCH_IBP_DW256_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_2_MST_I0_INST_PFX     in_0_out_2_
`define MSS_BUS_SWITCH_IBP_DW256_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_3_MST_I0_INST_PFX     in_0_out_3_
`define MSS_BUS_SWITCH_IBP_DW256_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_MST_I0_DW              64
`define MSS_BUS_SWITCH_IBP_DW256_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I0_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I1_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW256_MST_I1_UNIQ_ID         1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I1_PFX             ibp_dw256_in_1_
`define MSS_BUS_SWITCH_IBP_DW256_0_MST_I1_INST_PFX     in_1_out_0_
`define MSS_BUS_SWITCH_IBP_DW256_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_1_MST_I1_INST_PFX     in_1_out_1_
`define MSS_BUS_SWITCH_IBP_DW256_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_2_MST_I1_INST_PFX     in_1_out_2_
`define MSS_BUS_SWITCH_IBP_DW256_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_3_MST_I1_INST_PFX     in_1_out_3_
`define MSS_BUS_SWITCH_IBP_DW256_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_MST_I1_DW              512
`define MSS_BUS_SWITCH_IBP_DW256_MST_I1_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I1_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I1_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I2_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW256_MST_I2_UNIQ_ID         2
`define MSS_BUS_SWITCH_IBP_DW256_MST_I2_PFX             ibp_dw256_in_2_
`define MSS_BUS_SWITCH_IBP_DW256_0_MST_I2_INST_PFX     in_2_out_0_
`define MSS_BUS_SWITCH_IBP_DW256_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_1_MST_I2_INST_PFX     in_2_out_1_
`define MSS_BUS_SWITCH_IBP_DW256_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_2_MST_I2_INST_PFX     in_2_out_2_
`define MSS_BUS_SWITCH_IBP_DW256_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_3_MST_I2_INST_PFX     in_2_out_3_
`define MSS_BUS_SWITCH_IBP_DW256_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_MST_I2_DW              512
`define MSS_BUS_SWITCH_IBP_DW256_MST_I2_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I2_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I2_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I3_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW256_MST_I3_UNIQ_ID         3
`define MSS_BUS_SWITCH_IBP_DW256_MST_I3_PFX             ibp_dw256_in_3_
`define MSS_BUS_SWITCH_IBP_DW256_0_MST_I3_INST_PFX     in_3_out_0_
`define MSS_BUS_SWITCH_IBP_DW256_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_1_MST_I3_INST_PFX     in_3_out_1_
`define MSS_BUS_SWITCH_IBP_DW256_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_2_MST_I3_INST_PFX     in_3_out_2_
`define MSS_BUS_SWITCH_IBP_DW256_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_3_MST_I3_INST_PFX     in_3_out_3_
`define MSS_BUS_SWITCH_IBP_DW256_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_MST_I3_DW              512
`define MSS_BUS_SWITCH_IBP_DW256_MST_I3_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I3_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I3_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I4_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW256_MST_I4_UNIQ_ID         4
`define MSS_BUS_SWITCH_IBP_DW256_MST_I4_PFX             ibp_dw256_in_4_
`define MSS_BUS_SWITCH_IBP_DW256_0_MST_I4_INST_PFX     in_4_out_0_
`define MSS_BUS_SWITCH_IBP_DW256_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_1_MST_I4_INST_PFX     in_4_out_1_
`define MSS_BUS_SWITCH_IBP_DW256_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_2_MST_I4_INST_PFX     in_4_out_2_
`define MSS_BUS_SWITCH_IBP_DW256_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_3_MST_I4_INST_PFX     in_4_out_3_
`define MSS_BUS_SWITCH_IBP_DW256_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_MST_I4_DW              512
`define MSS_BUS_SWITCH_IBP_DW256_MST_I4_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I4_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I4_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I5_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW256_MST_I5_UNIQ_ID         5
`define MSS_BUS_SWITCH_IBP_DW256_MST_I5_PFX             ibp_dw256_in_5_
`define MSS_BUS_SWITCH_IBP_DW256_0_MST_I5_INST_PFX     in_5_out_0_
`define MSS_BUS_SWITCH_IBP_DW256_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_1_MST_I5_INST_PFX     in_5_out_1_
`define MSS_BUS_SWITCH_IBP_DW256_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_2_MST_I5_INST_PFX     in_5_out_2_
`define MSS_BUS_SWITCH_IBP_DW256_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_3_MST_I5_INST_PFX     in_5_out_3_
`define MSS_BUS_SWITCH_IBP_DW256_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_MST_I5_DW              64
`define MSS_BUS_SWITCH_IBP_DW256_MST_I5_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I5_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I5_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I6_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW256_MST_I6_UNIQ_ID         6
`define MSS_BUS_SWITCH_IBP_DW256_MST_I6_PFX             ibp_dw256_in_6_
`define MSS_BUS_SWITCH_IBP_DW256_0_MST_I6_INST_PFX     in_6_out_0_
`define MSS_BUS_SWITCH_IBP_DW256_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_1_MST_I6_INST_PFX     in_6_out_1_
`define MSS_BUS_SWITCH_IBP_DW256_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_2_MST_I6_INST_PFX     in_6_out_2_
`define MSS_BUS_SWITCH_IBP_DW256_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_3_MST_I6_INST_PFX     in_6_out_3_
`define MSS_BUS_SWITCH_IBP_DW256_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_MST_I6_DW              32
`define MSS_BUS_SWITCH_IBP_DW256_MST_I6_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I6_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I6_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_DW256_0_MST_O_BUS_INST_PFX    npu_dmi0_axi_bs_
`define MSS_BUS_SWITCH_IBP_DW256_1_MST_O_BUS_INST_PFX    npu_cfg_axi_bs_
`define MSS_BUS_SWITCH_IBP_DW256_2_MST_O_BUS_INST_PFX    arcsync_axi_bs_
`define MSS_BUS_SWITCH_IBP_DW256_3_MST_O_BUS_INST_PFX    mss_mem_bs_

`define MSS_BUS_SWITCH_IBP_DW256_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_DW256_MST_O_BUS_DW           256
`define MSS_BUS_SWITCH_IBP_DW256_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_DW256_MST_O_BUS_PFX          ibp_dw256_out_
`define MSS_BUS_SWITCH_IBP_DW256_MST_O_ENPACK           0

`define MSS_BUS_SWITCH_IBP_DW256_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_DW256_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_DW256_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_MST_O_BUS_SPLT_IBP     0


//---------------------master ibp 256 bits------------------------------------------
`define MSS_BUS_SWITCH_IBP_DW256_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_DW256_MST_IDW                 4
`define MSS_BUS_SWITCH_IBP_DW256_MST_INUM               7

`define MSS_BUS_SWITCH_IBP_DW256_MST_I0_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW256_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_DW256_MST_I0_PFX             ibp_dw256_in_0_
`define MSS_BUS_SWITCH_IBP_DW256_0_MST_I0_INST_PFX     in_0_out_0_
`define MSS_BUS_SWITCH_IBP_DW256_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_1_MST_I0_INST_PFX     in_0_out_1_
`define MSS_BUS_SWITCH_IBP_DW256_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_2_MST_I0_INST_PFX     in_0_out_2_
`define MSS_BUS_SWITCH_IBP_DW256_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_3_MST_I0_INST_PFX     in_0_out_3_
`define MSS_BUS_SWITCH_IBP_DW256_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_MST_I0_DW              64
`define MSS_BUS_SWITCH_IBP_DW256_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I0_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I1_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW256_MST_I1_UNIQ_ID         1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I1_PFX             ibp_dw256_in_1_
`define MSS_BUS_SWITCH_IBP_DW256_0_MST_I1_INST_PFX     in_1_out_0_
`define MSS_BUS_SWITCH_IBP_DW256_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_1_MST_I1_INST_PFX     in_1_out_1_
`define MSS_BUS_SWITCH_IBP_DW256_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_2_MST_I1_INST_PFX     in_1_out_2_
`define MSS_BUS_SWITCH_IBP_DW256_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_3_MST_I1_INST_PFX     in_1_out_3_
`define MSS_BUS_SWITCH_IBP_DW256_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_MST_I1_DW              512
`define MSS_BUS_SWITCH_IBP_DW256_MST_I1_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I1_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I1_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I2_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW256_MST_I2_UNIQ_ID         2
`define MSS_BUS_SWITCH_IBP_DW256_MST_I2_PFX             ibp_dw256_in_2_
`define MSS_BUS_SWITCH_IBP_DW256_0_MST_I2_INST_PFX     in_2_out_0_
`define MSS_BUS_SWITCH_IBP_DW256_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_1_MST_I2_INST_PFX     in_2_out_1_
`define MSS_BUS_SWITCH_IBP_DW256_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_2_MST_I2_INST_PFX     in_2_out_2_
`define MSS_BUS_SWITCH_IBP_DW256_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_3_MST_I2_INST_PFX     in_2_out_3_
`define MSS_BUS_SWITCH_IBP_DW256_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_MST_I2_DW              512
`define MSS_BUS_SWITCH_IBP_DW256_MST_I2_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I2_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I2_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I3_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW256_MST_I3_UNIQ_ID         3
`define MSS_BUS_SWITCH_IBP_DW256_MST_I3_PFX             ibp_dw256_in_3_
`define MSS_BUS_SWITCH_IBP_DW256_0_MST_I3_INST_PFX     in_3_out_0_
`define MSS_BUS_SWITCH_IBP_DW256_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_1_MST_I3_INST_PFX     in_3_out_1_
`define MSS_BUS_SWITCH_IBP_DW256_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_2_MST_I3_INST_PFX     in_3_out_2_
`define MSS_BUS_SWITCH_IBP_DW256_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_3_MST_I3_INST_PFX     in_3_out_3_
`define MSS_BUS_SWITCH_IBP_DW256_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_MST_I3_DW              512
`define MSS_BUS_SWITCH_IBP_DW256_MST_I3_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I3_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I3_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I4_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW256_MST_I4_UNIQ_ID         4
`define MSS_BUS_SWITCH_IBP_DW256_MST_I4_PFX             ibp_dw256_in_4_
`define MSS_BUS_SWITCH_IBP_DW256_0_MST_I4_INST_PFX     in_4_out_0_
`define MSS_BUS_SWITCH_IBP_DW256_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_1_MST_I4_INST_PFX     in_4_out_1_
`define MSS_BUS_SWITCH_IBP_DW256_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_2_MST_I4_INST_PFX     in_4_out_2_
`define MSS_BUS_SWITCH_IBP_DW256_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_3_MST_I4_INST_PFX     in_4_out_3_
`define MSS_BUS_SWITCH_IBP_DW256_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_MST_I4_DW              512
`define MSS_BUS_SWITCH_IBP_DW256_MST_I4_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I4_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I4_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I5_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW256_MST_I5_UNIQ_ID         5
`define MSS_BUS_SWITCH_IBP_DW256_MST_I5_PFX             ibp_dw256_in_5_
`define MSS_BUS_SWITCH_IBP_DW256_0_MST_I5_INST_PFX     in_5_out_0_
`define MSS_BUS_SWITCH_IBP_DW256_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_1_MST_I5_INST_PFX     in_5_out_1_
`define MSS_BUS_SWITCH_IBP_DW256_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_2_MST_I5_INST_PFX     in_5_out_2_
`define MSS_BUS_SWITCH_IBP_DW256_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_3_MST_I5_INST_PFX     in_5_out_3_
`define MSS_BUS_SWITCH_IBP_DW256_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_MST_I5_DW              64
`define MSS_BUS_SWITCH_IBP_DW256_MST_I5_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I5_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I5_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I6_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW256_MST_I6_UNIQ_ID         6
`define MSS_BUS_SWITCH_IBP_DW256_MST_I6_PFX             ibp_dw256_in_6_
`define MSS_BUS_SWITCH_IBP_DW256_0_MST_I6_INST_PFX     in_6_out_0_
`define MSS_BUS_SWITCH_IBP_DW256_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_1_MST_I6_INST_PFX     in_6_out_1_
`define MSS_BUS_SWITCH_IBP_DW256_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_2_MST_I6_INST_PFX     in_6_out_2_
`define MSS_BUS_SWITCH_IBP_DW256_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_3_MST_I6_INST_PFX     in_6_out_3_
`define MSS_BUS_SWITCH_IBP_DW256_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_MST_I6_DW              32
`define MSS_BUS_SWITCH_IBP_DW256_MST_I6_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I6_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW256_MST_I6_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_DW256_0_MST_O_BUS_INST_PFX    npu_dmi0_axi_bs_
`define MSS_BUS_SWITCH_IBP_DW256_1_MST_O_BUS_INST_PFX    npu_cfg_axi_bs_
`define MSS_BUS_SWITCH_IBP_DW256_2_MST_O_BUS_INST_PFX    arcsync_axi_bs_
`define MSS_BUS_SWITCH_IBP_DW256_3_MST_O_BUS_INST_PFX    mss_mem_bs_

`define MSS_BUS_SWITCH_IBP_DW256_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_DW256_MST_O_BUS_DW           256
`define MSS_BUS_SWITCH_IBP_DW256_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_DW256_MST_O_BUS_PFX          ibp_dw256_out_
`define MSS_BUS_SWITCH_IBP_DW256_MST_O_ENPACK           0

`define MSS_BUS_SWITCH_IBP_DW256_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_DW256_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_DW256_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_DW256_MST_O_BUS_SPLT_IBP     0


//---------------------master ibp 512 bits------------------------------------------
`define MSS_BUS_SWITCH_IBP_DW512_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_DW512_MST_IDW                 4
`define MSS_BUS_SWITCH_IBP_DW512_MST_INUM               7

`define MSS_BUS_SWITCH_IBP_DW512_MST_I0_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW512_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_DW512_MST_I0_PFX             ibp_dw512_in_0_
`define MSS_BUS_SWITCH_IBP_DW512_0_MST_I0_INST_PFX     in_0_out_0_
`define MSS_BUS_SWITCH_IBP_DW512_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW512_1_MST_I0_INST_PFX     in_0_out_1_
`define MSS_BUS_SWITCH_IBP_DW512_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW512_2_MST_I0_INST_PFX     in_0_out_2_
`define MSS_BUS_SWITCH_IBP_DW512_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW512_3_MST_I0_INST_PFX     in_0_out_3_
`define MSS_BUS_SWITCH_IBP_DW512_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW512_MST_I0_DW              64
`define MSS_BUS_SWITCH_IBP_DW512_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW512_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW512_MST_I0_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW512_MST_I1_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW512_MST_I1_UNIQ_ID         1
`define MSS_BUS_SWITCH_IBP_DW512_MST_I1_PFX             ibp_dw512_in_1_
`define MSS_BUS_SWITCH_IBP_DW512_0_MST_I1_INST_PFX     in_1_out_0_
`define MSS_BUS_SWITCH_IBP_DW512_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW512_1_MST_I1_INST_PFX     in_1_out_1_
`define MSS_BUS_SWITCH_IBP_DW512_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW512_2_MST_I1_INST_PFX     in_1_out_2_
`define MSS_BUS_SWITCH_IBP_DW512_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW512_3_MST_I1_INST_PFX     in_1_out_3_
`define MSS_BUS_SWITCH_IBP_DW512_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW512_MST_I1_DW              512
`define MSS_BUS_SWITCH_IBP_DW512_MST_I1_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW512_MST_I1_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW512_MST_I1_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW512_MST_I2_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW512_MST_I2_UNIQ_ID         2
`define MSS_BUS_SWITCH_IBP_DW512_MST_I2_PFX             ibp_dw512_in_2_
`define MSS_BUS_SWITCH_IBP_DW512_0_MST_I2_INST_PFX     in_2_out_0_
`define MSS_BUS_SWITCH_IBP_DW512_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW512_1_MST_I2_INST_PFX     in_2_out_1_
`define MSS_BUS_SWITCH_IBP_DW512_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW512_2_MST_I2_INST_PFX     in_2_out_2_
`define MSS_BUS_SWITCH_IBP_DW512_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW512_3_MST_I2_INST_PFX     in_2_out_3_
`define MSS_BUS_SWITCH_IBP_DW512_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW512_MST_I2_DW              512
`define MSS_BUS_SWITCH_IBP_DW512_MST_I2_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW512_MST_I2_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW512_MST_I2_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW512_MST_I3_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW512_MST_I3_UNIQ_ID         3
`define MSS_BUS_SWITCH_IBP_DW512_MST_I3_PFX             ibp_dw512_in_3_
`define MSS_BUS_SWITCH_IBP_DW512_0_MST_I3_INST_PFX     in_3_out_0_
`define MSS_BUS_SWITCH_IBP_DW512_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW512_1_MST_I3_INST_PFX     in_3_out_1_
`define MSS_BUS_SWITCH_IBP_DW512_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW512_2_MST_I3_INST_PFX     in_3_out_2_
`define MSS_BUS_SWITCH_IBP_DW512_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW512_3_MST_I3_INST_PFX     in_3_out_3_
`define MSS_BUS_SWITCH_IBP_DW512_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW512_MST_I3_DW              512
`define MSS_BUS_SWITCH_IBP_DW512_MST_I3_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW512_MST_I3_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW512_MST_I3_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW512_MST_I4_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW512_MST_I4_UNIQ_ID         4
`define MSS_BUS_SWITCH_IBP_DW512_MST_I4_PFX             ibp_dw512_in_4_
`define MSS_BUS_SWITCH_IBP_DW512_0_MST_I4_INST_PFX     in_4_out_0_
`define MSS_BUS_SWITCH_IBP_DW512_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW512_1_MST_I4_INST_PFX     in_4_out_1_
`define MSS_BUS_SWITCH_IBP_DW512_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW512_2_MST_I4_INST_PFX     in_4_out_2_
`define MSS_BUS_SWITCH_IBP_DW512_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW512_3_MST_I4_INST_PFX     in_4_out_3_
`define MSS_BUS_SWITCH_IBP_DW512_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW512_MST_I4_DW              512
`define MSS_BUS_SWITCH_IBP_DW512_MST_I4_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW512_MST_I4_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW512_MST_I4_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW512_MST_I5_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW512_MST_I5_UNIQ_ID         5
`define MSS_BUS_SWITCH_IBP_DW512_MST_I5_PFX             ibp_dw512_in_5_
`define MSS_BUS_SWITCH_IBP_DW512_0_MST_I5_INST_PFX     in_5_out_0_
`define MSS_BUS_SWITCH_IBP_DW512_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW512_1_MST_I5_INST_PFX     in_5_out_1_
`define MSS_BUS_SWITCH_IBP_DW512_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW512_2_MST_I5_INST_PFX     in_5_out_2_
`define MSS_BUS_SWITCH_IBP_DW512_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW512_3_MST_I5_INST_PFX     in_5_out_3_
`define MSS_BUS_SWITCH_IBP_DW512_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW512_MST_I5_DW              64
`define MSS_BUS_SWITCH_IBP_DW512_MST_I5_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW512_MST_I5_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW512_MST_I5_W2N_MAY_OVF     1
`define MSS_BUS_SWITCH_IBP_DW512_MST_I6_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_DW512_MST_I6_UNIQ_ID         6
`define MSS_BUS_SWITCH_IBP_DW512_MST_I6_PFX             ibp_dw512_in_6_
`define MSS_BUS_SWITCH_IBP_DW512_0_MST_I6_INST_PFX     in_6_out_0_
`define MSS_BUS_SWITCH_IBP_DW512_0_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW512_1_MST_I6_INST_PFX     in_6_out_1_
`define MSS_BUS_SWITCH_IBP_DW512_1_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW512_2_MST_I6_INST_PFX     in_6_out_2_
`define MSS_BUS_SWITCH_IBP_DW512_2_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW512_3_MST_I6_INST_PFX     in_6_out_3_
`define MSS_BUS_SWITCH_IBP_DW512_3_MST_O_BUS_INST_CLK_EN_NAME  mss_mem_bs_clk_en
`define MSS_BUS_SWITCH_IBP_DW512_MST_I6_DW              32
`define MSS_BUS_SWITCH_IBP_DW512_MST_I6_ENPACK          1
`define MSS_BUS_SWITCH_IBP_DW512_MST_I6_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_DW512_MST_I6_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_DW512_0_MST_O_BUS_INST_PFX    npu_dmi0_axi_bs_
`define MSS_BUS_SWITCH_IBP_DW512_1_MST_O_BUS_INST_PFX    npu_cfg_axi_bs_
`define MSS_BUS_SWITCH_IBP_DW512_2_MST_O_BUS_INST_PFX    arcsync_axi_bs_
`define MSS_BUS_SWITCH_IBP_DW512_3_MST_O_BUS_INST_PFX    mss_mem_bs_

`define MSS_BUS_SWITCH_IBP_DW512_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_DW512_MST_O_BUS_DW           512
`define MSS_BUS_SWITCH_IBP_DW512_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_DW512_MST_O_BUS_PFX          ibp_dw512_out_
`define MSS_BUS_SWITCH_IBP_DW512_MST_O_ENPACK           0

`define MSS_BUS_SWITCH_IBP_DW512_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_DW512_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_DW512_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_DW512_MST_O_BUS_SPLT_IBP     0


//----------------master cft free 32 to 32------------------------------------------
`define MSS_BUS_SWITCH_IBP_32T32_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_32T32_MST_IDW                4
`define MSS_BUS_SWITCH_IBP_32T32_MST_INUM               1

`define MSS_BUS_SWITCH_IBP_32T32_MST_I0_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_32T32_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_32T32_MST_I0_PFX             in_
`define MSS_BUS_SWITCH_IBP_32T32_0_MST_I0_INST_PFX      in_

`define MSS_BUS_SWITCH_IBP_32T32_0_MST_O_BUS_INST_PFX   out_
`define MSS_BUS_SWITCH_IBP_32T32_MST_I0_DW              32
`define MSS_BUS_SWITCH_IBP_32T32_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_32T32_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_32T32_MST_I0_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_32T32_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_32T32_MST_O_BUS_DW           32
`define MSS_BUS_SWITCH_IBP_32T32_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_32T32_MST_O_BUS_PFX          out_
`define MSS_BUS_SWITCH_IBP_32T32_MST_O_ENPACK            0

`define MSS_BUS_SWITCH_IBP_32T32_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_32T32_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_32T32_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_32T32_MST_O_BUS_SPLT_IBP     0

//----------------master cft free 32 to 64------------------------------------------
`define MSS_BUS_SWITCH_IBP_32T64_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_32T64_MST_IDW                4
`define MSS_BUS_SWITCH_IBP_32T64_MST_INUM               1

`define MSS_BUS_SWITCH_IBP_32T64_MST_I0_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_32T64_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_32T64_MST_I0_PFX             in_
`define MSS_BUS_SWITCH_IBP_32T64_0_MST_I0_INST_PFX      in_

`define MSS_BUS_SWITCH_IBP_32T64_0_MST_O_BUS_INST_PFX   out_
`define MSS_BUS_SWITCH_IBP_32T64_MST_I0_DW              32
`define MSS_BUS_SWITCH_IBP_32T64_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_32T64_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_32T64_MST_I0_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_32T64_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_32T64_MST_O_BUS_DW           64
`define MSS_BUS_SWITCH_IBP_32T64_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_32T64_MST_O_BUS_PFX          out_
`define MSS_BUS_SWITCH_IBP_32T64_MST_O_ENPACK            0

`define MSS_BUS_SWITCH_IBP_32T64_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_32T64_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_32T64_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_32T64_MST_O_BUS_SPLT_IBP     0

//----------------master cft free 32 to 128------------------------------------------
`define MSS_BUS_SWITCH_IBP_32T128_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_32T128_MST_IDW                4
`define MSS_BUS_SWITCH_IBP_32T128_MST_INUM               1

`define MSS_BUS_SWITCH_IBP_32T128_MST_I0_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_32T128_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_32T128_MST_I0_PFX             in_
`define MSS_BUS_SWITCH_IBP_32T128_0_MST_I0_INST_PFX      in_

`define MSS_BUS_SWITCH_IBP_32T128_0_MST_O_BUS_INST_PFX   out_
`define MSS_BUS_SWITCH_IBP_32T128_MST_I0_DW              32
`define MSS_BUS_SWITCH_IBP_32T128_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_32T128_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_32T128_MST_I0_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_32T128_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_32T128_MST_O_BUS_DW           128
`define MSS_BUS_SWITCH_IBP_32T128_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_32T128_MST_O_BUS_PFX          out_
`define MSS_BUS_SWITCH_IBP_32T128_MST_O_ENPACK            0

`define MSS_BUS_SWITCH_IBP_32T128_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_32T128_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_32T128_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_32T128_MST_O_BUS_SPLT_IBP     0

//----------------master cft free 32 to 256------------------------------------------
`define MSS_BUS_SWITCH_IBP_32T256_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_32T256_MST_IDW                4
`define MSS_BUS_SWITCH_IBP_32T256_MST_INUM               1

`define MSS_BUS_SWITCH_IBP_32T256_MST_I0_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_32T256_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_32T256_MST_I0_PFX             in_
`define MSS_BUS_SWITCH_IBP_32T256_0_MST_I0_INST_PFX      in_

`define MSS_BUS_SWITCH_IBP_32T256_0_MST_O_BUS_INST_PFX   out_
`define MSS_BUS_SWITCH_IBP_32T256_MST_I0_DW              32
`define MSS_BUS_SWITCH_IBP_32T256_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_32T256_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_32T256_MST_I0_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_32T256_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_32T256_MST_O_BUS_DW           256
`define MSS_BUS_SWITCH_IBP_32T256_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_32T256_MST_O_BUS_PFX          out_
`define MSS_BUS_SWITCH_IBP_32T256_MST_O_ENPACK            0

`define MSS_BUS_SWITCH_IBP_32T256_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_32T256_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_32T256_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_32T256_MST_O_BUS_SPLT_IBP     0

//----------------master cft free 32 to 512------------------------------------------
`define MSS_BUS_SWITCH_IBP_32T512_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_32T512_MST_IDW                4
`define MSS_BUS_SWITCH_IBP_32T512_MST_INUM               1

`define MSS_BUS_SWITCH_IBP_32T512_MST_I0_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_32T512_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_32T512_MST_I0_PFX             in_
`define MSS_BUS_SWITCH_IBP_32T512_0_MST_I0_INST_PFX      in_

`define MSS_BUS_SWITCH_IBP_32T512_0_MST_O_BUS_INST_PFX   out_
`define MSS_BUS_SWITCH_IBP_32T512_MST_I0_DW              32
`define MSS_BUS_SWITCH_IBP_32T512_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_32T512_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_32T512_MST_I0_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_32T512_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_32T512_MST_O_BUS_DW           512
`define MSS_BUS_SWITCH_IBP_32T512_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_32T512_MST_O_BUS_PFX          out_
`define MSS_BUS_SWITCH_IBP_32T512_MST_O_ENPACK            0

`define MSS_BUS_SWITCH_IBP_32T512_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_32T512_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_32T512_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_32T512_MST_O_BUS_SPLT_IBP     0

//----------------master cft free 64 to 32------------------------------------------
`define MSS_BUS_SWITCH_IBP_64T32_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_64T32_MST_IDW                4
`define MSS_BUS_SWITCH_IBP_64T32_MST_INUM               1

`define MSS_BUS_SWITCH_IBP_64T32_MST_I0_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_64T32_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_64T32_MST_I0_PFX             in_
`define MSS_BUS_SWITCH_IBP_64T32_0_MST_I0_INST_PFX      in_

`define MSS_BUS_SWITCH_IBP_64T32_0_MST_O_BUS_INST_PFX    out_
`define MSS_BUS_SWITCH_IBP_64T32_MST_I0_DW              64
`define MSS_BUS_SWITCH_IBP_64T32_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_64T32_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_64T32_MST_I0_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_64T32_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_64T32_MST_O_BUS_DW           32
`define MSS_BUS_SWITCH_IBP_64T32_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_64T32_MST_O_BUS_PFX          out_
`define MSS_BUS_SWITCH_IBP_64T32_MST_O_ENPACK            0

`define MSS_BUS_SWITCH_IBP_64T32_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_64T32_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_64T32_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_64T32_MST_O_BUS_SPLT_IBP     0

//----------------master cft free 64 to 64------------------------------------------
`define MSS_BUS_SWITCH_IBP_64T64_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_64T64_MST_IDW                4
`define MSS_BUS_SWITCH_IBP_64T64_MST_INUM               1

`define MSS_BUS_SWITCH_IBP_64T64_MST_I0_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_64T64_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_64T64_MST_I0_PFX             in_
`define MSS_BUS_SWITCH_IBP_64T64_0_MST_I0_INST_PFX      in_

`define MSS_BUS_SWITCH_IBP_64T64_0_MST_O_BUS_INST_PFX    out_
`define MSS_BUS_SWITCH_IBP_64T64_MST_I0_DW              64
`define MSS_BUS_SWITCH_IBP_64T64_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_64T64_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_64T64_MST_I0_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_64T64_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_64T64_MST_O_BUS_DW           64
`define MSS_BUS_SWITCH_IBP_64T64_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_64T64_MST_O_BUS_PFX          out_
`define MSS_BUS_SWITCH_IBP_64T64_MST_O_ENPACK            0

`define MSS_BUS_SWITCH_IBP_64T64_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_64T64_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_64T64_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_64T64_MST_O_BUS_SPLT_IBP     0

//----------------master cft free 64 to 128------------------------------------------
`define MSS_BUS_SWITCH_IBP_64T128_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_64T128_MST_IDW                4
`define MSS_BUS_SWITCH_IBP_64T128_MST_INUM               1

`define MSS_BUS_SWITCH_IBP_64T128_MST_I0_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_64T128_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_64T128_MST_I0_PFX             in_
`define MSS_BUS_SWITCH_IBP_64T128_0_MST_I0_INST_PFX      in_

`define MSS_BUS_SWITCH_IBP_64T128_0_MST_O_BUS_INST_PFX    out_
`define MSS_BUS_SWITCH_IBP_64T128_MST_I0_DW              64
`define MSS_BUS_SWITCH_IBP_64T128_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_64T128_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_64T128_MST_I0_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_64T128_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_64T128_MST_O_BUS_DW           128
`define MSS_BUS_SWITCH_IBP_64T128_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_64T128_MST_O_BUS_PFX          out_
`define MSS_BUS_SWITCH_IBP_64T128_MST_O_ENPACK            0

`define MSS_BUS_SWITCH_IBP_64T128_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_64T128_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_64T128_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_64T128_MST_O_BUS_SPLT_IBP     0

//----------------master cft free 64 to 256------------------------------------------
`define MSS_BUS_SWITCH_IBP_64T256_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_64T256_MST_IDW                4
`define MSS_BUS_SWITCH_IBP_64T256_MST_INUM               1

`define MSS_BUS_SWITCH_IBP_64T256_MST_I0_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_64T256_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_64T256_MST_I0_PFX             in_
`define MSS_BUS_SWITCH_IBP_64T256_0_MST_I0_INST_PFX      in_

`define MSS_BUS_SWITCH_IBP_64T256_0_MST_O_BUS_INST_PFX    out_
`define MSS_BUS_SWITCH_IBP_64T256_MST_I0_DW              64
`define MSS_BUS_SWITCH_IBP_64T256_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_64T256_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_64T256_MST_I0_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_64T256_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_64T256_MST_O_BUS_DW           256
`define MSS_BUS_SWITCH_IBP_64T256_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_64T256_MST_O_BUS_PFX          out_
`define MSS_BUS_SWITCH_IBP_64T256_MST_O_ENPACK            0

`define MSS_BUS_SWITCH_IBP_64T256_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_64T256_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_64T256_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_64T256_MST_O_BUS_SPLT_IBP     0

//----------------master cft free 64 to 512------------------------------------------
`define MSS_BUS_SWITCH_IBP_64T512_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_64T512_MST_IDW                4
`define MSS_BUS_SWITCH_IBP_64T512_MST_INUM               1

`define MSS_BUS_SWITCH_IBP_64T512_MST_I0_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_64T512_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_64T512_MST_I0_PFX             in_
`define MSS_BUS_SWITCH_IBP_64T512_0_MST_I0_INST_PFX      in_

`define MSS_BUS_SWITCH_IBP_64T512_0_MST_O_BUS_INST_PFX    out_
`define MSS_BUS_SWITCH_IBP_64T512_MST_I0_DW              64
`define MSS_BUS_SWITCH_IBP_64T512_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_64T512_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_64T512_MST_I0_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_64T512_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_64T512_MST_O_BUS_DW           512
`define MSS_BUS_SWITCH_IBP_64T512_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_64T512_MST_O_BUS_PFX          out_
`define MSS_BUS_SWITCH_IBP_64T512_MST_O_ENPACK            0

`define MSS_BUS_SWITCH_IBP_64T512_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_64T512_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_64T512_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_64T512_MST_O_BUS_SPLT_IBP     0

//----------------master cft free 128 to 32------------------------------------------
`define MSS_BUS_SWITCH_IBP_128T32_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_128T32_MST_IDW                4
`define MSS_BUS_SWITCH_IBP_128T32_MST_INUM               1

`define MSS_BUS_SWITCH_IBP_128T32_MST_I0_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_128T32_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_128T32_MST_I0_PFX             in_
`define MSS_BUS_SWITCH_IBP_128T32_0_MST_I0_INST_PFX      in_

`define MSS_BUS_SWITCH_IBP_128T32_0_MST_O_BUS_INST_PFX    out_
`define MSS_BUS_SWITCH_IBP_128T32_MST_I0_DW              128
`define MSS_BUS_SWITCH_IBP_128T32_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_128T32_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_128T32_MST_I0_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_128T32_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_128T32_MST_O_BUS_DW           32
`define MSS_BUS_SWITCH_IBP_128T32_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_128T32_MST_O_BUS_PFX          out_
`define MSS_BUS_SWITCH_IBP_128T32_MST_O_ENPACK            0

`define MSS_BUS_SWITCH_IBP_128T32_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_128T32_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_128T32_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_128T32_MST_O_BUS_SPLT_IBP     0

//----------------master cft free 128 to 64------------------------------------------
`define MSS_BUS_SWITCH_IBP_128T64_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_128T64_MST_IDW                4
`define MSS_BUS_SWITCH_IBP_128T64_MST_INUM               1

`define MSS_BUS_SWITCH_IBP_128T64_MST_I0_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_128T64_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_128T64_MST_I0_PFX             in_
`define MSS_BUS_SWITCH_IBP_128T64_0_MST_I0_INST_PFX      in_

`define MSS_BUS_SWITCH_IBP_128T64_0_MST_O_BUS_INST_PFX    out_
`define MSS_BUS_SWITCH_IBP_128T64_MST_I0_DW              128
`define MSS_BUS_SWITCH_IBP_128T64_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_128T64_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_128T64_MST_I0_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_128T64_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_128T64_MST_O_BUS_DW           64
`define MSS_BUS_SWITCH_IBP_128T64_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_128T64_MST_O_BUS_PFX          out_
`define MSS_BUS_SWITCH_IBP_128T64_MST_O_ENPACK            0

`define MSS_BUS_SWITCH_IBP_128T64_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_128T64_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_128T64_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_128T64_MST_O_BUS_SPLT_IBP     0

//----------------master cft free 128 to 128------------------------------------------
`define MSS_BUS_SWITCH_IBP_128T128_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_128T128_MST_IDW                4
`define MSS_BUS_SWITCH_IBP_128T128_MST_INUM               1

`define MSS_BUS_SWITCH_IBP_128T128_MST_I0_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_128T128_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_128T128_MST_I0_PFX             in_
`define MSS_BUS_SWITCH_IBP_128T128_0_MST_I0_INST_PFX      in_

`define MSS_BUS_SWITCH_IBP_128T128_0_MST_O_BUS_INST_PFX    out_
`define MSS_BUS_SWITCH_IBP_128T128_MST_I0_DW              128
`define MSS_BUS_SWITCH_IBP_128T128_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_128T128_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_128T128_MST_I0_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_128T128_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_128T128_MST_O_BUS_DW           128
`define MSS_BUS_SWITCH_IBP_128T128_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_128T128_MST_O_BUS_PFX          out_
`define MSS_BUS_SWITCH_IBP_128T128_MST_O_ENPACK            0

`define MSS_BUS_SWITCH_IBP_128T128_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_128T128_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_128T128_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_128T128_MST_O_BUS_SPLT_IBP     0

//----------------master cft free 128 to 256------------------------------------------
`define MSS_BUS_SWITCH_IBP_128T256_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_128T256_MST_IDW                4
`define MSS_BUS_SWITCH_IBP_128T256_MST_INUM               1

`define MSS_BUS_SWITCH_IBP_128T256_MST_I0_OUT_NUM         256
`define MSS_BUS_SWITCH_IBP_128T256_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_128T256_MST_I0_PFX             in_
`define MSS_BUS_SWITCH_IBP_128T256_0_MST_I0_INST_PFX      in_

`define MSS_BUS_SWITCH_IBP_128T256_0_MST_O_BUS_INST_PFX    out_
`define MSS_BUS_SWITCH_IBP_128T256_MST_I0_DW              128
`define MSS_BUS_SWITCH_IBP_128T256_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_128T256_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_128T256_MST_I0_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_128T256_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_128T256_MST_O_BUS_DW           256
`define MSS_BUS_SWITCH_IBP_128T256_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_128T256_MST_O_BUS_PFX          out_
`define MSS_BUS_SWITCH_IBP_128T256_MST_O_ENPACK            0

`define MSS_BUS_SWITCH_IBP_128T256_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_128T256_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_128T256_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_128T256_MST_O_BUS_SPLT_IBP     0

//----------------master cft free 128 to 512------------------------------------------
`define MSS_BUS_SWITCH_IBP_128T512_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_128T512_MST_IDW                4
`define MSS_BUS_SWITCH_IBP_128T512_MST_INUM               1

`define MSS_BUS_SWITCH_IBP_128T512_MST_I0_OUT_NUM         512
`define MSS_BUS_SWITCH_IBP_128T512_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_128T512_MST_I0_PFX             in_
`define MSS_BUS_SWITCH_IBP_128T512_0_MST_I0_INST_PFX      in_

`define MSS_BUS_SWITCH_IBP_128T512_0_MST_O_BUS_INST_PFX    out_
`define MSS_BUS_SWITCH_IBP_128T512_MST_I0_DW              128
`define MSS_BUS_SWITCH_IBP_128T512_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_128T512_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_128T512_MST_I0_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_128T512_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_128T512_MST_O_BUS_DW           512
`define MSS_BUS_SWITCH_IBP_128T512_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_128T512_MST_O_BUS_PFX          out_
`define MSS_BUS_SWITCH_IBP_128T512_MST_O_ENPACK            0

`define MSS_BUS_SWITCH_IBP_128T512_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_128T512_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_128T512_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_128T512_MST_O_BUS_SPLT_IBP     0


//----------------master cft free 256 to 32------------------------------------------
`define MSS_BUS_SWITCH_IBP_256T32_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_256T32_MST_IDW                4
`define MSS_BUS_SWITCH_IBP_256T32_MST_INUM               1

`define MSS_BUS_SWITCH_IBP_256T32_MST_I0_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_256T32_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_256T32_MST_I0_PFX             in_
`define MSS_BUS_SWITCH_IBP_256T32_0_MST_I0_INST_PFX      in_

`define MSS_BUS_SWITCH_IBP_256T32_0_MST_O_BUS_INST_PFX    out_
`define MSS_BUS_SWITCH_IBP_256T32_MST_I0_DW              256
`define MSS_BUS_SWITCH_IBP_256T32_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_256T32_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_256T32_MST_I0_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_256T32_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_256T32_MST_O_BUS_DW           32
`define MSS_BUS_SWITCH_IBP_256T32_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_256T32_MST_O_BUS_PFX          out_
`define MSS_BUS_SWITCH_IBP_256T32_MST_O_ENPACK            0

`define MSS_BUS_SWITCH_IBP_256T32_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_256T32_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_256T32_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_256T32_MST_O_BUS_SPLT_IBP     0

//----------------master cft free 256 to 64------------------------------------------
`define MSS_BUS_SWITCH_IBP_256T64_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_256T64_MST_IDW                4
`define MSS_BUS_SWITCH_IBP_256T64_MST_INUM               1

`define MSS_BUS_SWITCH_IBP_256T64_MST_I0_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_256T64_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_256T64_MST_I0_PFX             in_
`define MSS_BUS_SWITCH_IBP_256T64_0_MST_I0_INST_PFX      in_

`define MSS_BUS_SWITCH_IBP_256T64_0_MST_O_BUS_INST_PFX    out_
`define MSS_BUS_SWITCH_IBP_256T64_MST_I0_DW              256
`define MSS_BUS_SWITCH_IBP_256T64_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_256T64_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_256T64_MST_I0_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_256T64_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_256T64_MST_O_BUS_DW           64
`define MSS_BUS_SWITCH_IBP_256T64_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_256T64_MST_O_BUS_PFX          out_
`define MSS_BUS_SWITCH_IBP_256T64_MST_O_ENPACK            0

`define MSS_BUS_SWITCH_IBP_256T64_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_256T64_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_256T64_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_256T64_MST_O_BUS_SPLT_IBP     0

//----------------master cft free 256 to 128------------------------------------------
`define MSS_BUS_SWITCH_IBP_256T128_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_256T128_MST_IDW                4
`define MSS_BUS_SWITCH_IBP_256T128_MST_INUM               1

`define MSS_BUS_SWITCH_IBP_256T128_MST_I0_OUT_NUM         128
`define MSS_BUS_SWITCH_IBP_256T128_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_256T128_MST_I0_PFX             in_
`define MSS_BUS_SWITCH_IBP_256T128_0_MST_I0_INST_PFX      in_

`define MSS_BUS_SWITCH_IBP_256T128_0_MST_O_BUS_INST_PFX    out_
`define MSS_BUS_SWITCH_IBP_256T128_MST_I0_DW              256
`define MSS_BUS_SWITCH_IBP_256T128_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_256T128_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_256T128_MST_I0_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_256T128_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_256T128_MST_O_BUS_DW           128
`define MSS_BUS_SWITCH_IBP_256T128_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_256T128_MST_O_BUS_PFX          out_
`define MSS_BUS_SWITCH_IBP_256T128_MST_O_ENPACK            0

`define MSS_BUS_SWITCH_IBP_256T128_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_256T128_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_256T128_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_256T128_MST_O_BUS_SPLT_IBP     0

//----------------master cft free 256 to 256------------------------------------------
`define MSS_BUS_SWITCH_IBP_256T256_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_256T256_MST_IDW                4
`define MSS_BUS_SWITCH_IBP_256T256_MST_INUM               1

`define MSS_BUS_SWITCH_IBP_256T256_MST_I0_OUT_NUM         256
`define MSS_BUS_SWITCH_IBP_256T256_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_256T256_MST_I0_PFX             in_
`define MSS_BUS_SWITCH_IBP_256T256_0_MST_I0_INST_PFX      in_

`define MSS_BUS_SWITCH_IBP_256T256_0_MST_O_BUS_INST_PFX    out_
`define MSS_BUS_SWITCH_IBP_256T256_MST_I0_DW              256
`define MSS_BUS_SWITCH_IBP_256T256_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_256T256_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_256T256_MST_I0_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_256T256_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_256T256_MST_O_BUS_DW           256
`define MSS_BUS_SWITCH_IBP_256T256_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_256T256_MST_O_BUS_PFX          out_
`define MSS_BUS_SWITCH_IBP_256T256_MST_O_ENPACK            0

`define MSS_BUS_SWITCH_IBP_256T256_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_256T256_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_256T256_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_256T256_MST_O_BUS_SPLT_IBP     0

//----------------master cft free 256 to 512------------------------------------------
`define MSS_BUS_SWITCH_IBP_256T512_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_256T512_MST_IDW                4
`define MSS_BUS_SWITCH_IBP_256T512_MST_INUM               1

`define MSS_BUS_SWITCH_IBP_256T512_MST_I0_OUT_NUM         512
`define MSS_BUS_SWITCH_IBP_256T512_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_256T512_MST_I0_PFX             in_
`define MSS_BUS_SWITCH_IBP_256T512_0_MST_I0_INST_PFX      in_

`define MSS_BUS_SWITCH_IBP_256T512_0_MST_O_BUS_INST_PFX    out_
`define MSS_BUS_SWITCH_IBP_256T512_MST_I0_DW              256
`define MSS_BUS_SWITCH_IBP_256T512_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_256T512_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_256T512_MST_I0_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_256T512_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_256T512_MST_O_BUS_DW           512
`define MSS_BUS_SWITCH_IBP_256T512_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_256T512_MST_O_BUS_PFX          out_
`define MSS_BUS_SWITCH_IBP_256T512_MST_O_ENPACK            0

`define MSS_BUS_SWITCH_IBP_256T512_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_256T512_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_256T512_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_256T512_MST_O_BUS_SPLT_IBP     0


//----------------master cft free 512 to 32------------------------------------------
`define MSS_BUS_SWITCH_IBP_512T32_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_512T32_MST_IDW                4
`define MSS_BUS_SWITCH_IBP_512T32_MST_INUM               1

`define MSS_BUS_SWITCH_IBP_512T32_MST_I0_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_512T32_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_512T32_MST_I0_PFX             in_
`define MSS_BUS_SWITCH_IBP_512T32_0_MST_I0_INST_PFX      in_

`define MSS_BUS_SWITCH_IBP_512T32_0_MST_O_BUS_INST_PFX    out_
`define MSS_BUS_SWITCH_IBP_512T32_MST_I0_DW              512
`define MSS_BUS_SWITCH_IBP_512T32_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_512T32_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_512T32_MST_I0_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_512T32_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_512T32_MST_O_BUS_DW           32
`define MSS_BUS_SWITCH_IBP_512T32_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_512T32_MST_O_BUS_PFX          out_
`define MSS_BUS_SWITCH_IBP_512T32_MST_O_ENPACK            0

`define MSS_BUS_SWITCH_IBP_512T32_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_512T32_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_512T32_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_512T32_MST_O_BUS_SPLT_IBP     0

//----------------master cft free 512 to 64------------------------------------------
`define MSS_BUS_SWITCH_IBP_512T64_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_512T64_MST_IDW                4
`define MSS_BUS_SWITCH_IBP_512T64_MST_INUM               1

`define MSS_BUS_SWITCH_IBP_512T64_MST_I0_OUT_NUM         64
`define MSS_BUS_SWITCH_IBP_512T64_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_512T64_MST_I0_PFX             in_
`define MSS_BUS_SWITCH_IBP_512T64_0_MST_I0_INST_PFX      in_

`define MSS_BUS_SWITCH_IBP_512T64_0_MST_O_BUS_INST_PFX    out_
`define MSS_BUS_SWITCH_IBP_512T64_MST_I0_DW              512
`define MSS_BUS_SWITCH_IBP_512T64_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_512T64_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_512T64_MST_I0_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_512T64_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_512T64_MST_O_BUS_DW           64
`define MSS_BUS_SWITCH_IBP_512T64_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_512T64_MST_O_BUS_PFX          out_
`define MSS_BUS_SWITCH_IBP_512T64_MST_O_ENPACK            0

`define MSS_BUS_SWITCH_IBP_512T64_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_512T64_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_512T64_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_512T64_MST_O_BUS_SPLT_IBP     0

//----------------master cft free 512 to 128------------------------------------------
`define MSS_BUS_SWITCH_IBP_512T128_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_512T128_MST_IDW                4
`define MSS_BUS_SWITCH_IBP_512T128_MST_INUM               1

`define MSS_BUS_SWITCH_IBP_512T128_MST_I0_OUT_NUM         128
`define MSS_BUS_SWITCH_IBP_512T128_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_512T128_MST_I0_PFX             in_
`define MSS_BUS_SWITCH_IBP_512T128_0_MST_I0_INST_PFX      in_

`define MSS_BUS_SWITCH_IBP_512T128_0_MST_O_BUS_INST_PFX    out_
`define MSS_BUS_SWITCH_IBP_512T128_MST_I0_DW              512
`define MSS_BUS_SWITCH_IBP_512T128_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_512T128_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_512T128_MST_I0_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_512T128_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_512T128_MST_O_BUS_DW           128
`define MSS_BUS_SWITCH_IBP_512T128_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_512T128_MST_O_BUS_PFX          out_
`define MSS_BUS_SWITCH_IBP_512T128_MST_O_ENPACK            0

`define MSS_BUS_SWITCH_IBP_512T128_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_512T128_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_512T128_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_512T128_MST_O_BUS_SPLT_IBP     0

//----------------master cft free 512 to 256------------------------------------------
`define MSS_BUS_SWITCH_IBP_512T256_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_512T256_MST_IDW                4
`define MSS_BUS_SWITCH_IBP_512T256_MST_INUM               1

`define MSS_BUS_SWITCH_IBP_512T256_MST_I0_OUT_NUM         256
`define MSS_BUS_SWITCH_IBP_512T256_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_512T256_MST_I0_PFX             in_
`define MSS_BUS_SWITCH_IBP_512T256_0_MST_I0_INST_PFX      in_

`define MSS_BUS_SWITCH_IBP_512T256_0_MST_O_BUS_INST_PFX    out_
`define MSS_BUS_SWITCH_IBP_512T256_MST_I0_DW              512
`define MSS_BUS_SWITCH_IBP_512T256_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_512T256_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_512T256_MST_I0_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_512T256_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_512T256_MST_O_BUS_DW           256
`define MSS_BUS_SWITCH_IBP_512T256_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_512T256_MST_O_BUS_PFX          out_
`define MSS_BUS_SWITCH_IBP_512T256_MST_O_ENPACK            0

`define MSS_BUS_SWITCH_IBP_512T256_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_512T256_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_512T256_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_512T256_MST_O_BUS_SPLT_IBP     0

//----------------master cft free 512 to 512------------------------------------------
`define MSS_BUS_SWITCH_IBP_512T512_MST_AW                 49
`define MSS_BUS_SWITCH_IBP_512T512_MST_IDW                4
`define MSS_BUS_SWITCH_IBP_512T512_MST_INUM               1

`define MSS_BUS_SWITCH_IBP_512T512_MST_I0_OUT_NUM         512
`define MSS_BUS_SWITCH_IBP_512T512_MST_I0_UNIQ_ID         0
`define MSS_BUS_SWITCH_IBP_512T512_MST_I0_PFX             in_
`define MSS_BUS_SWITCH_IBP_512T512_0_MST_I0_INST_PFX      in_

`define MSS_BUS_SWITCH_IBP_512T512_0_MST_O_BUS_INST_PFX    out_
`define MSS_BUS_SWITCH_IBP_512T512_MST_I0_DW              512
`define MSS_BUS_SWITCH_IBP_512T512_MST_I0_ENPACK          1
`define MSS_BUS_SWITCH_IBP_512T512_MST_I0_LOCKABLE        1
`define MSS_BUS_SWITCH_IBP_512T512_MST_I0_W2N_MAY_OVF     1

`define MSS_BUS_SWITCH_IBP_512T512_MST_O_BUS_ENDIAN       0
`define MSS_BUS_SWITCH_IBP_512T512_MST_O_BUS_DW           512
`define MSS_BUS_SWITCH_IBP_512T512_MST_O_BUS_TYPE         ibp
`define MSS_BUS_SWITCH_IBP_512T512_MST_O_BUS_PFX          out_
`define MSS_BUS_SWITCH_IBP_512T512_MST_O_ENPACK            0

`define MSS_BUS_SWITCH_IBP_512T512_MST_O_BUS_BUF_ENTRIES  0
`define MSS_BUS_SWITCH_IBP_512T512_MST_O_HAS_CLK_EN       0
`define MSS_BUS_SWITCH_IBP_512T512_MST_O_BUS_CLK_EN_NAME  mss_bs_out_clk_en
`define MSS_BUS_SWITCH_IBP_512T512_MST_O_BUS_SPLT_IBP     0

