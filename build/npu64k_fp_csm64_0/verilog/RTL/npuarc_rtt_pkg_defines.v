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
//   rtt_pkg_defines
//
// ===========================================================================
//
// Description:
//  defines for RTT module
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o rtt_pkg_defines.vpp
//
// ===========================================================================

`include "npuarc_arc_rtt_defines.v"


//`define PC `PC_BITS

`define npuarc_OQ_WIDTH        60

`define  npuarc_RTT_BASE_ADDR  32'h8000_0000
`define  npuarc_RTT_MAX_ADDR   32'hFFFF_FFFF
`define npuarc_OCM 1'b0
`define  npuarc_INT_MEM  3'b010
`define npuarc_INT_BUF_FIFO_SIZE 11


//RTT Control Registers
`define  npuarc_RTT_BCR          5'h00                   //00
`define  npuarc_RTT_PR_SEL       (`npuarc_RTT_BCR+5'h1)         //01
`define  npuarc_RTT_FREEZE       (`npuarc_RTT_PR_SEL+5'h1)      //02
`define  npuarc_RTT_FREEZE_CTRL  (`npuarc_RTT_FREEZE+5'h1)      //03
`define  npuarc_RTT_TST          (`npuarc_RTT_FREEZE_CTRL+5'h1) //04
`define  npuarc_RTT_DBGR_MSGS_EN (`npuarc_RTT_TST+5'h1)         //05
`define  npuarc_EXT_START_STOP   (`npuarc_RTT_TR_STATUS +5'h1)  //15
`define  npuarc_FLUSH_COMMAND    (`npuarc_EXT_START_STOP +5'h1) //16
`define  npuarc_RTT_PRDCR_BCR    (`npuarc_FLUSH_COMMAND+5'h1)   //17

//RTT Config Registers
`define  npuarc_OCM_MEM_BASE    5'h10                    //10
`define  npuarc_OCM_SZ_REG      (`npuarc_OCM_MEM_BASE +5'h1)    //11
`define  npuarc_OCM_MEM_WR_PTR  (`npuarc_OCM_SZ_REG+5'h1  )     //12
`define  npuarc_OCM_MEM_RD_PTR  (`npuarc_OCM_MEM_WR_PTR +5'h1)  //13
`define  npuarc_RTT_TR_STATUS   (`npuarc_OCM_MEM_RD_PTR +5'h1)  //14
`define  npuarc_OFFLOAD_IF      (`npuarc_FLUSH_COMMAND +5'h1)   //17
`define  npuarc_AUTO_LOCK       (`npuarc_OFFLOAD_IF+5'h1  )     //18
`define  npuarc_NEXUS_CLK_DIV   (`npuarc_AUTO_LOCK+5'h1  )      //19
`define  npuarc_PR_EVTI_REG     (`npuarc_NEXUS_CLK_DIV +5'h1)   //1A

//Producer Registers
`define  npuarc_ADDR_FILTER_START0 6'h00                       //00
`define  npuarc_ADDR_FILTER_STOP0  (`npuarc_ADDR_FILTER_START0+6'h1 ) //01
`define  npuarc_ADDR_FILTER_START1 (`npuarc_ADDR_FILTER_STOP0+6'h1)   //02
`define  npuarc_ADDR_FILTER_STOP1  (`npuarc_ADDR_FILTER_START1+6'h1 ) //03
`define  npuarc_ADDR_FILTER_START2 (`npuarc_ADDR_FILTER_STOP1+6'h1)   //04
`define  npuarc_ADDR_FILTER_STOP2  (`npuarc_ADDR_FILTER_START2+6'h1 ) //05
`define  npuarc_ADDR_FILTER_START3 (`npuarc_ADDR_FILTER_STOP2+6'h1)   //06
`define  npuarc_ADDR_FILTER_STOP3  (`npuarc_ADDR_FILTER_START3+6'h1 ) //07
`define  npuarc_ADDR_FILTER_START4 (`npuarc_ADDR_FILTER_STOP3+6'h1)   //08
`define  npuarc_ADDR_FILTER_STOP4  (`npuarc_ADDR_FILTER_START4+6'h1 ) //09
`define  npuarc_ADDR_FILTER_START5 (`npuarc_ADDR_FILTER_STOP4+6'h1)   //0A
`define  npuarc_ADDR_FILTER_STOP5  (`npuarc_ADDR_FILTER_START5+6'h1 ) //0B
`define  npuarc_ADDR_FILTER_START6 (`npuarc_ADDR_FILTER_STOP5+6'h1)   //0C
`define  npuarc_ADDR_FILTER_STOP6  (`npuarc_ADDR_FILTER_START6+6'h1 ) //0D
`define  npuarc_ADDR_FILTER_START7 (`npuarc_ADDR_FILTER_STOP6+6'h1)   //0E
`define  npuarc_ADDR_FILTER_STOP7  (`npuarc_ADDR_FILTER_START7+6'h1 ) //0F
`define  npuarc_DATA_FILTER0_LSW   (`npuarc_ADDR_FILTER_STOP7+6'h1 )  //10
`define  npuarc_DATA_FILTER0_MSW   (`npuarc_DATA_FILTER0_LSW+6'h1 )   //11
`define  npuarc_DATA_FILTER1_LSW   (`npuarc_DATA_FILTER0_MSW+6'h1 )   //12
`define  npuarc_DATA_FILTER1_MSW   (`npuarc_DATA_FILTER1_LSW+6'h1 )   //13
`define  npuarc_CSTSEN_REG_ADDR    (`npuarc_ADDR_FILTER_START0+6'h1B) //1B
`define  npuarc_CTIEN_REG_ADDR     (`npuarc_ADDR_FILTER_START0+6'h1C) //1C
`define  npuarc_SYNCRFR_REG_ADDR   (`npuarc_ADDR_FILTER_START0+6'h1D) //1D
`define  npuarc_DSEN_REG_ADDR      (`npuarc_ADDR_FILTER_START0+6'h1E) //1E
`define  npuarc_ATID_REG_ADDR      (`npuarc_ADDR_FILTER_START0+6'h1F) //1F
// Producer control function Registers
`define  npuarc_PRDCTYPE           (`npuarc_DATA_FILTER1_MSW+5'h1)    //14
`define  npuarc_FILTER_TYPE        (`npuarc_PRDCTYPE+5'h1)            //15
`define  npuarc_TRIGGER_REG        (`npuarc_FILTER_TYPE+5'h1)         //16
`define  npuarc_PR_SRC_EN          (`npuarc_TRIGGER_REG+5'h1 )        //17
`define  npuarc_PR_FREEZE_STATUS   (`npuarc_PR_SRC_EN +5'h1 )         //18
`define  npuarc_PR_WP_STATUS       (`npuarc_PR_FREEZE_STATUS+5'h1 )   //19
`define  npuarc_PR_WP_ENABLE       (`npuarc_PR_WP_STATUS+5'h1 )       //1A
`define  npuarc_W_NUM_PRDCR  5'd`ncores
`define  npuarc_NUM_PR    4'd8
`define npuarc_VDSPM_BUF_DEPTH  2
`define npuarc_VDSPM_BUF_LOCS  1 << `npuarc_VDSPM_BUF_DEPTH
`define npuarc_VDSPM_FREEZE_LEVEL  2
`define  npuarc_VDSPSW_WDT       70
`define  npuarc_NEXUS_MSEO_WDT 1'b1  // 1'b0 - 1-bit, 1'b1 - 2-bit
`define npuarc_MSEO_WDT  2


`define npuarc_MDO_PORTS 2'b01 //2'b00 - 4-bit, 2'b01 - 8-bit, 2'b10 - 16-bit
`define npuarc_MDO_WDT  8
`define npuarc_SHT_CNT_BITS 80
`define npuarc_SHT_CNT_WRAP 80
`define npuarc_PAD_BITS 6


`define npuarc_MEM_STRG_WDT (`npuarc_MSEO_WDT+`npuarc_MDO_WDT)
`define npuarc_MSG_TYPE_LOST_WDT 12
`define npuarc_ETYPE_WDT 4
`define npuarc_RCODE_WDT 4
`define npuarc_RDAT_WDT 32



// Because this file is done differently from other defines,
// it requires a `let expression to be computed above

// Bits definition
`define npuarc_BCR 29
`define npuarc_PR_SEL 8
`define npuarc_OCM_BASE_ADDR 32
`define npuarc_OCM_SZ 32
`define npuarc_OCM_WR_PTR 32
`define npuarc_OCM_RD_PTR (`npuarc_OCM_WR_PTR)
`define npuarc_TR_STATUS 13
//`define ATBCR_WDT 7
`define npuarc_ATID_WDT 7
`define npuarc_SYNCRFR_WDT 16
`define npuarc_RTT_ADDR 32
`define npuarc_AUX_ADDR 32
`define npuarc_AUX_DATA 32
`define npuarc_VDSP_AUX_DATA 33
`define npuarc_MEM_ADDR 32
`define npuarc_RTT_DATA 32
//`define MEM_DATA 64
`define npuarc_DTM_WDT 170

`define npuarc_FSIZE 64

`define npuarc_RTT_DATA_MSB (`npuarc_RTT_DATA-1)
`define npuarc_RTT_REG_DATA 32
`define npuarc_RTT_REG_DATA_MSB (`npuarc_RTT_REG_DATA-1)
`define npuarc_RTT_ADDR8 8
`define npuarc_RTT_CORE_FILTER_DATA 6
`define npuarc_OCM_ADDR (`npuarc_RTT_DATA)
`define npuarc_RTT_TR_STATUS_MSB (`npuarc_TR_STATUS-1)
`define npuarc_OFFLOAD_CONFIG 2'b01
`define npuarc_PR_TYPE 2
`define npuarc_FR_STATUS 13
`define npuarc_PR_WP 8
`define npuarc_PR_EVTI 2
`define npuarc_RTT_CR_ADDR 6
`define npuarc_RTT_TIME_STMP_CNTR_BITS 8
`define npuarc_RTT_TIME_STMP 8
`define npuarc_RTT_PID 8
`define npuarc_TSTAMP_OF_WDT 10
`define npuarc_I_CNT 8
`define npuarc_MEM_DSZ 2
`define npuarc_RTT_TRG `npuarc_RTT_NUM_FILTERS

`define npuarc_ATB_FIFO_DEPTH 16



`define npuarc_ATBYTE_WIDTH  3

`define npuarc_SWE_ATBYTE_WIDTH  3

`define npuarc_DSM_WDT 70
// 120
`define npuarc_CSTM_WDT 100
`define npuarc_PTM_WDT 120
`define npuarc_PCM_WDT 70
`define npuarc_CRM_WDT 120
`define npuarc_DSM_BUF_DEPTH  1
`define npuarc_PCM_BUF_DEPTH  2
`define npuarc_PTCM_BUF_DEPTH  2
`define npuarc_RFM_BUF_DEPTH 3
`define npuarc_ERRM_BUF_DEPTH 2
`define npuarc_PTM_BUF_DEPTH  2
`define npuarc_DTM_BUF_DEPTH  3
`define npuarc_CRM_BUF_DEPTH 5
`define npuarc_AUXM_BUF_DEPTH 4
`define npuarc_OTM_BUF_DEPTH 1
`define npuarc_CSTM_BUF_DEPTH 1
`define npuarc_WPM_BUF_DEPTH 2
`define npuarc_PRDCR_BUF_DEPTH 10

`define npuarc_TSTAMP_WDT 8
`define npuarc_CST_WDT 64
`define npuarc_NUM_MSG_SRC 14
`define npuarc_PRNUM_WDT 6
`define npuarc_SHFT_REG_WDT 170

`define npuarc_SHT_CNT_WDT 7

`define npuarc_SYSB_ADDR_WDT 32
`define npuarc_SYSB_BLEN_WDT 4
`define npuarc_SYSB_DATA_WDT 64
`define npuarc_SYSB_MASK_WDT 8

`define npuarc_AUXM_WDT 120
`define npuarc_ERRM_WDT 50
`define npuarc_OTM_WDT 40
`define npuarc_RFM_WDT 70
`define npuarc_WPM_WDT 40
`define npuarc_HIST_WDT 32
`define npuarc_SYNC_CNT_WDT 8

`define npuarc_DSM_BUF_LOCS  1 << `npuarc_DSM_BUF_DEPTH
`define npuarc_PCM_BUF_LOCS  1 << `npuarc_PCM_BUF_DEPTH
`define npuarc_PTCM_BUF_LOCS 1 << `npuarc_PTCM_BUF_DEPTH
`define npuarc_PTM_BUF_LOCS  1 << `npuarc_PTM_BUF_DEPTH
`define npuarc_DTM_BUF_LOCS  1 << `npuarc_DTM_BUF_DEPTH
`define npuarc_CRM_BUF_LOCS  1 << `npuarc_CRM_BUF_DEPTH
`define npuarc_AUXM_BUF_LOCS 1 << `npuarc_AUXM_BUF_DEPTH
`define npuarc_ERRM_BUF_LOCS 1 << `npuarc_ERRM_BUF_DEPTH
`define npuarc_OTM_BUF_LOCS  1 << `npuarc_OTM_BUF_DEPTH
`define npuarc_RFM_BUF_LOCS  1 << `npuarc_RFM_BUF_DEPTH
`define npuarc_WPM_BUF_LOCS  1 << `npuarc_WPM_BUF_DEPTH
`define npuarc_CSTM_BUF_LOCS 1 << `npuarc_CSTM_BUF_DEPTH
`define npuarc_INT_BUF_LOCS  1 << `npuarc_INT_BUF_FIFO_SIZE

`define npuarc_DSM_FREEZE_LEVEL  1
`define npuarc_PCM_FREEZE_LEVEL  2
`define npuarc_PTCM_FREEZE_LEVEL 2
`define npuarc_WPM_FREEZE_LEVEL  2
`define npuarc_AUXM_FREEZE_LEVEL 8
`define npuarc_PTM_FREEZE_LEVEL  2
`define npuarc_DTM_FREEZE_LEVEL  4
`define npuarc_CRM_FREEZE_LEVEL  2
`define npuarc_ERRM_FREEZE_LEVEL 2
`define npuarc_RFM_FREEZE_LEVEL  4
`define npuarc_OTM_FREEZE_LEVEL  1
`define npuarc_CSTM_FREEZE_LEVEL 1
`define npuarc_INT_BUF_FREEZE_LEVEL  100


  `define npuarc_a_w     32
  `define npuarc_c_d_w   64
  `define npuarc_b_d_w   64
  `define npuarc_c_alsb  3
  `define npuarc_b_alsb  3


`include "npuarc_exported_defines.v"

// producer-specific info has been moved out into a header file
// where can compute define names.
// Parameters Specific to NTA

`define npuarc_IQ_WIDTH             60
`define npuarc_IQ_BUF_DEPTH         6
//`let IQ_SIZE=LOG2CEIL(`IQ_BUF_DEPTH);
`define npuarc_IQ_SIZE              3
`define npuarc_IQ_BUF_FULL_PTR      5 
`define npuarc_IQ_BUF_AL_FULL_PTR   4 
`define npuarc_CELLS_IN_IQ_ENTRY    6 
`define npuarc_TOT_CLIENTS          1 
`define npuarc_NXS_MSG_CNT_WDT      3
`define npuarc_CLNT_CRED_WDT        4 
`define npuarc_CREDITS4CLIENT       8 
//`define CLNT_CRED_WDT 4 
`define npuarc_iQ_data_width      60
`define npuarc_iQ_data_width_clnt 60
`define npuarc_iQ_buffer_credits 6
//`define MAX_FWD_LIMIT_PER_iQ 7 //Actual Limit is 7


`define npuarc_oQ_im_buffer_size 2


//Calculating oQ_buffer_depth by using ARChitect Parameter `INT_BUF_FIFO_SIZE
`define npuarc_oQ_buffer_depth 1 << `npuarc_INT_BUF_FIFO_SIZE
`define npuarc_oQ_ptr_is_pow_of2 1

`define npuarc_AXI_DATA_WIDTH 64
`define npuarc_OCM_BASE_ADDRESS 0

`define npuarc_nta_if_wr_width `npuarc_iQ_data_width-1:0
//`configure nxs_fifo_rd_width 180
`define npuarc_nta_buffer_depth 4
`define npuarc_nta_ip_credit_msb `npuarc_nta_buffer_depth
`define npuarc_nta_ip_credit_range `npuarc_nta_ip_credit_msb:0







  



`define npuarc_CORE_IS_HS6X  0

`define npuarc_RTT_NUM_SWE_PORTS (`npuarc_RTT_NUM_NPU_SLICES + `npuarc_RTT_NPU_STU_PORT)
`define npuarc_SWEM_WDT  80
`define npuarc_SWEM_BUF_DEPTH  4
`define npuarc_SWEM_BUF_LOCS  1 << `npuarc_SWEM_BUF_DEPTH
`define npuarc_SWE_PRDCR_BNK  3
