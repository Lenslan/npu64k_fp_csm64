// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2020 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary 
// work of Synopsys, Inc., and is fully protected under copyright and 
// trade secret laws. You may not view, use, disclose, copy, or distribute 
// this file or any information contained herein except pursuant to a 
// valid written license from Synopsys, Inc.
//
// Certain materials incorporated herein are copyright (C) 2010 - 2011, The
// University Court of the University of Edinburgh. All Rights Reserved.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
//  
// 
// 
//   ####   #####     ##    #    #   ####
//  #       #    #   #  #   ##  ##  #
//   ####   #    #  #    #  # ## #   ####
//       #  #####   ######  #    #       #
//  #    #  #   #   #    #  #    #  #    #
//   ####   #    #  #    #  #    #   ####
//
// ===========================================================================
//
// @f:rams
//
// Description:
// @p
//  The |srams| module instantiates the all memories in the design.
// @e
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_srams (



  input                              ic_data_bank0_clk,  
  input                              ic_data_ce0,  
  input  [`npuarc_IC_ADR_RANGE]             ic_data_addr0, 
  input  [`npuarc_IC_BANK_WIDTH-1:0]        ic_data_din0,  
  input                              ic_data_we0,  
  input  [`npuarc_IC_BANK_BYTE_SIZE-1:0]    ic_data_wem0,  
  input                              ic_data_ds0,
  input                              ic_data_sd0,
  output [`npuarc_IC_BANK_WIDTH-1:0]        ic_data_dout0,
  input                              ic_data_bank1_clk,  
  input                              ic_data_ce1,  
  input  [`npuarc_IC_ADR_RANGE]             ic_data_addr1, 
  input  [`npuarc_IC_BANK_WIDTH-1:0]        ic_data_din1,  
  input                              ic_data_we1,  
  input  [`npuarc_IC_BANK_BYTE_SIZE-1:0]    ic_data_wem1,  
  input                              ic_data_ds1,
  input                              ic_data_sd1,
  output [`npuarc_IC_BANK_WIDTH-1:0]        ic_data_dout1,

  input                              ic_tag_way0_clk,   
  input                              ic_tag_ce0,   
  input  [`npuarc_IC_IDX_RANGE]             ic_tag_addr0,  
  input  [`npuarc_IC_TRAM_RANGE]            ic_tag_din0,   
  input                              ic_tag_we0,   
  input   [`npuarc_IC_TRAM_MASK_RANGE]      ic_tag_wem0,
  input                              ic_tag_ds0,
  input                              ic_tag_sd0,
  output [`npuarc_IC_TRAM_RANGE]            ic_tag_dout0,
  input                              ic_tag_way1_clk,   
  input                              ic_tag_ce1,   
  input  [`npuarc_IC_IDX_RANGE]             ic_tag_addr1,  
  input  [`npuarc_IC_TRAM_RANGE]            ic_tag_din1,   
  input                              ic_tag_we1,   
  input   [`npuarc_IC_TRAM_MASK_RANGE]      ic_tag_wem1,
  input                              ic_tag_ds1,
  input                              ic_tag_sd1,
  output [`npuarc_IC_TRAM_RANGE]            ic_tag_dout1,
  input                              ic_tag_way2_clk,   
  input                              ic_tag_ce2,   
  input  [`npuarc_IC_IDX_RANGE]             ic_tag_addr2,  
  input  [`npuarc_IC_TRAM_RANGE]            ic_tag_din2,   
  input                              ic_tag_we2,   
  input   [`npuarc_IC_TRAM_MASK_RANGE]      ic_tag_wem2,
  input                              ic_tag_ds2,
  input                              ic_tag_sd2,
  output [`npuarc_IC_TRAM_RANGE]            ic_tag_dout2,
  input                              ic_tag_way3_clk,   
  input                              ic_tag_ce3,   
  input  [`npuarc_IC_IDX_RANGE]             ic_tag_addr3,  
  input  [`npuarc_IC_TRAM_RANGE]            ic_tag_din3,   
  input                              ic_tag_we3,   
  input   [`npuarc_IC_TRAM_MASK_RANGE]      ic_tag_wem3,
  input                              ic_tag_ds3,
  input                              ic_tag_sd3,
  output [`npuarc_IC_TRAM_RANGE]            ic_tag_dout3,
  
// spyglass disable_block W240
// SMD: Signal declared but not used
// SJ:  not used in all configs
  input                              rst,
// spyglass enable_block W240


  input                              clk_tag_even_w0,
  input                              dc_tag_even_cs_w0,  
  input                              dc_tag_even_we_w0,  
  input  [`npuarc_DC_TRAM_RANGE]            dc_tag_even_wem_w0, 
  input  [`npuarc_DC_IDX_RANGE]             dc_tag_even_addr_w0,
  input  [`npuarc_DC_TRAM_RANGE]            dc_tag_even_din_w0, 
  input                              dc_tag_even_ds_w0,
  input                              dc_tag_even_sd_w0,
  output [`npuarc_DC_TRAM_RANGE]            dc_tag_even_dout_w0, 
                    
  input                              clk_tag_odd_w0,
  input                              dc_tag_odd_cs_w0,  
  input                              dc_tag_odd_we_w0,  
  input  [`npuarc_DC_TRAM_RANGE]            dc_tag_odd_wem_w0, 
  input  [`npuarc_DC_IDX_RANGE]             dc_tag_odd_addr_w0,
  input  [`npuarc_DC_TRAM_RANGE]            dc_tag_odd_din_w0, 
  input                              dc_tag_odd_ds_w0,
  input                              dc_tag_odd_sd_w0,
  output [`npuarc_DC_TRAM_RANGE]            dc_tag_odd_dout_w0, 
  
  input                              clk_tag_even_w1,
  input                              dc_tag_even_cs_w1,  
  input                              dc_tag_even_we_w1,  
  input  [`npuarc_DC_TRAM_RANGE]            dc_tag_even_wem_w1, 
  input  [`npuarc_DC_IDX_RANGE]             dc_tag_even_addr_w1,
  input  [`npuarc_DC_TRAM_RANGE]            dc_tag_even_din_w1, 
  input                              dc_tag_even_ds_w1,
  input                              dc_tag_even_sd_w1,
  output [`npuarc_DC_TRAM_RANGE]            dc_tag_even_dout_w1, 
                    
  input                              clk_tag_odd_w1,
  input                              dc_tag_odd_cs_w1,  
  input                              dc_tag_odd_we_w1,  
  input  [`npuarc_DC_TRAM_RANGE]            dc_tag_odd_wem_w1, 
  input  [`npuarc_DC_IDX_RANGE]             dc_tag_odd_addr_w1,
  input  [`npuarc_DC_TRAM_RANGE]            dc_tag_odd_din_w1, 
  input                              dc_tag_odd_ds_w1,
  input                              dc_tag_odd_sd_w1,
  output [`npuarc_DC_TRAM_RANGE]            dc_tag_odd_dout_w1, 
  
  input                              clk_data_even_lo,     
  input                              dc_data_even_cs_lo,   
  input                              dc_data_even_we_lo,   
  input  [`npuarc_DC_DBL_BE_RANGE]          dc_data_even_wem_lo,  
  input  [`npuarc_DC_ADR_RANGE]             dc_data_even_addr_lo, 
  input  [`npuarc_DC_DRAM_RANGE]            dc_data_even_din_lo,
  input                              dc_data_even_ds_lo,
  input                              dc_data_even_sd_lo,
  output [`npuarc_DC_DRAM_RANGE]            dc_data_even_dout_lo,

  input                              clk_data_even_hi,     
  input                              dc_data_even_cs_hi,   
  input                              dc_data_even_we_hi,   
  input  [`npuarc_DC_DBL_BE_RANGE]          dc_data_even_wem_hi,  
  input  [`npuarc_DC_ADR_RANGE]             dc_data_even_addr_hi, 
  input  [`npuarc_DC_DRAM_RANGE]            dc_data_even_din_hi,
  input                              dc_data_even_ds_hi,
  input                              dc_data_even_sd_hi,
  output [`npuarc_DC_DRAM_RANGE]            dc_data_even_dout_hi, 

  input                              clk_data_odd_lo,      
  input                              dc_data_odd_cs_lo,    
  input                              dc_data_odd_we_lo,    
  input  [`npuarc_DC_DBL_BE_RANGE]          dc_data_odd_wem_lo,  
  input  [`npuarc_DC_ADR_RANGE]             dc_data_odd_addr_lo,  
  input  [`npuarc_DC_DRAM_RANGE]            dc_data_odd_din_lo,
  input                              dc_data_odd_ds_lo,
  input                              dc_data_odd_sd_lo,
  output [`npuarc_DC_DRAM_RANGE]            dc_data_odd_dout_lo,

  input                              clk_data_odd_hi,      
  input                              dc_data_odd_cs_hi,    
  input                              dc_data_odd_we_hi,    
  input  [`npuarc_DC_DBL_BE_RANGE]          dc_data_odd_wem_hi,   
  input  [`npuarc_DC_ADR_RANGE]             dc_data_odd_addr_hi,  
  input  [`npuarc_DC_DRAM_RANGE]            dc_data_odd_din_hi,
  input                              dc_data_odd_ds_hi,
  input                              dc_data_odd_sd_hi,
  output [`npuarc_DC_DRAM_RANGE]            dc_data_odd_dout_hi,


  
  input                              clk_dccm_bank0_lo,
  input                              clk_dccm_bank0_hi,
  input                              dccm_bank0_cs_lo,  
  input                              dccm_bank0_cs_hi,  
  input  [`npuarc_DCCM_ADR_RANGE]           dccm_bank0_addr_lo,
  input  [`npuarc_DCCM_ADR_RANGE]           dccm_bank0_addr_hi,
  input                              dccm_bank0_we_lo,  
  input                              dccm_bank0_we_hi,  
  input  [`npuarc_DBL_DCCM_RANGE]           dccm_bank0_din,    
  input  [`npuarc_DBL_DCCM_BE_RANGE]        dccm_bank0_wem,    
  input                              dccm_bank0_ds,
  input                              dccm_bank0_sd,
  output [`npuarc_DBL_DCCM_RANGE]           dccm_bank0_dout,

  input                              clk_dccm_bank1_lo,
  input                              clk_dccm_bank1_hi,
  input                              dccm_bank1_cs_lo,  
  input                              dccm_bank1_cs_hi,  
  input  [`npuarc_DCCM_ADR_RANGE]           dccm_bank1_addr_lo,
  input  [`npuarc_DCCM_ADR_RANGE]           dccm_bank1_addr_hi,
  input                              dccm_bank1_we_lo,  
  input                              dccm_bank1_we_hi,  
  input  [`npuarc_DBL_DCCM_RANGE]           dccm_bank1_din,    
  input  [`npuarc_DBL_DCCM_BE_RANGE]        dccm_bank1_wem,    
  input                              dccm_bank1_ds,
  input                              dccm_bank1_sd,
  output [`npuarc_DBL_DCCM_RANGE]           dccm_bank1_dout,



  // NTLB PD0 (tag) ram interface
  input                            ntlb_pd0_clk,
  input                            ntlb_pd0_ce,
  input                            ntlb_pd0_we,
  input  [`npuarc_NTLB_NUM_WAYS_ECC-1:0]  ntlb_pd0_wem,
  input  [`npuarc_NTLB_PD0_ADDR_MSB:0]    ntlb_pd0_addr,
  input  [`npuarc_NTLB_PD0_DATA_MSB:0]    ntlb_pd0_wdata,
  output [`npuarc_NTLB_PD0_DATA_MSB:0]    ntlb_pd0_rdata,

  input                             ntlb_pd0_ds,
  input                             ntlb_pd0_sd,
  input                             ntlb_pd1_ds,
  input                             ntlb_pd1_sd,
  
  // NTLB PD1 (data) ram interface
  input                            ntlb_pd1_clk,
  input                            ntlb_pd1_ce,
  input                            ntlb_pd1_we,
  input  [`npuarc_NTLB_PD1_ADDR_MSB:0]    ntlb_pd1_addr,
  input  [`npuarc_NTLB_PD1_DATA_MSB:0]    ntlb_pd1_wdata,
  output [`npuarc_NTLB_PD1_DATA_MSB:0]    ntlb_pd1_rdata,


  // I/O ports to BPU RAMS 
  input  [`npuarc_BR_BC_DATA_RANGE]        bc_din0,   
  input  [`npuarc_BR_BC_IDX_RANGE]         bc_addr0,  
  input                             bc_me0,    
  input                             bc_we0,    
  input  [`npuarc_BR_BC_DATA_RANGE]        bc_wem0,   
  input                             bc_ds0,
  input                             bc_sd0,
  output [`npuarc_BR_BC_DATA_RANGE]        bc_dout0,  

  input  [`npuarc_BR_PT_DATA_RANGE]                      gs_din0,   
  input  [`npuarc_BR_PT_RANGE]             gs_addr0,  
  input                             gs_me0,    
  input                             gs_we0,    
  input  [`npuarc_BR_PT_DATA_RANGE]                      gs_wem0,   
  input                             gs_ds0,
  input                             gs_sd0,
  output  [`npuarc_BR_PT_DATA_RANGE]                     gs_dout0,  
  input                             bc_ram0_clk,
  input                             pt_ram0_clk,

  input  [`npuarc_BR_BC_DATA_RANGE]        bc_din1,
  input  [`npuarc_BR_BC_IDX_RANGE]         bc_addr1,
  input                             bc_me1,
  input                             bc_we1,
  input  [`npuarc_BR_BC_DATA_RANGE]        bc_wem1,
  input                             bc_ds1,
  input                             bc_sd1,
  output  [`npuarc_BR_BC_DATA_RANGE]       bc_dout1,


  input  [`npuarc_BR_PT_DATA_RANGE]                      gs_din1,
  input  [`npuarc_BR_PT_RANGE]             gs_addr1,
  input                             gs_me1,
  input                             gs_we1,
  input  [`npuarc_BR_PT_DATA_RANGE]                      gs_wem1,
  input                             gs_ds1,
  input                             gs_sd1,
  output  [`npuarc_BR_PT_DATA_RANGE]                     gs_dout1,
  input                             bc_ram1_clk,
  input                             pt_ram1_clk,
  
//  input                             imem_clk,
// spyglass disable_block W240
// SMD: Signal declared but not used
// SJ:  not used in all configs

  input                             test_mode,  // configure ram bypass mux if SCANTEST_RAM_BYPASS_MUX switch on

  input                             clk,
// spyglass enable_block W240
  input                             ls  
);

// spyglass disable_block Setup_blackbox01 ErrorAnalyzeBBox SYNTH_5064 Ac_unsync01
// SMD: Port coverage for black-box
// SMD: UnsynthesizedDU: Design Unit not synthesizable
// SMD: ASSERT statements unsynthesizble
// SMD: unsynchronized crossing: destination blackbox 
// SJ:  rams blackbox for spyglass
// SJ:  Assert statements to check and fail tests, not mean to be synthesized

// Allows ability to configure mux to bypass memory

// Instruction Cache RAM bypass
  
  











    
`define CC_TOP     mptb_top.imptb_sys.iarchipelago.ihs_cluster_top.icc_top



    
//////////////////////////////////////////////////////////////////////////////
// Module instantiation - Instruction Cache RAM wrappers                    //
//////////////////////////////////////////////////////////////////////////////

npuarc_ic_data_ram u_ic_data_ram0 (
  .clk              (ic_data_bank0_clk  ),
  .din              (ic_data_din0 ),
  .addr             (ic_data_addr0),
  .cs               (ic_data_ce0  ),
  .we               (ic_data_we0  ),
  .wem              (ic_data_wem0 ),
  .ds               (ic_data_ds0  ),
  .sd               (ic_data_sd0  ),
  .ls               (ls            ),
    .dout             (ic_data_dout0)
   );


npuarc_ic_data_ram u_ic_data_ram1 (
  .clk              (ic_data_bank1_clk  ),
  .din              (ic_data_din1 ),
  .addr             (ic_data_addr1),
  .cs               (ic_data_ce1  ),
  .we               (ic_data_we1  ),
  .wem              (ic_data_wem1 ),
  .ds               (ic_data_ds1  ),
  .sd               (ic_data_sd1  ),
  .ls               (ls            ),
    .dout             (ic_data_dout1)
   );


npuarc_ic_tag_ram  u_ic_tag_ram0 (
  .clk              (ic_tag_way0_clk  ),
  .din              (ic_tag_din0  ),
  .addr             (ic_tag_addr0 ),
  .cs               (ic_tag_ce0   ),
  .we               (ic_tag_we0   ),
  .wem              (ic_tag_wem0  ),
  .ds               (ic_tag_ds0   ),
  .sd               (ic_tag_sd0   ),
  .ls               (ls            ),
    .dout             (ic_tag_dout0 )
);

npuarc_ic_tag_ram  u_ic_tag_ram1 (
  .clk              (ic_tag_way1_clk  ),
  .din              (ic_tag_din1  ),
  .addr             (ic_tag_addr1 ),
  .cs               (ic_tag_ce1   ),
  .we               (ic_tag_we1   ),
  .wem              (ic_tag_wem1  ),
  .ds               (ic_tag_ds1   ),
  .sd               (ic_tag_sd1   ),
  .ls               (ls            ),
    .dout             (ic_tag_dout1 )
);

npuarc_ic_tag_ram  u_ic_tag_ram2 (
  .clk              (ic_tag_way2_clk  ),
  .din              (ic_tag_din2  ),
  .addr             (ic_tag_addr2 ),
  .cs               (ic_tag_ce2   ),
  .we               (ic_tag_we2   ),
  .wem              (ic_tag_wem2  ),
  .ds               (ic_tag_ds2   ),
  .sd               (ic_tag_sd2   ),
  .ls               (ls            ),
    .dout             (ic_tag_dout2 )
);

npuarc_ic_tag_ram  u_ic_tag_ram3 (
  .clk              (ic_tag_way3_clk  ),
  .din              (ic_tag_din3  ),
  .addr             (ic_tag_addr3 ),
  .cs               (ic_tag_ce3   ),
  .we               (ic_tag_we3   ),
  .wem              (ic_tag_wem3  ),
  .ds               (ic_tag_ds3   ),
  .sd               (ic_tag_sd3   ),
  .ls               (ls            ),
    .dout             (ic_tag_dout3 )
);




//////////////////////////////////////////////////////////////////////////////
// Module instantiation - Data Cache RAM wrappers                           //
//////////////////////////////////////////////////////////////////////////////
npuarc_dc_tag_ram  u_dc_tag_ram_even_way0 (
  .clk              (clk_tag_even_w0    ),
  .din              (dc_tag_even_din_w0 ),
    .dout             (dc_tag_even_dout_w0),
  .addr             (dc_tag_even_addr_w0),
  .cs               (dc_tag_even_cs_w0  ),
  .we               (dc_tag_even_we_w0  ),
  .ds               (dc_tag_even_ds_w0  ),
  .sd               (dc_tag_even_sd_w0  ),
  .ls               (ls                  ),
  .wem              (dc_tag_even_wem_w0 )
);


npuarc_dc_tag_ram  u_dc_tag_ram_odd_way0 (
  .clk              (clk_tag_odd_w0    ),
  .din              (dc_tag_odd_din_w0 ),
    .dout             (dc_tag_odd_dout_w0),
  .addr             (dc_tag_odd_addr_w0),
  .cs               (dc_tag_odd_cs_w0  ),
  .we               (dc_tag_odd_we_w0  ),
  .ds               (dc_tag_odd_ds_w0  ),
  .sd               (dc_tag_odd_sd_w0  ),
  .ls               (ls                 ),
  .wem              (dc_tag_odd_wem_w0 )
);

npuarc_dc_tag_ram  u_dc_tag_ram_even_way1 (
  .clk              (clk_tag_even_w1    ),
  .din              (dc_tag_even_din_w1 ),
    .dout             (dc_tag_even_dout_w1),
  .addr             (dc_tag_even_addr_w1),
  .cs               (dc_tag_even_cs_w1  ),
  .we               (dc_tag_even_we_w1  ),
  .ds               (dc_tag_even_ds_w1  ),
  .sd               (dc_tag_even_sd_w1  ),
  .ls               (ls                  ),
  .wem              (dc_tag_even_wem_w1 )
);


npuarc_dc_tag_ram  u_dc_tag_ram_odd_way1 (
  .clk              (clk_tag_odd_w1    ),
  .din              (dc_tag_odd_din_w1 ),
    .dout             (dc_tag_odd_dout_w1),
  .addr             (dc_tag_odd_addr_w1),
  .cs               (dc_tag_odd_cs_w1  ),
  .we               (dc_tag_odd_we_w1  ),
  .ds               (dc_tag_odd_ds_w1  ),
  .sd               (dc_tag_odd_sd_w1  ),
  .ls               (ls                 ),
  .wem              (dc_tag_odd_wem_w1 )
);


npuarc_dc_data_ram u_dc_data_ram_even_lo (
  .clk              (clk_data_even_lo    ),
  .din              (dc_data_even_din_lo ), 
    .dout             (dc_data_even_dout_lo),
  .addr             (dc_data_even_addr_lo),
  .cs               (dc_data_even_cs_lo  ),
  .we               (dc_data_even_we_lo  ),
  .ds               (dc_data_even_ds_lo  ),
  .sd               (dc_data_even_sd_lo  ),
  .ls               (ls                  ),
  .wem              (dc_data_even_wem_lo )
);


npuarc_dc_data_ram u_dc_data_ram_even_hi (
  .clk              (clk_data_even_hi    ),
  .din              (dc_data_even_din_hi ),
    .dout             (dc_data_even_dout_hi),
  .addr             (dc_data_even_addr_hi),
  .cs               (dc_data_even_cs_hi  ),
  .we               (dc_data_even_we_hi  ),
  .ds               (dc_data_even_ds_hi  ),
  .sd               (dc_data_even_sd_hi  ),
  .ls               (ls                  ),
  .wem              (dc_data_even_wem_hi )
);


npuarc_dc_data_ram u_dc_data_ram_odd_lo (
  .clk              (clk_data_odd_lo    ),
  .din              (dc_data_odd_din_lo ),
    .dout             (dc_data_odd_dout_lo),
  .addr             (dc_data_odd_addr_lo),
  .cs               (dc_data_odd_cs_lo  ),
  .we               (dc_data_odd_we_lo  ),
  .ds               (dc_data_odd_ds_lo  ),
  .sd               (dc_data_odd_sd_lo  ),
  .ls               (ls                 ),
  .wem              (dc_data_odd_wem_lo )
);


npuarc_dc_data_ram u_dc_data_ram_odd_hi (
  .clk              (clk_data_odd_hi    ),
  .din              (dc_data_odd_din_hi ),
    .dout             (dc_data_odd_dout_hi),
  .addr             (dc_data_odd_addr_hi),
  .cs               (dc_data_odd_cs_hi  ),
  .we               (dc_data_odd_we_hi  ),
  .ds               (dc_data_odd_ds_hi  ),
  .sd               (dc_data_odd_sd_hi  ),
  .ls               (ls                 ),
  .wem              (dc_data_odd_wem_hi )
);





//////////////////////////////////////////////////////////////////////////////
// Module instantiation - DCCM RAM wrappers                                 //
//////////////////////////////////////////////////////////////////////////////
  

    // Uniform per-bank dccm signals: bank 0.
    wire           uni_dccm_bank0_clk; 
    wire       uni_dccm_bank0_cs;
    wire       uni_dccm_bank0_we;
    wire [`npuarc_DCCM_DRAM_MSB:0]   uni_dccm_bank0_din;
    wire [`npuarc_DCCM_DRAM_MSB:0]   uni_dccm_bank0_dout;
    wire [`npuarc_DCCM_ADR_RANGE]   uni_dccm_bank0_addr;
    wire [`npuarc_DCCM_BE_MSB:0]   uni_dccm_bank0_wem;
    assign uni_dccm_bank0_clk   = clk_dccm_bank0_lo;
    assign uni_dccm_bank0_cs    = dccm_bank0_cs_lo;
    assign uni_dccm_bank0_we    = dccm_bank0_we_lo;
    assign uni_dccm_bank0_din   = dccm_bank0_din[`npuarc_DBL_DCCM_LO_RANGE];
    assign uni_dccm_bank0_addr  = dccm_bank0_addr_lo;
    assign uni_dccm_bank0_wem   = dccm_bank0_wem[`npuarc_DBL_DCCM_BE_LO_RANGE];
    assign dccm_bank0_dout[`npuarc_DBL_DCCM_LO_RANGE]  = uni_dccm_bank0_dout;

    // Uniform per-bank dccm signals: bank 1.
    wire           uni_dccm_bank1_clk; 
    wire       uni_dccm_bank1_cs;
    wire       uni_dccm_bank1_we;
    wire [`npuarc_DCCM_DRAM_MSB:0]   uni_dccm_bank1_din;
    wire [`npuarc_DCCM_DRAM_MSB:0]   uni_dccm_bank1_dout;
    wire [`npuarc_DCCM_ADR_RANGE]   uni_dccm_bank1_addr;
    wire [`npuarc_DCCM_BE_MSB:0]   uni_dccm_bank1_wem;

    assign uni_dccm_bank1_clk   = clk_dccm_bank0_hi;
    assign uni_dccm_bank1_cs    = dccm_bank0_cs_hi;
    assign uni_dccm_bank1_we    = dccm_bank0_we_hi;
    assign uni_dccm_bank1_din   = dccm_bank0_din[`npuarc_DBL_DCCM_HI_RANGE];
    assign uni_dccm_bank1_addr  = dccm_bank0_addr_hi;
    assign uni_dccm_bank1_wem   = dccm_bank0_wem[`npuarc_DBL_DCCM_BE_HI_RANGE];
    assign dccm_bank0_dout[`npuarc_DBL_DCCM_HI_RANGE]  = uni_dccm_bank1_dout;

    // Uniform per-bank dccm signals: bank 2.
    wire           uni_dccm_bank2_clk; 
    wire       uni_dccm_bank2_cs;
    wire       uni_dccm_bank2_we;
    wire [`npuarc_DCCM_DRAM_MSB:0]   uni_dccm_bank2_din;
    wire [`npuarc_DCCM_DRAM_MSB:0]   uni_dccm_bank2_dout;
    wire [`npuarc_DCCM_ADR_RANGE]   uni_dccm_bank2_addr;
    wire [`npuarc_DCCM_BE_MSB:0]   uni_dccm_bank2_wem;
    assign uni_dccm_bank2_clk   = clk_dccm_bank1_lo;
    assign uni_dccm_bank2_cs    = dccm_bank1_cs_lo;
    assign uni_dccm_bank2_we    = dccm_bank1_we_lo;
    assign uni_dccm_bank2_din   = dccm_bank1_din[`npuarc_DBL_DCCM_LO_RANGE];
    assign uni_dccm_bank2_addr  = dccm_bank1_addr_lo;
    assign uni_dccm_bank2_wem   = dccm_bank1_wem[`npuarc_DBL_DCCM_BE_LO_RANGE];
    assign dccm_bank1_dout[`npuarc_DBL_DCCM_LO_RANGE]  = uni_dccm_bank2_dout;

    // Uniform per-bank dccm signals: bank 3.
    wire           uni_dccm_bank3_clk; 
    wire       uni_dccm_bank3_cs;
    wire       uni_dccm_bank3_we;
    wire [`npuarc_DCCM_DRAM_MSB:0]   uni_dccm_bank3_din;
    wire [`npuarc_DCCM_DRAM_MSB:0]   uni_dccm_bank3_dout;
    wire [`npuarc_DCCM_ADR_RANGE]   uni_dccm_bank3_addr;
    wire [`npuarc_DCCM_BE_MSB:0]   uni_dccm_bank3_wem;

    assign uni_dccm_bank3_clk   = clk_dccm_bank1_hi;
    assign uni_dccm_bank3_cs    = dccm_bank1_cs_hi;
    assign uni_dccm_bank3_we    = dccm_bank1_we_hi;
    assign uni_dccm_bank3_din   = dccm_bank1_din[`npuarc_DBL_DCCM_HI_RANGE];
    assign uni_dccm_bank3_addr  = dccm_bank1_addr_hi;
    assign uni_dccm_bank3_wem   = dccm_bank1_wem[`npuarc_DBL_DCCM_BE_HI_RANGE];
    assign dccm_bank1_dout[`npuarc_DBL_DCCM_HI_RANGE]  = uni_dccm_bank3_dout;

// Uniform per-bank dccm instances.
npuarc_dccm_ram u_dccm_ram_lo0 (
    .clk  (uni_dccm_bank0_clk   ),
    .din  (uni_dccm_bank0_din  ),
    .addr  (uni_dccm_bank0_addr  ),
    .cs    (uni_dccm_bank0_cs  ),
    .we    (uni_dccm_bank0_we  ),
    .wem  (uni_dccm_bank0_wem  ),
    .dout  (uni_dccm_bank0_dout  ),
    .ds    (dccm_bank0_ds   ),
    .sd    (dccm_bank0_sd        ),
    .ls    (ls         )
    );
npuarc_dccm_ram u_dccm_ram_hi0 (
    .clk  (uni_dccm_bank1_clk   ),
    .din  (uni_dccm_bank1_din  ),
    .addr  (uni_dccm_bank1_addr  ),
    .cs    (uni_dccm_bank1_cs  ),
    .we    (uni_dccm_bank1_we  ),
    .wem  (uni_dccm_bank1_wem  ),
    .dout  (uni_dccm_bank1_dout  ),
    .ds    (dccm_bank0_ds   ),
    .sd    (dccm_bank0_sd        ),
    .ls    (ls         )
    );



npuarc_dccm_ram u_dccm_ram_lo1 (
    .clk  (uni_dccm_bank2_clk   ),
    .din  (uni_dccm_bank2_din  ),
    .addr  (uni_dccm_bank2_addr  ),
    .cs    (uni_dccm_bank2_cs  ),
    .we    (uni_dccm_bank2_we  ),
    .wem  (uni_dccm_bank2_wem  ),
    .dout  (uni_dccm_bank2_dout  ),
    .ds    (dccm_bank1_ds   ),
    .sd    (dccm_bank1_sd        ),
    .ls    (ls         )
    );
npuarc_dccm_ram u_dccm_ram_hi1 (
    .clk  (uni_dccm_bank3_clk   ),
    .din  (uni_dccm_bank3_din  ),
    .addr  (uni_dccm_bank3_addr  ),
    .cs    (uni_dccm_bank3_cs  ),
    .we    (uni_dccm_bank3_we  ),
    .wem  (uni_dccm_bank3_wem  ),
    .dout  (uni_dccm_bank3_dout  ),
    .ds    (dccm_bank1_ds   ),
    .sd    (dccm_bank1_sd        ),
    .ls    (ls         )
    );





//////////////////////////////////////////////////////////////////////////////
// Module instantiation - MMU NTLB RAM wrappers                             //
//////////////////////////////////////////////////////////////////////////////
  
// NTLB PD0 (tag) ram
//
npuarc_mmu_ntlb_pd0_ram
#(
.RAM_DATA_WIDTH (`npuarc_NTLB_PD0_DATA_WIDTH),
.RAM_ADDR_WIDTH (`npuarc_NTLB_PD0_ADDR_WIDTH),
.RAM_DEPTH      (`npuarc_NTLB_PD0_DEPTH)
)
  u_mmu_ntlb_ram_pd0 (
  .clk              (ntlb_pd0_clk  ),
  .cs               (ntlb_pd0_ce   ),
  .we               (ntlb_pd0_we   ),
  .wem              (ntlb_pd0_wem  ),
  .addr             (ntlb_pd0_addr ),
  .din              (ntlb_pd0_wdata),
  .ds               (ntlb_pd0_ds   ),
  .sd               (ntlb_pd0_sd   ),
  .ls               (ls            ),
  .dout             (ntlb_pd0_rdata)
);


// NTLB PD1 (data) ram
//
npuarc_mmu_ntlb_pd1_ram
#(
.RAM_DATA_WIDTH (`npuarc_NTLB_PD1_DATA_WIDTH),
.RAM_ADDR_WIDTH (`npuarc_NTLB_PD1_ADDR_WIDTH),
.RAM_DEPTH      (`npuarc_NTLB_PD1_DEPTH)
)
  u_mmu_ntlb_ram_pd1 (
  .clk              (ntlb_pd1_clk  ),
  .cs               (ntlb_pd1_ce   ),
  .we               (ntlb_pd1_we   ),
  .addr             (ntlb_pd1_addr ),
  .din              (ntlb_pd1_wdata),
  .ds               (ntlb_pd1_ds   ),
  .sd               (ntlb_pd1_sd   ),
  .ls               (ls            ),
  .dout             (ntlb_pd1_rdata)
);



// instantiate branch cache bank 0

npuarc_bc_ram u0_bc_ram (
  .clk   (bc_ram0_clk),
  .din   (bc_din0),
  .addr  (bc_addr0),
  .cs    (bc_me0),
  .we    (bc_we0),
  .wem   (bc_wem0),
  .ds    (bc_ds0),
  .sd    (bc_sd0),
  .ls    (ls    ),
  .dout  (bc_dout0)
);


// instantiate Gshare RAM bank 0

npuarc_pt_ram u0_pt_ram (
  .clk   (pt_ram0_clk),
  .din   (gs_din0),
  .addr  (gs_addr0),
  .cs    (gs_me0),
  .we    (gs_we0),
  .wem   (gs_wem0),
  .ds    (gs_ds0),
  .sd    (gs_sd0),
  .ls    (ls    ),
  .dout  (gs_dout0)
);


npuarc_bc_ram u1_bc_ram (
  .clk   (bc_ram1_clk),
  .din   (bc_din1),
  .addr  (bc_addr1),
  .cs    (bc_me1),
  .we    (bc_we1),
  .wem   (bc_wem1),
  .ds    (bc_ds1),
  .sd    (bc_sd1),
  .ls    (ls),
  .dout  (bc_dout1)

);


npuarc_pt_ram u1_pt_ram (
  .clk   (pt_ram1_clk),
  .din   (gs_din1),
  .addr  (gs_addr1),
  .cs    (gs_me1),
  .we    (gs_we1),
  .wem   (gs_wem1),
  .ds    (gs_ds1),
  .sd    (gs_sd1),
  .ls    (ls    ),
  .dout  (gs_dout1)
);



// spyglass enable_block Setup_blackbox01 ErrorAnalyzeBBox SYNTH_5064 Ac_unsync01

endmodule // alb_srams   
