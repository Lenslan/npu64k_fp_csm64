// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2013 Synopsys, Inc. All rights reserved.
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
// ######   ######   #######
// #     #  #     #  #
// #     #  #     #  #
// ######   ######   #####
// #        #   #    #
// #        #    #   #
// #        #     #  #######
//
//
//     ######   #######   #####   #######  ######   #######
//     #     #  #        #     #  #     #  #     #  #
//     #     #  #        #        #     #  #     #  #
//     #     #  #####    #        #     #  #     #  #####
//     #     #  #        #        #     #  #     #  #
//     #     #  #        #     #  #     #  #     #  #
//     ######   #######   #####   #######  ######   #######   ########
//    
//    
//     #######     #      #####   #    #   #####
//        #       # #    #     #  #   #   #     #
//        #      #   #   #        #  #    #
//        #     #     #   #####   ###      #####
//        #     #######        #  #  #          #
//        #     #     #  #     #  #   #   #     #
//        #     #     #   #####   #    #   #####
//
// ===========================================================================
//
// Description:
//
//  This file implements a set of instruction decode tasks for the
//  ARCompact instruction set, in order to pre-decode the two read
//  register addresses, the instruction size, and the presence of
//  long-immediate data (LIMM) on each source operand.
//
// ===========================================================================



//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Task to initialize all combinational outputs of the predecode module     //
// to their default, i.e. inactive, values.                                 //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

`deflines init_local_regs_pre_task_m;
begin
  rf_ra0       = 6'd0;    // default register address, port 0
  rf_ra1       = 6'd0;    // default register address, port 1
  is_16bit     = 1'b0;    // by default instruction size is 32 bits
  has_limm     = 1'b0;    // by default inst does not have limm data
  limm_r0      = 1'b0;    // by default port 0 is not a limm data
  limm_r1      = 1'b0;    // by default port 1 is not a limm data
  rf_renb0     = 1'b0;    // by default port 0 is not a valid read
  rf_renb1     = 1'b0;    // by default port 1 is not a valid read
end
`enddeflines


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Register extraction tasks, which also set the register field enable      //
// signals. Only read port controls are decoded by these tasks.             //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

`deflines regs_b_32_pre_task_m;
begin
  rf_ra0   = { inst[14:12], inst[26:24] };
  limm_r0  = (rf_ra0 == 6'd62);
  rf_renb0 = ~limm_r0;
end
`enddeflines

`deflines regs_b_src2_32_pre_task_m;
begin
  rf_ra1   = { inst[14:12], inst[26:24] };
  limm_r1  = (rf_ra1 == 6'd62);
  rf_renb1 = ~limm_r1;
end
`enddeflines

`deflines regs_b_cond_32_pre_task_m;
begin
  rf_ra0   = { inst[14:12], inst[26:24] };
  rf_renb0 = (rf_ra0 != 6'd62);
end
`enddeflines


`deflines regs_c_32_pre_task_m;
begin
  rf_ra1   = inst[11:6];
  limm_r1  = (rf_ra1 == 6'd62);
  rf_renb1 = ~limm_r1;
end
`enddeflines

`deflines regs_c_src1_32_pre_task_m;
begin
  rf_ra0   = inst[11:6];
  limm_r0  = (rf_ra0 == 6'd62);
  rf_renb0 = ~limm_r0;
end
`enddeflines


`deflines regs_c_nl_32_pre_task_m;
begin
  rf_ra1   = inst[11:6];
  limm_r1  = 1'b0;
  rf_renb1 = 1'b1;
end
`enddeflines


`deflines regs_bc_32_pre_task_m;
begin
  `npuarc_regs_b_32_pre_task_m;
  `npuarc_regs_c_32_pre_task_m;
end
`enddeflines

`deflines regs_cb_32_pre_task_m;
begin
  `npuarc_regs_b_src2_32_pre_task_m;
  `npuarc_regs_c_src1_32_pre_task_m;
end
`enddeflines


`deflines regs_b_src1_16_pre_task_m;
begin
  rf_ra0   = { 2'b00, inst[26], inst[26:24] };
  rf_renb0 = 1'b1;
end
`enddeflines


`deflines regs_b_src2_16_pre_task_m;
begin
  rf_ra1   = { 2'b00, inst[26], inst[26:24] };
  rf_renb1 = 1'b1;
end
`enddeflines


`deflines regs_c_src2_16_pre_task_m;
begin
  rf_ra1   = { 2'b00, inst[23], inst[23:21] };
  rf_renb1 = 1'b1;
end
`enddeflines


`deflines regs_bc_16_pre_task_m;
begin
  `npuarc_regs_b_src1_16_pre_task_m;
  `npuarc_regs_c_src2_16_pre_task_m;
end
`enddeflines


`deflines regs_h_src1_16_a6k_pre_task_m;
begin
  rf_ra0   = { 1'b0, inst[17:16], inst[23:21] };
  limm_r0  = (rf_ra0[4:0] == 5'd30);
  rf_renb0 = ~limm_r0;
end
`enddeflines


`deflines regs_h_src2_16_a6k_pre_task_m;
begin
  rf_ra1   = { 1'b0, inst[17:16], inst[23:21] };
  limm_r1  = (rf_ra1[4:0] == 5'd30);
  rf_renb1 = ~limm_r1;
end
`enddeflines


`deflines regs_bh_16_a6k_pre_task_m;
begin
  `npuarc_regs_b_src1_16_pre_task_m;
  `npuarc_regs_h_src2_16_a6k_pre_task_m;
end
`enddeflines


`deflines regs_ilinkp0_pre_task_m;
begin
  rf_ra0   = 6'd29;
  rf_renb0 = 1'b1;
end
`enddeflines


`deflines regs_sp_src1_pre_task_m;
begin
  rf_ra0   = 6'd28;
  rf_renb0 = 1'b1;
end
`enddeflines


`deflines regs_gp_r01_src1_pre_task_m;
begin
  rf_ra0   = 6'd26;     // GP register
  rf_renb0 = 1'b1;      // always read GP register
  rf_ra1   = 6'd0;      // possible store data from R0
  rf_renb1 = inst[20];  // read reg1 if st_s r0,[gp,s11]
end
`enddeflines


`deflines regs_gp_src1_pre_task_m;
begin
  rf_ra0   = 6'd26;   // GP register
  rf_renb0 = 1'b1;    // always read GP register
end
`enddeflines


`deflines regs_pcl_src1_pre_task_m;
begin
  rf_ra0   = 6'd63;
  rf_renb0 = 1'b1;
end
`enddeflines


`deflines regs_blink_src1_pre_task_m;
begin
  rf_ra0   = 6'd31;
  rf_renb0 = 1'b1;
end
`enddeflines

`deflines regs_blink_src2_pre_task_m;
begin
  rf_ra1   = 6'd31;
  rf_renb1 = inst[26]; // exclude nop_s and swi_s
end
`enddeflines


`deflines push_16_pre_task_m;
begin
  rf_renb1 = 1'b1;
  if ( inst[20:16] == 5'd1 )
    rf_ra1 = { 2'd0, inst[26], inst[26:24] };
  else if (inst[20:16] == 5'd17)
    rf_ra1 = 6'd31;
end
`enddeflines
