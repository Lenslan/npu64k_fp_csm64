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
// Certain materials incorporated herein are copyright (C) 2010 - 2013, The
// University Court of the University of Edinburgh. All Rights Reserved.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
//  #     #  ######   #     #  
//  ##   ##  #     #  #     #  
//  # # # #  #     #  #     #  
//  #  #  #  ######   #     #  
//  #     #  #        #     #  
//  #     #  #        #     #  
//  #     #  #         #####   
//
// ===========================================================================
//
// Description:
//
//  This module implements the configurable MPU of the ARCv2HS CPU.
//
// ==========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

`include "const.def"

module npuarc_alb_mpu (

  // General input signals
  //
  input                       clk,                  // clock
  input                       rst_a,                // asynchronous reset
  input                       kernel_mode,          // has Kernel mode privileges
  input                       db_active,            //
  input                       mmu_en_r,
  output reg                  mpu_en_r,
  input                       x2_fa0_transl,
  input                       x2_da0_transl,

  // SA Stage
  input                       sa_pass,              //
  input      [`npuarc_PC_RANGE]      sa_pc_r,              // (SA) PC 

  // X1 Stage
  input                       x1_pass,              //
  input                       x1_enable,            //

  // X2 Stage
  input                       x2_pass,              //
  input                       x2_enable,            //
  input                       x2_kill,              //
  input                       x2_uop_inst_r,        // X2 is a multi-op insn.
  input                       x2_load_r,            // 
  input                       x2_store_r,           // 
  input                       x2_pref_r,
  input      [`npuarc_ADDR_RANGE]    x2_mem_addr0_r,       // (X2) memory address
  output reg                  x2_mpu_data_flt,      // 

  // X3 Stage
  input                       x3_pass,              //
  input                       x3_enable,            // 
  output reg                  mpu_exec_viol_r,      // (X3) Fetch violation
  output reg                  mpu_data_viol_r,      // (X3) Data violation
  output reg [`npuarc_ADDR_RANGE]    mpu_efa_r,            // (X3) EFA register value

  // CA Stage
  input                       ca_enable,            // 
  input                       ca_mpu_excpn_r,       // MPU Exception
  input                       ca_uop_inprol_r,      // (CA) Prologue Sequence
  input                       excpn_prologue_evt,
  input                       excpn_in_prologue_r,

  // MPU interface for IFU
  input      [`npuarc_PC_RGN_RANGE]  ifetch_addr_mpu,      // fetch address from IFU
  output reg                  ifetch_viol,          // execute permission violation

  input                       irq_u_act,            // Snapshot of the STATUS32.U bit when an interrupt is taken
                                                    // when Active[15:0] == 0
  input [`npuarc_IRQ_ACT_ACT_RANGE]  irq_act_nxt,          // IRQ Active next
  input                       irq_u_ctrl,           // Indicates if user context is saved to user stack
  input [`npuarc_INTEVT_RANGE]       int_evts,             // Interrupt State
  input                       ca_rtie_op_r,         // RTIE at commit stage

  // Aux Write Interface
  input                       aux_mpu_wen_r,        // Aux Write En
  input      [6:0]            aux_mpu_waddr_r,      // Aux write address
  input      [`npuarc_DATA_RANGE]    wa_sr_data_r,         // Aux write data
  input                       aux_mpu_ren_r,        // Aux Read En
  input      [6:0]            aux_mpu_raddr_r,      // Aux Read address
  input                       aux_write,            // Aux write op
  output reg [`npuarc_DATA_RANGE]    mpu_aux_rdata,        // Aux Read Data
  output reg                  mpu_aux_illegal,      // SR/LR op is illegal
  output reg                  mpu_aux_k_rd,         // op needs Kernel R perm
  output reg                  mpu_aux_k_wr,         // op needs Kernel W perm
  output reg                  mpu_aux_unimpl,       // LR/SR reg is not present
  output reg                  mpu_aux_serial_sr,    // SR must serialize
  output reg                  mpu_aux_strict_sr     // SR must serialize

);

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Auxiliary registers, next state, select and write enable signals       //
//                                                                        //
// With a few exceptions, all auxiliary registers are dealt with in a     //
// regular form. For each aux reg, there are a number of flip-flops       //
// to hold the required bits, a next state wire or reg signal that has    //
// the updating value, a select signal decoded from the 12-bit base aux   //
// address on a pending SR op, and a write enable signal that allows      //
// the update to the register content.                                    //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
reg                           mpu_en_ue_r;    // default user execute perm.
reg                           mpu_en_uw_r;    // default user write perm.
reg                           mpu_en_urd_r;   // default user read perm.
reg                           mpu_en_ke_r;    // default kernel execute perm.
reg                           mpu_en_kw_r;    // default kernel write perm.
reg                           mpu_en_krd_r;   // default krenel read perm.
reg                           mpu_en_en;      // MPU_EN write enable

reg       [`npuarc_MPU_ECR_MR_RANGE] mpu_ecr_mr_r;   // MPU_ECR.MR field
reg       [`npuarc_MPU_ECR_VT_RANGE] mpu_ecr_vt_r;   // MPU_ECR.VT field
reg       [`npuarc_MPU_ECR_MR_RANGE] mpu_ecr_mr_nxt; // next MPU_ECR.MR field
reg       [`npuarc_MPU_ECR_VT_RANGE] mpu_ecr_vt_nxt; // next MPU_ECR.VT field

reg       [`npuarc_MPU_ECR_MR_RANGE] x3_ecr_mr_r;    // speculative MPU_ECR.MR field
reg       [`npuarc_MPU_ECR_VT_RANGE] x3_ecr_vt_r;    // speculative MPU_ECR.VT field
reg       [`npuarc_MPU_ECR_MR_RANGE] x3_ecr_mr_nxt;  // next spec. MPU_ECR.MR
reg       [`npuarc_MPU_ECR_VT_RANGE] x3_ecr_vt_nxt;  // next spec. MPU_ECR.VT field

reg       [`npuarc_MPU_ECR_MR_RANGE] ca_ecr_mr_r;    // speculative MPU_ECR.MR field
reg       [`npuarc_MPU_ECR_VT_RANGE] ca_ecr_vt_r;    // speculative MPU_ECR.VT field
reg                           ca_cg0;         // ca stage


reg       [`npuarc_RDB_BASE_RANGE]   rdb0_base_r;
reg                           rdb0_v_r;
reg                           mpu_rdb0_en;
//
reg       [`npuarc_RDP_SIZE_RANGE]   rdp0_size_r;
reg                           rdp0_ue_r;
reg                           rdp0_uw_r;
reg                           rdp0_urd_r;
reg                           rdp0_ke_r;
reg                           rdp0_kw_r;
reg                           rdp0_krd_r;
reg                           mpu_rdp0_en;

reg       [`npuarc_RDB_BASE_RANGE]   rdb1_base_r;
reg                           rdb1_v_r;
reg                           mpu_rdb1_en;
//
reg       [`npuarc_RDP_SIZE_RANGE]   rdp1_size_r;
reg                           rdp1_ue_r;
reg                           rdp1_uw_r;
reg                           rdp1_urd_r;
reg                           rdp1_ke_r;
reg                           rdp1_kw_r;
reg                           rdp1_krd_r;
reg                           mpu_rdp1_en;

reg       [`npuarc_RDB_BASE_RANGE]   rdb2_base_r;
reg                           rdb2_v_r;
reg                           mpu_rdb2_en;
//
reg       [`npuarc_RDP_SIZE_RANGE]   rdp2_size_r;
reg                           rdp2_ue_r;
reg                           rdp2_uw_r;
reg                           rdp2_urd_r;
reg                           rdp2_ke_r;
reg                           rdp2_kw_r;
reg                           rdp2_krd_r;
reg                           mpu_rdp2_en;

reg       [`npuarc_RDB_BASE_RANGE]   rdb3_base_r;
reg                           rdb3_v_r;
reg                           mpu_rdb3_en;
//
reg       [`npuarc_RDP_SIZE_RANGE]   rdp3_size_r;
reg                           rdp3_ue_r;
reg                           rdp3_uw_r;
reg                           rdp3_urd_r;
reg                           rdp3_ke_r;
reg                           rdp3_kw_r;
reg                           rdp3_krd_r;
reg                           mpu_rdp3_en;

reg       [`npuarc_RDB_BASE_RANGE]   rdb4_base_r;
reg                           rdb4_v_r;
reg                           mpu_rdb4_en;
//
reg       [`npuarc_RDP_SIZE_RANGE]   rdp4_size_r;
reg                           rdp4_ue_r;
reg                           rdp4_uw_r;
reg                           rdp4_urd_r;
reg                           rdp4_ke_r;
reg                           rdp4_kw_r;
reg                           rdp4_krd_r;
reg                           mpu_rdp4_en;

reg       [`npuarc_RDB_BASE_RANGE]   rdb5_base_r;
reg                           rdb5_v_r;
reg                           mpu_rdb5_en;
//
reg       [`npuarc_RDP_SIZE_RANGE]   rdp5_size_r;
reg                           rdp5_ue_r;
reg                           rdp5_uw_r;
reg                           rdp5_urd_r;
reg                           rdp5_ke_r;
reg                           rdp5_kw_r;
reg                           rdp5_krd_r;
reg                           mpu_rdp5_en;

reg       [`npuarc_RDB_BASE_RANGE]   rdb6_base_r;
reg                           rdb6_v_r;
reg                           mpu_rdb6_en;
//
reg       [`npuarc_RDP_SIZE_RANGE]   rdp6_size_r;
reg                           rdp6_ue_r;
reg                           rdp6_uw_r;
reg                           rdp6_urd_r;
reg                           rdp6_ke_r;
reg                           rdp6_kw_r;
reg                           rdp6_krd_r;
reg                           mpu_rdp6_en;

reg       [`npuarc_RDB_BASE_RANGE]   rdb7_base_r;
reg                           rdb7_v_r;
reg                           mpu_rdb7_en;
//
reg       [`npuarc_RDP_SIZE_RANGE]   rdp7_size_r;
reg                           rdp7_ue_r;
reg                           rdp7_uw_r;
reg                           rdp7_urd_r;
reg                           rdp7_ke_r;
reg                           rdp7_kw_r;
reg                           rdp7_krd_r;
reg                           mpu_rdp7_en;

reg       [`npuarc_MPU_REGION_RANGE] mask_diff_r;    // 1 => pending mask update
reg       [`npuarc_MPU_REGION_RANGE] mask_diff_nxt;  // next mask_diff_r value
reg                           mask_diff_en;   // enable write to mask_diff_r

reg       [`npuarc_RDP_SIZE_RANGE]   new_size_r;     // newly-assigned size 
reg                           new_size_en;    // enable write to new_size_r


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Local registers and wires                                              //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

reg     [`npuarc_RDB_BASE_RANGE]     addr_mask0_r;
reg     [`npuarc_RDB_BASE_RANGE]     addr_mask1_r;
reg     [`npuarc_RDB_BASE_RANGE]     addr_mask2_r;
reg     [`npuarc_RDB_BASE_RANGE]     addr_mask3_r;
reg     [`npuarc_RDB_BASE_RANGE]     addr_mask4_r;
reg     [`npuarc_RDB_BASE_RANGE]     addr_mask5_r;
reg     [`npuarc_RDB_BASE_RANGE]     addr_mask6_r;
reg     [`npuarc_RDB_BASE_RANGE]     addr_mask7_r;
reg     [`npuarc_RDB_BASE_RANGE]     addr_mask_nxt;
// leda NTL_CON13A off
// LMD: non driving internal net Range
// LJ:  Not all bits of bus used

wire    [`npuarc_DATA_RANGE]         base_mask_4;
wire    [`npuarc_DATA_RANGE]         base_mask_5;
wire    [`npuarc_DATA_RANGE]         base_mask_6;
wire    [`npuarc_DATA_RANGE]         base_mask_7;
wire    [`npuarc_DATA_RANGE]         base_mask_8;
wire    [`npuarc_DATA_RANGE]         base_mask_9;
wire    [`npuarc_DATA_RANGE]         base_mask_10;
wire    [`npuarc_DATA_RANGE]         base_mask_11;
wire    [`npuarc_DATA_RANGE]         base_mask_12;
wire    [`npuarc_DATA_RANGE]         base_mask_13;
wire    [`npuarc_DATA_RANGE]         base_mask_14;
wire    [`npuarc_DATA_RANGE]         base_mask_15;
wire    [`npuarc_DATA_RANGE]         base_mask_16;
wire    [`npuarc_DATA_RANGE]         base_mask_17;
wire    [`npuarc_DATA_RANGE]         base_mask_18;
wire    [`npuarc_DATA_RANGE]         base_mask_19;
wire    [`npuarc_DATA_RANGE]         base_mask_20;
wire    [`npuarc_DATA_RANGE]         base_mask_21;
wire    [`npuarc_DATA_RANGE]         base_mask_22;
wire    [`npuarc_DATA_RANGE]         base_mask_23;
wire    [`npuarc_DATA_RANGE]         base_mask_24;
wire    [`npuarc_DATA_RANGE]         base_mask_25;
wire    [`npuarc_DATA_RANGE]         base_mask_26;
wire    [`npuarc_DATA_RANGE]         base_mask_27;
wire    [`npuarc_DATA_RANGE]         base_mask_28;
wire    [`npuarc_DATA_RANGE]         base_mask_29;
wire    [`npuarc_DATA_RANGE]         base_mask_30;
wire    [`npuarc_DATA_RANGE]         base_mask_31;
// leda NTL_CON13A on
reg                           int_kernel_mode;
reg                           d_kernel_mode; // Kernel mode privileges for data (rw) oper
reg     [`npuarc_RDB_RGN_RANGE]      fetch_addr;
reg     [`npuarc_RDB_RGN_RANGE]      data_addr;
reg     [`npuarc_MPU_REGION_RANGE]   e_perms;
reg     [`npuarc_MPU_REGION_RANGE]   w_perms;
reg     [`npuarc_MPU_REGION_RANGE]   r_perms;
reg                           e_default;
reg                           w_default;
reg                           r_default;

reg                           irq_epil_kmode_r;
reg                           irq_epil_kmode_n;
reg                           irq_epil_kmode_g;

reg     [`npuarc_MPU_REGION_RANGE]   ifetch_perms;
reg     [`npuarc_RDB_RGN_RANGE]      ifetch_addr;
reg                           ifetch_default;
reg     [`npuarc_MPU_REGION_RANGE]   ifetch_hit;

reg                           valid_ifetch;
reg     [`npuarc_MPU_REGION_RANGE]   ihit;
reg                           valid_fetch;
reg                           valid_data_access;
reg                           valid_load_access;
reg                           valid_store_access;
reg     [`npuarc_MPU_REGION_RANGE]   dhit;

reg                           exec_v;
reg                           data_v;
reg     [`npuarc_MPU_ECR_MR_RANGE]   exec_mr;
reg     [`npuarc_MPU_ECR_MR_RANGE]   data_mr;

reg     [`npuarc_PC_RANGE]           x1_pc_r;          // X1 stage PC
reg     [`npuarc_PC_RANGE]           x2_pc_r;          // X2 stage PC

reg                           x1_pc_cg0;        // X1 stage 
reg                           x2_pc_cg0;        // X2 stage
reg                           x3_pc_cg0;        // X3 stage
reg                           x3_me_cg0;        // X3 stage
reg                           x3_md_cg0;        // X3 stage

reg                           mpu_exec_viol;    // (X2) Execute violation
reg                           mpu_data_viol;    // (X2) Data violation
reg     [`npuarc_ADDR_RANGE]         mpu_efa_nxt;      // (X2) EFA register value



////////////////////////////////////////////////////////////////////////////
//                                                                        //
// States for the MPU exception-reporting state machine                   //
//                                                                        //
////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// MPU_ECR field values                                                   //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

parameter MPU_ECR_VT_EXECV        =  2'b00;     // Execute violation

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Mask values for MPU_RDP.BASE                                           //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

parameter RDP_BASE_MASK_4         =  32'hffffffe0; //  32b region mask
parameter RDP_BASE_MASK_5         =  32'hffffffc0; //  64b region mask
parameter RDP_BASE_MASK_6         =  32'hffffff80; // 128b region mask
parameter RDP_BASE_MASK_7         =  32'hffffff00; // 256b region mask
parameter RDP_BASE_MASK_8         =  32'hfffffe00; // 512b region mask
parameter RDP_BASE_MASK_9         =  32'hfffffc00; //   1k region mask
parameter RDP_BASE_MASK_10        =  32'hfffff800; //   2k region mask
parameter RDP_BASE_MASK_11        =  32'hfffff000; //   4k region mask
parameter RDP_BASE_MASK_12        =  32'hffffe000; //   8k region mask
parameter RDP_BASE_MASK_13        =  32'hffffc000; //  16k region mask
parameter RDP_BASE_MASK_14        =  32'hffff8000; //  32k region mask
parameter RDP_BASE_MASK_15        =  32'hffff0000; //  64k region mask
parameter RDP_BASE_MASK_16        =  32'hfffe0000; // 128k region mask
parameter RDP_BASE_MASK_17        =  32'hfffc0000; // 256k region mask
parameter RDP_BASE_MASK_18        =  32'hfff80000; // 512k region mask
parameter RDP_BASE_MASK_19        =  32'hfff00000; //   1M region mask
parameter RDP_BASE_MASK_20        =  32'hffe00000; //   2M region mask
parameter RDP_BASE_MASK_21        =  32'hffc00000; //   4M region mask
parameter RDP_BASE_MASK_22        =  32'hff800000; //   8M region mask
parameter RDP_BASE_MASK_23        =  32'hff000000; //  16M region mask
parameter RDP_BASE_MASK_24        =  32'hfe000000; //  32M region mask
parameter RDP_BASE_MASK_25        =  32'hfc000000; //  64M region mask
parameter RDP_BASE_MASK_26        =  32'hf8000000; // 128M region mask
parameter RDP_BASE_MASK_27        =  32'hf0000000; // 256M region mask
parameter RDP_BASE_MASK_28        =  32'he0000000; // 512M region mask
parameter RDP_BASE_MASK_29        =  32'hc0000000; //   1G region mask
parameter RDP_BASE_MASK_30        =  32'h80000000; //   2G region mask
parameter RDP_BASE_MASK_31        =  32'h00000000; //   4G region mask

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Assign const vectors from which base mask sub-fields can be extracted  //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

assign base_mask_4 =  RDP_BASE_MASK_4;
assign base_mask_5 =  RDP_BASE_MASK_5;
assign base_mask_6 =  RDP_BASE_MASK_6;
assign base_mask_7 =  RDP_BASE_MASK_7;
assign base_mask_8 =  RDP_BASE_MASK_8;
assign base_mask_9 =  RDP_BASE_MASK_9;
assign base_mask_10 =  RDP_BASE_MASK_10;
assign base_mask_11 =  RDP_BASE_MASK_11;
assign base_mask_12 =  RDP_BASE_MASK_12;
assign base_mask_13 =  RDP_BASE_MASK_13;
assign base_mask_14 =  RDP_BASE_MASK_14;
assign base_mask_15 =  RDP_BASE_MASK_15;
assign base_mask_16 =  RDP_BASE_MASK_16;
assign base_mask_17 =  RDP_BASE_MASK_17;
assign base_mask_18 =  RDP_BASE_MASK_18;
assign base_mask_19 =  RDP_BASE_MASK_19;
assign base_mask_20 =  RDP_BASE_MASK_20;
assign base_mask_21 =  RDP_BASE_MASK_21;
assign base_mask_22 =  RDP_BASE_MASK_22;
assign base_mask_23 =  RDP_BASE_MASK_23;
assign base_mask_24 =  RDP_BASE_MASK_24;
assign base_mask_25 =  RDP_BASE_MASK_25;
assign base_mask_26 =  RDP_BASE_MASK_26;
assign base_mask_27 =  RDP_BASE_MASK_27;
assign base_mask_28 =  RDP_BASE_MASK_28;
assign base_mask_29 =  RDP_BASE_MASK_29;
assign base_mask_30 =  RDP_BASE_MASK_30;
assign base_mask_31 =  RDP_BASE_MASK_31;

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Decode next base address mask value from new_size_r                    //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : mask_PROC

  case (new_size_r)
  `npuarc_RDP_SIZE_BITS'd5: addr_mask_nxt = base_mask_5[`npuarc_RDB_RGN_RANGE];
  `npuarc_RDP_SIZE_BITS'd6: addr_mask_nxt = base_mask_6[`npuarc_RDB_RGN_RANGE];
  `npuarc_RDP_SIZE_BITS'd7: addr_mask_nxt = base_mask_7[`npuarc_RDB_RGN_RANGE];
  `npuarc_RDP_SIZE_BITS'd8: addr_mask_nxt = base_mask_8[`npuarc_RDB_RGN_RANGE];
  `npuarc_RDP_SIZE_BITS'd9: addr_mask_nxt = base_mask_9[`npuarc_RDB_RGN_RANGE];
  `npuarc_RDP_SIZE_BITS'd10: addr_mask_nxt = base_mask_10[`npuarc_RDB_RGN_RANGE];
  `npuarc_RDP_SIZE_BITS'd11: addr_mask_nxt = base_mask_11[`npuarc_RDB_RGN_RANGE];
  `npuarc_RDP_SIZE_BITS'd12: addr_mask_nxt = base_mask_12[`npuarc_RDB_RGN_RANGE];
  `npuarc_RDP_SIZE_BITS'd13: addr_mask_nxt = base_mask_13[`npuarc_RDB_RGN_RANGE];
  `npuarc_RDP_SIZE_BITS'd14: addr_mask_nxt = base_mask_14[`npuarc_RDB_RGN_RANGE];
  `npuarc_RDP_SIZE_BITS'd15: addr_mask_nxt = base_mask_15[`npuarc_RDB_RGN_RANGE];
  `npuarc_RDP_SIZE_BITS'd16: addr_mask_nxt = base_mask_16[`npuarc_RDB_RGN_RANGE];
  `npuarc_RDP_SIZE_BITS'd17: addr_mask_nxt = base_mask_17[`npuarc_RDB_RGN_RANGE];
  `npuarc_RDP_SIZE_BITS'd18: addr_mask_nxt = base_mask_18[`npuarc_RDB_RGN_RANGE];
  `npuarc_RDP_SIZE_BITS'd19: addr_mask_nxt = base_mask_19[`npuarc_RDB_RGN_RANGE];
  `npuarc_RDP_SIZE_BITS'd20: addr_mask_nxt = base_mask_20[`npuarc_RDB_RGN_RANGE];
  `npuarc_RDP_SIZE_BITS'd21: addr_mask_nxt = base_mask_21[`npuarc_RDB_RGN_RANGE];
  `npuarc_RDP_SIZE_BITS'd22: addr_mask_nxt = base_mask_22[`npuarc_RDB_RGN_RANGE];
  `npuarc_RDP_SIZE_BITS'd23: addr_mask_nxt = base_mask_23[`npuarc_RDB_RGN_RANGE];
  `npuarc_RDP_SIZE_BITS'd24: addr_mask_nxt = base_mask_24[`npuarc_RDB_RGN_RANGE];
  `npuarc_RDP_SIZE_BITS'd25: addr_mask_nxt = base_mask_25[`npuarc_RDB_RGN_RANGE];
  `npuarc_RDP_SIZE_BITS'd26: addr_mask_nxt = base_mask_26[`npuarc_RDB_RGN_RANGE];
  `npuarc_RDP_SIZE_BITS'd27: addr_mask_nxt = base_mask_27[`npuarc_RDB_RGN_RANGE];
  `npuarc_RDP_SIZE_BITS'd28: addr_mask_nxt = base_mask_28[`npuarc_RDB_RGN_RANGE];
  `npuarc_RDP_SIZE_BITS'd29: addr_mask_nxt = base_mask_29[`npuarc_RDB_RGN_RANGE];
  `npuarc_RDP_SIZE_BITS'd30: addr_mask_nxt = base_mask_30[`npuarc_RDB_RGN_RANGE];
  `npuarc_RDP_SIZE_BITS'd31: addr_mask_nxt = base_mask_31[`npuarc_RDB_RGN_RANGE];
  default: addr_mask_nxt = base_mask_4[`npuarc_RDB_RGN_RANGE];
  endcase

end // block : mask_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Asynchronous logic for selecting aux register values for LR and SR     //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : mpu_aux_ren_PROC

  //////////////////////////////////////////////////////////////////////////
  // Gate the aux_wdata signals with the SR operation control signal
  // to minimize spurious transitions when not performing SR operations.
  //

  mpu_aux_rdata     = `npuarc_DATA_SIZE'd0;
  mpu_aux_k_rd      = 1'b0;
  mpu_aux_k_wr      = 1'b0;
  mpu_aux_unimpl    = 1'b1;
  mpu_aux_illegal   = 1'b0;
  mpu_aux_strict_sr = 1'b0;
  mpu_aux_serial_sr = 1'b0;

  if (aux_mpu_ren_r == 1'b1)
  begin
    
    case ({5'h08, aux_mpu_raddr_r})

      `npuarc_MPU_EN_AUX:     // K_RW
      begin
        mpu_aux_rdata[`npuarc_MPU_EN_BIT]     = mpu_en_r;
        mpu_aux_rdata[`npuarc_MPU_EN_E_BIT]   = mpu_en_ue_r;
        mpu_aux_rdata[`npuarc_MPU_EN_W_BIT]   = mpu_en_uw_r;
        mpu_aux_rdata[`npuarc_MPU_EN_RD_BIT]  = mpu_en_urd_r;
        mpu_aux_rdata[`npuarc_MPU_EN_UE_BIT]  = mpu_en_ke_r;
        mpu_aux_rdata[`npuarc_MPU_EN_UW_BIT]  = mpu_en_kw_r;
        mpu_aux_rdata[`npuarc_MPU_EN_URD_BIT] = mpu_en_krd_r;
        mpu_aux_unimpl                 = 1'b0;
        mpu_aux_k_rd                   = 1'b1;
        mpu_aux_k_wr                   = 1'b1;
        mpu_aux_strict_sr              = aux_write;

      end
      
      `npuarc_MPU_ECR_AUX:    // K
      begin
        mpu_aux_rdata               = {   8'd0,                       // 31-24
                                            `npuarc_EV_PROT_V,               // 23-16
                                            6'd0,                     // 15-10
                                            mpu_ecr_vt_r,             // 9-8
                                            {4{mpu_ecr_mr_r[3]}},   // 7-
                                            mpu_ecr_mr_r              //  -0
                                        };
        mpu_aux_unimpl                = 1'b0;
        mpu_aux_k_rd                  = 1'b1;
        mpu_aux_illegal               = aux_write;
      end

      `npuarc_AUX_REG_BITS'd1058:    // K_RW
      begin
        mpu_aux_rdata               = {   
                                            rdb0_base_r,
                                            {4{1'd0}},
                                            rdb0_v_r
                                        };
        mpu_aux_unimpl                = 1'b0;
        mpu_aux_k_rd                  = 1'b1;
        mpu_aux_k_wr                  = 1'b1;

        // ser. if MPU is live
        //
        mpu_aux_strict_sr             = aux_write & mpu_en_r;

      end

      `npuarc_AUX_REG_BITS'd1059:
      begin
        mpu_aux_rdata               = {   20'd0,
                                            rdp0_size_r[`npuarc_RDP_SIZE_HI],
                                            rdp0_krd_r,
                                            rdp0_kw_r,
                                            rdp0_ke_r,
                                            rdp0_urd_r,
                                            rdp0_uw_r,
                                            rdp0_ue_r,
                                            1'd0,
                                            rdp0_size_r[`npuarc_RDP_SIZE_LO]
                                        };
        mpu_aux_unimpl                = 1'b0;
        mpu_aux_k_rd                  = 1'b1;
        mpu_aux_k_wr                  = 1'b1;

        // ser. if MPU is live
        //
        mpu_aux_strict_sr             = aux_write & mpu_en_r;

      end

      `npuarc_AUX_REG_BITS'd1060:    // K_RW
      begin
        mpu_aux_rdata               = {   
                                            rdb1_base_r,
                                            {4{1'd0}},
                                            rdb1_v_r
                                        };
        mpu_aux_unimpl                = 1'b0;
        mpu_aux_k_rd                  = 1'b1;
        mpu_aux_k_wr                  = 1'b1;

        // ser. if MPU is live
        //
        mpu_aux_strict_sr             = aux_write & mpu_en_r;

      end

      `npuarc_AUX_REG_BITS'd1061:
      begin
        mpu_aux_rdata               = {   20'd0,
                                            rdp1_size_r[`npuarc_RDP_SIZE_HI],
                                            rdp1_krd_r,
                                            rdp1_kw_r,
                                            rdp1_ke_r,
                                            rdp1_urd_r,
                                            rdp1_uw_r,
                                            rdp1_ue_r,
                                            1'd0,
                                            rdp1_size_r[`npuarc_RDP_SIZE_LO]
                                        };
        mpu_aux_unimpl                = 1'b0;
        mpu_aux_k_rd                  = 1'b1;
        mpu_aux_k_wr                  = 1'b1;

        // ser. if MPU is live
        //
        mpu_aux_strict_sr             = aux_write & mpu_en_r;

      end

      `npuarc_AUX_REG_BITS'd1062:    // K_RW
      begin
        mpu_aux_rdata               = {   
                                            rdb2_base_r,
                                            {4{1'd0}},
                                            rdb2_v_r
                                        };
        mpu_aux_unimpl                = 1'b0;
        mpu_aux_k_rd                  = 1'b1;
        mpu_aux_k_wr                  = 1'b1;

        // ser. if MPU is live
        //
        mpu_aux_strict_sr             = aux_write & mpu_en_r;

      end

      `npuarc_AUX_REG_BITS'd1063:
      begin
        mpu_aux_rdata               = {   20'd0,
                                            rdp2_size_r[`npuarc_RDP_SIZE_HI],
                                            rdp2_krd_r,
                                            rdp2_kw_r,
                                            rdp2_ke_r,
                                            rdp2_urd_r,
                                            rdp2_uw_r,
                                            rdp2_ue_r,
                                            1'd0,
                                            rdp2_size_r[`npuarc_RDP_SIZE_LO]
                                        };
        mpu_aux_unimpl                = 1'b0;
        mpu_aux_k_rd                  = 1'b1;
        mpu_aux_k_wr                  = 1'b1;

        // ser. if MPU is live
        //
        mpu_aux_strict_sr             = aux_write & mpu_en_r;

      end

      `npuarc_AUX_REG_BITS'd1064:    // K_RW
      begin
        mpu_aux_rdata               = {   
                                            rdb3_base_r,
                                            {4{1'd0}},
                                            rdb3_v_r
                                        };
        mpu_aux_unimpl                = 1'b0;
        mpu_aux_k_rd                  = 1'b1;
        mpu_aux_k_wr                  = 1'b1;

        // ser. if MPU is live
        //
        mpu_aux_strict_sr             = aux_write & mpu_en_r;

      end

      `npuarc_AUX_REG_BITS'd1065:
      begin
        mpu_aux_rdata               = {   20'd0,
                                            rdp3_size_r[`npuarc_RDP_SIZE_HI],
                                            rdp3_krd_r,
                                            rdp3_kw_r,
                                            rdp3_ke_r,
                                            rdp3_urd_r,
                                            rdp3_uw_r,
                                            rdp3_ue_r,
                                            1'd0,
                                            rdp3_size_r[`npuarc_RDP_SIZE_LO]
                                        };
        mpu_aux_unimpl                = 1'b0;
        mpu_aux_k_rd                  = 1'b1;
        mpu_aux_k_wr                  = 1'b1;

        // ser. if MPU is live
        //
        mpu_aux_strict_sr             = aux_write & mpu_en_r;

      end

      `npuarc_AUX_REG_BITS'd1066:    // K_RW
      begin
        mpu_aux_rdata               = {   
                                            rdb4_base_r,
                                            {4{1'd0}},
                                            rdb4_v_r
                                        };
        mpu_aux_unimpl                = 1'b0;
        mpu_aux_k_rd                  = 1'b1;
        mpu_aux_k_wr                  = 1'b1;

        // ser. if MPU is live
        //
        mpu_aux_strict_sr             = aux_write & mpu_en_r;

      end

      `npuarc_AUX_REG_BITS'd1067:
      begin
        mpu_aux_rdata               = {   20'd0,
                                            rdp4_size_r[`npuarc_RDP_SIZE_HI],
                                            rdp4_krd_r,
                                            rdp4_kw_r,
                                            rdp4_ke_r,
                                            rdp4_urd_r,
                                            rdp4_uw_r,
                                            rdp4_ue_r,
                                            1'd0,
                                            rdp4_size_r[`npuarc_RDP_SIZE_LO]
                                        };
        mpu_aux_unimpl                = 1'b0;
        mpu_aux_k_rd                  = 1'b1;
        mpu_aux_k_wr                  = 1'b1;

        // ser. if MPU is live
        //
        mpu_aux_strict_sr             = aux_write & mpu_en_r;

      end

      `npuarc_AUX_REG_BITS'd1068:    // K_RW
      begin
        mpu_aux_rdata               = {   
                                            rdb5_base_r,
                                            {4{1'd0}},
                                            rdb5_v_r
                                        };
        mpu_aux_unimpl                = 1'b0;
        mpu_aux_k_rd                  = 1'b1;
        mpu_aux_k_wr                  = 1'b1;

        // ser. if MPU is live
        //
        mpu_aux_strict_sr             = aux_write & mpu_en_r;

      end

      `npuarc_AUX_REG_BITS'd1069:
      begin
        mpu_aux_rdata               = {   20'd0,
                                            rdp5_size_r[`npuarc_RDP_SIZE_HI],
                                            rdp5_krd_r,
                                            rdp5_kw_r,
                                            rdp5_ke_r,
                                            rdp5_urd_r,
                                            rdp5_uw_r,
                                            rdp5_ue_r,
                                            1'd0,
                                            rdp5_size_r[`npuarc_RDP_SIZE_LO]
                                        };
        mpu_aux_unimpl                = 1'b0;
        mpu_aux_k_rd                  = 1'b1;
        mpu_aux_k_wr                  = 1'b1;

        // ser. if MPU is live
        //
        mpu_aux_strict_sr             = aux_write & mpu_en_r;

      end

      `npuarc_AUX_REG_BITS'd1070:    // K_RW
      begin
        mpu_aux_rdata               = {   
                                            rdb6_base_r,
                                            {4{1'd0}},
                                            rdb6_v_r
                                        };
        mpu_aux_unimpl                = 1'b0;
        mpu_aux_k_rd                  = 1'b1;
        mpu_aux_k_wr                  = 1'b1;

        // ser. if MPU is live
        //
        mpu_aux_strict_sr             = aux_write & mpu_en_r;

      end

      `npuarc_AUX_REG_BITS'd1071:
      begin
        mpu_aux_rdata               = {   20'd0,
                                            rdp6_size_r[`npuarc_RDP_SIZE_HI],
                                            rdp6_krd_r,
                                            rdp6_kw_r,
                                            rdp6_ke_r,
                                            rdp6_urd_r,
                                            rdp6_uw_r,
                                            rdp6_ue_r,
                                            1'd0,
                                            rdp6_size_r[`npuarc_RDP_SIZE_LO]
                                        };
        mpu_aux_unimpl                = 1'b0;
        mpu_aux_k_rd                  = 1'b1;
        mpu_aux_k_wr                  = 1'b1;

        // ser. if MPU is live
        //
        mpu_aux_strict_sr             = aux_write & mpu_en_r;

      end

      `npuarc_AUX_REG_BITS'd1072:    // K_RW
      begin
        mpu_aux_rdata               = {   
                                            rdb7_base_r,
                                            {4{1'd0}},
                                            rdb7_v_r
                                        };
        mpu_aux_unimpl                = 1'b0;
        mpu_aux_k_rd                  = 1'b1;
        mpu_aux_k_wr                  = 1'b1;

        // ser. if MPU is live
        //
        mpu_aux_strict_sr             = aux_write & mpu_en_r;

      end

      `npuarc_AUX_REG_BITS'd1073:
      begin
        mpu_aux_rdata               = {   20'd0,
                                            rdp7_size_r[`npuarc_RDP_SIZE_HI],
                                            rdp7_krd_r,
                                            rdp7_kw_r,
                                            rdp7_ke_r,
                                            rdp7_urd_r,
                                            rdp7_uw_r,
                                            rdp7_ue_r,
                                            1'd0,
                                            rdp7_size_r[`npuarc_RDP_SIZE_LO]
                                        };
        mpu_aux_unimpl                = 1'b0;
        mpu_aux_k_rd                  = 1'b1;
        mpu_aux_k_wr                  = 1'b1;

        // ser. if MPU is live
        //
        mpu_aux_strict_sr             = aux_write & mpu_en_r;

      end

      default:
        // aux_mpu_raddr_r is not implemented in this module
        //
        mpu_aux_unimpl  = 1'b1;
        
    endcase
  end
end // block : mpu_aux_ren_PROC

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational logic for selecting an SR                                  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
always @*
begin : mpu_aux_wen_PROC

   mpu_en_en         = 1'b0;

  mpu_rdb0_en    = 1'b0;
  mpu_rdp0_en    = 1'b0;
  mpu_rdb1_en    = 1'b0;
  mpu_rdp1_en    = 1'b0;
  mpu_rdb2_en    = 1'b0;
  mpu_rdp2_en    = 1'b0;
  mpu_rdb3_en    = 1'b0;
  mpu_rdp3_en    = 1'b0;
  mpu_rdb4_en    = 1'b0;
  mpu_rdp4_en    = 1'b0;
  mpu_rdb5_en    = 1'b0;
  mpu_rdp5_en    = 1'b0;
  mpu_rdb6_en    = 1'b0;
  mpu_rdp6_en    = 1'b0;
  mpu_rdb7_en    = 1'b0;
  mpu_rdp7_en    = 1'b0;

  mask_diff_nxt     = `npuarc_MPU_REGION_BITS'd0;
  mask_diff_en      = 1'b0;
  new_size_en       = 1'b0;

  if (aux_mpu_wen_r == 1'b1)
  begin

    case ({5'h00, aux_mpu_waddr_r})
//spyglass disable_block W263
// SMD: Reports case expression, select width mismatch
// SJ:  1. 2 operand 12-bits bitwise and
//      2. case statment 12-bit.
//      Therefore syntax is correct
      (`npuarc_MPU_EN_AUX & ({5'h00, 7'h7F})):  mpu_en_en = 1'b1;
//spyglass enable_block W263
//spyglass disable_block W263
// SMD: Reports case expression, select width mismatch
// SJ:  1. 2 operand 12-bits bitwise and
//      2. case statment 12-bit.
//      Therefore syntax is correct
      (`npuarc_AUX_REG_BITS'd1058 & ({5'h00, 7'h7F})):  mpu_rdb0_en = 1'b1;
//spyglass enable_block W263
//spyglass disable_block W263
// SMD: Reports case expression, select width mismatch
// SJ:  1. 2 operand 12-bits bitwise and
//      2. case statment 12-bit.
//      Therefore syntax is correct
      (`npuarc_AUX_REG_BITS'd1059 & ({5'h00, 7'h7F})):  
//spyglass enable_block W263
      begin
        mpu_rdp0_en        = 1'b1;
        new_size_en           = mpu_rdp0_en;
        mask_diff_nxt[0]     = mpu_rdp0_en;
      end
//spyglass disable_block W263
// SMD: Reports case expression, select width mismatch
// SJ:  1. 2 operand 12-bits bitwise and
//      2. case statment 12-bit.
//      Therefore syntax is correct
      (`npuarc_AUX_REG_BITS'd1060 & ({5'h00, 7'h7F})):  mpu_rdb1_en = 1'b1;
//spyglass enable_block W263
//spyglass disable_block W263
// SMD: Reports case expression, select width mismatch
// SJ:  1. 2 operand 12-bits bitwise and
//      2. case statment 12-bit.
//      Therefore syntax is correct
      (`npuarc_AUX_REG_BITS'd1061 & ({5'h00, 7'h7F})):  
//spyglass enable_block W263
      begin
        mpu_rdp1_en        = 1'b1;
        new_size_en           = mpu_rdp1_en;
        mask_diff_nxt[1]     = mpu_rdp1_en;
      end
//spyglass disable_block W263
// SMD: Reports case expression, select width mismatch
// SJ:  1. 2 operand 12-bits bitwise and
//      2. case statment 12-bit.
//      Therefore syntax is correct
      (`npuarc_AUX_REG_BITS'd1062 & ({5'h00, 7'h7F})):  mpu_rdb2_en = 1'b1;
//spyglass enable_block W263
//spyglass disable_block W263
// SMD: Reports case expression, select width mismatch
// SJ:  1. 2 operand 12-bits bitwise and
//      2. case statment 12-bit.
//      Therefore syntax is correct
      (`npuarc_AUX_REG_BITS'd1063 & ({5'h00, 7'h7F})):  
//spyglass enable_block W263
      begin
        mpu_rdp2_en        = 1'b1;
        new_size_en           = mpu_rdp2_en;
        mask_diff_nxt[2]     = mpu_rdp2_en;
      end
//spyglass disable_block W263
// SMD: Reports case expression, select width mismatch
// SJ:  1. 2 operand 12-bits bitwise and
//      2. case statment 12-bit.
//      Therefore syntax is correct
      (`npuarc_AUX_REG_BITS'd1064 & ({5'h00, 7'h7F})):  mpu_rdb3_en = 1'b1;
//spyglass enable_block W263
//spyglass disable_block W263
// SMD: Reports case expression, select width mismatch
// SJ:  1. 2 operand 12-bits bitwise and
//      2. case statment 12-bit.
//      Therefore syntax is correct
      (`npuarc_AUX_REG_BITS'd1065 & ({5'h00, 7'h7F})):  
//spyglass enable_block W263
      begin
        mpu_rdp3_en        = 1'b1;
        new_size_en           = mpu_rdp3_en;
        mask_diff_nxt[3]     = mpu_rdp3_en;
      end
//spyglass disable_block W263
// SMD: Reports case expression, select width mismatch
// SJ:  1. 2 operand 12-bits bitwise and
//      2. case statment 12-bit.
//      Therefore syntax is correct
      (`npuarc_AUX_REG_BITS'd1066 & ({5'h00, 7'h7F})):  mpu_rdb4_en = 1'b1;
//spyglass enable_block W263
//spyglass disable_block W263
// SMD: Reports case expression, select width mismatch
// SJ:  1. 2 operand 12-bits bitwise and
//      2. case statment 12-bit.
//      Therefore syntax is correct
      (`npuarc_AUX_REG_BITS'd1067 & ({5'h00, 7'h7F})):  
//spyglass enable_block W263
      begin
        mpu_rdp4_en        = 1'b1;
        new_size_en           = mpu_rdp4_en;
        mask_diff_nxt[4]     = mpu_rdp4_en;
      end
//spyglass disable_block W263
// SMD: Reports case expression, select width mismatch
// SJ:  1. 2 operand 12-bits bitwise and
//      2. case statment 12-bit.
//      Therefore syntax is correct
      (`npuarc_AUX_REG_BITS'd1068 & ({5'h00, 7'h7F})):  mpu_rdb5_en = 1'b1;
//spyglass enable_block W263
//spyglass disable_block W263
// SMD: Reports case expression, select width mismatch
// SJ:  1. 2 operand 12-bits bitwise and
//      2. case statment 12-bit.
//      Therefore syntax is correct
      (`npuarc_AUX_REG_BITS'd1069 & ({5'h00, 7'h7F})):  
//spyglass enable_block W263
      begin
        mpu_rdp5_en        = 1'b1;
        new_size_en           = mpu_rdp5_en;
        mask_diff_nxt[5]     = mpu_rdp5_en;
      end
//spyglass disable_block W263
// SMD: Reports case expression, select width mismatch
// SJ:  1. 2 operand 12-bits bitwise and
//      2. case statment 12-bit.
//      Therefore syntax is correct
      (`npuarc_AUX_REG_BITS'd1070 & ({5'h00, 7'h7F})):  mpu_rdb6_en = 1'b1;
//spyglass enable_block W263
//spyglass disable_block W263
// SMD: Reports case expression, select width mismatch
// SJ:  1. 2 operand 12-bits bitwise and
//      2. case statment 12-bit.
//      Therefore syntax is correct
      (`npuarc_AUX_REG_BITS'd1071 & ({5'h00, 7'h7F})):  
//spyglass enable_block W263
      begin
        mpu_rdp6_en        = 1'b1;
        new_size_en           = mpu_rdp6_en;
        mask_diff_nxt[6]     = mpu_rdp6_en;
      end
//spyglass disable_block W263
// SMD: Reports case expression, select width mismatch
// SJ:  1. 2 operand 12-bits bitwise and
//      2. case statment 12-bit.
//      Therefore syntax is correct
      (`npuarc_AUX_REG_BITS'd1072 & ({5'h00, 7'h7F})):  mpu_rdb7_en = 1'b1;
//spyglass enable_block W263
//spyglass disable_block W263
// SMD: Reports case expression, select width mismatch
// SJ:  1. 2 operand 12-bits bitwise and
//      2. case statment 12-bit.
//      Therefore syntax is correct
      (`npuarc_AUX_REG_BITS'd1073 & ({5'h00, 7'h7F})):  
//spyglass enable_block W263
      begin
        mpu_rdp7_en        = 1'b1;
        new_size_en           = mpu_rdp7_en;
        mask_diff_nxt[7]     = mpu_rdp7_en;
      end
      default:
      begin

        mpu_en_en         = 1'b0;

        mpu_rdb0_en    = 1'b0;
        mpu_rdp0_en    = 1'b0;
        mpu_rdb1_en    = 1'b0;
        mpu_rdp1_en    = 1'b0;
        mpu_rdb2_en    = 1'b0;
        mpu_rdp2_en    = 1'b0;
        mpu_rdb3_en    = 1'b0;
        mpu_rdp3_en    = 1'b0;
        mpu_rdb4_en    = 1'b0;
        mpu_rdp4_en    = 1'b0;
        mpu_rdb5_en    = 1'b0;
        mpu_rdp5_en    = 1'b0;
        mpu_rdb6_en    = 1'b0;
        mpu_rdp6_en    = 1'b0;
        mpu_rdb7_en    = 1'b0;
        mpu_rdp7_en    = 1'b0;

        mask_diff_nxt     = `npuarc_MPU_REGION_BITS'd0;
        mask_diff_en      = 1'b0;
        new_size_en       = 1'b0;

      end

    endcase

    mask_diff_en = (|mask_diff_nxt) | (|mask_diff_r);
  end
end // block : mpu_aux_wen_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Interrupt Epilogue Kernel Mode                                         //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
//
always @*
begin: irq_kmode_nxt_PROC

  //////////////////////////////////////////////////////////////////////////
  //  
  //  Capture Kernel Mode
  //  1. (Interrupt) RTIE operation to be Committed
  //
  irq_epil_kmode_g = 1'b0
                   | ca_rtie_op_r
                   ;

  //////////////////////////////////////////////////////////////////////////
  //  
  //  Set Kernel Mode
  //  1. User Context from User Stack needs to be restored when
  //     a. Outermost Epilogue
  //     b. User Context saved to User Stack
  //     c. Interrupts are active
  //
  irq_epil_kmode_n = 1'b1
                   & irq_u_ctrl
                   &  !( irq_u_act 
                       & (irq_act_nxt == `npuarc_NUMBER_OF_LEVELS'b0)
                       )
                   ;

end // block : irq_kmode_nxt_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Interrupt Epilogue Kernel Mode                                         //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
//
always @(posedge clk or posedge rst_a)
begin: irq_kmode_regs_PROC
  if (rst_a == 1'b1)
    irq_epil_kmode_r <= 1'b0;
  else if (irq_epil_kmode_g == 1'b1)
    irq_epil_kmode_r <= irq_epil_kmode_n;
end // block : irq_kmode_regs_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Asynchronous logic for determining permissions for each region         //
//                                                                        //
// Permission is given if the selected region has the kernel permission   //
// bit set in kernel mode, or if the user permission bit is set           //
// (in any mode).                                                         //
////////////////////////////////////////////////////////////////////////////

always @*
begin : region_perms_PROC

  int_kernel_mode = kernel_mode
                  | ca_uop_inprol_r
                  ;

  // Data in Kernel mode
  // Default : AR User mode is not set
  // When :
  // 1. *NOT in* Interrupt Prologue or Epilogue
  //   a. AR User mode is not set
  // 2. *    in* Interrupt Prologue or Epilogue
  //   a. If User context saved to *Kernel stack*
  //     i. Kernel mode (defaulted)
  //   b. If User context saved to *User stack*
  //     i. Prologue : AR User mode is not set
  //    ii. Epilogue : Saved IRQ User mode 
  // 
  d_kernel_mode   = 1'b0
                  | (  (kernel_mode | excpn_in_prologue_r)
                    & !(  1'b0
                       | int_evts[`npuarc_INTEVT_INPROL]
                       | int_evts[`npuarc_INTEVT_INEPIL]
                      )
                    )
                  | ( (1'b0
                       | int_evts[`npuarc_INTEVT_INPROL]
                       | int_evts[`npuarc_INTEVT_INEPIL]
                      )
                      & !irq_u_ctrl
                    )
                  | ( (1'b0
                       | int_evts[`npuarc_INTEVT_INPROL]
                      )
                      & irq_u_ctrl
                      & kernel_mode
                    )
                  | ( int_evts[`npuarc_INTEVT_INEPIL]
                    & irq_epil_kmode_r
                    )
                  ;

  //////////////////////////////////////////////////////////////////////////
  //  Determine the Execute permission for each region.
  //
  e_perms   = {
               ((rdp7_ke_r & int_kernel_mode) | rdp7_ue_r),
               ((rdp6_ke_r & int_kernel_mode) | rdp6_ue_r),
               ((rdp5_ke_r & int_kernel_mode) | rdp5_ue_r),
               ((rdp4_ke_r & int_kernel_mode) | rdp4_ue_r),
               ((rdp3_ke_r & int_kernel_mode) | rdp3_ue_r),
               ((rdp2_ke_r & int_kernel_mode) | rdp2_ue_r),
               ((rdp1_ke_r & int_kernel_mode) | rdp1_ue_r),
               ((rdp0_ke_r & int_kernel_mode) | rdp0_ue_r)
              };
            
  e_default = ((mpu_en_ke_r & int_kernel_mode) | mpu_en_ue_r);
          
  //////////////////////////////////////////////////////////////////////////
  // Determine the Speculative Instruction Fetch permission for each region.
  // Speculative instruction fetch is permitted when either the kernel
  // or user execute permission is granted.
  // In either case executable code is presumed to be available and fetchable.
  // Instructions that are fetched speculatively are only committed when
  // the proper kernel permission is available.
  //
  ifetch_perms   = {
                (rdp7_ke_r | rdp7_ue_r),
                (rdp6_ke_r | rdp6_ue_r),
                (rdp5_ke_r | rdp5_ue_r),
                (rdp4_ke_r | rdp4_ue_r),
                (rdp3_ke_r | rdp3_ue_r),
                (rdp2_ke_r | rdp2_ue_r),
                (rdp1_ke_r | rdp1_ue_r),
                (rdp0_ke_r | rdp0_ue_r)
              };
            
  ifetch_default = mpu_en_ke_r | mpu_en_ue_r;


          
  //////////////////////////////////////////////////////////////////////////
  //  Determine the Read permission for each region.
  //
  r_perms   = {
                ((rdp7_krd_r & d_kernel_mode) | rdp7_urd_r),
                ((rdp6_krd_r & d_kernel_mode) | rdp6_urd_r),
                ((rdp5_krd_r & d_kernel_mode) | rdp5_urd_r),
                ((rdp4_krd_r & d_kernel_mode) | rdp4_urd_r),
                ((rdp3_krd_r & d_kernel_mode) | rdp3_urd_r),
                ((rdp2_krd_r & d_kernel_mode) | rdp2_urd_r),
                ((rdp1_krd_r & d_kernel_mode) | rdp1_urd_r),
                ((rdp0_krd_r & d_kernel_mode) | rdp0_urd_r)
              };
              
  r_default = ((mpu_en_krd_r & d_kernel_mode) | mpu_en_urd_r);
          
  //////////////////////////////////////////////////////////////////////////
  //  Determine the Write permission for each region.
  //
  w_perms = {
              ((rdp7_kw_r & d_kernel_mode) | rdp7_uw_r),
              ((rdp6_kw_r & d_kernel_mode) | rdp6_uw_r),
              ((rdp5_kw_r & d_kernel_mode) | rdp5_uw_r),
              ((rdp4_kw_r & d_kernel_mode) | rdp4_uw_r),
              ((rdp3_kw_r & d_kernel_mode) | rdp3_uw_r),
              ((rdp2_kw_r & d_kernel_mode) | rdp2_uw_r),
              ((rdp1_kw_r & d_kernel_mode) | rdp1_uw_r),
              ((rdp0_kw_r & d_kernel_mode) | rdp0_uw_r)
            };
            
  w_default = ((mpu_en_kw_r & d_kernel_mode) | mpu_en_uw_r);
          
end // block : region_perms_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// X2 Stage Control                                                       //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : x1_ctrl_PROC

  x1_pc_cg0  = x1_enable & sa_pass;

end // block : x1_ctrl_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// X1 Stage Values                                                        //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: x1_pc_regs_PROC
  if (rst_a == 1'b1)
    begin
      x1_pc_r         <= `npuarc_PC_BITS'd`npuarc_RESET_PC;
    end
  else if (x1_pc_cg0 == 1'b1)
    begin
      x1_pc_r         <= sa_pc_r;
    end
end // block : x1_pc_regs_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// X2 Stage Control                                                       //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : x2_PROC

  x2_pc_cg0  = x2_enable & x1_pass;

end // block : x2_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// X2 Stage Values                                                        //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: x2_pc_regs_PROC
  if (rst_a == 1'b1)
    begin
      x2_pc_r         <= `npuarc_PC_BITS'd`npuarc_RESET_PC;
    end
  else if (x2_pc_cg0 == 1'b1)
    begin
      x2_pc_r         <= x1_pc_r;
    end
end // block : x2_pc_regs_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// X3 Stage Control                                                       //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : x3_ctrl_PROC

  x3_pc_cg0  = (x3_enable & x2_pass)
             & (mpu_exec_viol | mpu_data_viol)
             ;

  x3_md_cg0  = (x3_enable & x2_pass)
             | (x3_enable & mpu_data_viol_r)
             ;

  x3_me_cg0  = (x3_enable & x2_pass)
             | (x3_enable & mpu_exec_viol_r)
             ;

end // block : x3_ctrl_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Outputs to Exception Logic                                             //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: mpu_viol_regs_PROC
  if (rst_a == 1'b1)
  begin
      mpu_exec_viol_r  <= 1'b0;
      mpu_data_viol_r  <= 1'b0;
      mpu_efa_r        <= `npuarc_ADDR_SIZE'd0;
  end
  else
  begin
    if (x3_me_cg0 == 1'b1)
      mpu_exec_viol_r  <= mpu_exec_viol & (~x2_kill) & (~db_active);
    if (x3_md_cg0 == 1'b1)
      mpu_data_viol_r  <= mpu_data_viol & (~x2_kill) & (~db_active);
    if (x3_pc_cg0 == 1'b1)
      mpu_efa_r        <= mpu_efa_nxt;
  end
end // block : mpu_viol_regs_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Asynchronous logic for checking fetch address against active regions   //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : i_match_PROC

  //////////////////////////////////////////////////////////////////////////
  // fetch_addr is a selection of relevant bits from x1_pc_r, possibly
  // prepended with zeros up to the full address size if required.
  // This is the fetch region address that is matched against each region's
  // masked base address.
  //
  fetch_addr = x2_pc_r[`npuarc_PC_RGN_RANGE];

  //////////////////////////////////////////////////////////////////////////
  // valid_fetch is 1 if there is a valid access underway in the Fetch
  // stage in the current cycle, and the MPU is enabled.
  //
  valid_fetch = mpu_en_r & (~x2_uop_inst_r) 
              &  ( ~mmu_en_r                  
                  | (~x2_fa0_transl))
              ;
  
  //////////////////////////////////////////////////////////////////////////
  // Compare x1_pc_r with each region register, masking base address
  // bits not needed by the programmed size of each region.
  // A hit is validated by sa_valid_r and the validity of MPU_RDB.V for
  // each region.
  //
  ihit[0] = ( (~|((fetch_addr ^ rdb0_base_r) & addr_mask0_r))
             )
           & valid_fetch & rdb0_v_r;

  ihit[1] = ( (~|((fetch_addr ^ rdb1_base_r) & addr_mask1_r))
             )
           & valid_fetch & rdb1_v_r;

  ihit[2] = ( (~|((fetch_addr ^ rdb2_base_r) & addr_mask2_r))
             )
           & valid_fetch & rdb2_v_r;

  ihit[3] = ( (~|((fetch_addr ^ rdb3_base_r) & addr_mask3_r))
             )
           & valid_fetch & rdb3_v_r;

  ihit[4] = ( (~|((fetch_addr ^ rdb4_base_r) & addr_mask4_r))
             )
           & valid_fetch & rdb4_v_r;

  ihit[5] = ( (~|((fetch_addr ^ rdb5_base_r) & addr_mask5_r))
             )
           & valid_fetch & rdb5_v_r;

  ihit[6] = ( (~|((fetch_addr ^ rdb6_base_r) & addr_mask6_r))
             )
           & valid_fetch & rdb6_v_r;

  ihit[7] = ( (~|((fetch_addr ^ rdb7_base_r) & addr_mask7_r))
             )
           & valid_fetch & rdb7_v_r;





  
  //////////////////////////////////////////////////////////////////////////
  // Prioritize the instruction-fetch match results from each region.
  // A violation is reported if the selected region n does not have the
  // e_perm[n] bit set, or if no region was selected on a valid fetch cycle.
  //
  case (1'b1)
  ihit[0]:
    begin
    exec_v    = ~e_perms[0];
    exec_mr   = 4'd0;
    end
  ihit[1]:
    begin
    exec_v    = ~e_perms[1];
    exec_mr   = 4'd1;
    end
  ihit[2]:
    begin
    exec_v    = ~e_perms[2];
    exec_mr   = 4'd2;
    end
  ihit[3]:
    begin
    exec_v    = ~e_perms[3];
    exec_mr   = 4'd3;
    end
  ihit[4]:
    begin
    exec_v    = ~e_perms[4];
    exec_mr   = 4'd4;
    end
  ihit[5]:
    begin
    exec_v    = ~e_perms[5];
    exec_mr   = 4'd5;
    end
  ihit[6]:
    begin
    exec_v    = ~e_perms[6];
    exec_mr   = 4'd6;
    end
  ihit[7]:
    begin
    exec_v    = ~e_perms[7];
    exec_mr   = 4'd7;
    end
  default:
    begin
    exec_v    = valid_fetch & (~e_default);
    exec_mr   = {4{1'b1}};
    end 
  endcase

end // block : i_match_PROC


///////////////////////////////////////////////////////////////////////////
// Check speculative instruction fetch addresses from the IFU            //
///////////////////////////////////////////////////////////////////////////

// What if an MPU protection region is smaller than an icache line?
// That is discussed in the following:
// 
// An MPU protection region can potentially be configured to be smaller than an 
// icache line (or 128 byte block in the IFQ). 
// The minimum MPU region size is 32 bytes and the icache line size can be
// configured at 32, 64 or 128 bytes.
// Icache fetching occurs with the granularity of a cache line size.
// An instruction fetch to an address in an MPU region that has execute permission
// will not be blocked, even when another part of that cache line has no execute permission.
//
// To avoid partial protection of a cache line, the MPU protection
// region should be programmed to be larger than or equal to the icache line size,
// if an icache is configured or at least 128 bytes if an IFQ is configured.

always @*
begin : ifetch_PROC

  ifetch_addr = ifetch_addr_mpu[`npuarc_PC_RGN_RANGE];

  valid_ifetch = mpu_en_r
              &  ( ~mmu_en_r                  
                  | ifetch_addr[`npuarc_ADDR_MSB]) // 31
              ;
  //////////////////////////////////////////////////////////////////////////
  // Compare the fetch address with each region register, masking base address
  // bits not needed by the programmed size of each region.
  // A hit is validated by the validity of MPU_RDB.V for
  // each region and by overall MPU enable.
  //
  ifetch_hit[0] = ( (~|((ifetch_addr ^ rdb0_base_r) & addr_mask0_r))
             )
           & valid_ifetch & rdb0_v_r;

  ifetch_hit[1] = ( (~|((ifetch_addr ^ rdb1_base_r) & addr_mask1_r))
             )
           & valid_ifetch & rdb1_v_r;

  ifetch_hit[2] = ( (~|((ifetch_addr ^ rdb2_base_r) & addr_mask2_r))
             )
           & valid_ifetch & rdb2_v_r;

  ifetch_hit[3] = ( (~|((ifetch_addr ^ rdb3_base_r) & addr_mask3_r))
             )
           & valid_ifetch & rdb3_v_r;

  ifetch_hit[4] = ( (~|((ifetch_addr ^ rdb4_base_r) & addr_mask4_r))
             )
           & valid_ifetch & rdb4_v_r;

  ifetch_hit[5] = ( (~|((ifetch_addr ^ rdb5_base_r) & addr_mask5_r))
             )
           & valid_ifetch & rdb5_v_r;

  ifetch_hit[6] = ( (~|((ifetch_addr ^ rdb6_base_r) & addr_mask6_r))
             )
           & valid_ifetch & rdb6_v_r;

  ifetch_hit[7] = ( (~|((ifetch_addr ^ rdb7_base_r) & addr_mask7_r))
             )
           & valid_ifetch & rdb7_v_r;

  //////////////////////////////////////////////////////////////////////////
  // Prioritize the instruction-fetch match results from each region.
  // A violation is reported if the selected region n does not have the
  // ifetch_perms[n] bit set, or if no region was selected and the default
  // permission for ifetch is set to 0.
  //
  case (1'b1)
  ifetch_hit[0]:
    begin
    ifetch_viol  = ~ifetch_perms[0];
    end
  ifetch_hit[1]:
    begin
    ifetch_viol  = ~ifetch_perms[1];
    end
  ifetch_hit[2]:
    begin
    ifetch_viol  = ~ifetch_perms[2];
    end
  ifetch_hit[3]:
    begin
    ifetch_viol  = ~ifetch_perms[3];
    end
  ifetch_hit[4]:
    begin
    ifetch_viol  = ~ifetch_perms[4];
    end
  ifetch_hit[5]:
    begin
    ifetch_viol  = ~ifetch_perms[5];
    end
  ifetch_hit[6]:
    begin
    ifetch_viol  = ~ifetch_perms[6];
    end
  ifetch_hit[7]:
    begin
    ifetch_viol  = ~ifetch_perms[7];
    end
  default:
    begin
    ifetch_viol  = valid_ifetch & (~ifetch_default);
    end 
  endcase

end // block : ifetch_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Asynchronous logic for checking LD/ST address against active regions   //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : d_match_PROC

  //////////////////////////////////////////////////////////////////////////
  // data_addr is a selection of relevant bits from x2_mem_addr, that is 
  // matched against each region's masked base address.
  //
  data_addr    = x2_mem_addr0_r[`npuarc_RDB_RGN_RANGE];

  //////////////////////////////////////////////////////////////////////////
  // valid_data_access is 1 if there is a valid Load or Store in the Commit
  // stage in the current cycle.
  //
  valid_data_access = mpu_en_r & (x2_load_r | x2_store_r)
              &  ( ~mmu_en_r                  
                  | (~x2_da0_transl))
                    ;
  
  valid_load_access = mpu_en_r & x2_load_r
              &  ( ~mmu_en_r                  
                  | (~x2_da0_transl))
                    ;
  
  valid_store_access = mpu_en_r & x2_store_r
              &  ( ~mmu_en_r                  
                  | (~x2_da0_transl))
                    ;
  
  //////////////////////////////////////////////////////////////////////////
  // Match the masked X2 memory address against all MPU regions in parallel.
  //
  dhit[0] = ( (~|((data_addr    ^ rdb0_base_r) & addr_mask0_r))
             )
           & valid_data_access & rdb0_v_r;
             
  dhit[1] = ( (~|((data_addr    ^ rdb1_base_r) & addr_mask1_r))
             )
           & valid_data_access & rdb1_v_r;
             
  dhit[2] = ( (~|((data_addr    ^ rdb2_base_r) & addr_mask2_r))
             )
           & valid_data_access & rdb2_v_r;
             
  dhit[3] = ( (~|((data_addr    ^ rdb3_base_r) & addr_mask3_r))
             )
           & valid_data_access & rdb3_v_r;
             
  dhit[4] = ( (~|((data_addr    ^ rdb4_base_r) & addr_mask4_r))
             )
           & valid_data_access & rdb4_v_r;
             
  dhit[5] = ( (~|((data_addr    ^ rdb5_base_r) & addr_mask5_r))
             )
           & valid_data_access & rdb5_v_r;
             
  dhit[6] = ( (~|((data_addr    ^ rdb6_base_r) & addr_mask6_r))
             )
           & valid_data_access & rdb6_v_r;
             
  dhit[7] = ( (~|((data_addr    ^ rdb7_base_r) & addr_mask7_r))
             )
           & valid_data_access & rdb7_v_r;
             

  //////////////////////////////////////////////////////////////////////////
  // Prioritize the load/store match results from each region.
  // A violation is reported if the selected region n does not have the
  // r_perm[n] bit set when reading, or if it does not have the w_perm[n]
  // bit set when writing, or if no region was hit during a valid data access.
  //
  case (1'b1)
  dhit[0]: 
    begin
    data_v    = (x2_load_r & (~r_perms[0])) | (x2_store_r & (~w_perms[0]));
    data_mr   = 4'd0;
    end
  dhit[1]: 
    begin
    data_v    = (x2_load_r & (~r_perms[1])) | (x2_store_r & (~w_perms[1]));
    data_mr   = 4'd1;
    end
  dhit[2]: 
    begin
    data_v    = (x2_load_r & (~r_perms[2])) | (x2_store_r & (~w_perms[2]));
    data_mr   = 4'd2;
    end
  dhit[3]: 
    begin
    data_v    = (x2_load_r & (~r_perms[3])) | (x2_store_r & (~w_perms[3]));
    data_mr   = 4'd3;
    end
  dhit[4]: 
    begin
    data_v    = (x2_load_r & (~r_perms[4])) | (x2_store_r & (~w_perms[4]));
    data_mr   = 4'd4;
    end
  dhit[5]: 
    begin
    data_v    = (x2_load_r & (~r_perms[5])) | (x2_store_r & (~w_perms[5]));
    data_mr   = 4'd5;
    end
  dhit[6]: 
    begin
    data_v    = (x2_load_r & (~r_perms[6])) | (x2_store_r & (~w_perms[6]));
    data_mr   = 4'd6;
    end
  dhit[7]: 
    begin
    data_v    = (x2_load_r & (~r_perms[7])) | (x2_store_r & (~w_perms[7]));
    data_mr   = 4'd7;
    end
  default:  
    begin
    data_v    = (valid_load_access  & (~r_default))
              | (valid_store_access & (~w_default))
              ;
    data_mr   =  {4{1'b1}};
    end 
  endcase

  //////////////////////////////////////////////////////////////////////////
  // Define output signals reporting protection violations to the CPU.
  // A data violation is reported during the cycle in which it is detected.
  // An ifetch violation is reported if and when the triggering instruction
  // reaches the Commit stage. A detected ifetch violation may be discarded
  // before it reaches the Commit stage, by da_would_kill_fa when still in 
  // the Fetch stage, or by fch_restart when it is in the Execute or Commit 
  // stages.
  //
  mpu_data_viol   = data_v & (~x2_pref_r);
  mpu_exec_viol   = exec_v & x2_pass & x3_enable ;

  x2_mpu_data_flt = data_v;
  

  //////////////////////////////////////////////////////////////////////////
  // Select next speculative MPU_ECR field values, giving priority to fetch 
  // violations over load/store violations for the same instruction. 
  // Priority is always given to the oldest violation that has not been 
  // dismissed by a pipeline flush or an MPU exception acknowledgement.
  //
  x3_ecr_mr_nxt  = mpu_exec_viol
                  ? exec_mr
                  : data_mr
                  ;
  
  x3_ecr_vt_nxt  = mpu_exec_viol
                  ? MPU_ECR_VT_EXECV
                  : { x2_store_r, x2_load_r };

  //////////////////////////////////////////////////////////////////////////
  // Select the next address value to write to EFA in the case of an MPU
  // fetch exception being accepted.
  // EFA will receive the speculative EFA value from any outstanding and
  // unreported violation
  //
  mpu_efa_nxt     = mpu_exec_viol
                  ? { x2_pc_r, 1'b0 }
                  : x2_mem_addr0_r
                  ;
  
  //////////////////////////////////////////////////////////////////////////
  // Select the next address value to write to MPU_ECR.
  // MPU_ECR will receive the speculative violation information from the 
  // most recent unreported ifetch violation if it has reached the commit
  // stage intact. Otherwise, the currently detected data violation will be
  // received as the next MPU_ECR value
  //  
  mpu_ecr_mr_nxt  = excpn_prologue_evt
                  ? ca_ecr_mr_r
                  : mpu_ecr_mr_r
                  ;
  
  mpu_ecr_vt_nxt  = excpn_prologue_evt
                  ? ca_ecr_vt_r
                  : mpu_ecr_vt_r
                  ;
    
end // block : match_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining MPU_EN auxiliary register                   //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : mpu_en_PROC
  if (rst_a == 1'b1)
  begin
    mpu_en_r        <= 1'b0;
    mpu_en_ue_r     <= 1'b0;
    mpu_en_uw_r     <= 1'b0;
    mpu_en_urd_r    <= 1'b0;
    mpu_en_ke_r     <= 1'b0;
    mpu_en_kw_r     <= 1'b0;
    mpu_en_krd_r    <= 1'b0;
  end
  else if (mpu_en_en == 1'b1)
  begin
    mpu_en_r        <= wa_sr_data_r[`npuarc_MPU_EN_BIT];
    mpu_en_ue_r     <= wa_sr_data_r[`npuarc_MPU_EN_E_BIT];
    mpu_en_uw_r     <= wa_sr_data_r[`npuarc_MPU_EN_W_BIT];
    mpu_en_urd_r    <= wa_sr_data_r[`npuarc_MPU_EN_RD_BIT];
    mpu_en_ke_r     <= wa_sr_data_r[`npuarc_MPU_EN_UE_BIT];
    mpu_en_kw_r     <= wa_sr_data_r[`npuarc_MPU_EN_UW_BIT];
    mpu_en_krd_r    <= wa_sr_data_r[`npuarc_MPU_EN_URD_BIT];
  end
end // block : mpu_en_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining speculative MPU_MR register                 //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : x3_ecr_reg_PROC
  if (rst_a == 1'b1)
  begin
    x3_ecr_mr_r   <= `npuarc_MPU_ECR_MR_BITS'd0;
    x3_ecr_vt_r   <= `npuarc_MPU_ECR_VT_BITS'd0;
  end
  else if (x3_pc_cg0 == 1'b1)
  begin
    x3_ecr_mr_r   <= x3_ecr_mr_nxt;
    x3_ecr_vt_r   <= x3_ecr_vt_nxt;
  end
end // block : x3_ecr_reg_PROC



////////////////////////////////////////////////////////////////////////////
//                                                                        //
// CA Stage Control                                                       //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : ca_ctrl_PROC

  ca_cg0  = ca_enable & x3_pass;

end // block : ca_ctrl_PROC

always @(posedge clk or posedge rst_a)
begin : ca_ecr_reg_PROC
  if (rst_a == 1'b1)
  begin
    ca_ecr_mr_r   <= `npuarc_MPU_ECR_MR_BITS'd0;
    ca_ecr_vt_r   <= `npuarc_MPU_ECR_VT_BITS'd0;
  end
  else if (ca_cg0 == 1'b1)
  begin
    ca_ecr_mr_r   <= x3_ecr_mr_r;
    ca_ecr_vt_r   <= x3_ecr_vt_r;
  end
end // block : ca_ecr_reg_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining the  MPU_I auxiliary register               //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : mpu_ecr_fa_PROC
  if (rst_a == 1'b1)
  begin
    mpu_ecr_mr_r    <= `npuarc_MPU_ECR_MR_BITS'd0;
    mpu_ecr_vt_r    <= `npuarc_MPU_ECR_VT_BITS'd0;
  end
  else if (ca_mpu_excpn_r == 1'b1)
  begin
    mpu_ecr_mr_r    <= mpu_ecr_mr_nxt;
    mpu_ecr_vt_r    <= mpu_ecr_vt_nxt;
  end
end // block : mpu_ecr_fa_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining MPU_RDB0 auxiliary register                //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : mpu_rdb0_PROC
  if (rst_a == 1'b1)
  begin
    rdb0_base_r  <= `npuarc_RDB_BASE_BITS'd0;
    rdb0_v_r     <= 1'b0;
  end
  else if (mpu_rdb0_en == 1'b1)
  begin
    rdb0_base_r  <= wa_sr_data_r[`npuarc_RDB_RGN_RANGE];
    rdb0_v_r     <= wa_sr_data_r[`npuarc_RDB_V_BIT];
  end
end // block : mpu_rdb0_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining MPU_RDP0 auxiliary register                //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : mpu_rdp0_PROC
  if (rst_a == 1'b1)
  begin
    rdp0_size_r  <= `npuarc_RDP_SIZE_BITS'd0;
    rdp0_ue_r    <= 1'b0;
    rdp0_uw_r    <= 1'b0;
    rdp0_urd_r   <= 1'b0;
    rdp0_ke_r    <= 1'b0;
    rdp0_kw_r    <= 1'b0;
    rdp0_krd_r   <= 1'b0;
  end
  else if (mpu_rdp0_en == 1'b1)
  begin
    rdp0_size_r  <= { wa_sr_data_r[`npuarc_RDP_SIZE_UPPER], 
                         wa_sr_data_r[`npuarc_RDP_SIZE_LOWER] }; 
    rdp0_ue_r    <= wa_sr_data_r[`npuarc_RDP_E_BIT];
    rdp0_uw_r    <= wa_sr_data_r[`npuarc_RDP_W_BIT];
    rdp0_urd_r   <= wa_sr_data_r[`npuarc_RDP_RD_BIT];
    rdp0_ke_r    <= wa_sr_data_r[`npuarc_RDP_UE_BIT];
    rdp0_kw_r    <= wa_sr_data_r[`npuarc_RDP_UW_BIT];
    rdp0_krd_r   <= wa_sr_data_r[`npuarc_RDP_URD_BIT];
  end
end // block : mpu_rdp0_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining MPU_RDB1 auxiliary register                //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : mpu_rdb1_PROC
  if (rst_a == 1'b1)
  begin
    rdb1_base_r  <= `npuarc_RDB_BASE_BITS'd0;
    rdb1_v_r     <= 1'b0;
  end
  else if (mpu_rdb1_en == 1'b1)
  begin
    rdb1_base_r  <= wa_sr_data_r[`npuarc_RDB_RGN_RANGE];
    rdb1_v_r     <= wa_sr_data_r[`npuarc_RDB_V_BIT];
  end
end // block : mpu_rdb1_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining MPU_RDP1 auxiliary register                //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : mpu_rdp1_PROC
  if (rst_a == 1'b1)
  begin
    rdp1_size_r  <= `npuarc_RDP_SIZE_BITS'd0;
    rdp1_ue_r    <= 1'b0;
    rdp1_uw_r    <= 1'b0;
    rdp1_urd_r   <= 1'b0;
    rdp1_ke_r    <= 1'b0;
    rdp1_kw_r    <= 1'b0;
    rdp1_krd_r   <= 1'b0;
  end
  else if (mpu_rdp1_en == 1'b1)
  begin
    rdp1_size_r  <= { wa_sr_data_r[`npuarc_RDP_SIZE_UPPER], 
                         wa_sr_data_r[`npuarc_RDP_SIZE_LOWER] }; 
    rdp1_ue_r    <= wa_sr_data_r[`npuarc_RDP_E_BIT];
    rdp1_uw_r    <= wa_sr_data_r[`npuarc_RDP_W_BIT];
    rdp1_urd_r   <= wa_sr_data_r[`npuarc_RDP_RD_BIT];
    rdp1_ke_r    <= wa_sr_data_r[`npuarc_RDP_UE_BIT];
    rdp1_kw_r    <= wa_sr_data_r[`npuarc_RDP_UW_BIT];
    rdp1_krd_r   <= wa_sr_data_r[`npuarc_RDP_URD_BIT];
  end
end // block : mpu_rdp1_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining MPU_RDB2 auxiliary register                //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : mpu_rdb2_PROC
  if (rst_a == 1'b1)
  begin
    rdb2_base_r  <= `npuarc_RDB_BASE_BITS'd0;
    rdb2_v_r     <= 1'b0;
  end
  else if (mpu_rdb2_en == 1'b1)
  begin
    rdb2_base_r  <= wa_sr_data_r[`npuarc_RDB_RGN_RANGE];
    rdb2_v_r     <= wa_sr_data_r[`npuarc_RDB_V_BIT];
  end
end // block : mpu_rdb2_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining MPU_RDP2 auxiliary register                //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : mpu_rdp2_PROC
  if (rst_a == 1'b1)
  begin
    rdp2_size_r  <= `npuarc_RDP_SIZE_BITS'd0;
    rdp2_ue_r    <= 1'b0;
    rdp2_uw_r    <= 1'b0;
    rdp2_urd_r   <= 1'b0;
    rdp2_ke_r    <= 1'b0;
    rdp2_kw_r    <= 1'b0;
    rdp2_krd_r   <= 1'b0;
  end
  else if (mpu_rdp2_en == 1'b1)
  begin
    rdp2_size_r  <= { wa_sr_data_r[`npuarc_RDP_SIZE_UPPER], 
                         wa_sr_data_r[`npuarc_RDP_SIZE_LOWER] }; 
    rdp2_ue_r    <= wa_sr_data_r[`npuarc_RDP_E_BIT];
    rdp2_uw_r    <= wa_sr_data_r[`npuarc_RDP_W_BIT];
    rdp2_urd_r   <= wa_sr_data_r[`npuarc_RDP_RD_BIT];
    rdp2_ke_r    <= wa_sr_data_r[`npuarc_RDP_UE_BIT];
    rdp2_kw_r    <= wa_sr_data_r[`npuarc_RDP_UW_BIT];
    rdp2_krd_r   <= wa_sr_data_r[`npuarc_RDP_URD_BIT];
  end
end // block : mpu_rdp2_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining MPU_RDB3 auxiliary register                //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : mpu_rdb3_PROC
  if (rst_a == 1'b1)
  begin
    rdb3_base_r  <= `npuarc_RDB_BASE_BITS'd0;
    rdb3_v_r     <= 1'b0;
  end
  else if (mpu_rdb3_en == 1'b1)
  begin
    rdb3_base_r  <= wa_sr_data_r[`npuarc_RDB_RGN_RANGE];
    rdb3_v_r     <= wa_sr_data_r[`npuarc_RDB_V_BIT];
  end
end // block : mpu_rdb3_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining MPU_RDP3 auxiliary register                //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : mpu_rdp3_PROC
  if (rst_a == 1'b1)
  begin
    rdp3_size_r  <= `npuarc_RDP_SIZE_BITS'd0;
    rdp3_ue_r    <= 1'b0;
    rdp3_uw_r    <= 1'b0;
    rdp3_urd_r   <= 1'b0;
    rdp3_ke_r    <= 1'b0;
    rdp3_kw_r    <= 1'b0;
    rdp3_krd_r   <= 1'b0;
  end
  else if (mpu_rdp3_en == 1'b1)
  begin
    rdp3_size_r  <= { wa_sr_data_r[`npuarc_RDP_SIZE_UPPER], 
                         wa_sr_data_r[`npuarc_RDP_SIZE_LOWER] }; 
    rdp3_ue_r    <= wa_sr_data_r[`npuarc_RDP_E_BIT];
    rdp3_uw_r    <= wa_sr_data_r[`npuarc_RDP_W_BIT];
    rdp3_urd_r   <= wa_sr_data_r[`npuarc_RDP_RD_BIT];
    rdp3_ke_r    <= wa_sr_data_r[`npuarc_RDP_UE_BIT];
    rdp3_kw_r    <= wa_sr_data_r[`npuarc_RDP_UW_BIT];
    rdp3_krd_r   <= wa_sr_data_r[`npuarc_RDP_URD_BIT];
  end
end // block : mpu_rdp3_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining MPU_RDB4 auxiliary register                //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : mpu_rdb4_PROC
  if (rst_a == 1'b1)
  begin
    rdb4_base_r  <= `npuarc_RDB_BASE_BITS'd0;
    rdb4_v_r     <= 1'b0;
  end
  else if (mpu_rdb4_en == 1'b1)
  begin
    rdb4_base_r  <= wa_sr_data_r[`npuarc_RDB_RGN_RANGE];
    rdb4_v_r     <= wa_sr_data_r[`npuarc_RDB_V_BIT];
  end
end // block : mpu_rdb4_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining MPU_RDP4 auxiliary register                //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : mpu_rdp4_PROC
  if (rst_a == 1'b1)
  begin
    rdp4_size_r  <= `npuarc_RDP_SIZE_BITS'd0;
    rdp4_ue_r    <= 1'b0;
    rdp4_uw_r    <= 1'b0;
    rdp4_urd_r   <= 1'b0;
    rdp4_ke_r    <= 1'b0;
    rdp4_kw_r    <= 1'b0;
    rdp4_krd_r   <= 1'b0;
  end
  else if (mpu_rdp4_en == 1'b1)
  begin
    rdp4_size_r  <= { wa_sr_data_r[`npuarc_RDP_SIZE_UPPER], 
                         wa_sr_data_r[`npuarc_RDP_SIZE_LOWER] }; 
    rdp4_ue_r    <= wa_sr_data_r[`npuarc_RDP_E_BIT];
    rdp4_uw_r    <= wa_sr_data_r[`npuarc_RDP_W_BIT];
    rdp4_urd_r   <= wa_sr_data_r[`npuarc_RDP_RD_BIT];
    rdp4_ke_r    <= wa_sr_data_r[`npuarc_RDP_UE_BIT];
    rdp4_kw_r    <= wa_sr_data_r[`npuarc_RDP_UW_BIT];
    rdp4_krd_r   <= wa_sr_data_r[`npuarc_RDP_URD_BIT];
  end
end // block : mpu_rdp4_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining MPU_RDB5 auxiliary register                //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : mpu_rdb5_PROC
  if (rst_a == 1'b1)
  begin
    rdb5_base_r  <= `npuarc_RDB_BASE_BITS'd0;
    rdb5_v_r     <= 1'b0;
  end
  else if (mpu_rdb5_en == 1'b1)
  begin
    rdb5_base_r  <= wa_sr_data_r[`npuarc_RDB_RGN_RANGE];
    rdb5_v_r     <= wa_sr_data_r[`npuarc_RDB_V_BIT];
  end
end // block : mpu_rdb5_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining MPU_RDP5 auxiliary register                //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : mpu_rdp5_PROC
  if (rst_a == 1'b1)
  begin
    rdp5_size_r  <= `npuarc_RDP_SIZE_BITS'd0;
    rdp5_ue_r    <= 1'b0;
    rdp5_uw_r    <= 1'b0;
    rdp5_urd_r   <= 1'b0;
    rdp5_ke_r    <= 1'b0;
    rdp5_kw_r    <= 1'b0;
    rdp5_krd_r   <= 1'b0;
  end
  else if (mpu_rdp5_en == 1'b1)
  begin
    rdp5_size_r  <= { wa_sr_data_r[`npuarc_RDP_SIZE_UPPER], 
                         wa_sr_data_r[`npuarc_RDP_SIZE_LOWER] }; 
    rdp5_ue_r    <= wa_sr_data_r[`npuarc_RDP_E_BIT];
    rdp5_uw_r    <= wa_sr_data_r[`npuarc_RDP_W_BIT];
    rdp5_urd_r   <= wa_sr_data_r[`npuarc_RDP_RD_BIT];
    rdp5_ke_r    <= wa_sr_data_r[`npuarc_RDP_UE_BIT];
    rdp5_kw_r    <= wa_sr_data_r[`npuarc_RDP_UW_BIT];
    rdp5_krd_r   <= wa_sr_data_r[`npuarc_RDP_URD_BIT];
  end
end // block : mpu_rdp5_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining MPU_RDB6 auxiliary register                //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : mpu_rdb6_PROC
  if (rst_a == 1'b1)
  begin
    rdb6_base_r  <= `npuarc_RDB_BASE_BITS'd0;
    rdb6_v_r     <= 1'b0;
  end
  else if (mpu_rdb6_en == 1'b1)
  begin
    rdb6_base_r  <= wa_sr_data_r[`npuarc_RDB_RGN_RANGE];
    rdb6_v_r     <= wa_sr_data_r[`npuarc_RDB_V_BIT];
  end
end // block : mpu_rdb6_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining MPU_RDP6 auxiliary register                //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : mpu_rdp6_PROC
  if (rst_a == 1'b1)
  begin
    rdp6_size_r  <= `npuarc_RDP_SIZE_BITS'd0;
    rdp6_ue_r    <= 1'b0;
    rdp6_uw_r    <= 1'b0;
    rdp6_urd_r   <= 1'b0;
    rdp6_ke_r    <= 1'b0;
    rdp6_kw_r    <= 1'b0;
    rdp6_krd_r   <= 1'b0;
  end
  else if (mpu_rdp6_en == 1'b1)
  begin
    rdp6_size_r  <= { wa_sr_data_r[`npuarc_RDP_SIZE_UPPER], 
                         wa_sr_data_r[`npuarc_RDP_SIZE_LOWER] }; 
    rdp6_ue_r    <= wa_sr_data_r[`npuarc_RDP_E_BIT];
    rdp6_uw_r    <= wa_sr_data_r[`npuarc_RDP_W_BIT];
    rdp6_urd_r   <= wa_sr_data_r[`npuarc_RDP_RD_BIT];
    rdp6_ke_r    <= wa_sr_data_r[`npuarc_RDP_UE_BIT];
    rdp6_kw_r    <= wa_sr_data_r[`npuarc_RDP_UW_BIT];
    rdp6_krd_r   <= wa_sr_data_r[`npuarc_RDP_URD_BIT];
  end
end // block : mpu_rdp6_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining MPU_RDB7 auxiliary register                //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : mpu_rdb7_PROC
  if (rst_a == 1'b1)
  begin
    rdb7_base_r  <= `npuarc_RDB_BASE_BITS'd0;
    rdb7_v_r     <= 1'b0;
  end
  else if (mpu_rdb7_en == 1'b1)
  begin
    rdb7_base_r  <= wa_sr_data_r[`npuarc_RDB_RGN_RANGE];
    rdb7_v_r     <= wa_sr_data_r[`npuarc_RDB_V_BIT];
  end
end // block : mpu_rdb7_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining MPU_RDP7 auxiliary register                //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : mpu_rdp7_PROC
  if (rst_a == 1'b1)
  begin
    rdp7_size_r  <= `npuarc_RDP_SIZE_BITS'd0;
    rdp7_ue_r    <= 1'b0;
    rdp7_uw_r    <= 1'b0;
    rdp7_urd_r   <= 1'b0;
    rdp7_ke_r    <= 1'b0;
    rdp7_kw_r    <= 1'b0;
    rdp7_krd_r   <= 1'b0;
  end
  else if (mpu_rdp7_en == 1'b1)
  begin
    rdp7_size_r  <= { wa_sr_data_r[`npuarc_RDP_SIZE_UPPER], 
                         wa_sr_data_r[`npuarc_RDP_SIZE_LOWER] }; 
    rdp7_ue_r    <= wa_sr_data_r[`npuarc_RDP_E_BIT];
    rdp7_uw_r    <= wa_sr_data_r[`npuarc_RDP_W_BIT];
    rdp7_urd_r   <= wa_sr_data_r[`npuarc_RDP_RD_BIT];
    rdp7_ke_r    <= wa_sr_data_r[`npuarc_RDP_UE_BIT];
    rdp7_kw_r    <= wa_sr_data_r[`npuarc_RDP_UW_BIT];
    rdp7_krd_r   <= wa_sr_data_r[`npuarc_RDP_URD_BIT];
  end
end // block : mpu_rdp7_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining mask_diff_r register                        //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : mask_diff_PROC
  if (rst_a == 1'b1)
  begin
    mask_diff_r     <= `npuarc_MPU_NUM_REGIONS'd0;
  end
  else if (mask_diff_en == 1'b1)
  begin
    mask_diff_r     <= mask_diff_nxt;
  end
end // block : mask_diff_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining new_size_r register                         //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : new_size_PROC
  if (rst_a == 1'b1)
  begin
    new_size_r      <= `npuarc_RDP_SIZE_BITS'd0;
  end
  else if (new_size_en == 1'b1)
  begin
    new_size_r      <= { wa_sr_data_r[`npuarc_RDP_SIZE_UPPER], 
                         wa_sr_data_r[`npuarc_RDP_SIZE_LOWER] };
  end
end // block : new_size_PROC 

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining addr_mask0 register                        //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : addr_mask0_PROC
  if (rst_a == 1'b1)
  begin
    addr_mask0_r   <= `npuarc_RDB_BASE_BITS'd0;
  end
  else if (mask_diff_r[0] == 1'b1)
  begin
    addr_mask0_r   <= addr_mask_nxt;
  end
end // block : addr_mask0_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining addr_mask1 register                        //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : addr_mask1_PROC
  if (rst_a == 1'b1)
  begin
    addr_mask1_r   <= `npuarc_RDB_BASE_BITS'd0;
  end
  else if (mask_diff_r[1] == 1'b1)
  begin
    addr_mask1_r   <= addr_mask_nxt;
  end
end // block : addr_mask1_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining addr_mask2 register                        //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : addr_mask2_PROC
  if (rst_a == 1'b1)
  begin
    addr_mask2_r   <= `npuarc_RDB_BASE_BITS'd0;
  end
  else if (mask_diff_r[2] == 1'b1)
  begin
    addr_mask2_r   <= addr_mask_nxt;
  end
end // block : addr_mask2_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining addr_mask3 register                        //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : addr_mask3_PROC
  if (rst_a == 1'b1)
  begin
    addr_mask3_r   <= `npuarc_RDB_BASE_BITS'd0;
  end
  else if (mask_diff_r[3] == 1'b1)
  begin
    addr_mask3_r   <= addr_mask_nxt;
  end
end // block : addr_mask3_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining addr_mask4 register                        //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : addr_mask4_PROC
  if (rst_a == 1'b1)
  begin
    addr_mask4_r   <= `npuarc_RDB_BASE_BITS'd0;
  end
  else if (mask_diff_r[4] == 1'b1)
  begin
    addr_mask4_r   <= addr_mask_nxt;
  end
end // block : addr_mask4_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining addr_mask5 register                        //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : addr_mask5_PROC
  if (rst_a == 1'b1)
  begin
    addr_mask5_r   <= `npuarc_RDB_BASE_BITS'd0;
  end
  else if (mask_diff_r[5] == 1'b1)
  begin
    addr_mask5_r   <= addr_mask_nxt;
  end
end // block : addr_mask5_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining addr_mask6 register                        //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : addr_mask6_PROC
  if (rst_a == 1'b1)
  begin
    addr_mask6_r   <= `npuarc_RDB_BASE_BITS'd0;
  end
  else if (mask_diff_r[6] == 1'b1)
  begin
    addr_mask6_r   <= addr_mask_nxt;
  end
end // block : addr_mask6_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining addr_mask7 register                        //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : addr_mask7_PROC
  if (rst_a == 1'b1)
  begin
    addr_mask7_r   <= `npuarc_RDB_BASE_BITS'd0;
  end
  else if (mask_diff_r[7] == 1'b1)
  begin
    addr_mask7_r   <= addr_mask_nxt;
  end
end // block : addr_mask7_PROC


endmodule // module : alb_mpu
