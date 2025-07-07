//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2012 Synopsys, Inc. All rights reserved.
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
// ######   #######   #####   #######  ######   #######         
// #     #  #        #     #  #     #  #     #  #               
// #     #  #        #        #     #  #     #  #               
// #     #  #####    #        #     #  #     #  #####           
// #     #  #        #        #     #  #     #  #               
// #     #  #        #     #  #     #  #     #  #               
// ######   #######   #####   #######  ######   #######  #####  
//
//
//  #####   #######  #     #   #####   #######  
// #     #  #     #  ##    #  #     #     #     
// #        #     #  # #   #  #           #     
// #        #     #  #  #  #   #####      #     
// #        #     #  #   # #        #     #     
// #     #  #     #  #    ##  #     #     #     
//  #####   #######  #     #   #####      #     
//
// ===========================================================================
//
// Description:
//
//  This file defines all the constants used to perform instruction
//  decode for the ARCompact instruction set.
//
// ===========================================================================

// There are 32 major opcode groups, each of which is identified by a
// 5-bit field. The following `defines give names to each of these.

`define npuarc_GRP_BRANCH_32     5'd0
`define npuarc_GRP_BL_BRCC_32    5'd1
`define npuarc_GRP_LOAD_32       5'd2
`define npuarc_GRP_STORE_32      5'd3

`define npuarc_GRP_BASECASE_32   5'd4
`define npuarc_GRP_ARC_EXT0_32   5'd5
`define npuarc_GRP_ARC_EXT1_32   5'd6
`define npuarc_GRP_USR_EXT2_32   5'd7

`define npuarc_GRP_ARC_EXT0_16   5'd8
`define npuarc_GRP_ARC_EXT1_16   5'd9
`define npuarc_GRP_USR_EXT0_16   5'd10
`define npuarc_GRP_USR_EXT1_16   5'd11

`define npuarc_GRP_LD_ADD_RR_16  5'd12
`define npuarc_GRP_ADD_SUB_SH_16 5'd13
`define npuarc_GRP_MV_CMP_ADD_16 5'd14
`define npuarc_GRP_GEN_OPS_16    5'd15

`define npuarc_GRP_LD_WORD_16    5'd16
`define npuarc_GRP_LD_BYTE_16    5'd17
`define npuarc_GRP_LD_HALF_16    5'd18
`define npuarc_GRP_LD_HALFX_16   5'd19

`define npuarc_GRP_ST_WORD_16    5'd20
`define npuarc_GRP_ST_BYTE_16    5'd21
`define npuarc_GRP_ST_HALF_16    5'd22
`define npuarc_GRP_SH_SUB_BIT_16 5'd23

`define npuarc_GRP_SP_MEM_16     5'd24
`define npuarc_GRP_GP_MEM_16     5'd25
`define npuarc_GRP_LD_PCL_16     5'd26
`define npuarc_GRP_MV_IMM_16     5'd27

`define npuarc_GRP_ADD_IMM_16    5'd28
`define npuarc_GRP_BRCC_S_16     5'd29
`define npuarc_GRP_BCC_S_16      5'd30
`define npuarc_GRP_BL_S_16       5'd31

// There are four main operand formats in the 0x04
// group of instructions. These are listed below.
//
`define npuarc_REG_REG_FMT       2'b00
`define npuarc_REG_U6IMM_FMT     2'b01
`define npuarc_REG_S12IMM_FMT    2'b10
`define npuarc_REG_COND_FMT      2'b11

// The 0x04 group of instruction contains the following
// dual operand instructions (mov is an exception!)
//
`define npuarc_ADD_OP            6'h00
`define npuarc_ADC_OP            6'h01
`define npuarc_SUB_OP            6'h02
`define npuarc_SBC_OP            6'h03
`define npuarc_AND_OP            6'h04
`define npuarc_OR_OP             6'h05
`define npuarc_BIC_OP            6'h06
`define npuarc_XOR_OP            6'h07
`define npuarc_MAX_OP            6'h08
`define npuarc_MIN_OP            6'h09
`define npuarc_MOV_OP            6'h0a
`define npuarc_TST_OP            6'h0b
`define npuarc_CMP_OP            6'h0c
`define npuarc_RCMP_OP           6'h0d
`define npuarc_RSUB_OP           6'h0e
`define npuarc_BSET_OP           6'h0f
`define npuarc_BCLR_OP           6'h10
`define npuarc_BTST_OP           6'h11
`define npuarc_BXOR_OP           6'h12
`define npuarc_BMSK_OP           6'h13
`define npuarc_ADD1_OP           6'h14
`define npuarc_ADD2_OP           6'h15
`define npuarc_ADD3_OP           6'h16
`define npuarc_SUB1_OP           6'h17
`define npuarc_SUB2_OP           6'h18
`define npuarc_SUB3_OP           6'h19
`define npuarc_JCC_OP            6'h20
`define npuarc_JCC_D_OP          6'h21
`define npuarc_JLCC_OP           6'h22
`define npuarc_JLCC_D_OP         6'h23
`define npuarc_BI_OP             6'h24
`define npuarc_BIH_OP            6'h25
`define npuarc_LDI_OP            6'h26
`define npuarc_AEX_OP            6'h27
`define npuarc_LPCC_OP           6'h28
`define npuarc_FLAG_OP           6'h29
`define npuarc_LR_OP             6'h2a
`define npuarc_SR_OP             6'h2b
`define npuarc_BMSKN_OP          6'h2c
`define npuarc_XBFU_OP           6'h2d
`define npuarc_SOP_FMT           6'h2f
`define npuarc_LD_RR_FMT         3'b110

// The compare-branch instructions are listed
// below, together with their opcodes.
//
`define npuarc_BREQ_OP           3'h0
`define npuarc_BRNE_OP           3'h1
`define npuarc_BRLT_OP           3'h2
`define npuarc_BRGE_OP           3'h3
`define npuarc_BRLO_OP           3'h4
`define npuarc_BRHS_OP           3'h5
`define npuarc_BBIT0_OP          3'h6
`define npuarc_BBIT1_OP          3'h7

// The encodings of relational operator or bit tests for
// each of the BRcc, BBITn and SETcc instructions are given below.
//
`define npuarc_EQ_TEST         3'h0
`define npuarc_NE_TEST         3'h1
`define npuarc_LT_TEST         3'h2
`define npuarc_GE_TEST         3'h3
`define npuarc_LO_TEST         3'h4
`define npuarc_HS_TEST         3'h5
`define npuarc_LE_TEST         3'h6
`define npuarc_GT_TEST         3'h7

// All single-operand 32-bit opcodes
//
`define npuarc_ASL_OP            6'h00
`define npuarc_ASR_OP            6'h01
`define npuarc_LSR_OP            6'h02
`define npuarc_ROR_OP            6'h03
`define npuarc_RRC_OP            6'h04
`define npuarc_SEXB_OP           6'h05
`define npuarc_SEXW_OP           6'h06
`define npuarc_EXTB_OP           6'h07
`define npuarc_EXTW_OP           6'h08
`define npuarc_ABS_OP            6'h09
`define npuarc_NOT_OP            6'h0a
`define npuarc_RLC_OP            6'h0b
`define npuarc_EX_OP             6'h0c
`define npuarc_ROL_OP            6'h0d
`define npuarc_LDL_OP            6'h10
`define npuarc_STC_OP            6'h11
`define npuarc_LDDL_OP           6'h12
`define npuarc_STDC_OP           6'h13
`define npuarc_ZOP_FMT           6'h3f

// All zero-operand instructions
//
`define npuarc_SLEEP_OP          6'h01
`define npuarc_TRAP0_OP          6'h02
`define npuarc_SWI_OP            6'h02
`define npuarc_SYNC_OP           6'h03
`define npuarc_RTIE_OP           6'h04
`define npuarc_BRK_OP            6'h05
`define npuarc_SETI_OP           6'h06
`define npuarc_CLRI_OP           6'h07
`define npuarc_WEVT_OP           6'h08
`define npuarc_WLFC_OP           6'h09
`define npuarc_DSYNC_OP          6'h0a
`define npuarc_DMB_OP            6'h0b

//////////////////////////////////////////////////////////////////////////////
// Extension opcodes and instruction formats
//////////////////////////////////////////////////////////////////////////////

// Barrel shift operations are encoded in GRP_ARC_EXT0_32
// and are dual operand instructions
//
`define npuarc_ASLM_OP           6'h00
`define npuarc_LSRM_OP           6'h01
`define npuarc_ASRM_OP           6'h02
`define npuarc_RORM_OP           6'h03

// 64-bit multiplier operations are encoded in GRP_ARC_EXT0_32
// and are dual operand instructions
// [DEPRECATED in ARC 6000]
//
`define npuarc_MUL64_OP          6'h04
`define npuarc_MULU64_OP         6'h05

// Extension byte operations is encoded in GRP_ARC_EXT0_32
// and are all single operand instructions.
// These four operations are included under the SWAP_OPTION
//
`define npuarc_SWAP_OP           6'h00
`define npuarc_SWAPE_OP          6'h09
`define npuarc_LSL16_OP          6'h0a
`define npuarc_LSR16_OP          6'h0b

// Extension byte operations is encoded in GRP_ARC_EXT0_32
// and are all single operand instructions.
// These six operations are included under the SHIFT_ASSIST
// configuration option, when SWAP_OPTION is also enabled.
//
`define npuarc_ASR16_OP          6'h0c
`define npuarc_ASR8_OP           6'h0d
`define npuarc_LSR8_OP           6'h0e
`define npuarc_LSL8_OP           6'h0f
`define npuarc_ROL8_OP           6'h10
`define npuarc_ROR8_OP           6'h11

// NORM operations are encoded in GRP_ARC_EXT0_32
// and are single operand instructions
//
`define npuarc_NORM_OP           6'h01
`define npuarc_NORMW_OP          6'h08
`define npuarc_FFS_OP            6'h12
`define npuarc_FLS_OP            6'h13

// Extended arithmetic operations are encoded in GRP_ARC_EXT0_32
// [DEPRECATED in ARC 6000: ADDSDW_OP, SUBSDW_OP]
//
// dual operand extended-arith instructions
//
`define npuarc_ADDS_OP           6'h06
`define npuarc_SUBS_OP           6'h07
`define npuarc_ADDSDW_OP         6'h24
`define npuarc_SUBSDW_OP         6'h29
`define npuarc_ASLS_OP           6'h0a
`define npuarc_ASRS_OP           6'h0b

// single operand extended-arith instructions
//
`define npuarc_NEGS_OP           6'h07
`define npuarc_NEGSW_OP          6'h06

// DSP operations are encoded in GRP_ARC_EXT0_32
//
// dual operand DSP instructions
// [DEPRECATED in ARC 6000]
//
`define npuarc_DIVAW_OP          6'h08

// single operand DSP instructions
// [DEPRECATED in ARC 6000]
//
`define npuarc_SAT16_OP          6'h02
`define npuarc_RND16_OP          6'h03
`define npuarc_ABSSW_OP          6'h04
`define npuarc_ABSS_OP           6'h05

// Multiplication operations are encoded in GRP_BASECASE_32
// and are dual operand instructions
//
`define npuarc_MPYLO_OP          6'h1a
`define npuarc_MPYHI_OP          6'h1b
`define npuarc_MPYHIU_OP         6'h1c
`define npuarc_MPYLOU_OP         6'h1d
`define npuarc_MPYW_OP           6'h1e
`define npuarc_MPYUW_OP          6'h1f

// SETcc opcodes are encoded in the GRP_BASECASE_32 and are
// all dual operand instructions
//
`define npuarc_SETEQ_OP          6'h38
`define npuarc_SETNE_OP          6'h39
`define npuarc_SETLT_OP          6'h3a
`define npuarc_SETGE_OP          6'h3b
`define npuarc_SETLO_OP          6'h3c
`define npuarc_SETHS_OP          6'h3d
`define npuarc_SETLE_OP          6'h3e
`define npuarc_SETGT_OP          6'h3f

// DIV, DIVU, REM, REMU operations are encoded in GRP_ARC_EXT0_32
// These currently reuse the opcodes of DIVAW, MUL64 and MULU64, 
// which are not included in the ARC 6000 ISA.
//
`define npuarc_DIV_OP            6'h04
`define npuarc_DIVU_OP           6'h05
`define npuarc_REM_OP            6'h08
`define npuarc_REMU_OP           6'h09

// MAC, vector MPY/MAC, and vector ADD/SUB operations are
// encoded in GRP_ARC_EXT0_32, using opcodes 0x0E-0x1D and
// 0x30-0x3F.
//
// -- enabled when MPY_OPTION > 6
`define npuarc_MAC_OP            6'h0e
`define npuarc_MACU_OP           6'h0f
`define npuarc_DMPYH_OP          6'h10
`define npuarc_DMPYHU_OP         6'h11
`define npuarc_DMACH_OP          6'h12
`define npuarc_DMACHU_OP         6'h13
`define npuarc_VADD2H_OP         6'h14
`define npuarc_VSUB2H_OP         6'h15
`define npuarc_VADDSUB2H_OP      6'h16
`define npuarc_VSUBADD2H_OP      6'h17
// -- enabled when MPY_OPTION > 7
`define npuarc_MPYD_OP           6'h18
`define npuarc_MPYDU_OP          6'h19
`define npuarc_MACD_OP           6'h1a
`define npuarc_MACDU_OP          6'h1b
`define npuarc_VMPY2H_OP         6'h1c
`define npuarc_VMPY2HU_OP        6'h1d
`define npuarc_VMAC2H_OP         6'h1e
`define npuarc_VMAC2HU_OP        6'h1f
// -- enabled when MPY_OPTION > 8
`define npuarc_QMPYH_OP          6'h30
`define npuarc_QMPYHU_OP         6'h31
`define npuarc_DMPYWH_OP         6'h32
`define npuarc_DMPYWHU_OP        6'h33
`define npuarc_QMACH_OP          6'h34
`define npuarc_QMACHU_OP         6'h35
`define npuarc_DMACWH_OP         6'h36
`define npuarc_DMACHWHU_OP       6'h37
`define npuarc_VADD4H_OP         6'h38
`define npuarc_VSUB4H_OP         6'h39
`define npuarc_VADDSUB4H_OP      6'h3a
`define npuarc_VSUBADD4H_OP      6'h3b
`define npuarc_VADD2_OP          6'h3c
`define npuarc_VSUB2_OP          6'h3d
`define npuarc_VADDSUB_OP        6'h3e
`define npuarc_VSUBADD_OP        6'h3f

// Some DSP instructions are encoded in GRP_ARC_EXT0_32, 
// and are additional to MPY_OPTION8/9
`define npuarc_ASRSR_OP          6'h0C
`define npuarc_VALGN2H_OP        6'h0D
`define npuarc_VMPY2HWF_OP       6'h20
`define npuarc_VASL2H_OP         6'h21
`define npuarc_VASR2H_OP         6'h22
`define npuarc_VLSR2H_OP         6'h23
`define npuarc_VADD4B_OP         6'h24
`define npuarc_VSUB4B_OP         6'h25
`define npuarc_ADCS_OP           6'h26
`define npuarc_SBCS_OP           6'h27
`define npuarc_DMPYHWF_OP        6'h28
`define npuarc_VPACK2HL_OP       6'h29
`define npuarc_DMPYHF_OP         6'h2a
`define npuarc_DMPYHFR_OP        6'h2b
`define npuarc_DMACHF_OP         6'h2c
`define npuarc_DMACHFR_OP        6'h2d
`define npuarc_VPERM_OP          6'h2e
`define npuarc_SATH_OP           6'h02
`define npuarc_RNDH_OP           6'h03
`define npuarc_ABSSH_OP          6'h04
`define npuarc_ABSS_OP           6'h05
`define npuarc_NEGSH_OP          6'h06
`define npuarc_NEGS_OP           6'h07
`define npuarc_GETACC_OP         6'h18
`define npuarc_NORMACC_OP        6'h19
`define npuarc_SATF_OP           6'h1a
`define npuarc_VPACK2HBL_OP      6'h1c
`define npuarc_VPACK2HBM_OP      6'h1d
`define npuarc_VPACK2HBLF_OP     6'h1e
`define npuarc_VPACK2HBMF_OP     6'h1f
`define npuarc_VEXT2BHLF_OP      6'h20
`define npuarc_VEXT2BHMF_OP      6'h21
`define npuarc_VREP2HL_OP        6'h22
`define npuarc_VREP2HM_OP        6'h23
`define npuarc_VEXT2BHL_OP       6'h24
`define npuarc_VEXT2BHM_OP       6'h25
`define npuarc_VSEXT2BHL_OP      6'h26
`define npuarc_VSEXT2BHM_OP      6'h27
`define npuarc_VABS2H_OP         6'h28
`define npuarc_VABSS2H_OP        6'h29
`define npuarc_VNEG2H_OP         6'h2a
`define npuarc_VNEGS2H_OP        6'h2b
`define npuarc_VNORM2H_OP        6'h2c
`define npuarc_DIVF_OP           6'h10
`define npuarc_SQRT_OP           6'h30
`define npuarc_SQRTF_OP          6'h31
`define npuarc_MODAPP_OP         6'h3e
`define npuarc_ASLACC_OP         6'h00
`define npuarc_ASLSACC_OP        6'h01
`define npuarc_FLAGACC_OP        6'h04
`define npuarc_MODIF_OP          6'h05

// Some DSP instructions are encoded in GRP_ARC_EXT1_32
`define npuarc_MPYF_OP           6'h0A
`define npuarc_MPYFR_OP          6'h0B
`define npuarc_MACF_OP           6'h0C
`define npuarc_MACFR_OP          6'h0D
`define npuarc_MSUBF_OP          6'h0E
`define npuarc_MSUBFR_OP         6'h0F
`define npuarc_DIVF_OP           6'h10
`define npuarc_VMAC2HNFR_OP      6'h11
`define npuarc_MPYDF_OP          6'h12
`define npuarc_MACDF_OP          6'h13
`define npuarc_MSUBWHFL_OP       6'h14
`define npuarc_MSUBDF_OP         6'h15
`define npuarc_DMPYHBL_OP        6'h16
`define npuarc_DMPYHBM_OP        6'h17
`define npuarc_DMACHBL_OP        6'h18
`define npuarc_DMACHBM_OP        6'h19
`define npuarc_MSUBWHFLR_OP      6'h1A
`define npuarc_CMPYHFMR_OP       6'h1B
`define npuarc_MPYWHL_OP         6'h1C
`define npuarc_MACWHL_OP         6'h1D
`define npuarc_MPYWHUL_OP        6'h1E
`define npuarc_MACWHUL_OP        6'h1F
`define npuarc_MPYWHFM_OP        6'h20
`define npuarc_MPYWHFMR_OP       6'h21
`define npuarc_MACWHFM_OP        6'h22
`define npuarc_MACWHFMR_OP       6'h23
`define npuarc_MPYWHFL_OP        6'h24
`define npuarc_MPYWHFLR_OP       6'h25
`define npuarc_MACWHFL_OP        6'h26
`define npuarc_MACWHFLR_OP       6'h27
`define npuarc_MACWHKL_OP        6'h28
`define npuarc_MACWHKUL_OP       6'h29
`define npuarc_MPYWHKL_OP        6'h2A
`define npuarc_MPYWHKUL_OP       6'h2B
`define npuarc_MSUBWHFM_OP       6'h2C
`define npuarc_MSUBWHFMR_OP      6'h2D
`define npuarc_QMPYHF_OP         6'h3C
`define npuarc_DMPYWHF_OP        6'h3D
`define npuarc_QMACHF_OP         6'h3E
`define npuarc_DMACWHF_OP        6'h3F
`define npuarc_CBFLYHF1R_OP      6'h19


// FPU dual-operand (DOP format), single-precision instruction opcodes
//
`define npuarc_FSMUL             6'h00
`define npuarc_FSADD             6'h01
`define npuarc_FSSUB             6'h02
`define npuarc_FSCMP             6'h03
`define npuarc_FSCMPF            6'h04
`define npuarc_FSMADD            6'h05
`define npuarc_FSMSUB            6'h06
`define npuarc_FSDIV             6'h07
`define npuarc_FCVT32            6'h08
`define npuarc_FCVT32_64         6'h09
//
// FPU single-operand (SOP format), single-precision instruction opcodes
//
`define npuarc_FSSQRT            6'h00

// FPU dual-operand (DOP format), double-precision instruction opcodes
//
`define npuarc_FDMUL             6'h30
`define npuarc_FDADD             6'h31
`define npuarc_FDSUB             6'h32
`define npuarc_FDCMP             6'h33
`define npuarc_FDCMPF            6'h34
`define npuarc_FDMADD            6'h35
`define npuarc_FDMSUB            6'h36
`define npuarc_FDDIV             6'h37
`define npuarc_FCVT64            6'h38
`define npuarc_FCVT64_32         6'h39
//
// FPU single-operand (SOP format), single-precision instruction opcodes
//
`define npuarc_FDSQRT            6'h01


//////////////////////////////////////////////////////////////////////////////
// Auxiliary register addresses for base-case aux. registers
//////////////////////////////////////////////////////////////////////////////
//
`define npuarc_AUX_STATUS                32'h00000000
`define npuarc_AUX_SEMA                  32'h00000001
`define npuarc_AUX_LP_START              32'h00000002
`define npuarc_AUX_LP_END                32'h00000003
`define npuarc_AUX_IDENTITY              32'h00000004
`define npuarc_AUX_DEBUG                 32'h00000005
`define npuarc_AUX_PC                    32'h00000006
`define npuarc_AUX_ADCR                  32'h00000007
`define npuarc_AUX_APCR                  32'h00000008
`define npuarc_AUX_ACR                   32'h00000009
`define npuarc_AUX_STATUS32              32'h0000000A
`define npuarc_AUX_STATUS32_L1           32'h0000000B
`define npuarc_AUX_STATUS32_L2           32'h0000000C

`define npuarc_AUX_IC_IVIC               32'h00000010
`define npuarc_AUX_IC_CTRL               32'h00000011
`define npuarc_AUX_IC_LIL                32'h00000013
`define npuarc_AUX_DMC_CODE_RAM          32'h00000014
`define npuarc_AUX_TAG_ADDR_MASK         32'h00000015
`define npuarc_AUX_TAG_DATA_MASK         32'h00000016
`define npuarc_AUX_LINE_LENGTH_MASK      32'h00000017
`define npuarc_AUX_AUX_LDST_RAM          32'h00000018
`define npuarc_AUX_IC_IVIL               32'h00000019
`define npuarc_AUX_IC_RAM_ADDRESS        32'h0000001A
`define npuarc_AUX_IC_TAG                32'h0000001B
`define npuarc_AUX_IC_WP                 32'h0000001C
`define npuarc_AUX_IC_DATA               32'h0000001D
//
// Non-standard cache control register
`define npuarc_AUX_CACHE_CTRL            32'h0000001E

`define npuarc_AUX_SRAM_SEQ              32'h00000020
`define npuarc_AUX_COUNT0                32'h00000021
`define npuarc_AUX_CONTROL0              32'h00000022
`define npuarc_AUX_LIMIT0                32'h00000023
`define npuarc_AUX_PCPORT                32'h00000024
`define npuarc_AUX_INT_VECTOR_BASE       32'h00000025

`define npuarc_AUX_MACMODE               32'h00000041
`define npuarc_AUX_IRQ_LV12              32'h00000043

`define npuarc_AUX_XMAC0                 32'h00000044
`define npuarc_AUX_XMAC1                 32'h00000045
`define npuarc_AUX_XMAC2                 32'h00000046
`define npuarc_AUX_DC_IVDC               32'h00000047
`define npuarc_AUX_DC_CTRL               32'h00000048
`define npuarc_AUX_DC_LDL                32'h00000049
`define npuarc_AUX_DC_IVDL               32'h0000004A
`define npuarc_AUX_DC_FLSH               32'h0000004B
`define npuarc_AUX_DC_FLDL               32'h0000004C

`define npuarc_AUX_HEXDATA               32'h00000050
`define npuarc_AUX_HEXCTRL               32'h00000051
`define npuarc_AUX_LED                   32'h00000052
`define npuarc_AUX_LCDINSTR              32'h00000053
`define npuarc_AUX_AUX_LCD_DATA          32'h00000053
`define npuarc_AUX_LDCDATA               32'h00000054
`define npuarc_AUX_AUX_LCD_CNTRL         32'h00000054
`define npuarc_AUX_LCDSTAT               32'h00000055
`define npuarc_AUX_US_COUNT              32'h00000055
`define npuarc_AUX_DILSTAT               32'h00000056
`define npuarc_AUX_SWSTAT                32'h00000057
`define npuarc_AUX_LCD_BUTTON_REGISTER   32'h00000057
`define npuarc_AUX_DC_RAM_ADDR           32'h00000058
`define npuarc_AUX_DC_TAG                32'h00000059
`define npuarc_AUX_DC_WP                 32'h0000005A
`define npuarc_AUX_DC_DATA               32'h0000005B

//
// 32'h00000060 - 32'h0000007F = Build Configuration Registers (read only)
//
`define npuarc_AUX_BCR_VER               32'h00000060
`define npuarc_AUX_BTA_LINK_BUILD        32'h00000063
`define npuarc_AUX_TEL_INSTR_BUILD       32'h00000065
`define npuarc_AUX_VECBASE_AC_BUILD      32'h00000068
`define npuarc_AUX_RF_BUILD              32'h0000006E
`define npuarc_AUX_FP_BUILD              32'h0000006B
`define npuarc_AUX_DPFP_BUILD            32'h0000006C
`define npuarc_AUX_D_CACHE_BUILD         32'h00000072
`define npuarc_AUX_TIMER_BUILD           32'h00000075
`define npuarc_AUX_I_CACHE_BUILD         32'h00000077
`define npuarc_AUX_MULTIPLY_BUILD        32'h0000007B
`define npuarc_AUX_SWAP_BUILD            32'h0000007C
`define npuarc_AUX_NORM_BUILD            32'h0000007D
`define npuarc_AUX_MINMAX_BUILD          32'h0000007E
`define npuarc_AUX_BARREL_BUILD          32'h0000007F

//
// 32'h00000080 - 32'h0000009E = XY Memory Registers
//
`define npuarc_AUX_AX0                   32'h00000080
`define npuarc_AUX_AX1                   32'h00000081
`define npuarc_AUX_AX2                   32'h00000082
`define npuarc_AUX_AX3                   32'h00000083
`define npuarc_AUX_AY0                   32'h00000084
`define npuarc_AUX_AY1                   32'h00000085
`define npuarc_AUX_AY2                   32'h00000086
`define npuarc_AUX_AY3                   32'h00000087
`define npuarc_AUX_MX00                  32'h00000088
`define npuarc_AUX_MX01                  32'h00000089
`define npuarc_AUX_MX10                  32'h0000008A
`define npuarc_AUX_MX11                  32'h0000008B
`define npuarc_AUX_MX20                  32'h0000008C
`define npuarc_AUX_MX21                  32'h0000008D
`define npuarc_AUX_MX30                  32'h0000008E
`define npuarc_AUX_MX31                  32'h0000008F
`define npuarc_AUX_MY00                  32'h00000090
`define npuarc_AUX_MY01                  32'h00000091
`define npuarc_AUX_MY10                  32'h00000092
`define npuarc_AUX_MY11                  32'h00000093
`define npuarc_AUX_MY20                  32'h00000094
`define npuarc_AUX_MY21                  32'h00000095
`define npuarc_AUX_MY30                  32'h00000096
`define npuarc_AUX_MY31                  32'h00000097
`define npuarc_AUX_XYCONFIG              32'h00000098
`define npuarc_AUX_BURSTSYS              32'h00000099
`define npuarc_AUX_BURSTXYM              32'h0000009A
`define npuarc_AUX_BURSTSZ               32'h0000009B
`define npuarc_AUX_BURSTVAL              32'h0000009C
`define npuarc_AUX_XYLSBASEX             32'h0000009D
`define npuarc_AUX_XYLSBASEY             32'h0000009E

//
// 32'h000000C0 - 32'h000000FF = Build Configuration Registers (read only)
//
`define npuarc_AUX_ISA_CONFIG            32'h000000c2  // V2 only
`define npuarc_AUX_DMA_CONFIG            32'h000000fa  // V1 only
`define npuarc_AUX_SIMD_CONIFG           32'h000000fb  // V1 only
`define npuarc_AUX_SIMD_BUILD            32'h000000fc  // V1 only
`define npuarc_AUX_SIMD_DMA_BUILD        32'h000000fd  // V1 only

// Aux registers above the base set
//
`define npuarc_AUX_COUNT1                32'h00000100
`define npuarc_AUX_CONTROL1              32'h00000101
`define npuarc_AUX_LIMIT1                32'h00000102

// 32'h00000103 - 32'h0000011F = Reserved
// 32'h00000120 - 32'h0000013F = Reserved
// 32'h00000140 - 32'h000001FF = Reserved

`define npuarc_AUX_IRQ_LEV               32'h00000200
`define npuarc_AUX_IRQ_HINT              32'h00000201

// 32'h00000202 - 32'h0000021F = Reserved
// 32'h00000220 - 32'h00000237 = AP_A* (actionpoints)
// 32'h00000238 - 32'h000003FF = Reserved

`define npuarc_AUX_ERET                  32'h00000400
`define npuarc_AUX_ERBTA                 32'h00000401
`define npuarc_AUX_ERSTATUS              32'h00000402
`define npuarc_AUX_ECR                   32'h00000403
`define npuarc_AUX_EFA                   32'h00000404
`define npuarc_AUX_ICAUSE1               32'h0000040A
`define npuarc_AUX_ICAUSE2               32'h0000040B
`define npuarc_AUX_IENABLE               32'h0000040C
`define npuarc_AUX_ITRIGGER              32'h0000040D
`define npuarc_AUX_XPU                   32'h00000410
`define npuarc_AUX_BTA                   32'h00000412
`define npuarc_AUX_BTA_L1                32'h00000413
`define npuarc_AUX_BTA_L2                32'h00000414
`define npuarc_AUX_IRQ_PULSE_CANCEL      32'h00000415
`define npuarc_AUX_IRQ_PENDING           32'h00000416

// Optional extension auxiliary registers

`define npuarc_AUX_MULHI                 32'h00000012

// MMU Build Configuration Registers (BCRs)
//
`define npuarc_AUX_MMU_BUILD             32'h0000006F
`define npuarc_AUX_DATA_UNCACHED         32'h0000006A
//
// MMU Maintenance and Control Registers
//
`define npuarc_AUX_TLB_PD0               32'h00000405
`define npuarc_AUX_TLB_PD1               32'h00000406
`define npuarc_AUX_TLB_Index             32'h00000407
`define npuarc_AUX_TLB_Command           32'h00000408
`define npuarc_AUX_PID                   32'h00000409
`define npuarc_AUX_SCRATCH_DATA0         32'h00000418

// Floating-point extension auxiliary registers
//
`define npuarc_AUX_FP_STATUS             32'h00000300
`define npuarc_AUX_DPFP1L                32'h00000301
`define npuarc_AUX_DPFP1H                32'h00000302
`define npuarc_AUX_DPFP2L                32'h00000303
`define npuarc_AUX_DPFP2H                32'h00000304
`define npuarc_AUX_DPFP_STATUS           32'h00000305
