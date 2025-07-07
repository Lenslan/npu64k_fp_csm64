/*************************************************************************/
/**                                                                     **/
/** Copyright (C) 2021-2022 Synopsys, Inc.                              **/
/** All Rights Reserved.                                                **/
/**                                                                     **/
/** This Synopsys software and all associated documentation are         **/
/** proprietary to Synopsys, Inc. and may only be used pursuant to the  **/
/** terms and conditions of a written license agreement with Synopsys,  **/
/** Inc. All other use, reproduction, modification, or distribution of  **/
/** this Synopsys software or the associated documentation is strictly  **/
/** prohibited.                                                         **/
/**                                                                     **/
/*************************************************************************/
#define CORE_SFTY_PASSWD             	0x0
#define CORE_SFTY_CTRL				 	0x4
#define CORE_SFTY_DIAG               	0x8
#define CORE_SFTY_ERROR_STATUS       	0xc
#define CORE_SFTY_E2E_ERROR_STATUS   	0x10
#define CORE_SFTY_DCLS_ERROR_STATUS  	0x14
#define CORE_SFTY_ENABLE_INFO        	0x18
#define CORE_SFTY_DIAG_INFO          	0x1c
#define CORE_SFTY_TMR_ERR_INFO       	0x20
#define CORE_SFTY_BUS_ECC_ERROR_STATUS  0x24
#define CORE_SFTY_SB_ERROR_STATUS       0x28
#define CORE_SFTY_BUILD_AUX          	0xe0

#define SLICE_NPU_ERP_CTRL           0x000	
#define SLICE_NPU_ESYN 		         0x004	
#define SLICE_NPU_VM_STATUS0	     0x008
#define SLICE_NPU_VM_STATUS1	     0x00C
#define SLICE_NPU_VM_STATUS2	     0x010
#define SLICE_NPU_AM_STATUS0	     0x014
#define SLICE_NPU_AM_STATUS1	     0x018
#define SLICE_NPU_AM_STATUS2	     0x01C
#define SLICE_NPU_ESYN_CTRL	         0x020
#define SLICE_NPU_SBE_CNT            0x024	
#define SLICE_NPU_ERP_BUILD          0x028

#define SLICE_SFTY_PASSWD            0x40 
#define SLICE_SFTY_CTRL              0x44 
#define SLICE_SFTY_DIAG              0x48
#define SLICE_SFTY_ERROR_STATUS      0x4c
#define SLICE_SFTY_E2E_ERROR_STATUS  0x50
#define SLICE_SFTY_DCLS_ERROR_STATUS 0x54
#define SLICE_SFTY_STL_CTRL          0x58
#define SLICE_SFTY_ENABLE_INFO       0x5c
#define SLICE_SFTY_DIAG_INFO         0x60
#define SLICE_SFTY_TMR_ERR_INFO      0x64
#define SLICE_SFTY_SB_ERROR_STATUS   0x68
#define SLICE_SFTY_BUILD_AUX         0xe0
#define GRP_SFTY_PASSWD              0x0 
#define GRP_SFTY_CTRL                0x4
#define GRP_SFTY_DIAG                0x8
#define GRP_SFTY_ERROR_STATUS        0xc
#define GRP_SFTY_E2E_ERROR_STATUS    0x10
#define GRP_SFTY_DCLS_ERROR_STATUS   0x14
#define GRP_SFTY_ENABLE_INFO         0x18
#define GRP_SFTY_DIAG_INFO           0x1c
#define GRP_SFTY_TMR_ERR_INFO        0x20
#define GRP_DBANK_ECC_CTRL           0x24
#define GRP_SFTY_SB_ERROR_STATUS     0x28
#define GRP_SFTY_BUILD_AUX           0xe0

#define ARCSYNC_SFTY_PASSWD          0x34
#define ARCSYNC_SFTY_DIAG            0x38 
#define ARCSYNC_SFTY_STATUS          0x3C
#define ARCSYNC_SFTY_CTRL            0x40

