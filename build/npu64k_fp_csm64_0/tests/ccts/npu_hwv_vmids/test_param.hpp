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


#define IDMA_TEST 1 
#define ODMA_TEST 0 
#define T2T_TEST   1 
// size of buffer in XM (4096B) 
#define XM_CHN     32 
#define XM_COL     8 
#define XM_ROW     4 
#define XM_DEP     4 
// size of buffer in VM (chan as multiple of ISIZE) 
#define VM_CHN     32 
#define VM_CHA     2 
#define VM_COL     8 
#define VM_ROW     4 
#define VM_DEP     4 
// position in XM tensor 
#define XM_CHN_PTR   0 
#define XM_COL_PTR   0 
#define XM_ROW_PTR   0 
#define XM_DEP_PTR   0 
// position in VM tensor 
#define VM_CHN_PTR   0 
#define VM_CHA_PTR   0 
#define VM_COL_PTR   0 
#define VM_ROW_PTR   0 
#define VM_DEP_PTR   0 
// size of subtensor to be copied 
#define XM_SUB_CHN   32 
#define XM_SUB_COL    4 
#define XM_SUB_ROW    1 
#define XM_SUB_DEP    1 
 
//Actuall VM transfer 
#define VM_SUB_CHN   32 
#define VM_SUB_CHA   2 
#define VM_SUB_COL   4
#define VM_SUB_ROW   1 
#define VM_SUB_DEP   1 
 
#define XM_FUL_SHP   {XM_CHN, XM_COL, XM_ROW, XM_DEP} 
#define VM_FUL_SHP   {VM_CHN, VM_COL, VM_ROW, VM_DEP} 
#define XM_SUB_SHP   {XM_SUB_CHN, XM_SUB_COL, XM_SUB_ROW, XM_SUB_DEP} 
#define VM_SUB_SHP   {VM_SUB_CHN, VM_SUB_COL, VM_SUB_ROW, VM_SUB_DEP} 
#define XM_POS       {XM_CHN_PTR, XM_COL_PTR, XM_ROW_PTR, XM_DEP_PTR} 
#define VM_POS       {VM_CHN_PTR, VM_COL_PTR, VM_ROW_PTR, VM_DEP_PTR} 
 
#define PLANNAR_OFFSET 0 
#define PLANNAR_STRIDE 0 
#define ZERO_POINT 0 

static pix_t xmImg[] = {
    #include "xmImg.mhex"
};

static pix_t refImg[] = {
    #include "vmImg.mhex"
};

