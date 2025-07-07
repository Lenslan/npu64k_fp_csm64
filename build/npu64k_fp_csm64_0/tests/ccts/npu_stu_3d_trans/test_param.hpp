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
// size of buffer in XMI (4096B) 
#define XMI_CHN     32 
#define XMI_COL     8 
#define XMI_ROW     4 
#define XMI_DEP     4 
// size of buffer in XMO (chan as multiple of ISIZE) 
#define XMO_CHN     32 
#define XMO_CHA     2 
#define XMO_COL     8 
#define XMO_ROW     4 
#define XMO_DEP     4 
// position in XMI tensor 
#define XMI_CHN_PTR   2 
#define XMI_COL_PTR   0 
#define XMI_ROW_PTR   1 
#define XMI_DEP_PTR   0 
// position in XMO tensor 
#define XMO_CHN_PTR   0 
#define XMO_CHA_PTR   0 
#define XMO_COL_PTR   4 
#define XMO_ROW_PTR   1 
#define XMO_DEP_PTR   1 
// size of subtensor to be copied 
 #define XMI_SUB_CHN   16 
#define XMI_SUB_COL    2 
#define XMI_SUB_ROW    2 
#define XMI_SUB_DEP    2 
 
//Actuall XMO transfer 
#define XMO_SUB_CHN   16 
#define XMO_SUB_CHA   1 
#define XMO_SUB_COL   2 
#define XMO_SUB_ROW   2 
#define XMO_SUB_DEP   2 
 
#define XMI_FUL_SHP   {XMI_CHN, XMI_COL, XMI_ROW, XMI_DEP} 
#define XMO_FUL_SHP   {XMO_CHN, XMO_COL, XMO_ROW, XMO_DEP} 
#define XMI_SUB_SHP   {XMI_SUB_CHN, XMI_SUB_COL, XMI_SUB_ROW, XMI_SUB_DEP} 
#define XMO_SUB_SHP   {XMO_SUB_CHN, XMO_SUB_COL, XMO_SUB_ROW, XMO_SUB_DEP} 
#define XMI_POS       {XMI_CHN_PTR, XMI_COL_PTR, XMI_ROW_PTR, XMI_DEP_PTR} 
#define XMO_POS       {XMO_CHN_PTR, XMO_COL_PTR, XMO_ROW_PTR, XMO_DEP_PTR} 
 
#define PLANNAR_OFFSET 0 
#define PLANNAR_STRIDE 0 
#define ZERO_POINT 0 

static pix_t xmImg[] = {
    #include "xmi.mhex"
};

static pix_t refImg[] = {
    #include "xmo.mhex"
};

