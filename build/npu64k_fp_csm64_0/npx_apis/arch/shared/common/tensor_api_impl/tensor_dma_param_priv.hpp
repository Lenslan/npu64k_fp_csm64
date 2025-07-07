/*************************************************************************/
/**                                                                     **/
/** Copyright (C) 2021-2023 Synopsys, Inc.                              **/
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

friend struct dma_params_impl_main;
union {
  dma_hlapi_t                  d;        // iDMA/oDMA HLAPI struct
  stu_hlapi_t                  s;        // STU HLAPI struct
} hlapi;
dma_params_impl_spec           sel;      // select accelerator
dma_params_sd_type             styp;     // source type
dma_params_sd_type             dtyp;     // desintation type
bool                           scwr;     // source column-wise reordering
bool                           dcwr;     // destination column-wise reordering
bool                           rnk_sel;  // xm rank is either 4 or 5 dims
tensor_t<pix_t,8,B>            src_tns;  // XM source tensor [D/d][H/h][W/w][C/c][d][h][w][c]
impl_spec_container_t<B>       src_con;  // VM tensor
tensor_t<pix_t,8,B>            dst_tns;  // XM desintation tensor [D/d][H/h][W/w][C/c][d][h][w][c]
impl_spec_container_t<B>       dst_con;  // VM tensor
