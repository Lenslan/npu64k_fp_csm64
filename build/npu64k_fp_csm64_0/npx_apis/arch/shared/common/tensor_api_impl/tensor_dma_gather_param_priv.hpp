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
dma_hlapi_t                  d;         // iDMA HLAPI struct
dma_params_impl_spec         sel;       // select accelerator
dma_params_impl_shapes       shapes;    // shapes of tensors
tensor_t<pix_t,5,B>          dict_tns;  // XM dictionary tensor [h][w][c2][c1][c0]
impl_spec_container_t<B>     idx_con;   // VM index tensor [1][y][x][1][2]
impl_spec_container_t<B>     dst_con;   // VM destination tensor [y][x][c2][c1][c0]
