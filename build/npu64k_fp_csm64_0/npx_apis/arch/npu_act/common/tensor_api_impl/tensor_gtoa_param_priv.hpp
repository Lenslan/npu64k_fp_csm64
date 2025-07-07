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

gtoa_params_impl_main   hlapi;     // runtime parameters
shape<3>                ostride;
aoffset_t               onn;
impl_spec_container_t<B>   itens;     // input tensor information
impl_spec_container_t<B>   i1tens;    // secondary input tensor information
impl_spec_container_t<B>   tens;      // output tensor information
