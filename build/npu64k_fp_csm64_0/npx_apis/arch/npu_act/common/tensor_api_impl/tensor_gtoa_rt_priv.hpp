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

/*
 * tensor_gtoa_rt_priv.hpp
 *
 * File defining the private members of the generic tensor operation run-time class
 *
 */

// data members
public:
act_hlapi_t                   hlapi;    // HLAPI parameters
ctrl_dma_regs<act_hlapi_t>*   mmio;     // base address of accelerator MMIO registers
