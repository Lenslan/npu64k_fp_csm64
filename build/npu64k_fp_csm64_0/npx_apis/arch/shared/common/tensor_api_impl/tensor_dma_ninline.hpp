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
 * tensor_dma_ninline.hpp
 *
 * File defining tensor DMA non inline operations
 *
 */

//#define TENSOR_DMA_NINLINE_HPP_DEBUG
#ifdef TENSOR_DMA_NINLINE_HPP_DEBUG
  #define LDBGV(...) DBGV(__VA_ARGS__)
#else
  #define LDBGV(...)
#endif

//
// All identifiers related to the tensor API go into namespace tensor::v200
//
namespace tensor::v200 {

}

#undef LDBGV

