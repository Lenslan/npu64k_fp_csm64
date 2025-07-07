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
 * tensor_gtoa_cmse_inline.hpp
 *
 * File defining channelwise Mean Square Error API base on the generic tensor operation API
 *
 */
#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_CMSE_INLINE_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_CMSE_INLINE_HPP_

#define HLAPI gtoa_params<B>::hlapi

// chanel wise reduce mean squared error operation for feature-map (8b/16b) input
template <template <typename> class B>
gtoa_cmse_params<B>::gtoa_cmse_params(
    aoffset_t       noi,        // number output channels (not vectors)
    const shape<3>& ishpi,      // input shape
    size_t          num,        // total number of elements in pool
    act_dtype_t     intp,       // type of primary input
    act_dtype_t     outtp,      // type of output
    bool chnpad) : 
  gtoa_creduce_base_params<B>(noi, ishpi, intp, outtp) {

  // if num aligned with ISIZE or chnpad on the fly is disabled, chn_pa=-1
  int ch_pad = (num % ISIZE == 0 || !chnpad) ? -1 : num - (noi-ISIZE);
  init_cmse(HLAPI, ch_pad);
 
  // 1/num as fp32 number in SR0
  float recip = 1.0/(float)num;
  fp_e8m23_t frecip(recip);
  HLAPI.i.u.op.scl[0] = frecip.data;
}

#undef HLAPI

#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_CMSE_INLINE_HPP_
