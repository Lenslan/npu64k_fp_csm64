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
 * tensor_gtoa_creduce_inline.hpp
 *
 * File defining channelwise reduce creduce API base on the generic tensor
 * operation API
 *
 */
#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_CREDUCE_INLINE_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_CREDUCE_INLINE_HPP_

#define HLAPI gtoa_params<B>::hlapi

// chanel wise reduce base class for feature-map (8b/16b) input
template <template <typename> class B>
gtoa_creduce_params<B>::gtoa_creduce_params(
    aoffset_t noi,         // number output channels (not vectors)
    const shape<3> &ishpi, // input shape
    act_dtype_t intp,      // type of primary input
    act_dtype_t outtp,     // do we use stream
    act_cred_op_t opi)     // reduction operation to perform
    : gtoa_creduce_base_params<B>(noi, ishpi, intp, outtp) {

  switch (opi) {
  case gtoa_cred_and:
    init_creduce(HLAPI, op_band);
    break;
  case gtoa_cred_or:
    init_creduce(HLAPI, op_bor);
    break;
  case gtoa_cred_min:
    init_creduce(HLAPI, op_min);
    break;
  case gtoa_cred_max:
    init_creduce(HLAPI, op_max);
    break;
  case gtoa_cred_add:
    init_creduce(HLAPI, op_add);
    break;
  default:
    assert(0 && "unknown reduction instruction");
  }
}

#undef HLAPI

#endif // NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_CREDUCE_INLINE_HPP_
