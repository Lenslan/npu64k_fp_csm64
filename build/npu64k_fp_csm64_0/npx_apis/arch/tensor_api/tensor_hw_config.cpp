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
 * tensor_hw_config.cpp
 *
 * File defining singleton tensor API configuration object static members
 *
 */
#include "tensor_hw_config.hpp"


namespace tensor::v200 {
hw_config_t* hw_config_t::ptr = nullptr;


hw_config_t& hw_config_t::get_inst() {
  if (ptr == nullptr) {
    ptr = new hw_config_t();
  }
  return *ptr;
}
}
