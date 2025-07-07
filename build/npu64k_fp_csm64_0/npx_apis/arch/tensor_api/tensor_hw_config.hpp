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
 * tensor_hw_config.hpp
 *
 * File defining singleton tensor API configuration object
 *
 */

#ifndef TENSOR_API_HW_CONFIG_HPP_
#define TENSOR_API_HW_CONFIG_HPP_

#include <cstdint>
#include <iostream>
#include "npu_config.hpp"     // NOLINT [build/include_subdir]
#include "npu_defines.hpp"    // NOLINT [build/include_subdir]


// macro for SW reconfigurable tensor API VSIZE
#define TNSVSIZE   (hw_config_t::get_inst().get_vsize())
#define TNSVSIZEL2 (hw_config_t::get_inst().get_vsizel2())


//
// All identifiers related to the tensor API go into namespace tensor::v200
//
namespace tensor::v200 {
class hw_config_t {
  protected:
  // constructor
  inline hw_config_t() : 
    npu_slice_mac(NPU_SLICE_MAC),
    npu_has_float(NPU_HAS_FLOAT),
    npu_csm_size(NPU_CSM_SIZE/(1014*1024)) {
    // derive vsize
    switch (npu_slice_mac) {
    case 512:  npu_vsizel2 = 0; break;
    case 1024: npu_vsizel2 = 1; break;
    case 2048: npu_vsizel2 = 2; break;
    default:   npu_vsizel2 = 3; break;
    }
    npu_vsize = 1<<npu_vsizel2;
  }
  // singleton pointer
  static hw_config_t* ptr;

  public:
  // remove other constructors to avoid clone
  hw_config_t(hw_config_t &) = delete;
  void operator=(const hw_config_t &) = delete;

  // return object pointer
  static hw_config_t& get_inst();
  
  //
  // Access functions
  //

  // return version of hardware
  // 0x10: NPU release 1.00a (Victoria1), supported through legacy namespace
  // 0x11: NPU release 2.00a-lca01 (Victoria2 LCA)
  // 0x12: NPX release 2.00a (Victoria2 GA)
  inline uint32_t get_value_version() const {
    return npu_version;
  }
  inline void set_value_version(uint32_t v) {
    npu_version = v;
  }

  // return the number of MACs per NPX core: 1024 or 4096
  inline uint32_t get_value_npu_slice_mac() const {
    return npu_slice_mac;
  }

  inline void set_vsize(uint32_t vsize) {
    npu_vsize = (size_t)vsize;
    switch (npu_vsize) {
    case 1:
      npu_vsizel2 = 0;
      npu_slice_mac = 512;
      break;
    case 2:
      npu_vsizel2 = 1;
      npu_slice_mac = 1024;
      break;
    case 4:
      npu_vsizel2 = 2;
      npu_slice_mac = 2048;
      break;
    default:
      npu_vsizel2 = 3;
      npu_slice_mac = 4096;
      break;
    }
  }

  // reconfigure the number of MACs per NPX core: 1024 or 4096
  inline void set_value_npu_slice_mac(uint32_t v) {
    npu_slice_mac = v;
    // derive vsize
    switch (npu_slice_mac) {
    case 512:  npu_vsizel2 = 0; break;
    case 1024: npu_vsizel2 = 1; break;
    case 2048: npu_vsizel2 = 2; break;
    default:   npu_vsizel2 = 3; break;
    }
    npu_vsize = 1<<npu_vsizel2;
  } 

  // return convolution floating-point capability
  inline bool get_value_npu_has_float() const {
    return npu_has_float;
  }
  // enable/disable floating-point convolution tensor APIs
  inline void set_value_npu_has_float(bool v) {
    npu_has_float = v;
  }
  
  // return the CSM size in MB, if 0 then STU tensor APIs are disabled
  inline uint32_t get_value_npu_csm_size() const {
    return npu_csm_size;
  }
  // reconfigure the CSM size: 0..64 [MB], 0 disables STU tensor APIs
  inline void set_value_npu_csm_size(uint32_t v) {
    npu_csm_size = v;
  }
  
  //
  // only for Tensor API query
  //
  // check if STU present
  inline bool get_has_stu() const {
    return npu_csm_size > 0;
  }
  // return VSIZE vectorization
  inline size_t get_vsize() const {
    return npu_vsize;
  }
  inline size_t get_vsizel2() const {
    return npu_vsizel2;
  }

  private:
  uint32_t npu_version;
  uint32_t npu_slice_mac;
  size_t   npu_vsize;
  size_t   npu_vsizel2;
  bool     npu_has_float;
  uint32_t npu_csm_size;
};

}
#endif  // TENSOR_API_HW_CONFIG_HPP_
