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
 * tensor_sc_mem.hpp
 *
 * File defining tensor SystemC memory instance data type
 *
 */

#ifndef SHARED_COMMON_TENSOR_API_IMPL_TENSOR_SC_MEM_HPP_
#define SHARED_COMMON_TENSOR_API_IMPL_TENSOR_SC_MEM_HPP_

#include <iostream>
#include <memory>
#include <map>

#include "tlm"

#include "tensor_mem.hpp"  // NOLINT [build/include_subdir]

namespace tensor::v200 {
template<int W> class tlm_mem_t : public mem_t, public tlm::tlm_fw_transport_if<> {
 public:
  // TLM interface
  tlm::tlm_target_socket<W>& get_target() {
    return mem_port;
  }

  // constructor, base address and size in bytes
  inline tlm_mem_t(uint64_t b, size_t s)
  : mem_t(b, s)
  , mem_port("mem_port") {
    mem_port.bind(*this);
  }

  // constructor, no base address and size in bytes
  inline explicit tlm_mem_t(size_t s)
  : mem_t(s)
  , mem_port("mem_port") {
    mem_port.bind(*this);
  }

  //
  // TLM I/F
  //
  tlm::tlm_sync_enum nb_transport_fw(tlm::tlm_generic_payload& trans,
                                     tlm::tlm_phase&           phase,
                                     sc_core::sc_time&         t) override {
    return tlm::TLM_COMPLETED;
  }

  void b_transport(tlm::tlm_generic_payload& trans, sc_core::sc_time& delay) override {
    handle_trans(trans);
    auto duration = trans.get_data_length() / trans.get_streaming_width();
    delay += sc_core::sc_time(duration, sc_core::SC_NS);
  }

  bool get_direct_mem_ptr(tlm::tlm_generic_payload& trans,
                          tlm::tlm_dmi& dmi_data) override {
    dmi_data.allow_read_write();
    dmi_data.set_dmi_ptr(&mem[0]);
    dmi_data.set_start_address(base_addr);
    dmi_data.set_end_address(base_addr + size - 1);
    return true;
  }

  unsigned int transport_dbg(tlm::tlm_generic_payload& trans) override {
    handle_trans(trans);
    return trans.get_data_length();
  }

 private:
  void handle_trans(tlm::tlm_generic_payload& trans) {  // NOLINT [runtime/references]
    auto addr = trans.get_address();
    uint8_t* dp   = trans.get_data_ptr();
    auto len  = trans.get_data_length();
    // address range checks
    if (addr < base_addr ||
        addr > (base_addr + size) ||
        (addr + len) > (base_addr + size) ) {
      trans.set_response_status(tlm::TLM_ADDRESS_ERROR_RESPONSE);
      return;
    }
    addr -= base_addr;
    if (trans.is_read()) {
      for (uint64_t l = 0; l < len; l++) {
        *dp++ = mem[addr + l];
      }
    }
    if (trans.is_write()) {
      for (uint64_t l = 0; l < len; l++) {
        mem[addr + l] = *dp++;
      }
    }
    trans.set_response_status(tlm::TLM_OK_RESPONSE);
  }

  tlm::tlm_target_socket<W>  mem_port;  // TLM target port
};
}  // namespace tensor::v200
#endif  // SHARED_COMMON_TENSOR_API_IMPL_TENSOR_SC_MEM_HPP_
