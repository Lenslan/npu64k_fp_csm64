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
 * tensor_conv_inline.hpp
 *
 * File defining the native specific inline functions for the tensor convolution objects
 *
 */

#ifndef NPU_CONV_COMMON_TENSOR_API_IMPL_TENSOR_CONV_INLINE_HPP_
#define NPU_CONV_COMMON_TENSOR_API_IMPL_TENSOR_CONV_INLINE_HPP_

// All identifiers related to the tensor API go into namespace tensor::v200
namespace tensor::v200 {

//
// Set implementation specific parameters, optional else use default
//
template<template<typename> class B>
inline void conv_base<B>::set_impl_params(const conv_params_impl_spec& p) {
  impl_spec = p;
  if (impl_spec.cf_4b) {
    if (cf_tp == cf_cfg_8b_nozp_e) {
      cf_tp = cf_cfg_4b_nozp_e;
    }
    if (cf_tp == cf_cfg_8b_zp_e) {
      cf_tp = cf_cfg_4b_zp_e;
    }
  }
}

template<template<typename> class B>
inline void conv_base<B>::get_impl_params(conv_params_impl_spec&  // NOLINT [runtime/references]
    p) {
  p = impl_spec;
  p.cf_4b = cf_tp == cf_cfg_4b_nozp_e || cf_tp == cf_cfg_4b_zp_e;
}

//
// return compiled HLAPI
//
template<template<typename> class B>
inline void conv_base<B>::get_rt_params(conv_params_impl_main&  // NOLINT [runtime/references]
    h) {
  h = hlapi;
  if (pck_mpy == 2 && impl_spec.conv_mode == NINO(conv_mode_3x3dws1)) {
    // force depth-wise v2i8 pack mode
    h.i.bf &= ~CONV_BF_CONV_MODE_MASK;
    h.i.bf |= VIVO(conv_mode_3x3dws1)<<CONV_BF_CONV_MODE_START;
  }
}

//
// Run-time object constructor
//
inline conv_rt::conv_rt(
            conv_params_impl_main&                   p  // HLAPI parameter struct in DM
            ) {
  hlapi            = p;
  mmio             = nullptr;
  hlapi.i.common.next = globalptr_t<npu::hlapi_i_t>(nullptr);
}



inline void conv_rt::set_input(
              impl_spec_container_t<buffer_t>&      b  // tensor L1 allocation information
              ) {
  // VM local pointer addresses are per ixpix_t
  mem_write(&hlapi.i.fm_buf.base, localptr_t<ixpix_t>(mem_read(&b.data).get_base()));
  mem_write(&hlapi.i.fm_ptr, localptr_t<ixpix_t>(mem_read(&b.data).get_ptr()));
}

inline void conv_rt::set_inputb(
              impl_spec_container_t<buffer_t>&      b  // tensor L1 allocation information
              ) {
  // VM local pointer addresses are per ixpix_t, for secondary matrix
  mem_write(&hlapi.i.cf_ptr, localptr_t<ixpix_t>(mem_read(&b.data).get_ptr()));
}

//
// Set implementation specific attributes
//
inline void conv_rt::set_impl_params(const conv_rt_impl_spec& p) {
  mem_write(&hlapi.i.common.ctrl, mem_read(&p.ctrl));
  mem_write(&hlapi.i.common.id, mem_read(&p.id));
  mem_write(&mmio             , mem_read(&p.mmio));
}

inline void conv_rt::get_impl_params(conv_rt_impl_spec& p) {
  mem_write(&p.id, mem_read(&hlapi.i.common.id));
  mem_write(&p.ctrl, mem_read(&hlapi.i.common.ctrl));
  mem_write(&p.mmio, mem_read(&mmio));
}

//
// Change the shape of the convolution
//
inline void conv_rt::set_alt_shape(
                   const conv_params_impl_alt& alt   // set and alternative convolution shape
                   ) {
  assert(0 && "not implemented yet");
}
inline void conv_rt::set_alt_shapeb(
                   const conv_params_impl_alt& alt   // set and alternative convolution shape
                   ) {
  assert(0 && "not implemented yet");
}

//
// Initialize the tile specific parameters
//
inline void conv_rt::init_tile_params(
    conv_params_impl_coef<buffer_t>& cf        // coefficients for tile FC only
    ) {
  mem_write(&hlapi.i.cf_ptr, localptr_t<ixpix_t>(mem_read(&cf.cbuf).get_base()));
}

inline void conv_rt::init_tile_params(
    const shape<3>&        pp,                 // padding start position
    conv_params_impl_coef<buffer_t>& cf,       // coefficients for tile
    conv_params_impl_pad<buffer_t>&  pd        // input feature-map zero-point padding values
    ) {
  mem_write(&hlapi.i.fm_padpos, mem_read(&pp));
  mem_write(&hlapi.i.cf_ptr, localptr_t<ixpix_t>(mem_read(&cf.cbuf).get_base()));
  mem_write(&hlapi.i.pad_ptr, localptr_t<ixpix_t>(mem_read(&pd.ptns).get_base()));
}

inline void conv_rt::init_tile_paramsb(
    const shape<3>&        pp,                 // padding start position
    conv_params_impl_coef<buffer_t>& cf,       // coefficients for tile
    conv_params_impl_pad<buffer_t>&  pd        // input feature-map zero-point padding values
    ) {
  mem_write(&hlapi.i.fm_padpos, mem_read(&pp));
  mem_write(&hlapi.i.cf_ptr, localptr_t<ixpix_t>(mem_read(&cf.cbuf).get_base()));
  mem_write(&hlapi.i.pad_ptr, localptr_t<ixpix_t>(mem_read(&pd.ptns).get_base()));
}

//
// Optionally prepare for HW execution (prefetch)
//
inline void conv_rt::prepare() {
  ctrl_dma_regs<conv_hlapi_t>* t_mmio = mem_read(&mmio);  // pointer to the ctrl_regs
  assert(t_mmio != nullptr);  // else RT params not initialized
  // cout << "DEBUG: mmio_addr=" << std::noshowbase << std::internal << std::hex
  //      << std::setfill('0') << "0x" << reinterpret_cast<uint64_t>(t_mmio) << endl;
  // cout << "DEBUG: mmio.single addr=" << std::noshowbase << std::internal << std::hex
  //      << std::setfill('0') << "0x" << reinterpret_cast<uint64_t>(&(t_mmio->single)) << endl;

  mem_write(&hlapi.i.common.next, globalptr_t<hlapi_i_t>(nullptr));
  mmio_write(&(t_mmio->prefetch), globalptr_t<conv_hlapi_t>(fast2slice_dccm(&hlapi)));
  // mem_write( &(t_mmio->prefetch), globalptr_t<conv_hlapi_t>(fast2slice_dccm(&hlapi)) );
  // mem_read(&mmio)->prefetch = globalptr_t<conv_hlapi_t>(fast2slice_dccm(&hlapi));
}

inline void hlapi_report(ostream& os, conv_hlapi_t& h) {
  #ifndef RTL_ARC
  for (int i = 0; i < CONV_HLAPI_LOOPS; i++) {
    os << "iter[" << i << "] = " << mem_read(&(h.i.iter[i])) << endl;
  }
  os << "fmptr = " << mem_read(&h.i.fm_ptr) << endl;
  os << "fmbase = " << mem_read(&h.i.fm_buf.base) << ", len = "
     << mem_read(&h.i.fm_buf.len) << ", last = "
     << (mem_read(&h.i.fm_buf.base)+mem_read(&h.i.fm_buf.len)) << endl;
  os << "padlim = "; report(os, mem_read(&h.i.fm_padlim)); os << endl;
  os << "padpos = "; report(os, mem_read(&h.i.fm_padpos)); os << endl;
  os << "pdoffsets = "; report(os, mem_read(&h.i.fm_pdoffsets)); os << endl;
  os << "poffsets = "; report(os, mem_read(&h.i.fm_doffsets)); os << endl;
  os << "padptr = " << mem_read(&h.i.pad_ptr) << endl;
  os << "cfptr = " << mem_read(&h.i.cf_ptr) << endl;
  os << "accptr = " << mem_read(&h.i.acc_ptr) << endl;
  os << "bf = " << mem_read(&h.i.bf) << endl;
  #endif
}

inline void conv_rt::execute() {
  // hlapi_report(cout, hlapi);
  ctrl_dma_regs<conv_hlapi_t>* t_mmio = mem_read(&mmio);  // pointer to the ctrl_regs
  assert(t_mmio != nullptr);  // else RT params not initialized
  // cout << "DEBUG: mmio_addr=" << std::noshowbase << std::internal << std::hex
  //      << std::setfill('0') << "0x" << reinterpret_cast<uint64_t>(t_mmio) << endl;
  // cout << "DEBUG: mmio.single addr=" << std::noshowbase << std::internal << std::hex
  //      << std::setfill('0') << "0x" << reinterpret_cast<uint64_t>(&(t_mmio->single)) << endl;

  mem_write(&hlapi.i.common.next, globalptr_t<hlapi_i_t>(nullptr));
  mmio_write(&(t_mmio->single), globalptr_t<conv_hlapi_t>(fast2slice_dccm(&hlapi)));
  // mem_write( &(t_mmio->single), globalptr_t<conv_hlapi_t>(fast2slice_dccm(&hlapi)) );
  // mem_read(&mmio)->single = globalptr_t<conv_hlapi_t>(&hlapi);
}

inline void conv_rt::set_use_keep_acc(bool use_acc,     // new value for useAcc
                                      bool keep_acc) {  // new value for keepAcc
  uint32_t next_bf = mem_read(&hlapi.i.bf);
  if (use_acc) {
    // use from AM
    next_bf |=  (1 << CONV_BF_USE_ACC_START);
  } else {
    // init to 0
    next_bf &= ~(1 << CONV_BF_USE_ACC_START);
  }
  if (keep_acc) {
    // write to AM
    next_bf |=  (1 << CONV_BF_KEEP_ACC_START);
  } else {
    // write to FIFO
    next_bf &= ~(1 << CONV_BF_KEEP_ACC_START);
  }
  mem_write(&hlapi.i.bf, next_bf);
}
//
// Slide tensor input window of the underlying buffer in channel and spatial dimension
//
template <bool neg_check_only>
inline void conv_rt::update_ptr(const poffset_t& ofs) {
  localptr_t<ixpix_t> np =
    mem_read(&hlapi.i.fm_buf).incr_wrap<neg_check_only>(mem_read(&hlapi.i.fm_ptr), ofs);
  mem_write(&hlapi.i.fm_ptr, np);
}
inline void conv_rt::update_padpos(const shape<3>& s) {
  // update pad position
  for (int i = 0; i < 3; i++) {
    mem_write(&hlapi.i.fm_padpos[i], (aoffset_t)(mem_read(&hlapi.i.fm_padpos[i]) + s[i]));
  }
}
// secondary pointer update for matrix multiply
inline void conv_rt::update_ptrb(const poffset_t& ofs) {
  localptr_t<ixpix_t> np = mem_read(&hlapi.i.cf_ptr) + ofs;
  mem_write(&hlapi.i.cf_ptr, np);
}

// Input pointer getter
inline uint64_t conv_rt::get_input_ptr() {
  return mem_read(&hlapi.i.fm_ptr).get_ptr();
}

// Output pointer getter
inline uint64_t conv_rt::get_output_ptr() {
  return mem_read(&hlapi.i.acc_ptr);
}

// Set input buffer in VM
inline void conv_rt::set_input(localptr_t<ixpix_t> iptr) {
  mem_write(&hlapi.i.fm_buf.base, iptr);
  mem_write(&hlapi.i.fm_ptr, iptr);
}

// Set output buffer in AM
inline void conv_rt::set_output(localptr_t<ixacc_t> optr) {
  // divide by dynamic TNSVSIZE
  assert(optr.get_raw()%TNSVSIZE == 0 && "unaligned pointer");
  amptr_t p(optr.get_raw()>>TNSVSIZEL2);
  mem_write(&hlapi.i.acc_ptr, p);
}

inline void conv_rt::set_output(localptr_t<vyixacc_t> optr) {
  mem_write(&hlapi.i.acc_ptr, optr.get_raw());
}

//
// Set output buffer in AM
//
inline void conv_rt::set_output(acc_buf_impl_t<buffer_t>& b) {
  // scale pointer to units of vector width
  mem_write(&hlapi.i.acc_ptr, mem_read(&b).get_vptr());
}

inline void conv_rt::update_output(const poffset_t& ofs) {
  amptr_t np = mem_read(&hlapi.i.acc_ptr) + ofs;
  mem_write(&hlapi.i.acc_ptr, np);
}

// get set an implementation specific register
inline void conv_rt::set_impl_status(
    uint16_t sel,                        // select a particular status field
    uint32_t val                         // value to be written
    ) {
  switch (sel) {
  case HLAPI_STATUS_SEL_IO_CYCLES:
    mem_write(&hlapi.io.cycles, val);
    break;
  case HLAPI_STATUS_SEL_IO_COUNT:
    mem_write(&hlapi.io.count, val);
    break;
  case HLAPI_STATUS_SEL_O_STATUS:
    mem_write(&hlapi.o.status, val);
    break;
  case HLAPI_STATUS_SEL_O_RES:
    mem_write(&hlapi.o.res, val);
    break;
  default: assert(0);
  }
}

// Return implementation specific status fields
inline uint32_t conv_rt::get_impl_status(
    uint16_t sel                     // select a particular status field
    ) {
  uint32_t val;
  switch (sel) {
  case HLAPI_STATUS_SEL_IO_CYCLES:
    val = mem_read(&hlapi.io.cycles);
    break;
  case HLAPI_STATUS_SEL_IO_COUNT:
    val = mem_read(&hlapi.io.count);
    break;
  case HLAPI_STATUS_SEL_O_STATUS:
    val = mem_read(&hlapi.o.status);
    break;
  case HLAPI_STATUS_SEL_O_RES:
    val = mem_read(&hlapi.o.res);
    break;
  default:
    assert(0);
    val = 0;
    break;
  }
  return val;
}

//
// Create object in a target memory
//
inline conv_rt* create(mem_alloc_t& al, conv_params_impl_main& p) {  // NOLINT [runtime/references]
  conv_rt c(p);
  conv_rt* cpy;
  al.alloc(cpy);
  mem_write(cpy, c);
  return cpy;
}

//
// functions to create and issue lists of descriptors
//
// constructor
inline conv_rt_list::conv_rt_list() {
  ini = false;
}
// append an element
inline void conv_rt_list::append(conv_rt* rt) {
  if (!ini) {
    // list is still empty
    head = &(rt->hlapi);
    tail = &(rt->hlapi);
    mmio = mem_read(&rt->mmio);
    ini = true;
  } else {
    // append to tail of existing list
    mem_write(&tail->i.common.next, globalptr_t<hlapi_i_t>(fast2slice_dccm(&rt->hlapi.i.common)));
    tail = &(rt->hlapi);
  }
}

// prefetch the head of the list
inline void conv_rt_list::prepare() {
  assert(ini && "empty list");
  mmio_write(&mmio->prefetch, globalptr_t<conv_hlapi_t>(fast2slice_dccm(head)));
}

// issue the list
inline void conv_rt_list::execute() {
  assert(ini && "empty list");
  mmio_write(&mmio->concat_head, globalptr_t<conv_hlapi_t>(fast2slice_dccm(head)));
  mmio_write(&mmio->concat_tail, globalptr_t<conv_hlapi_t>(fast2slice_dccm(tail)));
  mmio_write(&mmio->issue, (uint32_t)2);
}
}
#endif  // NPU_CONV_COMMON_TENSOR_API_IMPL_TENSOR_CONV_INLINE_HPP_
