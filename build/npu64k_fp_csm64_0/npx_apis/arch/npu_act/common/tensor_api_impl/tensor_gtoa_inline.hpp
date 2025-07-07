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

//
// gtoa_params functions
//
template<template<typename> class B>
gtoa_params<B>::gtoa_params(){
  // set default hlapi bitfields to zero
  hlapi.i.bf          = 0;
  hlapi.i.u.op.bf     = 0;
  hlapi.i.u.op.io_en  = 0;
  hlapi.i.u.op.cmaskn = 0;
  hlapi.i.u.op.bnum   = 0;
  hlapi.i.u.op.bptr   = nullptr;
  hlapi.i.u.op.out.fm.pool.bf = 0;
  for (int i = 0; i < ACT_SREG_SAVE; i++) {
    hlapi.i.u.op.scl[i] = 0;
  }
}

// Precompute the pointer offset when updating an input feature-map tensor pointer
template<template<typename> class B>
poffset_t gtoa_params<B>::update_iptr0(
                     const shape<3>&        spat_offset, // spatial offset
                     aoffset_t              chan_offset  // channel offset
                     ) {
  return pbuf_wrap(itens.data.get_offset({chan_offset, 0, spat_offset[0], spat_offset[1], spat_offset[2]}),
                   hlapi.i.u.op.primary.fm_agu.buf.len);
}

// Precompute the pointer offset when updating an input feature-map tensor pointer
template<template<typename> class B>
poffset_t gtoa_params<B>::update_iptr1(
                     const shape<3>&        spat_offset, // spatial offset
                     aoffset_t              chan_offset  // channel offset
                     ) {
  return i1tens.data.get_offset({chan_offset, 0, spat_offset[0], spat_offset[1], spat_offset[2]});
}

// Precompute the pointer offset when updating an input feature-map tensor pointer
template<template<typename> class B>
poffset_t gtoa_params<B>::update_optr(
                     const shape<3>&        spat_offset, // spatial offset
                     aoffset_t              chan_offset  // channel offset
                     ) {
  return tens.data.get_offset({chan_offset, 0, spat_offset[0], spat_offset[1], spat_offset[2]});
}

// set per channel write mask
template<template<typename> class B>
inline void gtoa_params<B>::set_channel_mask(
                       const uint16_t       cmaskn // channel mask inverted
                       ) {
  hlapi.i.u.op.cmaskn = cmaskn;
}

// return GTOA run-time parameters
template<template<typename> class B>
inline void gtoa_params<B>::get_rt_params(gtoa_params_impl_main&       h) {
  if (hlapi.i.bf != 1) {
    // wrap offsets
    if ((hlapi.i.u.op.io_en&ACT_IO_EN_FM0) != 0) {
      for (int i = 0; i < ACT_FM_LOOPS; i++) {
        hlapi.i.u.op.primary.fm_agu.offsets[i] = vbuf_wrap(hlapi.i.u.op.primary.fm_agu.offsets[i], 
                                                           hlapi.i.u.op.primary.fm_agu.buf.len);
      }
    }
    if ((hlapi.i.u.op.io_en&ACT_IO_EN_FM1) != 0) {
      for (int i = 0; i < ACT_FM_LOOPS; i++) {
        hlapi.i.u.op.secondary.fm_agu.offsets[i] = vbuf_wrap(hlapi.i.u.op.secondary.fm_agu.offsets[i], 
                                                             hlapi.i.u.op.secondary.fm_agu.buf.len);
      }
    }
    if ((hlapi.i.u.op.io_en&ACT_IO_EN_OFM) != 0) {
      for (int i = 0; i < ACT_FM_LOOPS; i++) {
        hlapi.i.u.op.out.fm.fm_agu.offsets[i] = vbuf_wrap(hlapi.i.u.op.out.fm.fm_agu.offsets[i],
                                                          hlapi.i.u.op.out.fm.fm_agu.buf.len);
      }
    }
  }
  // fill the HLAPI structure
  h = hlapi;
}


///////////////////////////////////////////////////////////////////////////////////////////////
//
// Generic tensor operation run-time functions
//
///////////////////////////////////////////////////////////////////////////////////////////////

// GTO run-time constructor
inline gtoa_rt::gtoa_rt(
                        gtoa_params_impl_main&       h // HLAPI structure
                        ) {
  hlapi = h;
  mmio = nullptr;
  hlapi.i.common.next = globalptr_t<npu::hlapi_i_t>(nullptr);
}

// Set implementation specific run-time attributes
inline void gtoa_rt::set_impl_params(
                                     const gtoa_rt_impl_spec&  p  // structure with run-time specific parameters
                                     ) {
  mem_write(&hlapi.i.common.ctrl,   mem_read(&p.ctrl));
  mem_write(&hlapi.i.common.id,     mem_read(&p.id));
  mem_write(&mmio,                  mem_read(&p.mmio));
}
inline void gtoa_rt::get_impl_params(
                                     gtoa_rt_impl_spec&        p  // return structure with run-time specific parameters
                                     ) const {
  mem_write(&p.id,   mem_read(&hlapi.i.common.id));
  mem_write(&p.ctrl, mem_read(&hlapi.i.common.ctrl));
  mem_write(&p.mmio, mem_read(&mmio));
}

// Set/get scalar input/output values
inline void gtoa_rt::set_scalar(
                                const aoffset_t&               i,  // index of scalar to pass
                                const int32_t&                 s   // scalar value to pass
                                ) {
  mem_write(&hlapi.i.u.op.scl[ mem_read(&i)], mem_read(&s));
}
inline int32_t gtoa_rt::get_scalar() const {                       // return value of scalar 0
  return mem_read(&hlapi.i.u.op.scl[0]);
}

// Initialize the tile specific parameters (per channel parameters)
inline void gtoa_rt::init_tile_params(
                                      const gtoa_params_impl_pchan<buffer_t>& p  // structure with run-time tile specific parameters
                                      ) {
  mem_write(&hlapi.i.u.op.bnum, (aoffset_t)(mem_read(&p.tns).get_tens_size()));
  mem_write(&hlapi.i.u.op.bptr, localptr_t<ixpix_t>(mem_read(&p.tns).get_ptr()));
}


// Optionally initialize the tile specific fused maxpooling parameters
inline void gtoa_rt::set_maxpool_buffer(
                                        const gtoa_maxpool_buffer& obuf   // maxpooling tile overlap buffer
                                        ) {
  mem_write(&hlapi.i.u.op.out.fm.pool.st_base, localptr_t<ixpix_t>(mem_read(&obuf.buf).get_base()));
}

inline void gtoa_rt::set_padpos(
                                const shape<2>&            padpos // pooling padding position
                                ) {
  mem_write(&hlapi.i.u.op.padpos, padpos);
}

inline void gtoa_rt::update_padpos(
                                const shape<2>&            padpos // pooling padding position
                                ) {
  for (int i = 0; i < 2; i++) {
    mem_write(&hlapi.i.u.op.padpos[i], (aoffset_t)(mem_read(&hlapi.i.u.op.padpos[i]) + padpos[i]));
  }
}

// set per channel mask
inline void gtoa_rt::set_channel_mask(
                                const uint16_t             cmaskn // channel mask inverted
                                ) {
  mem_write(&hlapi.i.u.op.cmaskn, cmaskn);
}


// Set input and output feature-map tensors
inline void gtoa_rt::set_input0(impl_spec_container_t<buffer_t>&         l) {
  mem_write(&hlapi.i.u.op.primary.fm_agu.ptr,      localptr_t<ixpix_t>(mem_read(&l.data).get_ptr()));
  mem_write(&hlapi.i.u.op.primary.fm_agu.buf.base, localptr_t<ixpix_t>(mem_read(&l.data).get_base()));
  mem_write(&hlapi.i.u.op.primary.fm_agu.buf.len,  (uint16_t)mem_read(&l.data).get_size());
}
inline void gtoa_rt::set_input1(impl_spec_container_t<buffer_t>&         l) {
  mem_write(&hlapi.i.u.op.secondary.fm_agu.ptr,      localptr_t<ixpix_t>(mem_read(&l.data).get_ptr()));
  mem_write(&hlapi.i.u.op.secondary.fm_agu.buf.base, localptr_t<ixpix_t>(mem_read(&l.data).get_base()));
  mem_write(&hlapi.i.u.op.secondary.fm_agu.buf.len,  (uint16_t)mem_read(&l.data).get_size());
}
inline void gtoa_rt::set_inputs(impl_spec_container_t<buffer_t>&         l, aoffset_t s) {
  tensor_t<ixpix_t,5,buffer_t> l_data = mem_read(&l.data);
  tensor_t<ixpix_t,5,buffer_t> t1(l_data);

  mem_write(&hlapi.i.u.op.primary.fm_agu.ptr,      localptr_t<ixpix_t>(l_data.get_ptr()));
  mem_write(&hlapi.i.u.op.primary.fm_agu.buf.base, localptr_t<ixpix_t>(l_data.get_base()));
  mem_write(&hlapi.i.u.op.primary.fm_agu.buf.len,  (uint16_t)(l_data.get_size()));

  t1.shift(2, s); 
  mem_write(&hlapi.i.u.op.secondary.fm_agu.ptr,      localptr_t<ixpix_t>(t1.get_ptr()));
  mem_write(&hlapi.i.u.op.secondary.fm_agu.buf.base, localptr_t<ixpix_t>(t1.get_base()));
  mem_write(&hlapi.i.u.op.secondary.fm_agu.buf.len,  (uint16_t)(t1.get_size()));
}

inline void gtoa_rt::set_output(impl_spec_container_t<buffer_t>&         l) {
  mem_write(&hlapi.i.u.op.out.fm.fm_agu.ptr,      localptr_t<ixpix_t>(mem_read(&l.data).get_ptr()));
  mem_write(&hlapi.i.u.op.out.fm.fm_agu.buf.base, localptr_t<ixpix_t>(mem_read(&l.data).get_base()));
  mem_write(&hlapi.i.u.op.out.fm.fm_agu.buf.len,  (uint16_t)mem_read(&l.data).get_size());
}

// Change the microcode of the GTA
inline void gtoa_rt::set_alt_func(
                            const gtoa_params_impl_modif& m   // select an alternative generic tensor operation function
                            ) {
  mem_write(&hlapi.i.u.op.act_prog, mem_read(&m));
}

// Change the output type
inline void gtoa_rt::set_alt_output_fm(
                            const gtoa_params_impl_alt_fm&   a,  // select an alternative output feature-map AGU parameters
                            impl_spec_container_t<buffer_t>& l   // output feature-map buffer
                            ) {
  mem_write(&hlapi.i.u.op.bf,                     mem_read(&a.bf));
  mem_write(&hlapi.i.u.op.io_en,                  mem_read(&a.io_en));
  mem_write(&hlapi.i.u.op.out.fm.enable,          mem_read(&a.enable));
  mem_write(&hlapi.i.u.op.out.fm.fm_agu.iter,     mem_read(&a.fm_agu.iter));
  mem_write(&hlapi.i.u.op.out.fm.fm_agu.offsets,  mem_read(&a.fm_agu.offsets));
  mem_write(&hlapi.i.u.op.out.fm.fm_agu.stride,   mem_read(&a.fm_agu.stride));
  // pointer set from actual buffer
  mem_write(&hlapi.i.u.op.out.fm.fm_agu.ptr,      localptr_t<ixpix_t>(mem_read(&l.data).get_ptr()));
  mem_write(&hlapi.i.u.op.out.fm.fm_agu.buf.base, localptr_t<ixpix_t>(mem_read(&l.data).get_base()));
  mem_write(&hlapi.i.u.op.out.fm.fm_agu.buf.len,  (uint16_t)mem_read(&l.data).get_size());
}

inline void gtoa_rt::set_alt_output_acc(
                            const gtoa_params_impl_alt_acc& a,  // select an alternative output accumulator AGU parameters
                            acc_buf_impl_t<buffer_t>&       b   // output accumulator buffer
                            ) {
  mem_write(&hlapi.i.u.op.io_en,               mem_read(&a.io_en));
  mem_write(&hlapi.i.u.op.out.acc_agu.iter,    mem_read(&a.acc_agu.iter));
  mem_write(&hlapi.i.u.op.out.acc_agu.offsets, mem_read(&a.acc_agu.offsets));
  // pointer set from actual buffer
  mem_write(&hlapi.i.u.op.out.acc_agu.ptr,     mem_read(&b).get_vptr());
}

inline void gtoa_rt::set_inastr(bool inastr) {   // new value for inastr
  tmask_t io_en = mem_read(&hlapi.i.u.op.io_en);
  io_en |=  (inastr ? ACT_IO_EN_ASTR0 : ACT_IO_EN_AC0);
  io_en &= ~(inastr ? ACT_IO_EN_AC0 : ACT_IO_EN_ASTR0);
  mem_write(&hlapi.i.u.op.io_en, io_en);
}

// Change the shape of the input and output tensors as precomputed
inline void gtoa_rt::set_alt_shape(
                            const gtoa_params_impl_alt& alt   // set and alternative generic tensor operation shape
                            ) {
  assert (0 && "not implemented yet");
}

// Move the tensor pointer
template <bool neg_check_only>
inline void gtoa_rt::update_iptr0(
                                  const poffset_t&             ofs   // pointer offset
                                  ) {
  localptr_t<ixpix_t> ptr =
    mem_read(&hlapi.i.u.op.primary.fm_agu.buf).incr_wrap<neg_check_only>(mem_read(&hlapi.i.u.op.primary.fm_agu.ptr), mem_read(&ofs));
  mem_write(&hlapi.i.u.op.primary.fm_agu.ptr, ptr);
}
template <bool neg_check_only>
inline void gtoa_rt::update_iptr1(
                                  const poffset_t&             ofs   // pointer offset
                                  ) {
  localptr_t<ixpix_t> ptr =
    mem_read(&hlapi.i.u.op.secondary.fm_agu.buf).incr_wrap<neg_check_only>(mem_read(&hlapi.i.u.op.secondary.fm_agu.ptr), mem_read(&ofs));
  mem_write(&hlapi.i.u.op.secondary.fm_agu.ptr, ptr);
}
inline void gtoa_rt::update_iptrs(
                                  const poffset_t&             ofs   // pointer offset
                                  ) {
  poffset_t o(mem_read(&ofs));
  localptr_t<ixpix_t> ptr = mem_read(&hlapi.i.u.op.primary.fm_agu.buf).incr_wrap(mem_read(&hlapi.i.u.op.primary.fm_agu.ptr), o);
  mem_write(&hlapi.i.u.op.primary.fm_agu.ptr, ptr);
  ptr = mem_read(&hlapi.i.u.op.secondary.fm_agu.buf).incr_wrap(mem_read(&hlapi.i.u.op.secondary.fm_agu.ptr), o);
  mem_write(&hlapi.i.u.op.secondary.fm_agu.ptr, ptr);
}
template <bool neg_check_only>
inline void gtoa_rt::update_optr(
                                 const poffset_t&              ofs   // pointer offset
                                 ) {
  
  localptr_t<ixpix_t> ptr =
    mem_read(&hlapi.i.u.op.out.fm.fm_agu.buf).incr_wrap<neg_check_only>(mem_read(&hlapi.i.u.op.out.fm.fm_agu.ptr), mem_read(&ofs));
  mem_write(&hlapi.i.u.op.out.fm.fm_agu.ptr, ptr);
}
inline void gtoa_rt::update_gather_iptr0(
                                  const poffset_t&             ofs   // pointer offset
                                  ) {
  localptr_t<ixpix_t> ptr = mem_read(&hlapi.i.u.op.primary.fm_agu.buf.base) + mem_read(&ofs);
  mem_write(&hlapi.i.u.op.primary.fm_agu.buf.base, ptr);
}
inline void gtoa_rt::set_acc_input0(
                                    const acc_buf_impl_t<buffer_t>&      ain   // select an accumulator input buffer
                                    ) {
  
  mem_write(&hlapi.i.u.op.primary.acc_agu.ptr, mem_read(&ain).get_vptr());
}
inline void gtoa_rt::set_acc_input1(
                                    const acc_buf_impl_t<buffer_t>&      ain   // select an accumulator input buffer
                                    ) {
  mem_write(&hlapi.i.u.op.secondary.acc_agu.ptr, mem_read(&ain).get_vptr());
}
inline void gtoa_rt::set_acc_output(
                                    acc_buf_impl_t<buffer_t>&            ain   // select an accumulator input buffer
                                    ) {
  mem_write(&hlapi.i.u.op.out.acc_agu.ptr, mem_read(&ain).get_vptr());
}

// Input pointer getters 
inline uint64_t gtoa_rt::get_acc_input0_ptr() {
  return mem_read(&hlapi.i.u.op.primary.acc_agu.ptr);
}
inline uint64_t gtoa_rt::get_acc_input1_ptr() {
  return mem_read(&hlapi.i.u.op.secondary.acc_agu.ptr);
}
inline uint64_t gtoa_rt::get_fm_input0_ptr() {
  return mem_read(&hlapi.i.u.op.primary.fm_agu.ptr).get_ptr();
}
inline uint64_t gtoa_rt::get_fm_input1_ptr() {
  return mem_read(&hlapi.i.u.op.secondary.fm_agu.ptr).get_ptr();
}

// Output pointer getters
inline uint64_t gtoa_rt::get_acc_output_ptr() {
  return mem_read(&hlapi.i.u.op.out.acc_agu.ptr);
}
inline uint64_t gtoa_rt::get_fm_output_ptr() {
  return mem_read(&hlapi.i.u.op.out.fm.fm_agu.ptr).get_ptr();
}

// Set input and output accumulator buffers
inline void gtoa_rt::set_acc_input0(localptr_t<ixacc_t> iptr) {
  assert (iptr.get_raw()%TNSVSIZE == 0 && "unaligned pointer");
  uint16_t p(iptr.get_raw()>>TNSVSIZEL2);
  mem_write(&hlapi.i.u.op.primary.acc_agu.ptr, p);
}
inline void gtoa_rt::set_acc_input1(localptr_t<ixacc_t> iptr) {
  assert (iptr.get_raw()%TNSVSIZE == 0 && "unaligned pointer");
  uint16_t p(iptr.get_raw()>>TNSVSIZEL2);
  mem_write(&hlapi.i.u.op.secondary.acc_agu.ptr, p);
}
inline void gtoa_rt::set_acc_output(localptr_t<ixacc_t> optr) {
  // divide by dynamic TNSVSIZE
  assert (optr.get_raw()%TNSVSIZE == 0 && "unaligned pointer");
  uint16_t p(optr.get_raw()>>TNSVSIZEL2);
  mem_write(&hlapi.i.u.op.out.acc_agu.ptr, p);
}

// Set input and output accumulator buffers
inline void gtoa_rt::set_acc_input0(localptr_t<vyixacc_t> iptr) {
  mem_write(&hlapi.i.u.op.primary.acc_agu.ptr, iptr.get_raw());
}
inline void gtoa_rt::set_acc_input1(localptr_t<vyixacc_t> iptr) {
  mem_write(&hlapi.i.u.op.secondary.acc_agu.ptr, iptr.get_raw());
}
inline void gtoa_rt::set_acc_output(localptr_t<vyixacc_t> optr) {
  mem_write(&hlapi.i.u.op.out.acc_agu.ptr, optr.get_raw());
}

// Set input and output feature-map buffers
inline void gtoa_rt::set_input0(localptr_t<ixpix_t> iptr) {
  mem_write(&hlapi.i.u.op.primary.fm_agu.ptr, iptr);
  mem_write(&hlapi.i.u.op.primary.fm_agu.buf.base, iptr);
}
inline void gtoa_rt::set_input1(localptr_t<ixpix_t> iptr) {
  mem_write(&hlapi.i.u.op.secondary.fm_agu.ptr, iptr);
  mem_write(&hlapi.i.u.op.secondary.fm_agu.buf.base, iptr);
}
inline void gtoa_rt::set_output(localptr_t<ixpix_t> optr) {
  mem_write(&hlapi.i.u.op.out.fm.fm_agu.ptr, optr);
  mem_write(&hlapi.i.u.op.out.fm.fm_agu.buf.base, optr);
}

// Optionally prepare for HW execution (prefetch)
inline void gtoa_rt::prepare() {
  assert((mem_read(&mmio) != nullptr) && "need to set up mmio base"); // else RT params not initialized
  mem_write(&hlapi.i.common.next, globalptr_t<hlapi_i_t>(nullptr));
  mmio_write(&mem_read(&mmio)->prefetch, globalptr_t<act_hlapi_t>(fast2slice_dccm(&hlapi)));
}
inline void gtoa_rt::execute() {
  assert((mem_read(&mmio) != nullptr) && "need to set up mmio base"); // else RT params not initialized
  mem_write(&hlapi.i.common.next, globalptr_t<hlapi_i_t>(nullptr));
  mmio_write(&mem_read(&mmio)->single, globalptr_t<act_hlapi_t>(fast2slice_dccm(&hlapi)));
}
// get set an implementation specific register
inline void gtoa_rt::set_impl_status(
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
inline uint32_t gtoa_rt::get_impl_status(
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
// functions to create and issue lists of descriptors
//
// constructor
inline gtoa_rt_list::gtoa_rt_list() {
  ini = false;
}
// append an element
inline void gtoa_rt_list::append(gtoa_rt* rt) {
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
inline void gtoa_rt_list::prepare() {
  assert(ini && "empty list");
  mmio_write(&mmio->prefetch, globalptr_t<act_hlapi_t>(fast2slice_dccm(head)));
}
// issue the list
inline void gtoa_rt_list::execute() {
  assert(ini && "empty list");
  mmio_write(&mmio->concat_head, globalptr_t<act_hlapi_t>(fast2slice_dccm(head)));
  mmio_write(&mmio->concat_tail, globalptr_t<act_hlapi_t>(fast2slice_dccm(tail)));
  mmio_write(&mmio->issue, (uint32_t)2);
}


//
// Create object in a target memory
//
inline gtoa_rt* create(mem_alloc_t& al, gtoa_params_impl_main& p) {
  gtoa_rt c(p);
  gtoa_rt* cpy;
  al.alloc(cpy);
  mem_write(cpy, c);
  return cpy;
}
