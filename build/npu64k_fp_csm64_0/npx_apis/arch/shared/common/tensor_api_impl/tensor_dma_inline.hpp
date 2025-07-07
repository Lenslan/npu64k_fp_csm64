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
 * tensor_dma_inline.hpp
 *
 * File defining tensor DMA inline operations
 *
 */

#ifndef TENSOR_DMA_INLINE_INCLUDED
#define TENSOR_DMA_INLINE_INCLUDED

#include <type_traits>

//#define TENSOR_DMA_NINLINE_HPP_DEBUG
#ifdef TENSOR_DMA_NINLINE_HPP_DEBUG
  #define LDBGV(...) DBGV(__VA_ARGS__)
#else
  #define LDBGV(...)
#endif

namespace tensor::v200 {
//
// Constructor
//
template<template<typename> class B>
inline dma_params<B>::dma_params() {
  hlapi.d.i.zero_point    = 0;
  hlapi.d.i.bc            = 0;
  hlapi.d.i.attrb         = 0;
  hlapi.d.i.planar_stride = 0;
  hlapi.d.i.planar_offset = 0;
}

//
// DMA parameter inline functions
//
template<template<typename> class B>
inline void dma_params<B>::set_impl_params(
                                        const dma_params_impl_spec& p // structure with implementation specific parameters
                                        ) {
  sel = p;
}

template<template<typename> class B>
inline void dma_params<B>::get_impl_params(
                                        dma_params_impl_spec& p       // return structure with implementation specific parameters
                                        ) {
  p = sel;
}

template<template<typename> class B>
inline void dma_params<B>::set_src(const tensor_t<pix_t,4,B>&                      stns) {       // XM source tensor no CWR
  styp     = sd_type_tns;
  // add 4 unit dimensions in tensor
  src_tns  = stns.split(3,1).split(4,1).split(5,1).split(6,1);
  scwr     = false;
  rnk_sel  = false;
}

template<template<typename> class B>
inline void dma_params<B>::set_src(const tensor_t<pix_t,5,B>&                      stns) {       // XM source tensor no CWR
  styp     = sd_type_tns;
  // add 3 unit dimensions in tensor
  src_tns  = stns.split(4,1).split(5,1).split(6,1);
  scwr     = false;
  rnk_sel  = true;
}

template<template<typename> class B>
inline void dma_params<B>::set_src(const tensor_t<pix_t,6,B>&                      stns) {       // XM source tensor, manual CWR (6d done outside)
  styp     = sd_type_tns;
  // add 2 unit dimensions in tensor
  src_tns  = stns.split(5,1).split(6,1);
  scwr     = true;
}

template<template<typename> class B>
inline void dma_params<B>::set_src(const tensor_t<pix_t,8,B>&                      stns) {       // XM source tensor CWR
  styp     = sd_type_tns;
  src_tns  = stns;
  scwr     = true;
}

template<template<typename> class B>
inline void dma_params<B>::set_src(const impl_spec_container_t<B>&                 scon) {       // implementation specific source
  styp     = sd_type_con;
  src_con  = scon;
  scwr     = false;
}

template<template<typename> class B>
inline void dma_params<B>::set_dst(const tensor_t<pix_t,4,B>&                      dtns) {       // destination tensor
  dtyp     = sd_type_tns;
  // add 4 unit dimensions in tensor
  dst_tns  = dtns.split(3,1).split(4,1).split(5,1).split(6,1);
  dcwr     = false;
  rnk_sel  = false;
}

template<template<typename> class B>
inline void dma_params<B>::set_dst(const tensor_t<pix_t,5,B>&                      dtns) {       // destination tensor
  dtyp     = sd_type_tns;
  // add 3 unit dimensions in tensor
  dst_tns  = dtns.split(4,1).split(5,1).split(6,1);
  dcwr     = false;
  rnk_sel  = true;
}

template<template<typename> class B>
inline void dma_params<B>::set_dst(const tensor_t<pix_t,6,B>&                      dtns) {       // destination tensor, manual CWR
  dtyp     = sd_type_tns;
  // add 2 unit dimensions in tensor
  dst_tns  = dtns.split(5,1).split(6,1);
  dcwr     = true;
}

template<template<typename> class B>
inline void dma_params<B>::set_dst(const tensor_t<pix_t,8,B>&                      dtns) {       // destination tensor
  dtyp     = sd_type_tns;
  dst_tns  = dtns;
  dcwr     = true;
}

template<template<typename> class B>
inline void dma_params<B>::set_dst(const impl_spec_container_t<B>&                 dcon) {       // implementation specific desintation
  dtyp     = sd_type_con;
  dst_con  = dcon;
  dcwr     = false;
}

// set padding zero-point
template<template<typename> class B>
inline void dma_params<B>::set_pad_val(
                                       pix_t v
                                       ) {
  hlapi.d.i.zero_point = v;
}

// set per channel write mask
template<template<typename> class B>
inline void dma_params<B>::set_channel_mask(
                       const uint16_t                  vm_wmsk  // channel mask inverted
                       ) {
  hlapi.d.i.vm_wmsk = vm_wmsk;
}
template<template<typename> class B>
inline void dma_params<B>::set_channel_mask(
                       const uint16_t                  vm_wmsk, // channel mask inverted
                       dma_params_impl_main&           p        // HLAPI structs
                       ) {
  p.hlapi.d.i.vm_wmsk = vm_wmsk;
}

// set Broadcast DMA flags
template<template<typename> class B>
inline void dma_params<B>::set_bdma(
                       dma_bc_t                        bflags    // B-DMA flags
                       ) {
  hlapi.d.i.bc = bflags;
}
template<template<typename> class B>
inline void dma_params<B>::set_bdma(
                       dma_bc_t                        bflags,   // B-DMA flags
                       dma_params_impl_main&           p        // HLAPI structs
                       ) {
  p.hlapi.d.i.bc = bflags;
}

template<template<typename> class B>
inline void dma_params<B>::modif_src(
                                     const tensor_t<pix_t,4,B>&      stns,
                                     dma_params_impl_modif&          alt        // encoded alternative shape
                                     ) {
  // source is in XM
  alt.offsets[NUM_FM_LOOPS-1] = stns.get_offset_last(0); // offset to next channel
  alt.offsets[NUM_FM_LOOPS-2] = stns.get_offset_last(1); // offset from last in channel to next column
  alt.offsets[NUM_FM_LOOPS-3] = stns.get_offset_last(2); // offset from last channel in last column to next row
  alt.offsets[NUM_FM_LOOPS-4] = stns.get_offset_last(3); // offset from last channel in last column in last row to next depth
  alt.iter[NUM_FM_LOOPS-1]    = stns.get_dim(0);
  alt.iter[NUM_FM_LOOPS-2]    = stns.get_dim(1);
  alt.iter[NUM_FM_LOOPS-3]    = stns.get_dim(2);
  alt.iter[NUM_FM_LOOPS-4]    = stns.get_dim(3);
  for (int i = 0; i < NUM_FM_LOOPS-4; i++) {
    alt.iter[i] = 1;
  }
}

template<template<typename> class B>
inline void dma_params<B>::modif_src_dst(
                                     const tensor_t<pix_t,8,B>&      tns,       // CWR tensor in XM
                                     const impl_spec_container_t<B>& vcon,      // tensor in VM
                                     dma_params_impl_modif&          vmalt,     // encoded alternative shape
                                     dma_params_impl_modif&          xmalt      // encoded alternative destination shape
                                     ) {
  assert((scwr || dcwr ) && "source or destination needs to be column-wise reordered");
  // CWR in XM
  tensor_t<ixpix_t,4,B> jtns(vcon.data.join(0));
  // resize the VM dimensions a multiple of the inner 4 XM dimensions [D*d][H*h][W*w][C*c]
  shape<8> sshp = tns.get_shape();
  assert(sshp[0] % ISIZE == 0 && "XM CWR inner channel dimension should be multiple of ISIZE");
  shape<4> tshp({(aoffset_t)(sshp[0]*sshp[4]/ISIZE),
                 (aoffset_t)(sshp[1]*sshp[5]),
                 (aoffset_t)(sshp[2]*sshp[6]),
                 (aoffset_t)(sshp[3]*sshp[7])});
  jtns.resize(0,NRND_UP(jtns.get_dim(0),tshp[0]));
  jtns.resize(1,NRND_UP(jtns.get_dim(1),tshp[1]));
  jtns.resize(2,NRND_UP(jtns.get_dim(2),tshp[2]));
  jtns.resize(3,NRND_UP(jtns.get_dim(3),tshp[3]));
  // split the VM tensor into 8D
  tensor_t<ixpix_t,5,B> splttns0(jtns.split(3,sshp[7]));
  tensor_t<ixpix_t,6,B> splttns1(splttns0.split(2,sshp[6]));
  tensor_t<ixpix_t,7,B> splttns2(splttns1.split(1,sshp[5]));
  tensor_t<ixpix_t,8,B> splttns(splttns2.split(0,sshp[4]));
  // move unit dimensions to outer
  tensor_t<ixpix_t,8,B> vmtns(splttns.transpose({0,2,4,6,1,3,5,7}));
  tensor_t<pix_t,8,B>   xmtns(tns);
  int c = 1;
  for (int i = 7; i >= 1; i--) {
    if (sshp[i] == 1) {
      vmtns = vmtns.reduce(i).split(6,1);
      xmtns = xmtns.reduce(i).split(6,1);
    } else {
      c++;
    }
  }
  assert (c <= 6 && "only 6D can be non-zero");
  (void)c;
  for (int i = 0; i < 6; i++) {
    vmalt.offsets[NUM_FM_LOOPS-1-i] = vmtns.get_offset_last(i);
    vmalt.iter[NUM_FM_LOOPS-1-i]    = vmtns.get_dim(i);
    xmalt.offsets[NUM_FM_LOOPS-1-i] = xmtns.get_offset_last(i);
    xmalt.iter[NUM_FM_LOOPS-1-i]    = xmtns.get_dim(i);
  }
}

template<template<typename> class B>
inline void dma_params<B>::modif_src(
                                     const impl_spec_container_t<B>& scon,
                                     dma_params_impl_modif&          alt        // encoded alternative shape
                                     ) {
  // source is VM
  alt.offsets[NUM_FM_LOOPS-1] = scon.data.get_offset_last(0);
  alt.offsets[NUM_FM_LOOPS-2] = scon.data.get_offset_last(1);
  alt.offsets[NUM_FM_LOOPS-3] = scon.data.get_offset_last(2);
  alt.offsets[NUM_FM_LOOPS-4] = scon.data.get_offset_last(3);
  alt.offsets[NUM_FM_LOOPS-5] = scon.data.get_offset_last(4);
  alt.iter[NUM_FM_LOOPS-1]    = scon.data.get_dim(0);
  alt.iter[NUM_FM_LOOPS-2]    = scon.data.get_dim(1);
  alt.iter[NUM_FM_LOOPS-3]    = scon.data.get_dim(2);
  alt.iter[NUM_FM_LOOPS-4]    = scon.data.get_dim(3);
  alt.iter[NUM_FM_LOOPS-5]    = scon.data.get_dim(4);
  for (int i = 0; i < NUM_FM_LOOPS-5; i++) {
    alt.iter[i] = 1;
  }
}

template<template<typename> class B>
inline void dma_params<B>::modif_dst(
                                     const tensor_t<pix_t,4,B>&      dtns,
                                     dma_params_impl_modif&          alt        // encoded alternative shape
                                     ) {
  // destination is in XM
  alt.offsets[NUM_FM_LOOPS-1] = dtns.get_offset_last(0); // offset to next channel
  alt.offsets[NUM_FM_LOOPS-2] = dtns.get_offset_last(1); // offset from last in channel to next column
  alt.offsets[NUM_FM_LOOPS-3] = dtns.get_offset_last(2); // offset from last channel in last column to next row
  alt.offsets[NUM_FM_LOOPS-4] = dtns.get_offset_last(3); // offset from last channel in last column in last row to next depth
  alt.iter[NUM_FM_LOOPS-1]    = dtns.get_dim(0);
  alt.iter[NUM_FM_LOOPS-2]    = dtns.get_dim(1);
  alt.iter[NUM_FM_LOOPS-3]    = dtns.get_dim(2);
  alt.iter[NUM_FM_LOOPS-4]    = dtns.get_dim(3);
  for (int i = 0; i < NUM_FM_LOOPS-4; i++) {
    alt.iter[i] = 1;
  }
}

template<template<typename> class B>
inline void dma_params<B>::modif_dst(
                                     const impl_spec_container_t<B>& dcon,
                                     dma_params_impl_modif&          alt        // encoded alternative shape
                                     ) {
  // source is VM
  alt.offsets[NUM_FM_LOOPS-1] = dcon.data.get_offset_last(0);
  alt.offsets[NUM_FM_LOOPS-2] = dcon.data.get_offset_last(1);
  alt.offsets[NUM_FM_LOOPS-3] = dcon.data.get_offset_last(2);
  alt.offsets[NUM_FM_LOOPS-4] = dcon.data.get_offset_last(3);
  alt.offsets[NUM_FM_LOOPS-5] = dcon.data.get_offset_last(4);
  alt.iter[NUM_FM_LOOPS-1]    = dcon.data.get_dim(0);
  alt.iter[NUM_FM_LOOPS-2]    = dcon.data.get_dim(1);
  alt.iter[NUM_FM_LOOPS-3]    = dcon.data.get_dim(2);
  alt.iter[NUM_FM_LOOPS-4]    = dcon.data.get_dim(3);
  alt.iter[NUM_FM_LOOPS-5]    = dcon.data.get_dim(4);
  for (int i = 0; i < NUM_FM_LOOPS-5; i++) {
    alt.iter[i] = 1;
  }
}

template<template<typename> class B>
void dma_params<B>::get_rt_params(dma_params_impl_main& p) {
  // fill the HLAPI structs
  p.sel = sel;
  p.hlapi.d.i.zero_point    = hlapi.d.i.zero_point;
  p.hlapi.d.i.bc            = hlapi.d.i.bc;
  p.hlapi.d.i.attrb         = hlapi.d.i.attrb;
  p.hlapi.d.i.planar_stride = hlapi.d.i.planar_stride;
  p.hlapi.d.i.planar_offset = hlapi.d.i.planar_offset;
  switch (sel.hw) {
  case dma_impl_stu:
    assert (styp == sd_type_tns && dtyp == sd_type_tns && "STU only does tensor to tensor copy");
    LDBGV(cout << "dst_tns(dims): 0: " << dst_tns.get_dim(0) << " 1: " << dst_tns.get_dim(1) << " 2: " << dst_tns.get_dim(2) << " 3: " << dst_tns.get_dim(3) << endl;)
    LDBGV(cout << "dst_tns(offsets): 0: " << dst_tns.get_offset(0) << " 1: " << dst_tns.get_offset(1) << " 2: " << dst_tns.get_offset(2) << " 3: " << dst_tns.get_offset(3) << endl;)
    p.hlapi.s.i.xmi_seq.boost = ((sel.bf & 0x2) ? 1 : 0) | ((sel.bf & 0x18) >> 2) ; // boost mode flags in [0] and outstanding config in [1:2] 
    p.hlapi.s.i.xmi_seq.ptr      = src_tns.get_ptr();
    p.hlapi.s.i.xmi_seq.buf      = xm_buf_t<pix_t>(src_tns.get_base(), src_tns.get_size());
    for (int i = 0; i < 6; i++) {
      p.hlapi.s.i.xmi_seq.offsets[NUM_FM_LOOPS-1-i] = src_tns.get_offset_last(i);
      p.hlapi.s.i.xmi_seq.iter[NUM_FM_LOOPS-1-i]    = src_tns.get_dim(i);
    }
    p.hlapi.s.i.xmo_seq.boost = ((sel.bf & 0x4) ? 1 : 0) | ((sel.bf & 0x60) >> 4) ; // boost mode flags in [0] and outstanding config in [1:2]
    p.hlapi.s.i.xmo_seq.ptr      = dst_tns.get_ptr();
    p.hlapi.s.i.xmo_seq.buf      = xm_buf_t<pix_t>(dst_tns.get_base(), dst_tns.get_size());
    for (int i = 0; i < 6; i++) {
      p.hlapi.s.i.xmo_seq.offsets[NUM_FM_LOOPS-1-i] = dst_tns.get_offset_last(i);
      p.hlapi.s.i.xmo_seq.iter[NUM_FM_LOOPS-1-i]    = dst_tns.get_dim(i);
    }
    // set outer to 1 iteration
    for (int i = 0; i < NUM_FM_LOOPS-6; i++) {
      p.hlapi.s.i.xmi_seq.iter[i]    = 1;
      p.hlapi.s.i.xmo_seq.iter[i]    = 1;
    }
    // wrap all offsets
    for (int i = 0; i < NUM_FM_LOOPS; i++) {
      p.hlapi.s.i.xmi_seq.offsets[i] = pbuf_wrap(p.hlapi.s.i.xmi_seq.offsets[i], p.hlapi.s.i.xmi_seq.buf.len);
      p.hlapi.s.i.xmo_seq.offsets[i] = pbuf_wrap(p.hlapi.s.i.xmo_seq.offsets[i], p.hlapi.s.i.xmo_seq.buf.len);
    }
    // copy to descriptor in DM
  #ifdef TENSOR_DMA_NINLINE_HPP_DEBUG
    cout << "copy to STU descriptor in DM" << endl;
    cout << "hlapi.s.i.xmi_seq.boost = "                   << (p.hlapi.s.i.xmi_seq.boost & 0x1) << endl;
    cout << "hlapi.s.i.xmi_seq.ost_cfg = "                 << ((p.hlapi.s.i.xmi_seq.boost & 0x6) >> 1) << endl;
    cout << "hlapi.s.i.xmi_seq.ptr      = "                << p.hlapi.s.i.xmi_seq.ptr << endl;
    cout << "hlapi.s.i.xmi_seq.buf.base = "                << p.hlapi.s.i.xmi_seq.buf.base << endl;
    cout << "hlapi.s.i.xmi_seq.buf.len  = "                << p.hlapi.s.i.xmi_seq.buf.len << endl;
    cout << "hlapi.s.i.xmi_seq.offsets[NUM_FM_LOOPS-1] = " << p.hlapi.s.i.xmi_seq.offsets[NUM_FM_LOOPS-1] << endl;
    cout << "hlapi.s.i.xmi_seq.offsets[NUM_FM_LOOPS-2] = " << p.hlapi.s.i.xmi_seq.offsets[NUM_FM_LOOPS-2] << endl;
    cout << "hlapi.s.i.xmi_seq.offsets[NUM_FM_LOOPS-3] = " << p.hlapi.s.i.xmi_seq.offsets[NUM_FM_LOOPS-3] << endl;
    cout << "hlapi.s.i.xmi_seq.offsets[NUM_FM_LOOPS-4] = " << p.hlapi.s.i.xmi_seq.offsets[NUM_FM_LOOPS-4] << endl;
    cout << "hlapi.s.i.xmi_seq.iter[NUM_FM_LOOPS-1] =    " << p.hlapi.s.i.xmi_seq.iter[NUM_FM_LOOPS-1] << endl;
    cout << "hlapi.s.i.xmi_seq.iter[NUM_FM_LOOPS-2] =    " << p.hlapi.s.i.xmi_seq.iter[NUM_FM_LOOPS-2] << endl;
    cout << "hlapi.s.i.xmi_seq.iter[NUM_FM_LOOPS-3] =    " << p.hlapi.s.i.xmi_seq.iter[NUM_FM_LOOPS-3] << endl;
    cout << "hlapi.s.i.xmi_seq.iter[NUM_FM_LOOPS-4] =    " << p.hlapi.s.i.xmi_seq.iter[NUM_FM_LOOPS-4] << endl;
    cout << "hlapi.s.i.xmo_seq.boost = "                   << (p.hlapi.s.i.xmo_seq.boost & 0x1) << endl; 
    cout << "hlapi.s.i.xmo_seq.ost_cfg = "                 << ((p.hlapi.s.i.xmo_seq.boost & 0x6) >> 1) << endl;
    cout << "hlapi.s.i.xmo_seq.ptr      = "                << p.hlapi.s.i.xmo_seq.ptr << endl;
    cout << "hlapi.s.i.xmo_seq.buf.base = "                << p.hlapi.s.i.xmo_seq.buf.base << endl;
    cout << "hlapi.s.i.xmo_seq.buf.len  = "                << p.hlapi.s.i.xmo_seq.buf.len << endl;
    cout << "hlapi.s.i.xmo_seq.offsets[NUM_FM_LOOPS-1] = " << p.hlapi.s.i.xmo_seq.offsets[NUM_FM_LOOPS-1] << endl;
    cout << "hlapi.s.i.xmo_seq.offsets[NUM_FM_LOOPS-2] = " << p.hlapi.s.i.xmo_seq.offsets[NUM_FM_LOOPS-2] << endl;
    cout << "hlapi.s.i.xmo_seq.offsets[NUM_FM_LOOPS-3] = " << p.hlapi.s.i.xmo_seq.offsets[NUM_FM_LOOPS-3] << endl;
    cout << "hlapi.s.i.xmo_seq.offsets[NUM_FM_LOOPS-4] = " << p.hlapi.s.i.xmo_seq.offsets[NUM_FM_LOOPS-4] << endl;
    cout << "hlapi.s.i.xmo_seq.iter[NUM_FM_LOOPS-1] =    " << p.hlapi.s.i.xmo_seq.iter[NUM_FM_LOOPS-1] << endl;
    cout << "hlapi.s.i.xmo_seq.iter[NUM_FM_LOOPS-2] =    " << p.hlapi.s.i.xmo_seq.iter[NUM_FM_LOOPS-2] << endl;
    cout << "hlapi.s.i.xmo_seq.iter[NUM_FM_LOOPS-3] =    " << p.hlapi.s.i.xmo_seq.iter[NUM_FM_LOOPS-3] << endl;
    cout << "hlapi.s.i.xmo_seq.iter[NUM_FM_LOOPS-4] =    " << p.hlapi.s.i.xmo_seq.iter[NUM_FM_LOOPS-4] << endl;
  #endif
    break;
  case dma_impl_idma:
    assert (styp == sd_type_tns && "iDMA only does tensor in XM");
    p.hlapi.d.i.vm_wmsk = 0;
    switch (dtyp) {
    case sd_type_con:
      // tensor to container
      // reduce if target width is bigger than source width
      {
        if (scwr) {
          // XM is columnwise reordered, need to reshape VM tensor to match XM
          // join the group and channel dimensions
          tensor_t<ixpix_t,4,B> jtns(dst_con.data.join(0));
          // resize the VM dimensions a multiple of the inner 4 XM dimensions [D*d][H*h][W*w][C*c]
          shape<8> sshp = src_tns.get_shape();
          assert(sshp[0] % ISIZE == 0 && "XM CWR inner channel dimension should be multiple of ISIZE");
          shape<4> tshp({(aoffset_t)(sshp[0]*sshp[4]/ISIZE),
                         (aoffset_t)(sshp[1]*sshp[5]),
                         (aoffset_t)(sshp[2]*sshp[6]),
                         (aoffset_t)(sshp[3]*sshp[7])});
          jtns.resize(0,NRND_UP(jtns.get_dim(0),tshp[0]));
          jtns.resize(1,NRND_UP(jtns.get_dim(1),tshp[1]));
          jtns.resize(2,NRND_UP(jtns.get_dim(2),tshp[2]));
          jtns.resize(3,NRND_UP(jtns.get_dim(3),tshp[3]));
          // split the VM tensor into 8D
          tensor_t<ixpix_t,5,B> splttns0(jtns.split(3,sshp[7]));
          tensor_t<ixpix_t,6,B> splttns1(splttns0.split(2,sshp[6]));
          tensor_t<ixpix_t,7,B> splttns2(splttns1.split(1,sshp[5]));
          tensor_t<ixpix_t,8,B> splttns(splttns2.split(0,sshp[4]));
          // move unit dimensions to outer
          tensor_t<ixpix_t,8,B> vmtns(splttns.transpose({0,2,4,6,1,3,5,7}));
          tensor_t<pix_t,8,B>   xmtns(src_tns);
          int c = 1;
          for (int i = 7; i >= 1; i--) {
            if (sshp[i] == 1) {
              vmtns = vmtns.reduce(i).split(6,1);
              xmtns = xmtns.reduce(i).split(6,1);
            } else {
              c++;
            }
          }
          assert (c <= 6 && "only 6D can be non-zero");
          (void)c;
          // VM and XM offsets
          p.hlapi.d.i.vm_seq.ptr      = vmtns.get_ptr();
          p.hlapi.d.i.vm_seq.buf      = buf_t<ixpix_t>(vmtns.get_base(), vmtns.get_size());
          p.hlapi.d.i.vm_seq.stride   = 1;
          p.hlapi.d.i.xm_seq.compress = 0;
          p.hlapi.d.i.xm_seq.cblen    = 0;
          p.hlapi.d.i.xm_seq.ptr      = xmtns.get_ptr();
          p.hlapi.d.i.xm_seq.buf      = xm_buf_t<pix_t>(xmtns.get_base(), xmtns.get_size());
          for (int i = 0; i < 6; i++) {
            p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-1-i] = vmtns.get_offset_last(i);
            p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-1-i]    = vmtns.get_dim(i);
            p.hlapi.d.i.xm_seq.offsets[NUM_FM_LOOPS-1-i] = xmtns.get_offset_last(i);
            p.hlapi.d.i.xm_seq.iter[NUM_FM_LOOPS-1-i]    = xmtns.get_dim(i);
          }
        } else {
          // XM is not columnwise reordered
          aoffset_t tw = rnk_sel ? dst_con.data.get_dim(2) : src_tns.get_dim(1); // get tw from dst or src based on rank selection flag
          tensor_t<ixpix_t,5,B> dtns(dst_con.data.slice({0,0,0,0,0},{dst_con.data.get_dim(0),dst_con.data.get_dim(1),tw,dst_con.data.get_dim(3),dst_con.data.get_dim(4)}));
          p.hlapi.d.i.vm_seq.ptr      = dtns.get_ptr();
          p.hlapi.d.i.vm_seq.buf      = buf_t<ixpix_t>(dtns.get_base(), dtns.get_size());
          p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-1] = dtns.get_offset_last(0);
          p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-2] = dtns.get_offset_last(1);
          p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-3] = dtns.get_offset_last(2);
          p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-4] = dtns.get_offset_last(3);
          p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-5] = dtns.get_offset_last(4);
          p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-1]    = dtns.get_dim(0);
          p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-2]    = dtns.get_dim(1);
          p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-3]    = tw;
          p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-4]    = dtns.get_dim(3);
          p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-5]    = dtns.get_dim(4);
          p.hlapi.d.i.vm_seq.stride   = 1;
          for (int i = 0; i < NUM_FM_LOOPS-5; i++) {
            p.hlapi.d.i.vm_seq.iter[i]    = 1;
          }
          p.hlapi.d.i.xm_seq.compress = sel.bf;
          p.hlapi.d.i.xm_seq.cblen    = 15;
          p.hlapi.d.i.xm_seq.ptr      = src_tns.get_ptr();
          p.hlapi.d.i.xm_seq.buf      = xm_buf_t<pix_t>(src_tns.get_base(), src_tns.get_size());
          for (int i = 0; i < 6; i++) {
            p.hlapi.d.i.xm_seq.offsets[NUM_FM_LOOPS-1-i] = src_tns.get_offset_last(i);
            p.hlapi.d.i.xm_seq.iter[NUM_FM_LOOPS-1-i]    = src_tns.get_dim(i);
          }
          for (int i = 0; i < NUM_FM_LOOPS-6; i++) {
            p.hlapi.d.i.xm_seq.iter[i]    = 1;
          }
        }
      }
      break;
    default:
      // tensor to tensor
      assert(dst_tns.get_offset(0) == 1);
      LDBGV(cout << "dst_tns(dims): 0: " << dst_tns.get_dim(0) << " 1: " << dst_tns.get_dim(1) << " 2: " << dst_tns.get_dim(2) << " 3: " << dst_tns.get_dim(3) << endl;)
      LDBGV(cout << "dst_tns(offsets): 0: " << dst_tns.get_offset(0) << " 1: " << dst_tns.get_offset(1) << " 2: " << dst_tns.get_offset(2) << " 3: " << dst_tns.get_offset(3) << endl;)
      p.hlapi.d.i.vm_seq.ptr      = reinterpret_cast<ixpix_t*>(dst_tns.get_ptr());
      p.hlapi.d.i.vm_seq.buf      = buf_t<ixpix_t>(reinterpret_cast<ixpix_t*>(dst_tns.get_base()), dst_tns.get_size()/ISIZE);
      p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-1]    = dst_tns.get_dim(0)/ISIZE;
      p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-2]    = dst_tns.get_dim(1);
      p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-3]    = dst_tns.get_dim(2);
      p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-4]    = dst_tns.get_dim(3);
      p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-1] = 1;
      p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-2] = (dst_tns.get_offset(1)+(ISIZE-p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-1]*ISIZE)*dst_tns.get_offset(0))/ISIZE;
      p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-3] = (dst_tns.get_offset(2)+(ISIZE-p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-1]*ISIZE)*dst_tns.get_offset(0)+(1-p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-2])*dst_tns.get_offset(1))/ISIZE;
      p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-4] = (dst_tns.get_offset(3)+(ISIZE-p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-1]*ISIZE)*dst_tns.get_offset(0)+(1-p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-2])*dst_tns.get_offset(1)+(1-p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-3])*dst_tns.get_offset(2))/ISIZE;
      p.hlapi.d.i.vm_seq.stride   = 1;
      p.hlapi.d.i.xm_seq.compress = sel.bf;
      p.hlapi.d.i.xm_seq.cblen    = 15;
      p.hlapi.d.i.xm_seq.ptr      = src_tns.get_ptr();
      p.hlapi.d.i.xm_seq.buf      = xm_buf_t<pix_t>(src_tns.get_base(), src_tns.get_size());
      for (int i = 0; i < 6; i++) {
        p.hlapi.d.i.xm_seq.offsets[NUM_FM_LOOPS-1-i] = src_tns.get_offset_last(i);
        p.hlapi.d.i.xm_seq.iter[NUM_FM_LOOPS-1-i]    = src_tns.get_dim(i);
      }
      for (int i = 0; i < NUM_FM_LOOPS-6; i++) {
        p.hlapi.d.i.xm_seq.iter[i] = 1;
      }
      // TBD: for test
      p.hlapi.d.i.xm_seq.o.moffsets[NUM_FM_LOOPS-1] = src_tns.get_offset_last(0); // offset to next channel
      p.hlapi.d.i.xm_seq.o.moffsets[NUM_FM_LOOPS-2] = src_tns.get_offset_last(1); // offset from last in channel to next column
      p.hlapi.d.i.xm_seq.o.moffsets[NUM_FM_LOOPS-3] = src_tns.get_offset_last(2); // offset from last channel in last column to next row
      p.hlapi.d.i.xm_seq.o.moffsets[NUM_FM_LOOPS-4] = src_tns.get_offset_last(3); // offset from last channel in last column in last row to next depth
      for (int i = 0; i < NUM_FM_LOOPS-4; i++) {
        p.hlapi.d.i.vm_seq.iter[i]    = 1;
      }
      break;
    }
    // wrap all offsets
    for (int i = 0; i < NUM_FM_LOOPS; i++) {
      p.hlapi.d.i.vm_seq.offsets[i] = vbuf_wrap(p.hlapi.d.i.vm_seq.offsets[i], p.hlapi.d.i.vm_seq.buf.len);
      p.hlapi.d.i.xm_seq.offsets[i] = pbuf_wrap(p.hlapi.d.i.xm_seq.offsets[i], p.hlapi.d.i.xm_seq.buf.len);
    }
    // copy to descriptor in DM
  #ifdef TENSOR_DMA_NINLINE_HPP_DEBUG
    cout << "copy to iDMA descriptor in DM" << endl;
    cout << "hlapi.d.i.vm_seq.ptr = " << p.hlapi.d.i.vm_seq.ptr.get_raw() << endl;
    cout << "hlapi.d.i.vm_seq.buf.base = " << p.hlapi.d.i.vm_seq.buf.base << endl;
    cout << "hlapi.d.i.vm_seq.buf.len = " << p.hlapi.d.i.vm_seq.buf.len << endl;
    cout << "hlapi.d.i.vm_seq.offsets["<<NUM_FM_LOOPS-1<<"] = " << p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-1] << endl;
    cout << "hlapi.d.i.vm_seq.offsets["<<NUM_FM_LOOPS-2<<"] = " << p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-2] << endl; 
    cout << "hlapi.d.i.vm_seq.offsets["<<NUM_FM_LOOPS-3<<"] = " << p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-3] << endl;
    cout << "hlapi.d.i.vm_seq.offsets["<<NUM_FM_LOOPS-4<<"] = " << p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-4] << endl;
    cout << "hlapi.d.i.vm_seq.offsets["<<NUM_FM_LOOPS-5<<"] = " << p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-5] << endl;
    cout << "hlapi.d.i.vm_seq.iter["<<NUM_FM_LOOPS-1<<"]    = " << p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-1] << endl;
    cout << "hlapi.d.i.vm_seq.iter["<<NUM_FM_LOOPS-2<<"]    = " << p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-2] << endl;
    cout << "hlapi.d.i.vm_seq.iter["<<NUM_FM_LOOPS-3<<"]    = " << p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-3] << endl;
    cout << "hlapi.d.i.vm_seq.iter["<<NUM_FM_LOOPS-4<<"]    = " << p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-4] << endl;
    cout << "hlapi.d.i.vm_seq.iter["<<NUM_FM_LOOPS-5<<"]    = " << p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-5] << endl;
    cout << "hlapi.d.i.vm_seq.stride   = " << p.hlapi.d.i.vm_seq.stride << endl;
    cout << "hlapi.d.i.xm_seq.compress = " << p.hlapi.d.i.xm_seq.compress << endl; 
    cout << "hlapi.d.i.xm_seq.ptr      = " << p.hlapi.d.i.xm_seq.ptr << endl;
    cout << "hlapi.d.i.xm_seq.buf.base      = " << p.hlapi.d.i.xm_seq.buf.base << endl;
    cout << "hlapi.d.i.xm_seq.buf.len      = " << p.hlapi.d.i.xm_seq.buf.len << endl;
    cout << "hlapi.d.i.xm_seq.offsets["<<NUM_FM_LOOPS-1<<"] = " << p.hlapi.d.i.xm_seq.offsets[NUM_FM_LOOPS-1] << endl;
    cout << "hlapi.d.i.xm_seq.offsets["<<NUM_FM_LOOPS-2<<"] = " << p.hlapi.d.i.xm_seq.offsets[NUM_FM_LOOPS-2] << endl;
    cout << "hlapi.d.i.xm_seq.offsets["<<NUM_FM_LOOPS-3<<"] = " << p.hlapi.d.i.xm_seq.offsets[NUM_FM_LOOPS-3] << endl;
    cout << "hlapi.d.i.xm_seq.offsets["<<NUM_FM_LOOPS-4<<"] = " << p.hlapi.d.i.xm_seq.offsets[NUM_FM_LOOPS-4] << endl;
    cout << "hlapi.d.i.xm_seq.offsets["<<NUM_FM_LOOPS-5<<"] = " << p.hlapi.d.i.xm_seq.offsets[NUM_FM_LOOPS-5] << endl;
    cout << "hlapi.d.i.xm_seq.iter["<<NUM_FM_LOOPS-1<<"] = " << p.hlapi.d.i.xm_seq.iter[NUM_FM_LOOPS-1] << endl;
    cout << "hlapi.d.i.xm_seq.iter["<<NUM_FM_LOOPS-2<<"] = " << p.hlapi.d.i.xm_seq.iter[NUM_FM_LOOPS-2] << endl;
    cout << "hlapi.d.i.xm_seq.iter["<<NUM_FM_LOOPS-3<<"] = " << p.hlapi.d.i.xm_seq.iter[NUM_FM_LOOPS-3] << endl;
    cout << "hlapi.d.i.xm_seq.iter["<<NUM_FM_LOOPS-4<<"] = " << p.hlapi.d.i.xm_seq.iter[NUM_FM_LOOPS-4] << endl;
    cout << "hlapi.d.i.xm_seq.iter["<<NUM_FM_LOOPS-5<<"] = " << p.hlapi.d.i.xm_seq.iter[NUM_FM_LOOPS-5] << endl;
    cout << "hlapi.d.i.planar_stride = " << p.hlapi.d.i.planar_stride << endl;
    cout << "hlapi.d.i.planar_offset = " << p.hlapi.d.i.planar_offset << endl;
  #endif
    break;
  case dma_impl_odma:
    assert (dtyp == sd_type_tns && "oDMA only does tensor in XM");
    switch (styp) {
    case sd_type_con:
      // tensor to container
      // reduce if source width is bigger than source width
      {
        if (dcwr) {
          // XM is columnwise reordered, need to reshape VM tensor to match XM
          // join the group and channel dimensions
          tensor_t<ixpix_t,4,B> jtns(src_con.data.join(0));
          // resize the VM dimensions to a multiple of the inner 4 XM dimensions [D*d][H*h][W*w][C*c]
          shape<8> sshp = dst_tns.get_shape();
          assert(sshp[0] % ISIZE == 0 && "XM CWR inner channel dimension should be multiple of ISIZE");
          shape<4> tshp({(aoffset_t)(sshp[0]*sshp[4]/ISIZE),
                         (aoffset_t)(sshp[1]*sshp[5]),
                         (aoffset_t)(sshp[2]*sshp[6]),
                         (aoffset_t)(sshp[3]*sshp[7])});
          jtns.resize(0,NRND_UP(jtns.get_dim(0),tshp[0]));
          jtns.resize(1,NRND_UP(jtns.get_dim(1),tshp[1]));
          jtns.resize(2,NRND_UP(jtns.get_dim(2),tshp[2]));
          jtns.resize(3,NRND_UP(jtns.get_dim(3),tshp[3]));
          // split the VM tensor into 8D
          tensor_t<ixpix_t,5,B> splttns0(jtns.split(3,sshp[7]));
          tensor_t<ixpix_t,6,B> splttns1(splttns0.split(2,sshp[6]));
          tensor_t<ixpix_t,7,B> splttns2(splttns1.split(1,sshp[5]));
          tensor_t<ixpix_t,8,B> splttns(splttns2.split(0,sshp[4]));
          // move unit dimensions to outer
          tensor_t<ixpix_t,8,B> vmtns(splttns.transpose({0,2,4,6,1,3,5,7}));
          tensor_t<pix_t,8,B>   xmtns(dst_tns);
          int c = 1;
          for (int i = 7; i >= 1; i--) {
            if (sshp[i] == 1) {
              vmtns = vmtns.reduce(i).split(6,1);
              xmtns = xmtns.reduce(i).split(6,1);
            } else {
              c++;
            }
          }
          assert (c <= 6 && "only 6D can be non-zero");
          (void)c;
          // VM and XM offsets
          p.hlapi.d.i.vm_seq.ptr      = vmtns.get_ptr();
          p.hlapi.d.i.vm_seq.buf      = buf_t<ixpix_t>(vmtns.get_base(), vmtns.get_size());
          p.hlapi.d.i.vm_seq.stride   = 1;
          p.hlapi.d.i.xm_seq.compress = 0;
          p.hlapi.d.i.xm_seq.cblen    = 0;
          p.hlapi.d.i.xm_seq.ptr      = xmtns.get_ptr();
          p.hlapi.d.i.xm_seq.buf      = xm_buf_t<pix_t>(xmtns.get_base(), xmtns.get_size());
          for (int i = 0; i < 6; i++) {
            p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-1-i] = vmtns.get_offset_last(i);
            p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-1-i]    = vmtns.get_dim(i);
            p.hlapi.d.i.xm_seq.offsets[NUM_FM_LOOPS-1-i] = xmtns.get_offset_last(i);
            p.hlapi.d.i.xm_seq.iter[NUM_FM_LOOPS-1-i]    = xmtns.get_dim(i);
          }
        } else {
          // XM is not columnwise reordered
          aoffset_t sw = rnk_sel ? src_con.data.get_dim(2) : dst_tns.get_dim(1); // get sw from src or dst based on rank selection flag
          tensor_t<ixpix_t,5,B> stns(src_con.data.slice({0,0,0,0,0},{src_con.data.get_dim(0),src_con.data.get_dim(1),sw,src_con.data.get_dim(3),src_con.data.get_dim(4)}));
          p.hlapi.d.i.vm_seq.ptr      = stns.get_ptr();
          p.hlapi.d.i.vm_seq.buf      = buf_t<ixpix_t>(stns.get_base(), stns.get_size());
          p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-1] = stns.get_offset_last(0);
          p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-2] = stns.get_offset_last(1);
          p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-3] = stns.get_offset_last(2);
          p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-4] = stns.get_offset_last(3);
          p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-5] = stns.get_offset_last(4);
          p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-1]    = stns.get_dim(0);
          p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-2]    = stns.get_dim(1);
          p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-3]    = sw;
          p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-4]    = stns.get_dim(3);
          p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-5]    = stns.get_dim(4);
          for (int i = 0; i < NUM_FM_LOOPS-5; i++) {
            p.hlapi.d.i.vm_seq.iter[i]    = 1;
          }
          p.hlapi.d.i.vm_seq.stride   = 1;
          p.hlapi.d.i.xm_seq.compress = sel.bf;
          p.hlapi.d.i.xm_seq.ptr      = dst_tns.get_ptr();
          p.hlapi.d.i.xm_seq.buf      = xm_buf_t<pix_t>(dst_tns.get_base(), dst_tns.get_size());
          for (int i = 0; i < 6; i++) {
            p.hlapi.d.i.xm_seq.offsets[NUM_FM_LOOPS-1-i] = dst_tns.get_offset_last(i);
            p.hlapi.d.i.xm_seq.iter[NUM_FM_LOOPS-1-i]    = dst_tns.get_dim(i);
          }
          for (int i = 0; i < NUM_FM_LOOPS-6; i++) {
            p.hlapi.d.i.xm_seq.iter[i] = 0;
          }
        }
      }
      break;
    default:
      // tensor to tensor
      assert(src_tns.get_offset(0) == 1);
      p.hlapi.d.i.vm_seq.ptr      = reinterpret_cast<ixpix_t*>(src_tns.get_ptr());
      p.hlapi.d.i.vm_seq.buf      = buf_t<ixpix_t>(reinterpret_cast<ixpix_t*>(src_tns.get_base()), src_tns.get_size()/ISIZE);
      p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-1]    = src_tns.get_dim(0)/ISIZE;
      p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-2]    = src_tns.get_dim(1);
      p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-3]    = src_tns.get_dim(2);
      p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-4]    = src_tns.get_dim(3);
      p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-1] = 1;
      p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-2] = (src_tns.get_offset(1)+(ISIZE-p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-1]*ISIZE)*src_tns.get_offset(0))/ISIZE;
      p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-3] = (src_tns.get_offset(2)+(ISIZE-p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-1]*ISIZE)*src_tns.get_offset(0)+(1-p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-2])*src_tns.get_offset(1))/ISIZE;
      p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-4] = (src_tns.get_offset(3)+(ISIZE-p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-1]*ISIZE)*src_tns.get_offset(0)+(1-p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-2])*src_tns.get_offset(1)+(1-p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-3])*src_tns.get_offset(2))/ISIZE;
      for (int i = 0; i < NUM_FM_LOOPS-4; i++) {
        p.hlapi.d.i.vm_seq.iter[i]    = 1;
      }
      p.hlapi.d.i.vm_seq.stride   = 1;
      p.hlapi.d.i.xm_seq.compress = sel.bf;
      p.hlapi.d.i.xm_seq.ptr      = dst_tns.get_ptr();
      p.hlapi.d.i.xm_seq.buf      = xm_buf_t<pix_t>(dst_tns.get_base(), dst_tns.get_size());
      for (int i = 0; i < 6; i++) {
        p.hlapi.d.i.xm_seq.offsets[NUM_FM_LOOPS-1-i] = dst_tns.get_offset_last(i);
        p.hlapi.d.i.xm_seq.iter[NUM_FM_LOOPS-1-i]    = dst_tns.get_dim(i);
      }
      for (int i = 0; i < NUM_FM_LOOPS-6; i++) {
        p.hlapi.d.i.xm_seq.iter[i]    = 1;
      }
      break;
    }
    // wrap all offsets
    for (int i = 0; i < NUM_FM_LOOPS; i++) {
      p.hlapi.d.i.vm_seq.offsets[i] = vbuf_wrap(p.hlapi.d.i.vm_seq.offsets[i], p.hlapi.d.i.vm_seq.buf.len);
      p.hlapi.d.i.xm_seq.offsets[i] = pbuf_wrap(p.hlapi.d.i.xm_seq.offsets[i], p.hlapi.d.i.xm_seq.buf.len);
    }
    // copy to descriptor in DM
  #ifdef DUMP_TNS
    cout << "copy to oDMA descriptor in DM" << endl;
    cout << "hlapi.d.i.vm_seq.ptr = " << p.hlapi.d.i.vm_seq.ptr << endl;
    cout << "hlapi.d.i.vm_seq.buf.base = " << p.hlapi.d.i.vm_seq.buf.base << endl;
    cout << "hlapi.d.i.vm_seq.buf.len = " << p.hlapi.d.i.vm_seq.buf.len << endl;
    cout << "hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-1] = " << p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-1] << endl;
    cout << "hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-2] = " << p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-2] << endl; 
    cout << "hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-3] = " << p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-3] << endl;
    cout << "hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-4] = " << p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-4] << endl;
    cout << "hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-5] = " << p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-5] << endl;
    cout << "hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-1]    = " << p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-1] << endl;
    cout << "hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-2]    = " << p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-2] << endl;
    cout << "hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-3]    = " << p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-3] << endl;
    cout << "hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-4]    = " << p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-4] << endl;
    cout << "hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-5]    = " << p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-5] << endl;
    cout << "hlapi.d.i.vm_seq.stride   = " << p.hlapi.d.i.vm_seq.stride << endl;
    cout << "hlapi.d.i.xm_seq.compress = " << p.hlapi.d.i.xm_seq.compress << endl; 
    cout << "hlapi.d.i.xm_seq.ptr      = " << p.hlapi.d.i.xm_seq.ptr << endl;
    cout << "hlapi.d.i.xm_seq.buf.base      = " << p.hlapi.d.i.xm_seq.buf.base << endl;
    cout << "hlapi.d.i.xm_seq.buf.len      = " << p.hlapi.d.i.xm_seq.buf.len << endl;
    cout << "hlapi.d.i.xm_seq.offsets[NUM_FM_LOOPS-1] = " << p.hlapi.d.i.xm_seq.offsets[NUM_FM_LOOPS-1] << endl;
    cout << "hlapi.d.i.xm_seq.offsets[NUM_FM_LOOPS-2] = " << p.hlapi.d.i.xm_seq.offsets[NUM_FM_LOOPS-2] << endl;
    cout << "hlapi.d.i.xm_seq.offsets[NUM_FM_LOOPS-3] = " << p.hlapi.d.i.xm_seq.offsets[NUM_FM_LOOPS-3] << endl;
    cout << "hlapi.d.i.xm_seq.offsets[NUM_FM_LOOPS-4] = " << p.hlapi.d.i.xm_seq.offsets[NUM_FM_LOOPS-4] << endl;
    cout << "hlapi.d.i.xm_seq.iter[NUM_FM_LOOPS-1] = " << p.hlapi.d.i.xm_seq.iter[NUM_FM_LOOPS-1] << endl;
    cout << "hlapi.d.i.xm_seq.iter[NUM_FM_LOOPS-2] = " << p.hlapi.d.i.xm_seq.iter[NUM_FM_LOOPS-2] << endl;
    cout << "hlapi.d.i.xm_seq.iter[NUM_FM_LOOPS-3] = " << p.hlapi.d.i.xm_seq.iter[NUM_FM_LOOPS-3] << endl;
    cout << "hlapi.d.i.xm_seq.iter[NUM_FM_LOOPS-4] = " << p.hlapi.d.i.xm_seq.iter[NUM_FM_LOOPS-4] << endl;
    cout << "hlapi.d.i.planar_stride = " << p.hlapi.d.i.planar_stride << endl;
    cout << "hlapi.d.i.planar_offset = " << p.hlapi.d.i.planar_offset << endl;
  #endif
    break;
  default: assert(0);
  }
}

//
// Run-time functions
//

// constructor
inline dma_rt::dma_rt(
                      dma_params_impl_main&                                  p  // convolution parameter class object
                      ) {
  pars   = p;
  mmio.s = nullptr;
  pars.hlapi.s.i.common.next = globalptr_t<npu::hlapi_i_t>(nullptr);
}

// set per channel write mask
inline void dma_rt::set_channel_mask(
                                const uint16_t                               vm_wmsk  // channel mask inverted
                               ) {
  mem_write(&pars.hlapi.d.i.vm_wmsk, vm_wmsk);
}

// set Broadcast DMA flags
inline void dma_rt::set_bdma(
                                dma_bc_t                             bflags// channel mask inverted
                               ) {
  mem_write(&pars.hlapi.d.i.bc, bflags);
}

// Set implementation specific run-time attributes
inline void dma_rt::set_impl_params(
                                    const dma_rt_impl_spec&                  p  // structure with run-time specific parameters
                                    ) {
  if (mem_read(&pars.sel.hw) == dma_impl_stu) {
    mem_write(&pars.hlapi.s.i.common.ctrl, mem_read(&p.ctrl));
    mem_write(&pars.hlapi.s.i.common.id, mem_read(&p.id));
    mem_write(&mmio.s, mem_read(&p.mmio.s));
  } else {
    mem_write(&pars.hlapi.d.i.common.ctrl, mem_read(&p.ctrl));
    mem_write(&pars.hlapi.d.i.common.id, mem_read(&p.id));
    mem_write(&mmio.d, mem_read(&p.mmio.d));
  }
}

// Get implementation specific run-time attributes
inline void dma_rt::get_impl_params(
                                    dma_rt_impl_spec&                        p  // return structure with run-time specific parameters
                                    ) {
  if (mem_read(&pars.sel.hw) == dma_impl_stu) {
    mem_write(&p.ctrl,  mem_read(&pars.hlapi.s.i.common.ctrl));
    mem_write(&p.id,    mem_read(&pars.hlapi.s.i.common.id));
    mem_write(&p.mmio.s, mem_read(&p.mmio.s));
  } else {
    mem_write(&p.ctrl,  mem_read(&pars.hlapi.d.i.common.ctrl));
    mem_write(&p.id,    mem_read(&pars.hlapi.d.i.common.id));
    mem_write(&p.mmio.d, mem_read(&p.mmio.d));
  }
}

// Set relocated source
template <size_t R>
inline void dma_rt::set_src(const tensor_t<pix_t,R>& stns) {
  switch (mem_read(&pars.sel.hw)) {
  case dma_impl_stu:
    {
      tensor_t<pix_t,R> st(mem_read(&stns));
      mem_write(&pars.hlapi.s.i.xmi_seq.ptr, globalptr_t<pix_t>(st.get_ptr()));
      mem_write(&pars.hlapi.s.i.xmi_seq.buf.base, globalptr_t<pix_t>(st.get_base()));
    }
    break;
  case dma_impl_idma:
    {
      tensor_t<pix_t,R> st(mem_read(&stns));
      mem_write(&pars.hlapi.d.i.xm_seq.ptr, globalptr_t<pix_t>(st.get_ptr()));
      mem_write(&pars.hlapi.d.i.xm_seq.buf.base, globalptr_t<pix_t>(st.get_base()));
    }
    break;
  case dma_impl_odma:
    {
      tensor_t<pix_t,R> st(mem_read(&stns));
      mem_write(&pars.hlapi.d.i.vm_seq.ptr, localptr_t<ixpix_t>(reinterpret_cast<ixpix_t*>(st.get_ptr())));
      mem_write(&pars.hlapi.d.i.vm_seq.buf.base, localptr_t<ixpix_t>(reinterpret_cast<ixpix_t*>(st.get_base())));
    }
    break;
  default: 
    assert(0 && "unsupported implementation mode");
    break;
  }
}

// Set relocated source
inline void dma_rt::set_src(const buffer_t<pix_t>&         sbuf) {
  // iDMA
  mem_write(&pars.hlapi.d.i.xm_seq.ptr, globalptr_t<pix_t>(sbuf.get_base()));
  mem_write(&pars.hlapi.d.i.xm_seq.buf.base, globalptr_t<pix_t>(sbuf.get_base()));
}

// Set input ptr in XM
inline void dma_rt::set_xm_ptr(globalptr_t<pix_t>          ptr) {
  mem_write(&pars.hlapi.d.i.xm_seq.ptr, ptr);
  mem_write(&pars.hlapi.d.i.xm_seq.buf.base, ptr);
}

inline void dma_rt::set_src(const buffer_t<ixpix_t>&           sbuf) {
  // oDMA
  mem_write(&pars.hlapi.d.i.vm_seq.ptr, localptr_t<ixpix_t>(sbuf.get_base()));
  mem_write(&pars.hlapi.d.i.vm_seq.buf.base, localptr_t<ixpix_t>(sbuf.get_base()));
}

// Set relocated destination
inline void dma_rt::set_dst(const buffer_t<ixpix_t>&           dbuf) {
  // iDMA
  mem_write(&pars.hlapi.d.i.vm_seq.ptr, localptr_t<ixpix_t>(dbuf.get_base()));
  mem_write(&pars.hlapi.d.i.vm_seq.buf.base, localptr_t<ixpix_t>(dbuf.get_base()));
}

inline void dma_rt::set_dst(const buffer_t<pix_t>&         dbuf) {
  // oDMA
  mem_write(&pars.hlapi.d.i.xm_seq.ptr, globalptr_t<pix_t>(dbuf.get_base()));
  mem_write(&pars.hlapi.d.i.xm_seq.buf.base, globalptr_t<pix_t>(dbuf.get_base()));
}
inline void dma_rt::set_src(const impl_spec_container_t<buffer_t>&                     scon) {
  // oDMA
  tensor_t<ixpix_t,5> st(mem_read(&scon.data));
  mem_write(&pars.hlapi.d.i.vm_seq.ptr, localptr_t<ixpix_t>(reinterpret_cast<ixpix_t*>(st.get_ptr())));
  mem_write(&pars.hlapi.d.i.vm_seq.buf.base, localptr_t<ixpix_t>(reinterpret_cast<ixpix_t*>(st.get_base())));
}
inline void dma_rt::set_isrc(const impl_spec_container_t<buffer_t>&                     scon) {
  // gather index source
  tensor_t<ixpix_t,5> st(mem_read(&scon.data));
  mem_write(&pars.hlapi.d.i.xm_seq.p.g.gptr, localptr_t<ixpix_t>(reinterpret_cast<ixpix_t*>(st.get_ptr())));
  mem_write(&pars.hlapi.d.i.xm_seq.b.g.gbuf.base, localptr_t<ixpix_t>(reinterpret_cast<ixpix_t*>(st.get_base())));
}

// Set relocated destination
template <size_t R>
inline void dma_rt::set_dst(const tensor_t<pix_t,R>&                               dtns) {
  switch (mem_read(&pars.sel.hw)) {
  case dma_impl_stu:
    {
      tensor_t<pix_t,R> dt(mem_read(&dtns));
      mem_write(&pars.hlapi.s.i.xmo_seq.ptr, globalptr_t<pix_t>(dt.get_ptr()));
      mem_write(&pars.hlapi.s.i.xmo_seq.buf.base, globalptr_t<pix_t>(dt.get_base()));
    }
    break;
  case dma_impl_idma:
    {
      tensor_t<pix_t,R> dt(mem_read(&dtns));
      mem_write(&pars.hlapi.d.i.vm_seq.ptr, localptr_t<ixpix_t>(reinterpret_cast<ixpix_t*>(dt.get_ptr())));
      mem_write(&pars.hlapi.d.i.vm_seq.buf.base, localptr_t<ixpix_t>(reinterpret_cast<ixpix_t*>(dt.get_base())));
    }
    break;
  case dma_impl_odma:
    {
      tensor_t<pix_t,R> dt(mem_read(&dtns));
      mem_write(&pars.hlapi.d.i.xm_seq.ptr, globalptr_t<pix_t>(dt.get_ptr()));
      mem_write(&pars.hlapi.d.i.xm_seq.buf.base, globalptr_t<pix_t>(dt.get_base()));
    }
    break;
  default: 
    assert(0 && "unsupported implementation mode");
    break;
  }
}
inline void dma_rt::set_dst(
                            const impl_spec_container_t<buffer_t>&                           dcon
                            ) {
  tensor_t<ixpix_t,5> dt(mem_read(&dcon.data));
  mem_write(&pars.hlapi.d.i.vm_seq.ptr, localptr_t<ixpix_t>(reinterpret_cast<ixpix_t*>(dt.get_ptr())));
  mem_write(&pars.hlapi.d.i.vm_seq.buf.base, localptr_t<ixpix_t>(reinterpret_cast<ixpix_t*>(dt.get_base())));
}

// Source pointer getter
inline uint64_t dma_rt::get_src_ptr() {
  uint64_t src_ptr = 0;

  switch (mem_read(&pars.sel.hw)) {
  case dma_impl_stu:
    {
      src_ptr = reinterpret_cast<uint64_t>(mem_read(&pars.hlapi.s.i.xmi_seq.ptr).get_ptr());
    }
    break;
  case dma_impl_idma:
    {
      src_ptr = reinterpret_cast<uint64_t>(mem_read(&pars.hlapi.d.i.xm_seq.ptr).get_ptr());
    }
    break;
  case dma_impl_odma:
    {
      src_ptr = mem_read(&pars.hlapi.d.i.vm_seq.ptr).get_ptr();
    }
    break;
  default: 
    assert(0 && "unsupported implementation mode");
    break;
  }

  return src_ptr;
}

// Destination pointer getter
inline uint64_t dma_rt::get_dst_ptr() {
  uint64_t dst_ptr = 0;

  switch (mem_read(&pars.sel.hw)) {
  case dma_impl_stu:
    {
      dst_ptr = reinterpret_cast<uint64_t>(mem_read(&pars.hlapi.s.i.xmo_seq.ptr).get_ptr());
    }
    break;
  case dma_impl_idma:
    {
      dst_ptr = mem_read(&pars.hlapi.d.i.vm_seq.ptr).get_ptr();
    }
    break;
  case dma_impl_odma:
    {
      dst_ptr = reinterpret_cast<uint64_t>(mem_read(&pars.hlapi.d.i.xm_seq.ptr).get_ptr());
    }
    break;
  default: 
    assert(0 && "unsupported implementation mode");
    break;
  }

  return dst_ptr;
}

// Update relocated source
inline void dma_rt::update_src(
                               const poffset_t&                               soff
                               ) {
  switch (mem_read(&pars.sel.hw)) {
  case dma_impl_odma:
    // L1 container in VM
    {
      localptr_t<ixpix_t> p(mem_read(&pars.hlapi.d.i.vm_seq.ptr));
      buf_t<ixpix_t>      b(mem_read(&pars.hlapi.d.i.vm_seq.buf));
      p = b.incr_wrap(p, soff);
      mem_write(&pars.hlapi.d.i.vm_seq.ptr, p);
    }
    break;
  case dma_impl_idma:
    // XM pix_t tensor
    {
      globalptr_t<pix_t> p(mem_read(&pars.hlapi.d.i.xm_seq.ptr));
      xm_buf_t<pix_t>    b(mem_read(&pars.hlapi.d.i.xm_seq.buf));
      p = b.incr_wrap(p, soff);
      mem_write(&pars.hlapi.d.i.xm_seq.ptr, p);
    }
    break;
  case dma_impl_stu:
    // XM pix_t tensor
    {
      globalptr_t<pix_t> p(mem_read(&pars.hlapi.s.i.xmi_seq.ptr));
      xm_buf_t<pix_t>    b(mem_read(&pars.hlapi.s.i.xmi_seq.buf));
      p = b.incr_wrap(p, soff);
      mem_write(&pars.hlapi.s.i.xmi_seq.ptr, p);
    }
    break;
  }
}

inline void dma_rt::update_gather_src(
                               const poffset_t&                               soff
                               ) {
  switch (mem_read(&pars.sel.hw)) {
  case dma_impl_idma:
    // XM pix_t tensor
    {
      globalptr_t<pix_t> p(mem_read(&pars.hlapi.d.i.xm_seq.buf.base));
      p += soff;
      mem_write(&pars.hlapi.d.i.xm_seq.ptr, p);
      mem_write(&pars.hlapi.d.i.xm_seq.buf.base, p);
    }
    break;
  default:
    {
      assert(0 && "unsupported implementation mode");
    }
    break;
  }
}

// Update relocated index
inline void dma_rt::update_isrc(
                               const poffset_t&                               soff
                               ) {
  switch (mem_read(&pars.sel.hw)) {
  case dma_impl_idma:
    // L1 container in VM
    {
      localptr_t<ixpix_t> p(mem_read(&pars.hlapi.d.i.xm_seq.p.g.gptr));
      buf_t<ixpix_t>      b(mem_read(&pars.hlapi.d.i.xm_seq.b.g.gbuf));
      p = b.incr_wrap(p, soff);
      mem_write(&pars.hlapi.d.i.xm_seq.p.g.gptr, p);
    }
    break;
  default:
    break;
  }
}

// Update relocated destination
inline void dma_rt::update_dst(
                               const poffset_t&                               doff
                               ) {
  switch (mem_read(&pars.sel.hw)) {
  case dma_impl_idma:
    // L1 container in VM
    {
      localptr_t<ixpix_t> p(mem_read(&pars.hlapi.d.i.vm_seq.ptr));
      buf_t<ixpix_t>      b(mem_read(&pars.hlapi.d.i.vm_seq.buf));
      p = b.incr_wrap(p, doff);
      mem_write(&pars.hlapi.d.i.vm_seq.ptr, p);
    }
    break;
  case dma_impl_odma:
    // XM pix_t tensor
    {
      globalptr_t<pix_t> p(mem_read(&pars.hlapi.d.i.xm_seq.ptr));
      xm_buf_t<pix_t>    b(mem_read(&pars.hlapi.d.i.xm_seq.buf));
      p = b.incr_wrap(p, doff);
      mem_write(&pars.hlapi.d.i.xm_seq.ptr, p);
    }
    break;
  case dma_impl_stu:
    // XM pix_t tensor
    {
      globalptr_t<pix_t> p(mem_read(&pars.hlapi.s.i.xmo_seq.ptr));
      xm_buf_t<pix_t>    b(mem_read(&pars.hlapi.s.i.xmo_seq.buf));
      p = b.incr_wrap(p, doff);
      mem_write(&pars.hlapi.s.i.xmo_seq.ptr, p);
    }
    break;
  }
}

// Offset relocated source & destination pointers
template <bool neg_check_only>
inline void dma_rt::update_src_dst(
                                   const poffset_t&                               xm_off,
                                   const poffset_t&                               vm_off
                               ) {
  globalptr_t<pix_t> p(mem_read(&pars.hlapi.d.i.xm_seq.ptr));
  xm_buf_t<pix_t>    b(mem_read(&pars.hlapi.d.i.xm_seq.buf));
  p = b.incr_wrap<neg_check_only>(p, xm_off);
  mem_write(&pars.hlapi.d.i.xm_seq.ptr, p);

  localptr_t<ixpix_t> p1(mem_read(&pars.hlapi.d.i.vm_seq.ptr));
  buf_t<ixpix_t>      b1(mem_read(&pars.hlapi.d.i.vm_seq.buf));
  p1 = b1.incr_wrap<neg_check_only>(p1, vm_off);
  mem_write(&pars.hlapi.d.i.vm_seq.ptr, p1);
}

    // update for column-wise reordering
inline void dma_rt::update_src_dst(
                                   const dma_params_impl_modif& vmalt,
                                   const dma_params_impl_modif& xmalt
                               ) {
  assert(mem_read(&pars.sel.hw) == dma_impl_odma || mem_read(&pars.sel.hw) == dma_impl_idma);
  
  // VM update
  mem_write(&pars.hlapi.d.i.vm_seq.iter, vmalt.iter);
  for (int i = 0; i < NUM_FM_LOOPS; i++) {
    mem_write(&(pars.hlapi.d.i.vm_seq.offsets[i]), (aoffset_t)vmalt.offsets[i]);
  }
  // XM update
  mem_write(&pars.hlapi.d.i.xm_seq.iter, xmalt.iter);
  mem_write(&pars.hlapi.d.i.xm_seq.offsets, xmalt.offsets);
}

// update for XM and VM tensors
inline void dma_rt::update_src_dst(
                                   const tensor_t<pix_t,5>&      xm_tns,
                                   const tensor_t<pix_t,5>&      vm_tns
                               ) {
  dma_params_impl_modif vmalt;
  dma_params_impl_modif xmalt;
  vmalt.offsets[5] = vm_tns.get_offset_last(0);
  vmalt.offsets[4] = vm_tns.get_offset_last(1);
  vmalt.offsets[3] = vm_tns.get_offset_last(2);
  vmalt.offsets[2] = vm_tns.get_offset_last(3);
  vmalt.offsets[1] = vm_tns.get_offset_last(4);
  vmalt.iter[5]    = vm_tns.get_dim(0);
  vmalt.iter[4]    = vm_tns.get_dim(1);
  vmalt.iter[3]    = vm_tns.get_dim(2);
  vmalt.iter[2]    = vm_tns.get_dim(3);
  vmalt.iter[1]    = vm_tns.get_dim(4);
  vmalt.iter[0]    = 1;
  xmalt.offsets[5] = xm_tns.get_offset_last(0);
  xmalt.offsets[4] = xm_tns.get_offset_last(1);
  xmalt.offsets[3] = xm_tns.get_offset_last(2);
  xmalt.offsets[2] = xm_tns.get_offset_last(3);
  xmalt.offsets[1] = xm_tns.get_offset_last(4);
  xmalt.iter[5]    = xm_tns.get_dim(0);
  xmalt.iter[4]    = xm_tns.get_dim(1);
  xmalt.iter[3]    = xm_tns.get_dim(2);
  xmalt.iter[2]    = xm_tns.get_dim(3);
  xmalt.iter[1]    = xm_tns.get_dim(4);
  xmalt.iter[0]    = 1;
  // VM update
  mem_write(&pars.hlapi.d.i.vm_seq.iter, vmalt.iter);
  for (int i = 0; i < NUM_FM_LOOPS; i++) {
    mem_write(&(pars.hlapi.d.i.vm_seq.offsets[i]), (aoffset_t)vmalt.offsets[i]);
  }
  // XM update
  mem_write(&pars.hlapi.d.i.xm_seq.iter, xmalt.iter);
  mem_write(&pars.hlapi.d.i.xm_seq.offsets, xmalt.offsets);
}

// update for manually constructed BFF XM and VM tensors
inline void dma_rt::update_src_dst(
                                   const tensor_t<pix_t,6>&   xm_tns,
                                   const tensor_t<ixpix_t,6>& vm_tns
                                  ) {
  dma_params_impl_modif vmalt;
  dma_params_impl_modif xmalt;
  vmalt.offsets[NUM_FM_LOOPS-1] = vm_tns.get_offset_last(0);
  vmalt.offsets[NUM_FM_LOOPS-2] = vm_tns.get_offset_last(1);
  vmalt.offsets[NUM_FM_LOOPS-3] = vm_tns.get_offset_last(2);
  vmalt.offsets[NUM_FM_LOOPS-4] = vm_tns.get_offset_last(3);
  vmalt.offsets[NUM_FM_LOOPS-5] = vm_tns.get_offset_last(4);
  vmalt.offsets[NUM_FM_LOOPS-6] = vm_tns.get_offset_last(5);
  vmalt.iter[NUM_FM_LOOPS-1]    = vm_tns.get_dim(0);
  vmalt.iter[NUM_FM_LOOPS-2]    = vm_tns.get_dim(1);
  vmalt.iter[NUM_FM_LOOPS-3]    = vm_tns.get_dim(2);
  vmalt.iter[NUM_FM_LOOPS-4]    = vm_tns.get_dim(3);
  vmalt.iter[NUM_FM_LOOPS-5]    = vm_tns.get_dim(4);
  vmalt.iter[NUM_FM_LOOPS-6]    = vm_tns.get_dim(5);
  xmalt.offsets[NUM_FM_LOOPS-1] = xm_tns.get_offset_last(0);
  xmalt.offsets[NUM_FM_LOOPS-2] = xm_tns.get_offset_last(1);
  xmalt.offsets[NUM_FM_LOOPS-3] = xm_tns.get_offset_last(2);
  xmalt.offsets[NUM_FM_LOOPS-4] = xm_tns.get_offset_last(3);
  xmalt.offsets[NUM_FM_LOOPS-5] = xm_tns.get_offset_last(4);
  xmalt.offsets[NUM_FM_LOOPS-6] = xm_tns.get_offset_last(5);
  xmalt.iter[NUM_FM_LOOPS-1]    = xm_tns.get_dim(0);
  xmalt.iter[NUM_FM_LOOPS-2]    = xm_tns.get_dim(1);
  xmalt.iter[NUM_FM_LOOPS-3]    = xm_tns.get_dim(2);
  xmalt.iter[NUM_FM_LOOPS-4]    = xm_tns.get_dim(3);
  xmalt.iter[NUM_FM_LOOPS-5]    = xm_tns.get_dim(4);
  xmalt.iter[NUM_FM_LOOPS-6]    = xm_tns.get_dim(5);
  // VM update
  mem_write(&pars.hlapi.d.i.vm_seq.iter, vmalt.iter);
  for (int i = 0; i < NUM_FM_LOOPS; i++) {
    mem_write(&(pars.hlapi.d.i.vm_seq.offsets[i]), (aoffset_t)vmalt.offsets[i]);
  }
  // XM update
  mem_write(&pars.hlapi.d.i.xm_seq.iter, xmalt.iter);
  mem_write(&pars.hlapi.d.i.xm_seq.offsets, xmalt.offsets);
}

inline void dma_rt::update_src(
                               const dma_params_impl_modif& alt
                               ) {
  switch (mem_read(&pars.sel.hw)) {
  case dma_impl_odma:
    // L1 container in VM
    {
      mem_write(&pars.hlapi.d.i.vm_seq.iter, alt.iter);
      for (int i = 0; i < NUM_FM_LOOPS; i++) {
        mem_write(&(pars.hlapi.d.i.vm_seq.offsets[i]), (aoffset_t)alt.offsets[i]);
      }
    }
    break;
  case dma_impl_idma:
    // XM pix_t tensor
    mem_write(&pars.hlapi.d.i.xm_seq.iter, alt.iter);
    mem_write(&pars.hlapi.d.i.xm_seq.offsets, alt.offsets);
    break;
  case dma_impl_stu:
    // XM pix_t tensor
    mem_write(&pars.hlapi.s.i.xmi_seq.iter, alt.iter);
    mem_write(&pars.hlapi.s.i.xmi_seq.offsets, alt.offsets);
    break;
  }
}

inline void dma_rt::update_dst(
                               const dma_params_impl_modif& alt
                               ) {
  switch (mem_read(&pars.sel.hw)) {
  case dma_impl_idma:
    // L1 container in VM
    {
      mem_write(&pars.hlapi.d.i.vm_seq.iter, alt.iter);
      for (int i = 0; i < NUM_FM_LOOPS; i++) {
        mem_write(&(pars.hlapi.d.i.vm_seq.offsets[i]), (aoffset_t)alt.offsets[i]);
      }
    }
    break;
  case dma_impl_odma:
    // XM pix_t tensor
    mem_write(&pars.hlapi.d.i.xm_seq.iter, alt.iter);
    mem_write(&pars.hlapi.d.i.xm_seq.offsets, alt.offsets);
    break;
  case dma_impl_stu:
    // XM pix_t tensor
    mem_write(&pars.hlapi.s.i.xmo_seq.iter, alt.iter);
    mem_write(&pars.hlapi.s.i.xmo_seq.offsets, alt.offsets);
    break;
  }
}


// get set an implementation specific register
inline void dma_rt::set_impl_status(
                                     uint16_t rg,                         // select a particular status field
                                     uint32_t val                         // value to be written
                                     ) {
  switch (mem_read(&pars.sel.hw)) {
  case dma_impl_stu:
    switch ((int)rg) {
    case HLAPI_STATUS_SEL_IO_CYCLES:
      mem_write(&pars.hlapi.s.io.cycles, val);
      break;
    case HLAPI_STATUS_SEL_IO_COUNT:
      mem_write(&pars.hlapi.s.io.count, val);
      break;
    case HLAPI_STATUS_SEL_O_STATUS:
      mem_write(&pars.hlapi.s.o.status, val);
      break;
    case HLAPI_STATUS_SEL_O_RES:
      mem_write(&pars.hlapi.s.o.res, val);
      break;
    default: assert(0);
    }
    break;
  default:
    switch ((int)rg) {
    case HLAPI_STATUS_SEL_IO_CYCLES:
      mem_write(&pars.hlapi.d.io.cycles, val);
      break;
    case HLAPI_STATUS_SEL_IO_COUNT:
      mem_write(&pars.hlapi.d.io.count, val);
      break;
    case HLAPI_STATUS_SEL_O_STATUS:
      mem_write(&pars.hlapi.d.o.status, val);
      break;
    case HLAPI_STATUS_SEL_O_RES:
      mem_write(&pars.hlapi.d.o.res, val);
      break;
   default: assert(0);
   }
   break;
  }
}

// Return implementation specific status fields
inline uint32_t dma_rt::get_impl_status(
                                         uint16_t rg                     // select a particular status field
                                    ) {
  uint32_t val;
  switch (mem_read(&pars.sel.hw)) {
  case dma_impl_stu:
    switch ((int)rg) {
    case HLAPI_STATUS_SEL_IO_CYCLES:
      val = mem_read(&pars.hlapi.s.io.cycles);
      break;
    case HLAPI_STATUS_SEL_IO_COUNT:
      val = mem_read(&pars.hlapi.s.io.count);
      break;
    case HLAPI_STATUS_SEL_O_STATUS:
      val = mem_read(&pars.hlapi.s.o.status);
      break;
    case HLAPI_STATUS_SEL_O_RES:
      val = mem_read(&pars.hlapi.s.o.res);
      break;
    default: 
      assert(0); 
      val = 0; 
      break;
    }
    break;
  default:
    switch ((int)rg) {
    case HLAPI_STATUS_SEL_IO_CYCLES:
      val = mem_read(&pars.hlapi.d.io.cycles);
      break;
    case HLAPI_STATUS_SEL_IO_COUNT:
      val = mem_read(&pars.hlapi.d.io.count);
      break;
    case HLAPI_STATUS_SEL_O_STATUS:
      val = mem_read(&pars.hlapi.d.o.status);
      break;
    case HLAPI_STATUS_SEL_O_RES:
      val = mem_read(&pars.hlapi.d.o.res);
      break;
    default: 
      assert(0); 
      val = 0; 
      break;
    }
    break;
  }
  return val;
}

// Optionally prepare for HW execution (prefetch)
inline void dma_rt::prepare() {
  if (mem_read(&pars.sel.hw) == dma_impl_stu) {
    // do STU transaction
    assert(mem_read(&mmio.s) != nullptr); // else RT params not initialized
    mem_write(&pars.hlapi.s.i.common.next, globalptr_t<hlapi_i_t>(nullptr));
    mmio_write(&mem_read(&mmio.s)->prefetch, globalptr_t<stu_hlapi_t>(fast2global_dccm(&pars.hlapi.s)));
  } else {
    // do iDMA or oDMA transaction
    assert(mem_read(&mmio.d) != nullptr); // else RT params not initialized
    mem_write(&pars.hlapi.d.i.common.next, globalptr_t<hlapi_i_t>(nullptr));
    mmio_write(&mem_read(&mmio.d)->prefetch, globalptr_t<dma_hlapi_t>(fast2slice_dccm(&pars.hlapi.d)));
  }
}


inline void dma_rt::execute() {
  //hlapi_report(cout, hlapi);
  if (mem_read(&pars.sel.hw) == dma_impl_stu) {
    // do STU transaction
    assert(mem_read(&mmio.s) != nullptr); // else RT params not initialized
    mem_write(&pars.hlapi.s.i.common.next, globalptr_t<hlapi_i_t>(nullptr));
    mmio_write(&mem_read(&mmio.s)->single, globalptr_t<stu_hlapi_t>(fast2global_dccm(&pars.hlapi.s)));
  } else {
    // do iDMA or oDMA transaction
    assert(mem_read(&mmio.d) != nullptr); // else RT params not initialized
    mem_write(&pars.hlapi.d.i.common.next, globalptr_t<hlapi_i_t>(nullptr));
    mmio_write(&mem_read(&mmio.d)->single, globalptr_t<dma_hlapi_t>(fast2slice_dccm(&pars.hlapi.d)));
  }
}


//
// functions to create and issue lists of descriptors
//
// constructor
inline dma_rt_list::dma_rt_list() {
  ini = false;
}
// append an element
inline void dma_rt_list::append(dma_rt* rt) {
  if (!ini) {
    // list is still empty
    tps = mem_read(&(rt->pars.sel.hw)) == dma_impl_stu;
    if (tps) {
      head.s = &(rt->pars.hlapi.s);
      tail.s = &(rt->pars.hlapi.s);
      mmio.s = mem_read(&rt->mmio.s);
    } else {
      head.d = &(rt->pars.hlapi.d);
      tail.d = &(rt->pars.hlapi.d);
      mmio.d = mem_read(&rt->mmio.d);
    }
    ini = true;
  } else {
    // append to tail of existing list
    if (tps) {
      mem_write(&tail.s->i.common.next, globalptr_t<hlapi_i_t>(fast2global_dccm(&rt->pars.hlapi.s.i.common)));
      tail.s = &(rt->pars.hlapi.s);
    } else {
      mem_write(&tail.d->i.common.next, globalptr_t<hlapi_i_t>(fast2slice_dccm(&rt->pars.hlapi.d.i.common)));
      tail.d = &(rt->pars.hlapi.d);
    }
  }
}
// prefetch the head of the list
inline void dma_rt_list::prepare() {
  assert(ini && "empty list");
  if (tps) {
    mmio_write(&mmio.s->prefetch, globalptr_t<stu_hlapi_t>(fast2global_dccm(head.s)));
  } else {
    mmio_write(&mmio.d->prefetch, globalptr_t<dma_hlapi_t>(fast2slice_dccm(head.d)));
  }
}
// issue the list
inline void dma_rt_list::execute() {
  assert(ini && "empty list");
  if (tps) {
    mmio_write(&mmio.s->concat_head, globalptr_t<stu_hlapi_t>(fast2global_dccm(head.s)));
    mmio_write(&mmio.s->concat_tail, globalptr_t<stu_hlapi_t>(fast2global_dccm(tail.s)));
    mmio_write(&mmio.s->issue, (uint32_t)2);
  } else {
    mmio_write(&mmio.d->concat_head, globalptr_t<dma_hlapi_t>(fast2slice_dccm(head.d)));
    mmio_write(&mmio.d->concat_tail, globalptr_t<dma_hlapi_t>(fast2slice_dccm(tail.d)));
    mmio_write(&mmio.d->issue, (uint32_t)2);
  }
}

inline dma_rt* create(mem_alloc_t& al, dma_params_impl_main& p) {
  dma_rt c(p);
  dma_rt* cpy;
  al.alloc(cpy);
  mem_write(cpy, c);
  return cpy;
}
}  // namespace tensor::v200
#undef LDBGV
#endif
