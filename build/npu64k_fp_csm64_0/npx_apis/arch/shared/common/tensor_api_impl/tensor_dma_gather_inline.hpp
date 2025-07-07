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
 * tensor_dma_gather_inline.hpp
 *
 * File defining tensor DMA inline operations
 *
 */

#ifndef TENSOR_DMA_GATHER_INLINE_INCLUDED
#define TENSOR_DMA_GATHER_INLINE_INCLUDED

#include <type_traits>

//#define TENSOR_DMA_NINLINE_HPP_DEBUG
#ifdef TENSOR_DMA_NINLINE_HPP_DEBUG
  #define LDBGV(...) DBGV(__VA_ARGS__)
#else
  #define LDBGV(...)
#endif

//
// DMA parameter inline functions
//
namespace tensor::v200 {
template<template<typename> class B>
inline tensor::v200::dma_gather_params<B>::dma_gather_params(
                    const shape<3>& inneri,    // shape of inner tensor [C2][C1][C0]
                    const shape<2>& ishpi,     // shape of the outer dictionary tensor [H][W]
                    const shape<2>& oshpi      // shape of the outer index and output tensor [Y][X]
                                      ) {
  int co = RDIV_UP(inneri[0], ISIZE);  // number of channels multiple of ISIZE
  int wo = RDIV_UP(oshpi[0], ISIZE/2); // each index requires 16b
  shapes.idxshape  = {2/*h&w*/,1,(aoffset_t)wo,oshpi[1],1};
  shapes.dictshape = {inneri[0],inneri[1],inneri[2],ishpi[0],ishpi[1]};
  shapes.oshape    = {(aoffset_t)co,inneri[1],inneri[2],(aoffset_t)(wo*ISIZE/2),oshpi[1]};
}

template<template<typename> class B>
inline void dma_gather_params<B>::set_impl_params(
                            const dma_params_impl_spec& p // structure with implementation specific parameters
                            ) {
  sel = p;
}

template<template<typename> class B>
inline void dma_gather_params<B>::get_impl_params(
                            dma_params_impl_spec&       p // return structure with implementation specific parameters
                            ) {
  p = sel;
}


template<template<typename> class B>
inline void dma_gather_params<B>::get_shapes(
                                      dma_params_impl_shapes& s  // NOLINT [runtime/references]
                                      ) {
  s = shapes;
}

template <template <typename> class B>
void dma_gather_params<B>::set_src(const tensor_t<pix_t,5,B>& p) {
  dict_tns = p;
}

// input1 is the index tensor, shape [Y][X][2]
template <template <typename> class B>
void dma_gather_params<B>::set_src(const impl_spec_container_t<B> &p) {
  idx_con = p;
}

// output is the result, shape [Y][X][C2][C1][C0]
template <template <typename> class B>
void dma_gather_params<B>::set_dst(const impl_spec_container_t<B> &p) {
  dst_con = p;
}

// get run-time parameters
template <template <typename> class B>
void dma_gather_params<B>::get_rt_params(dma_params_impl_main& p) {
  // general parameters
  p.sel                       = sel;
  p.sel.hw                    = dma_impl_idma;
  p.hlapi.d.i.attrb           = 0;
  p.hlapi.d.i.attrb           = NPU_IDMA_ATTR_MASK_GATHER;
  p.hlapi.d.i.xm_seq.compress = sel.bf;
  p.hlapi.d.i.xm_seq.cblen    = 0;
  p.hlapi.d.i.zero_point      = 0;
  p.hlapi.d.i.bc              = 0;
  p.hlapi.d.i.planar_stride   = 0;
  p.hlapi.d.i.planar_offset   = 0;
  p.hlapi.d.i.vm_wmsk         = 0;
  // index VM sequence
  tensor_t<ixpix_t,5,B> stns(idx_con.data);
  p.hlapi.d.i.xm_seq.p.g.gptr                    = stns.get_ptr();
  p.hlapi.d.i.xm_seq.b.g.gbuf                    = buf_t<ixpix_t>(stns.get_base(), stns.get_size());
  p.hlapi.d.i.xm_seq.o.g.goffsets[2]             = stns.get_offset_last(0);
  p.hlapi.d.i.xm_seq.o.g.goffsets[1]             = stns.get_offset_last(2);
  p.hlapi.d.i.xm_seq.o.g.goffsets[0]             = stns.get_offset_last(3);
  // dictionany XM sequence
  p.hlapi.d.i.xm_seq.ptr                         = dict_tns.get_base();
  p.hlapi.d.i.xm_seq.buf                         = xm_buf_t<pix_t>(dict_tns.get_base(), dict_tns.get_size());
  for (int i = 0; i < 3; i++) {
    p.hlapi.d.i.xm_seq.offsets[NUM_FM_LOOPS-1-i] = dict_tns.get_offset_last(i);
    p.hlapi.d.i.xm_seq.iter[NUM_FM_LOOPS-1-i]    = dict_tns.get_dim(i);
  }
  // outer offsets
  p.hlapi.d.i.xm_seq.offsets[1]                  = dict_tns.get_offset(3);
  p.hlapi.d.i.xm_seq.offsets[0]                  = dict_tns.get_offset(4);
  // force iterators > 3 to 1
  for (int i = 3; i < NUM_FM_LOOPS; i++) {
    p.hlapi.d.i.xm_seq.iter[NUM_FM_LOOPS-1-i]    = 1;
  }
  // index size as outer XM
  p.hlapi.d.i.xm_seq.iter[1]                     = stns.get_dim(2);
  p.hlapi.d.i.xm_seq.iter[0]                     = stns.get_dim(3);
  // destination VM sequence
  tensor_t<ixpix_t,5,B> dtns(dst_con.data);
  p.hlapi.d.i.vm_seq.ptr      = dtns.get_ptr();
  p.hlapi.d.i.vm_seq.buf      = buf_t<ixpix_t>(dtns.get_base(), dtns.get_size());
  p.hlapi.d.i.vm_seq.stride   = 1;
  p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-1] = dtns.get_offset_last(0);
  p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-2] = dtns.get_offset_last(1);
  p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-3] = dtns.get_offset_last(2);
  p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-4] = dtns.get_offset_last(3);
  p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-5] = dtns.get_offset_last(4);
  p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-1]    = dtns.get_dim(0);
  p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-2]    = dtns.get_dim(1);
  p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-3]    = dtns.get_dim(2);
  p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-4]    = dtns.get_dim(3);
  p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-5]    = dtns.get_dim(4);
  p.hlapi.d.i.vm_seq.stride   = 1;
  for (int i = 0; i < NUM_FM_LOOPS-5; i++) {
    p.hlapi.d.i.vm_seq.iter[i]    = 1;
  }
  
  #ifdef TENSOR_DMA_NINLINE_HPP_DEBUG
    cout << "hlapi.d.i.planar_stride = " << p.hlapi.d.i.planar_stride << endl;
    cout << "hlapi.d.i.planar_offset = " << p.hlapi.d.i.planar_offset << endl;
    cout << "hlapi.d.i.vm_wmsk= " << p.hlapi.d.i.vm_wmsk << endl;
    cout << "hlapi.d.i.vm_seq.ptr = " << p.hlapi.d.i.vm_seq.ptr.get_raw() << endl;
    cout << "hlapi.d.i.vm_seq.buf.base = " << p.hlapi.d.i.vm_seq.buf.base << endl;
    cout << "hlapi.d.i.vm_seq.buf.len = " << p.hlapi.d.i.vm_seq.buf.len << endl;
    cout << "hlapi.d.i.vm_seq.offsets["<<NUM_FM_LOOPS-1<<"] = " << p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-1] << endl;
    cout << "hlapi.d.i.vm_seq.offsets["<<NUM_FM_LOOPS-2<<"] = " << p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-2] << endl; 
    cout << "hlapi.d.i.vm_seq.offsets["<<NUM_FM_LOOPS-3<<"] = " << p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-3] << endl;
    cout << "hlapi.d.i.vm_seq.offsets["<<NUM_FM_LOOPS-4<<"] = " << p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-4] << endl;
    cout << "hlapi.d.i.vm_seq.offsets["<<NUM_FM_LOOPS-5<<"] = " << p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-5] << endl;
    cout << "hlapi.d.i.vm_seq.offsets["<<NUM_FM_LOOPS-6<<"] = " << p.hlapi.d.i.vm_seq.offsets[NUM_FM_LOOPS-6] << endl;
    cout << "hlapi.d.i.vm_seq.iter["<<NUM_FM_LOOPS-1<<"]    = " << p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-1] << endl;
    cout << "hlapi.d.i.vm_seq.iter["<<NUM_FM_LOOPS-2<<"]    = " << p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-2] << endl;
    cout << "hlapi.d.i.vm_seq.iter["<<NUM_FM_LOOPS-3<<"]    = " << p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-3] << endl;
    cout << "hlapi.d.i.vm_seq.iter["<<NUM_FM_LOOPS-4<<"]    = " << p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-4] << endl;
    cout << "hlapi.d.i.vm_seq.iter["<<NUM_FM_LOOPS-5<<"]    = " << p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-5] << endl;
    cout << "hlapi.d.i.vm_seq.iter["<<NUM_FM_LOOPS-6<<"]    = " << p.hlapi.d.i.vm_seq.iter[NUM_FM_LOOPS-6] << endl;
    cout << "hlapi.d.i.vm_seq.stride   = " << p.hlapi.d.i.vm_seq.stride << endl;
    cout << "hlapi.d.i.xm_seq.compress = " << p.hlapi.d.i.xm_seq.compress << endl; 
    cout << "hlapi.d.i.xm_seq.cblen = " << p.hlapi.d.i.xm_seq.cblen << endl; 
    cout << "hlapi.d.i.xm_seq.ptr      = " << p.hlapi.d.i.xm_seq.ptr << endl;
    cout << "hlapi.d.i.xm_seq.buf.base      = " << p.hlapi.d.i.xm_seq.buf.base << endl;
    cout << "hlapi.d.i.xm_seq.buf.len      = " << p.hlapi.d.i.xm_seq.buf.len << endl;
    cout << "gather/compress attr:" << endl;
    cout << "hlapi.d.i.xm_seq.p.g.gptr      = " << p.hlapi.d.i.xm_seq.p.g.gptr << endl;
    cout << "hlapi.d.i.xm_seq.b.g.gbuf.base      = " << p.hlapi.d.i.xm_seq.b.g.gbuf.base << endl;
    cout << "hlapi.d.i.xm_seq.b.g.gbuf.len       = " << p.hlapi.d.i.xm_seq.b.g.gbuf.len  << endl;
    cout << "hlapi.d.i.xm_seq.o.g.goffsets[2]     = " << p.hlapi.d.i.xm_seq.o.g.goffsets[2]  << endl;
    cout << "hlapi.d.i.xm_seq.o.g.goffsets[1]     = " << p.hlapi.d.i.xm_seq.o.g.goffsets[1]  << endl;
    cout << "hlapi.d.i.xm_seq.o.g.goffsets[0]     = " << p.hlapi.d.i.xm_seq.o.g.goffsets[0]  << endl;
    cout << "hlapi.d.i.xm_seq.offsets["<<NUM_FM_LOOPS-1<<"] = " << p.hlapi.d.i.xm_seq.offsets[NUM_FM_LOOPS-1] << endl;
    cout << "hlapi.d.i.xm_seq.offsets["<<NUM_FM_LOOPS-2<<"] = " << p.hlapi.d.i.xm_seq.offsets[NUM_FM_LOOPS-2] << endl;
    cout << "hlapi.d.i.xm_seq.offsets["<<NUM_FM_LOOPS-3<<"] = " << p.hlapi.d.i.xm_seq.offsets[NUM_FM_LOOPS-3] << endl;
    cout << "hlapi.d.i.xm_seq.offsets["<<NUM_FM_LOOPS-4<<"] = " << p.hlapi.d.i.xm_seq.offsets[NUM_FM_LOOPS-4] << endl;
    cout << "hlapi.d.i.xm_seq.offsets["<<NUM_FM_LOOPS-5<<"] = " << p.hlapi.d.i.xm_seq.offsets[NUM_FM_LOOPS-5] << endl;
    cout << "hlapi.d.i.xm_seq.offsets["<<NUM_FM_LOOPS-6<<"] = " << p.hlapi.d.i.xm_seq.offsets[NUM_FM_LOOPS-5] << endl;
    cout << "hlapi.d.i.xm_seq.iter["<<NUM_FM_LOOPS-1<<"] = " << p.hlapi.d.i.xm_seq.iter[NUM_FM_LOOPS-1] << endl;
    cout << "hlapi.d.i.xm_seq.iter["<<NUM_FM_LOOPS-2<<"] = " << p.hlapi.d.i.xm_seq.iter[NUM_FM_LOOPS-2] << endl;
    cout << "hlapi.d.i.xm_seq.iter["<<NUM_FM_LOOPS-3<<"] = " << p.hlapi.d.i.xm_seq.iter[NUM_FM_LOOPS-3] << endl;
    cout << "hlapi.d.i.xm_seq.iter["<<NUM_FM_LOOPS-4<<"] = " << p.hlapi.d.i.xm_seq.iter[NUM_FM_LOOPS-4] << endl;
    cout << "hlapi.d.i.xm_seq.iter["<<NUM_FM_LOOPS-5<<"] = " << p.hlapi.d.i.xm_seq.iter[NUM_FM_LOOPS-5] << endl;
    cout << "hlapi.d.i.xm_seq.iter["<<NUM_FM_LOOPS-6<<"] = " << p.hlapi.d.i.xm_seq.iter[NUM_FM_LOOPS-6] << endl;
  #endif
}
}
#undef LDBGV
#endif
