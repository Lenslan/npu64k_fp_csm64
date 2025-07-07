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
 * tensor_mem_alloc.hpp
 *
 * File defining a simple memory allocator for testbench purposes
 *
 */
#ifndef TENSOR_MEM_ALLOC_INCLUDED
#define TENSOR_MEM_ALLOC_INCLUDED

namespace tensor::v200 {
  // create one allocator per memory
  class mem_alloc_t {
  public:
    inline mem_alloc_t() = default;
    inline mem_alloc_t(const mem_alloc_t&) = default;
    inline mem_alloc_t(uint64_t bs, size_t sz, uint16_t al = 16) {
      base_addr = bs;
      aperture = sz;
      sp = 0;
      alignment = al;
    }
    // allocate a scalar type in the memory
    template<typename T> inline void alloc(T*& p) {
      p   = reinterpret_cast<T*>(base_addr+sp);
      sp += alignment*((sizeof(T)+alignment-1)/alignment);
      assert (sp <= aperture);
    }
    // allocate an array type in the memory
    template<typename T> inline void alloc(T*& p, size_t n) {
      p   = reinterpret_cast<T*>(base_addr+sp);
      sp += alignment*((n*sizeof(T)+alignment-1)/alignment);
      assert (sp <= aperture);
    }

    // allocate an array elements in the defaut/modelled memory
    template<typename T, template<typename> class B=buffer_t> inline void alloc(B<T>& p, size_t n) {
      T* ptr = reinterpret_cast<T*>(base_addr+sp);
      sp += alignment*((n*sizeof(T)+alignment-1)/alignment);
      assert (sp <= aperture);
      p = B<T>(ptr, n);
    }

    // increase running pointer until it aligns to given boundary in bytes
    inline void align(uint16_t b) {
        assert (b % alignment == 0);
        sp = b*((sp+b-1)/b);
        assert (sp <= aperture);
    }

    // deallocate (rewind running pointer)
    template<typename T> inline void dealloc(T* b) {
        uint64_t ptr = reinterpret_cast<uint64_t>(b);
        assert (ptr >= base_addr);
        assert (ptr-base_addr < sp);
        sp = alignment*((ptr-base_addr+alignment-1)/alignment);
    }

  private:
    uint64_t       base_addr; // memory base address
    size_t         aperture;  // memory aperture size
    uint64_t       sp;        // running pointer
    uint16_t       alignment; // memory allocation aligment
  };
}
#endif
