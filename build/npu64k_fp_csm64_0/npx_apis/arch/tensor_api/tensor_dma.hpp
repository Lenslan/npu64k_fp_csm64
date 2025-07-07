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
 * tensor_dma.hpp
 *
 * File defining tensor DMA operations
 *
 */

#ifndef TENSOR_DMA_INCLUDED
#define TENSOR_DMA_INCLUDED


// include interface datatypes
#include "tensor.hpp"


///////////////////////////////////////////////////////////////////////////////////////////////
//
// Include implementation specific data structures
//
///////////////////////////////////////////////////////////////////////////////////////////////
#include "tensor_dma_types.hpp"

//
// All identifiers related to the tensor API go into namespace tensor::v200
//
namespace tensor::v200 {
  ///////////////////////////////////////////////////////////////////////////////////////////////
  //
  // DMA parameter class
  //
  // This class is used by the AOT/JIT compiler to define the implementation specific parameters for a 
  // data copy operation. The parameter class is used in the construction of the accompanying run-time object.
  // 
  // The parameter object can be reused across multiple tiles of the same layer.
  //
  ///////////////////////////////////////////////////////////////////////////////////////////////
  template<template<typename> class B=buffer_t>
  class dma_params {
  public:
    //
    // Constructors
    //
    dma_params();
    dma_params(const dma_params&) = default;

    //
    // Set implementation specific parameters, optional else use default
    //
    void set_impl_params(
                         const dma_params_impl_spec& p // structure with implementation specific parameters
                         );
    void get_impl_params(
                         dma_params_impl_spec&       p // return structure with implementation specific parameters
                         );    

    //
    // Set source tensor
    //
    // XM non column-wise reordered
    void set_src(
                 const tensor_t<pix_t,4,B>&          stns
                 );

    void set_src(
                 const tensor_t<pix_t,5,B>&          stns
                 );             
    // XM/VM BFF pre-updated
    void set_src(
                 const tensor_t<pix_t,6,B>&          stns
                 );
    // XM column-wise reordered
    void set_src(
                 const tensor_t<pix_t,8,B>&          stns
                 );
    // VM
    void set_src(
                 const impl_spec_container_t<B>&     scon
                 );

    //
    // Set destination tensor
    //
    // XM non column-wise reordered
    void set_dst(
                 const tensor_t<pix_t,4,B>&          dtns
                 );

    void set_dst(
                 const tensor_t<pix_t,5,B>&          dtns
                 );
    // XM/VM BFF pre-updated
    void set_dst(
                 const tensor_t<pix_t,6,B>&          dtns
                 );
    // XM column-wise reordered
    void set_dst(
                 const tensor_t<pix_t,8,B>&          dtns
                 );
    // VM
    void set_dst(
                 const impl_spec_container_t<B>&     dcon
                 );

    // VM padding value (zero-point)
    void set_pad_val(
                     pix_t    v
                 );

    // set per channel write mask
    void set_channel_mask(
                          const uint16_t                  vm_wmsk  // channel mask inverted
                          );
    // depricated
    void set_channel_mask(
                          const uint16_t                  vm_wmsk, // channel mask inverted
                          dma_params_impl_main&           p        // HLAPI structs
                         );

    // set BDMA flags
    void set_bdma(
                  dma_bc_t                        bflags   // B-DMA flags
                  );
    // depricated
    void set_bdma(
                  dma_bc_t                        bflags,  // B-DMA flags
                  dma_params_impl_main&           p        // HLAPI structs
                 );

    // Create a modifier to set alternative source and destination shapes
    //
    // XM non column-wise reordered
    void modif_src(
                   const tensor_t<pix_t,4,B>&      stns,
                   dma_params_impl_modif&          alt        // encoded alternative shape
                   );
    // XM column-wise reordered
    void modif_src_dst(
                       const tensor_t<pix_t,8,B>&      tns,       // CWR tensor in XM
                       const impl_spec_container_t<B>& vcon,      // tensor in VM
                       dma_params_impl_modif&          vmalt,     // encoded alternative VM shape
                       dma_params_impl_modif&          xmalt      // encoded alternative XM shape
                       );
    void modif_src(
                   const tensor_t<pix_t,8,B>&      stns,
                   dma_params_impl_modif&          alt        // encoded alternative shape
                   );
    // VM
    void modif_src(
                   const impl_spec_container_t<B>& scon,
                   dma_params_impl_modif&          alt        // encoded alternative shape
                   );
    // XM non column-wise reordered
    void modif_dst(
                   const tensor_t<pix_t,4,B>&      dtns,
                   dma_params_impl_modif&          alt        // encoded alternative shape
                   );
    // VM
    void modif_dst(
                   const impl_spec_container_t<B>& dcon,
                   dma_params_impl_modif&          alt        // encoded alternative shape
                   );

    //
    // Return an opaque structure with run-time parameters
    //
    void get_rt_params(dma_params_impl_main&);
    
  private:
#include "tensor_dma_param_priv.hpp"    
  };


  ///////////////////////////////////////////////////////////////////////////////////////////////
  //
  // DMA run-time class
  //
  ///////////////////////////////////////////////////////////////////////////////////////////////
  class dma_rt {
  public:
    //
    // Constructor
    //
    dma_rt(
           dma_params_impl_main&                  p     // convolution parameter class object
           );
    
    //
    // Set implementation specific run-time attributes
    //
    void set_impl_params(
                         const dma_rt_impl_spec&  p    // structure with run-time specific parameters
                         );
    void get_impl_params(
                         dma_rt_impl_spec&        p    // return structure with run-time specific parameters
                         );

    // set per channel write mask
    void set_channel_mask(
                          const uint16_t                  vm_wmsk  // channel mask inverted
                         );
    // set BDMA flags
    void set_bdma(
                  dma_bc_t                        bflags  // B-DMA flags
                 );

    //
    // Set relocated source
    //
    template <size_t R>
    void set_src(
                 const tensor_t<pix_t,R>&         stns
                 );
    // XM
    void set_src(
                 const buffer_t<pix_t>&         sbuf
                 );
    // XM ptr
    void set_xm_ptr(
                    globalptr_t<pix_t>          ptr
                    );
    // VM
    void set_src(
                 const impl_spec_container_t<buffer_t>&     scon
                 );
    // VM
    void set_src(
                 const buffer_t<ixpix_t>&           sbuf
                 );
    
    // Gather index in VM
    void set_isrc(
                 const impl_spec_container_t<buffer_t>&     scon
                 );

    //
    // Set relocated destination
    //
    template <size_t R>
    void set_dst(
                 const tensor_t<pix_t,R>&         dtns
                 );
    // XM
    void set_dst(
                 const buffer_t<pix_t>&         dbuf
                 );
    // VM
    void set_dst(
                 const impl_spec_container_t<buffer_t>&           dcon
                 );
    // VM
    void set_dst(
                 const buffer_t<ixpix_t>&           dbuf
                 );                     

    //
    // Offset relocated source pointer only
    //
    void update_src(
                    const poffset_t&              soff
                    );

    //
    // Offset relocated source pointer for gather only
    //
    void update_gather_src(
                    const poffset_t&              soff
                    );

    //
    // Offset relocated index pointer only
    //
    void update_isrc(
                    const poffset_t&              soff
                    );

    //
    // Offset relocated destination pointer only
    //
    void update_dst(
                    const poffset_t&              doff
                    );
    //
    // Offset relocated source & destination pointers
    //
    template <bool neg_check_only = false>
    void update_src_dst(
                        const poffset_t&                               xm_off,
                        const poffset_t&                               vm_off
                    );
    
    //
    // Apply a shape modifier
    //
    void update_src(
                    const dma_params_impl_modif& alt        // encoded alternative shape
                    );
    void update_dst(
                    const dma_params_impl_modif& alt        // encoded alternative shape
                    );
    // update for column-wise reordering
    void update_src_dst(
                        const dma_params_impl_modif& vmalt,     // encoded alternative VM shape
                        const dma_params_impl_modif& xmalt      // encoded alternative XM shape
                    );
    // update for XM and VM tensors
    void update_src_dst(
                        const tensor_t<pix_t,5>&      xm_tns,
                        const tensor_t<pix_t,5>&      vm_tns
                    );
    // update for manually constructed BFF XM and VM tensors
    void update_src_dst(
                        const tensor_t<pix_t,6>&      xm_tns,
                        const tensor_t<ixpix_t,6>&    vm_tns
                    );

    //
    // Optionally prepare for HW execution (prefetch)
    //
    void prepare();

    //
    // Start execution of HLAPI
    //
    void execute();

    //
    // Set implementation specific status field
    //
    void set_impl_status(
                         uint16_t sel,                        // select a particular status field
                         uint32_t val                         // value to be written
                         );
    
    //
    // Return implementation specific status fields
    //
    uint32_t get_impl_status(
                             uint16_t sel                     // select a particular status field
                             );
    
    //
    // Return source pointer
    //
    uint64_t get_src_ptr();

    //
    // Return destination pointer
    //
    uint64_t get_dst_ptr();

  private:
    // include implementation specific private members
#include "tensor_dma_rt_priv.hpp"
  };

  // list object for DMA objects
  class dma_rt_list {
  public:
    // constructor
    dma_rt_list();
    // prefetch the head of the list
    void prepare();
    // append a descriptor to the end of the list
    void append(dma_rt* p);
    // execute the list of descriptors
    void execute();
  private:
    // include implementation specific private members
#include "tensor_dma_rt_list_priv.hpp"
  };

  //
  // Create a run-time object in a target memory
  //
  dma_rt* create(mem_alloc_t& al, dma_params_impl_main& p);

}
  // include implementation specific inline functions
#include "tensor_dma_inline.hpp"
#endif
