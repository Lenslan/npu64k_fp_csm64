/*
 * Copyright (C) 2021-2023 Synopsys, Inc. All rights reserved.
 *
 * SYNOPSYS CONFIDENTIAL - This is an unpublished, confidential, and
 * proprietary work of Synopsys, Inc., and may be subject to patent,
 * copyright, trade secret, and other legal or contractual protection.
 * This work may be used only pursuant to the terms and conditions of a
 * written license agreement with Synopsys, Inc. All other use, reproduction,
 * distribution, or disclosure of this work is strictly prohibited.
 *
 * The entire notice above must be reproduced on all authorized copies.
 */

`ifndef NPU_TYPES_INCLUDED
`define NPU_TYPES_INCLUDED

`include "npu_defines.v"

package npu_types;
  //
  // Main parameters
  //
  localparam int ISIZE = (`NPU_SLICE_MAC == 4096) ? 16 : 16; // channel vectorization
  localparam int VSIZE = (`NPU_SLICE_MAC == 4096) ? 8 : 2;   // spatial vectorization
  localparam int NUM_COEF_QUEUE = 8;  // the number of queue between VM and COEF 
  localparam int NUM_FM_QUEUE = (VSIZE == 2) ? 8 : 16;      // the number of queue between VM and COEF 
  localparam int ASIZE = 40;          // XM address vector width
  localparam int DMA_VM_LANES = (VSIZE == 2) ? 1 : 4;    // DMA VM lanes
  localparam int CONV_PAD_LD_LANES = 1; // convolution hardware padding load lanes
  localparam int GTOA_BPAR_LD_LANES = 1; // GTOA b parameter load lanes
  localparam int GTOA_MPST_LANES = 2; // GTOA mp stash lanes
  localparam int NUM_FM_LOOPS = 6;
  localparam int VSIZE_LOG2 = $clog2(VSIZE); //log2 of VSIZE

  //
  // AXI user signal widths
  //
  localparam int SLICE_MMIO_AWUW = 1;
  localparam int SLICE_MMIO_WUW  = 1;
  localparam int SLICE_MMIO_BUW  = 1;
  localparam int SLICE_MMIO_ARUW = 1;
  localparam int SLICE_MMIO_RUW  = 1;
  localparam int SLICE_DMA_AWUW  = 72; //Use as Stream ID and SubStream ID
  localparam int SLICE_DMA_WUW   = 1;
  localparam int SLICE_DMA_BUW   = 1;
  localparam int SLICE_DMA_ARUW  = 72; //Use as Stream ID and SubStream ID
  localparam int SLICE_DMA_RUW   = 1;

  
  //
  // Basic data types
  //
  localparam int PIX_W    = 8;       // activation data width
  localparam int COEF_W   = 8;       // coefficient data width
  localparam int ACC_W    = 32;      // accumulator width
  localparam int OFFSET_W = 16;      // offset and iterator width
  localparam int XM_OFFSET_W = 32;      // xm offset and iterator width
  typedef logic signed [PIX_W-1:0 ]           pix_t;    // activation data type
  typedef logic signed [COEF_W-1:0]           coef_t;   // coefficient data type
  typedef logic signed [ACC_W-1:0]            acc_t;    // accumulator data type
  typedef logic signed [OFFSET_W-1:0]         offset_t; // offset and iterator data type
  typedef logic signed [XM_OFFSET_W-1:0]      xm_offset_t; // xm offset and iterator data type
  //
  // Basic vector datatypes
  //
  typedef pix_t        [ISIZE-1:0]            ixpix_t;   // vector of activations in channel dimension
  typedef acc_t        [ISIZE-1:0]            ixacc_t;   // vector of accumulator in channel dimension
  typedef logic        [ISIZE-1:0]            ixbit_t;   // vector of strobes in channel dimension
  typedef ixpix_t      [VSIZE-1:0]            vyixpix_t; // vector of vector of channel activations in spatial dimension
  typedef ixacc_t      [VSIZE-1:0]            vyixacc_t; // vector of vector of channel accumulators in spatial dimension
  typedef ixbit_t      [VSIZE-1:0]            ixambit_t; // vector of strobes of channel activations in spatial dimension
  typedef logic        [15:0]                 gidx_t;    // 2D gather type
  // DMA broadcast type
  typedef logic        [31:0]                  dma_bc_t;  // DMA broadcast flag 

  //
  // Cyclic buffers
  //
  typedef logic [15:0]        vm_addr_t;        // VM address, total 16B *64K addresses = 1MB
  // cyclic buffer in VM
  typedef offset_t            vm_len_t;
  typedef offset_t            vm_inc_t;
  typedef struct packed {
    vm_len_t  len;
    vm_addr_t base;
  } buf_t;
  // cyclic buffer in XM, max length is 4GB
  typedef logic        [ASIZE-1:0] xm_ptr_t;    
  typedef logic        [31:0]      xm_len_t;
  typedef logic signed [31:0]      xm_inc_t;
  typedef struct packed {
    xm_len_t                        len;
    logic [63:ASIZE]                padm;
    xm_ptr_t                        base;
  } xm_buf_t;
// spyglass disable_block WRN_1024
// SMD: signed argument 'i' passed to $signed system function call
// SJ: Intended used 
  // functions for incrementing cyclic buffer
  function automatic vm_addr_t incr_vm(input vm_addr_t p, input vm_inc_t i, input buf_t b);
    logic [16:0] r;  // result
    logic [16:0] e;  // last position in buffer
    logic        os; // true if result is outside buffer
    // determine last position in buffer
    e = {1'b0,b.base} + {1'b0,b.len};
    // increment with sign extended offset
    r = {1'b0,p} + {i[15],i};
    // check for over/underflow
    os = r < {1'b0,b.base} || (r >= e);
    if (os) begin
      // outside of buffer, wrapping required
      if (i >= signed'(0)) 
      begin
        // overflow
        r -= {1'b0,b.len};
      end
      else 
      begin
        // underflow
// spyglass disable_block W164a
//SMD:Width mismatch
//SJ :Intentionally and ignore
        r += {1'b0,b.len};
// spyglass enable_block W164a
      end
    end
    return r[15:0];
  endfunction : incr_vm
  // functions for incrementing cyclic buffer
  function automatic xm_ptr_t incr_xm(input xm_ptr_t p, input xm_inc_t i, input xm_buf_t b);
    logic    [ASIZE:0]   r;  // result
    logic    [ASIZE-1:0] rw; // overflow/underflow result
    logic    [ASIZE:0]   e;  // last position in buffer
    logic                os; // true if result is outside buffer
    logic    [ASIZE:0]   ii; // i sign extended to ASIZE+1 bits
    ii = signed'(i);
    // determine first element after end of buffer
    e = {1'b0,b.base} + {1'b0,b.len};
    // increment
// spyglass disable_block W164a
//SMD:Width mismatch
//SJ :No overflow and ignore
    r  = {1'b0,p} + ii;
    // check for over/underflow
    os = (r < {1'b0,b.base}) || (r >= e);
    // precompute wrapping result
    rw = p + ii[ASIZE-1:0] + ({ASIZE{~i[31]}}^{{(ASIZE-32){1'b0}},b.len}) + {{(ASIZE-1){1'b0}},~i[31]};
// spyglass enable_block W164a
    if (os) 
    begin
      // outside of buffer, wrapping required
      r[ASIZE-1:0] = rw;
    end
    return r[ASIZE-1:0];
  endfunction : incr_xm
// spyglass enable_block WRN_1024
  
  //
  // Other types
  //
  typedef logic [63:0] timestamp_t;      // trace timestamp
  typedef logic [31:0] trace_id_t;       // trace HLAPI ID
  typedef logic [15:0] tmask_t;          // task mask
  typedef logic [9:0]  am_addr_t;        // AM address, total 512B*1K addresses  = 512KB
  // Spatial/Channel packing mode
  typedef enum logic [1:0] {
    pack_i16_e = 2'b00, // no spatial packing
    pack_i8_e  = 2'b01, // v2i8 spatial packing
    pack_i4_e  = 2'b10  // v4 i4 spatial packing
  } pack_mode_t;
  // IP tag register
  typedef enum logic [3:0] { 
                             id_type_conv, 
                             id_type_act, 
                             id_type_idma,
                             id_type_odma,
                             id_type_stu=7, 
                             id_type_conv_flt=8,
                             id_type_act_alu2=10,
                             id_type_act_str0=11,
                             id_type_act_alu2_str0=12
                             } id_type_t;
  typedef struct packed {
    id_type_t         tp;  // accelerator type
    logic     [7:0]   mj;  // major revision
    logic     [7:0]   mn;  // minor revision
  } id_reg_t;

  //
  // Define AXI4 attributes
  //
  localparam int NPU_AXI_ADDR_W   = 40; // Address vector width
  localparam int NPU_AXI_SIZE_W   = 3;  // Size vector width
  localparam int NPU_AXI_LEN_W    = 4;  // Length vector width
  localparam int NPU_AXI_WLEN_W   = 4;  // Wide length vector width
  localparam int NPU_AXI_BURST_W  = 2;  // Burst vector width
  localparam int NPU_AXI_LOCK_W   = 1;  // Lock vector width
  localparam int NPU_AXI_CACHE_W  = 4;  // Cache vector width
  localparam int NPU_AXI_PROT_W   = 3;  // Protection vector width
  localparam int NPU_AXI_RESP_W   = 2;  // Response width
  localparam int NPU_AXI_REGION_W = 4;  // Region field width

  // address, size, len, cache prot types
  typedef    logic [NPU_AXI_ADDR_W-1:0]   npu_axi_addr_t;
  typedef    logic [NPU_AXI_SIZE_W-1:0]   npu_axi_size_t;
  typedef    logic [NPU_AXI_LEN_W-1:0]    npu_axi_len_t;
  typedef    logic [NPU_AXI_WLEN_W-1:0]   npu_axi_wlen_t;
  typedef    logic [NPU_AXI_CACHE_W-1:0]  npu_axi_cache_t;
  typedef    logic [NPU_AXI_PROT_W-1:0]   npu_axi_prot_t;
  typedef    logic [NPU_AXI_REGION_W-1:0] npu_axi_region_t;
  // lock type
  typedef    enum logic [0:0] { npu_axi_lock_normal_e    = 1'b0, 
                                npu_axi_lock_exclusive_e = 1'b1 } npu_axi_lock_t;
  // burst type
  typedef    enum logic [1:0] { npu_axi_burst_fixed_e = 2'b00,
                                npu_axi_burst_incr_e  = 2'b01,
                                npu_axi_burst_wrap_e  = 2'b10 } npu_axi_burst_t;
  // response type
  typedef    enum logic [1:0] { npu_axi_resp_okay_e   = 2'b00,
                                npu_axi_resp_exokay_e = 2'b01,
                                npu_axi_resp_slverr_e = 2'b10,
                                npu_axi_resp_decerr_e = 2'b11 } npu_axi_resp_t;
  // NPU AXI4 command attributes
  typedef struct packed { 
    npu_axi_addr_t   addr;
    npu_axi_cache_t  cache;
    npu_axi_prot_t   prot;
    npu_axi_lock_t   lock;
    npu_axi_burst_t  burst;
    npu_axi_len_t    len;
    npu_axi_size_t   size;
    npu_axi_region_t region;
  } npu_axi_cmd_t;
  typedef struct packed { 
    npu_axi_addr_t   addr;
    npu_axi_cache_t  cache;
    npu_axi_prot_t   prot;
    npu_axi_lock_t   lock;
    npu_axi_burst_t  burst;
    npu_axi_wlen_t   len;
    npu_axi_size_t   size;
    npu_axi_region_t region;
  } npu_axi_wcmd_t;


  //
  // Common HLAPI parameters split into input, output and input/output
  //
// spyglass disable_block ReserveName
// SMD: Reserved Name used 
// SJ: Intended used 
  typedef struct packed {
    // outputs
    logic [31:0]              status;          // return status                        r7
    logic [31:0]              res;             // return result                        r6
  } hlapi_o_t;
  typedef struct packed {
    // input&outputs
    logic [31:0]              count;           // aggregated completion count          r5
    logic [31:0]              cycles;          // aggregated cycle-count               r4
  } hlapi_io_t;
  typedef struct packed {
    logic [7:0]             interrupt;       // if true send interrupt on completion r2
    logic [7:0]             ievent;          // if true send event on issue          r2
    logic [7:0]             devent;          // if true send event on completion     r2
  } ctrl_t;
  typedef struct packed {
    // inputs 
    trace_id_t                id;              // unique descriptor ID for tracing     r3
    logic [31:24]             pda;             // padding to 32b                       r2
    ctrl_t                    ctrl;            // Interrupt, event control type
    logic [63:ASIZE]          pdab;            // pointer padding to 64b
    xm_ptr_t                  next;            // pointer to next HLAPI                r0&r1
  } hlapi_i_t;
  typedef struct packed {
    hlapi_i_t common;
  } dummy_hlapi_i_t;
  typedef struct packed {
    hlapi_o_t       o;
    hlapi_io_t      io;
    dummy_hlapi_i_t i;
  } dummy_hlapi_t;
// spyglass enable_block ReserveName
  
  
  //
  // DMA HLAPI parameters split into VM/XM parts
  //
  localparam int ODMA_ID  = 3;
  localparam int ODMA_MAJ = 2;
  localparam int ODMA_MIN = 0;
  localparam int IDMA_ID  = 2;
  localparam int IDMA_MAJ = 2;
  localparam int IDMA_MIN = 0;

  // VM types
  typedef struct packed {   // VM address generator struct with parameterizable loop nesting: 256b
    offset_t [NUM_FM_LOOPS-1:0] iter;            // iteration loop number: 96b
    offset_t [NUM_FM_LOOPS-1:0] offsets;         // VM offsets: 96b
    offset_t                    stride;          // vector input/output stride: 16b
    buf_t                       buffer;          // cyclic buffer: 32b
    vm_addr_t                   ptr;             // pointer into buffer: 16b
  } hlapi_vm_agu_t;

  typedef struct packed {
    offset_t [2:0]                goffsets;
    offset_t [NUM_FM_LOOPS*2-4:0] pad2;
  } dma_gather_off_t;

  typedef struct packed {
    logic [63:0]                  pad1;
    buf_t                         gbuf;
  } dma_gather_buf_t;

  typedef struct packed {
    logic [47:0]                  pad0;
    vm_addr_t                     gptr;
  } dma_gather_ptr_t;

  // XM types
  typedef struct packed { // XM address generator struct: 832b
    offset_t     [NUM_FM_LOOPS-1:0] iter;            // iteration loop number: 96b
    //xm_offset_t  [NUM_FM_LOOPS-1:0] moffsets;      // METADATA offsets: 192b
    union packed {
      dma_gather_off_t                g;
      xm_offset_t  [NUM_FM_LOOPS-1:0] moffsets;      // METADATA offsets: 192b
    } o;
    xm_offset_t  [NUM_FM_LOOPS-1:0] offsets;         // XM offsets: 192b
    //xm_buf_t                        mbuffer;       // METADATA buffer: 96b
    union packed {
      dma_gather_buf_t                g;
      xm_buf_t                        mbuffer;       // METADATA buffer: 96b
    } b;                                             // union of function and padding
    xm_buf_t                        buffer;          // XM buffer: 96b
    //logic [63:0]                    mptr;          // METADATA ptr: 40b (+24b unused)
    union packed {
      dma_gather_ptr_t                g;
      logic [63:0]                    mptr;          // METADATA ptr: 40b (+24b unused)
    } p;                                             // union of function and padding
    logic [63:0]                    ptr;             // XM ptr: 40b (+24b unused)
    offset_t                        cblen;           // compressed block length in ixpix_t units: 16b
    logic [8:0]                     padc;            // Pad to 16b
    logic [1:0]                     rd_ost;          // AXI read outstanding configuration: 2'b00: up to 32 outstanding; 2'b01: up to 16 outstanding; 2'b10: up to 8 outstanding; 2'b11: up to 4 outstanding
    logic [1:0]                     wr_ost;          // AXI write outstanding configuration: 2'b00: up to 32 outstanding; 2'b01: up to 16 outstanding; 2'b10: up to 8 outstanding; 2'b11: up to 4 outstanding
    logic [1:0]                     boost;           // Skip Buffer Check: 0:skip AXI read check; 1:skip AXI write check
    logic                           compress;        // if true then compressed mode: 1b
  } hlapi_xm_agu_t;

  // Normal STU XM types
  typedef struct packed { // NPU STU XM address generator struct(w/o compression): 448b
    offset_t     [NUM_FM_LOOPS-1:0] iter;            // iteration loop number: 96b
    xm_offset_t  [NUM_FM_LOOPS-1:0] offsets;         // XM offsets: 192b
    xm_buf_t                        buffer;          // XM buffer: 96b
    logic [63:0]                    ptr;             // XM ptr: 64b
    logic [28:0]                    padb;            // Boost Mode
    logic [1:0]                     ost_cfg;         // Outstanding Config 
    logic                           boost;           // Boost Mode
  } hlapi_stu_agu_t;

  // DMA
  typedef struct packed {
    logic [15:0]                padc;            // pad to 64b
    logic [15:0]                vm_wmsk;         // VM byte write mask in iDMA: 0-> write into VM; 1-> skip write 
    offset_t                    planar_offset;   // pix_t channel offset in planar mode
    offset_t                    planar_stride;   // VM pix_t channel stride for planar mode, log2 encoded; value 0 means no planar mode
    dma_bc_t                    bc;              // broadcast flags for read data broadcast: 32b
    logic [7:0]                 padb;            // Pad to 16b
    pix_t                       zero_point;      // zero point for channel padding for XM to VM copy: 8b
    logic [13:0]                pada;            // Pad to 16b
    logic                       gather;          // if true then use GTOA XM AGU input for "gather" support
    logic                       cnst;            // if true then write a constant value, do not read; used only in iDMA
    hlapi_xm_agu_t              xm_seq;          // Struct specifying the destination XM access sequence 
    hlapi_vm_agu_t              vm_seq;          // Struct specifying the source VM access sequence
    hlapi_i_t                   common;          // Common Input field
  } dma_hlapi_i_t;
  
  // NPU DMA HLAPI Type 
  typedef struct packed {
    hlapi_o_t      o;
    hlapi_io_t     io;
    dma_hlapi_i_t  i;
  } dma_hlapi_t;
  
  // AXI bridge type
  typedef struct packed {
    xm_buf_t                       xm_ncmd; //next  addr, remaining length
    xm_buf_t                       xm_bcmd; //burst addr, length
    logic [8:0]                    shamt;   //burst shift
    logic [8:0]                    lst_len; //last beat lenth
    logic                          lst;     //last burst
  } axi_cmd_t;

  // Data Bus parameter
  //
  typedef logic [7:0]              bank;

  // AM AGU type
  typedef struct packed {
    am_addr_t       addr;   // start address
    offset_t  [6:0] iter;   // number of iterations [grp][no][ni][qd][col][row][onn]
  } am_agu_t;

  // AXI OUTSTANDING
  localparam int DMI_OST = 16;
  localparam int AXI_OST = 32;
  localparam int OFF_BUF = (`NPU_SLICE_MAC == 4096) ? 6 : 4;
  // XM BUFFER SIZE for iDMA (512/1024/2048/4096)
  localparam int IXM_BUF_SIZE  = `NPU_IDMA_BUFFER_SIZE;
  localparam int IXM_BUF_SIZE2 = $clog2(IXM_BUF_SIZE) - OFF_BUF;
  
  // XM BUFFER SIZE for oDMA
  localparam int OXM_BUF_SIZE  = `NPU_ODMA_BUFFER_SIZE;
  localparam int OXM_BUF_SIZE2 = $clog2(OXM_BUF_SIZE) - OFF_BUF;
  
  // XM BUFFER SIZE for STU
  localparam int XM_BUF_SIZE   = `NPU_STU_BUFFER_SIZE;
  localparam int XM_BUF_SIZE2  = $clog2(XM_BUF_SIZE) - OFF_BUF;

  // REORDER BUFFER SIZE
  localparam int REORDER_BUF_SIZE   = `NPU_REORDER_BUFFER_SIZE;

endpackage : npu_types
`endif
