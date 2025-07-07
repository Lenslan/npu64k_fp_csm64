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

//
// convolution stash module scalar AGU computing address of start of column
//  vcs -sverilog +incdir+../../shared/RTL ../../shared/RTL/npu_types.sv ../../shared/RTL/npu_iterator.sv ../../shared/RTL/npu_fifo.sv npu_conv_types.sv npu_conv_stash_vector.sv
//  analyze -format sverilog -vcs "+incdir+../../../shared/RTL ../../../shared/RTL/npu_types.sv ../../../shared/RTL/npu_iterator.sv ../../../shared/RTL/npu_fifo.sv ../npu_conv_types.sv ../npu_conv_stash_vector.sv"
//
 
`include "npu_defines.v"
`include "npu_axi_macros.svh"
`include "npu_vm_macros.svh"
`include "npu_conv_macros.svh"

module npu_conv_stash_vector
  import npu_types::*;
  import npu_conv_types::*;
  (
   // Clock and reset
   input  logic          clk,                          // Clock, all logic clocked at posedge
   input  logic          rst_a,                        // Asynchronous reset, active high
   // HLAPI interface
   input  logic          hlapi_valid,                  // Request new HLAPI start
   output logic          hlapi_accept,                 // Acknowledge new HLAPI start
// spyglass disable_block W240
//SMD:Unread input
//SJ :Ignore packed signal
   input  conv_hlapi_i_t hlapi_i,                      // HLAPI parameters
// spyglass enable_block W240
   // Scalar input interface
   input  logic          scalar_valid,                 // Scalar information is valid
   output logic          scalar_accept,                // Scalar information is accepted
   input  vm_scalar_t    scalar_data,                  // Scalar information
   // VM read interface
  `VMRMST(NUM_FM_QUEUE,vm_rd_),
   // Vector output interface
   output logic          vector_valid,                 // Load data is valid
   input  logic          vector_accept,                // Load data is accepted
   output vm_vector_t    vector_data                   // Load data
   );
  localparam int D = 5; // depth of read data FIFOs
  // local wires
  logic                        i_hlapi_valid;  // gated HLAPI valid
  logic                        i_hlapi_accept; // gated HLAPI accept
  logic                        it_req;         // iterator output request
  logic                        it_ack;         // iterator output acknowledge
  logic     [6:0]              it_first;       // iterator first flags
  logic     [6:0]              it_last;        // iterator last flags
  logic                        it_vald;        // iterator first/last flags valid
  offset_t  [6:0]              iter;           // iterator {grp<0>,no,ni,qd,col,row,inn<6>}
  logic                        cf_en;          // configuration reister enable
  offset_t  [NUM_FM_QUEUE-1:0] cf_stride_r;    // address stride
  offset_t  [NUM_FM_QUEUE-1:0] cf_pstride_r;   // column padding stride
  logic     [NUM_FM_QUEUE-1:0] cf_ren_r;       // read enables
  offset_t  [NUM_FM_QUEUE-1:0] cf_stride_nxt;  // address stride
  offset_t  [NUM_FM_QUEUE-1:0] cf_pstride_nxt; // column padding stride
  logic     [NUM_FM_QUEUE-1:0] cf_ren_nxt;     // read enables
  offset_t  [2:0]              cf_padlim_r;    // pad limit register
  buf_t                        cf_buf_r;       // VM buffer descriptor
  offset_t  [1:0]              cf_offset_r;    // pointer offsets, [H][D](0 channel, 1 row), fm_offsets[H][W][D]{e,2,1}
  offset_t  [1:0]              cf_offset_nxt;  // pointer offsets next
  offset_t  [1:1]              cf_poffset_r;   // padding offsets
  logic                        cf_fc_r;        // if true then fully conencted, replicate lane 0 data
  pack_mode_t                  cf_pack_r;      // packed padding mode
  logic                        ptr_en;         // pointer and padding positon enable
  vm_addr_t                    ptr_r;          // VM scalar pointer register
  vm_addr_t                    ptr_nxt;        // VM scalar pointer register next
  offset_t  [2:0]              padpos_r;       // padding position
  offset_t  [2:0]              padpos_nxt;     // padding position next
  logic                        cmdi_valid;
  logic                        cmdi_accept;
  vm_addr_t [NUM_FM_QUEUE-1:0] cmdi_addr;      // VM vector pointer register
  logic                        cmdo_valid;
  logic                        cmdo_accept;
  logic                        rdone_en;       // enable done register
  logic     [NUM_FM_QUEUE-1:0] rdone_r;        // VM access done bits
  logic     [NUM_FM_QUEUE-1:0] rdone_nxt;      // VM access done bits next  

  // read data FIFO output per bank
  logic     [NUM_FM_QUEUE-1:0] dfifo_valid;
  logic                        fifo_accept;    // common accept for for dfifo and pfifo
  ixpix_t   [NUM_FM_QUEUE-1:0] dfifo_data;
  // pad FIFO input
  logic                        padi_valid;
  logic                        padi_accept;
  stash_pad_t                  padi_data;
  logic                        pado_valid;
  stash_pad_t                  pado_data;

  //
  // capture HLAPI parameters
  //

  // determine number of channels, columns and rows to load
  // outputs: cf_stride_nxt, cf_pstride_nxt, cf_ren_nxt, cf_offset_nxt
  always_comb
    begin : rc_PROC
      logic    [2:0] ri;   // row increment
      offset_t       rows;
      logic          chns;
      logic          set_inn;
      logic          dw_inn;
      // defaults
      cf_stride_nxt   = cf_stride_r ;
      cf_pstride_nxt  = cf_pstride_r;

      rows = $unsigned(hlapi_i.iter[5]);
      chns = 1'b0;
      dw_inn = hlapi_i.fm_cfg==fm_cfg_16b_e || hlapi_i.fm_cfg==fm_cfg_bf16_e || hlapi_i.fm_cfg==fm_cfg_fp16_e;
      case (hlapi_i.conv_mode)
      `NINO(conv_mode_4x1g2s1):    begin cf_ren_nxt = {{(NUM_FM_QUEUE-VSIZE-3){1'b0}}, {(VSIZE+3){1'b1}}}; ri = 'd0; set_inn = 'b0; end
      `NINO(conv_mode_2x1g2s2):    begin cf_ren_nxt = {{(NUM_FM_QUEUE-VSIZE*2){1'b0}}, {(VSIZE*2){1'b1}}}; ri = 'd0; set_inn = 'b0; end
      `NINO(conv_mode_4x1g2s1dl2): begin cf_ren_nxt = {{(NUM_FM_QUEUE-VSIZE-6){1'b0}}, {(VSIZE+6){1'b1}}}; ri = 'd0; set_inn = 'b0; end
      `DINO(conv_mode_1x1):        begin cf_ren_nxt = {{(NUM_FM_QUEUE-VSIZE*2){1'b0}}, {(VSIZE*2){1'b1}}}; ri = 'd0; set_inn = 'b0; chns = 1'b1; end
      `NINO(conv_mode_1x1):        begin cf_ren_nxt = {{(NUM_FM_QUEUE-VSIZE-0){1'b0}}, {(VSIZE+0){1'b1}}}; ri = 'd0; set_inn = 'b0; end
      `NINO(conv_mode_2x1s1):      begin cf_ren_nxt = {{(NUM_FM_QUEUE-VSIZE-1){1'b0}}, {(VSIZE+1){1'b1}}}; ri = 'd0; set_inn = 'b0; end
      `NINO(conv_mode_2x1s2):      begin cf_ren_nxt = {{(NUM_FM_QUEUE-VSIZE*2){1'b0}}, {(VSIZE*2){1'b1}}}; ri = 'd0; set_inn = 'b0; end
      `NINO(conv_mode_2x1s1dl2):   begin cf_ren_nxt = {{(NUM_FM_QUEUE-VSIZE-2){1'b0}}, {(VSIZE+2){1'b1}}}; ri = 'd0; set_inn = 'b0; end
      `VIVO(conv_mode_3x3dws1),
      `NINO(conv_mode_3x3dws1):    begin cf_ren_nxt = {{(NUM_FM_QUEUE-VSIZE-2){1'b0}}, {(VSIZE+2){1'b1}}}; ri = 'd2; set_inn = dw_inn; end
      `NINO(conv_mode_2x3dws2):    begin cf_ren_nxt = {{(NUM_FM_QUEUE-VSIZE*2){1'b0}}, {(VSIZE*2){1'b1}}}; ri = 'd1; set_inn = dw_inn; rows = rows<<1'b1;  end
      `NINO(conv_mode_3x3dws1dl2): begin cf_ren_nxt = {{(NUM_FM_QUEUE-VSIZE-4){1'b0}}, {(VSIZE+4){1'b1}}}; ri = 'd4; set_inn = dw_inn; end
      `NINO(conv_mode_8x1dws1):    begin cf_ren_nxt = {{(NUM_FM_QUEUE-VSIZE-7){1'b0}}, {(VSIZE+7){1'b1}}}; ri = 'd0; set_inn = dw_inn; end
      default:                     begin cf_ren_nxt = {{(NUM_FM_QUEUE-1){1'b0}},       {(1){1'b1}}};       ri = 'd0; set_inn = 'b0; end //`FC(conv_mode_fc)
      endcase // case (hlapi_i.conv_mode)
      // add input rows for 3x3 convolutions
      rows    = rows + ri;
      iter    = hlapi_i.iter[6:0]; // no onn loop
      iter[5] = rows;
      iter[6] = (hlapi_i.iter[6][1] || set_inn == 1'b1) ? $unsigned(2) : $unsigned(1);
      // precompute address offsets
      for (int i = 0; i < NUM_FM_QUEUE; i++)
      begin
        cf_stride_nxt[i]  = unsigned'(i)*hlapi_i.fm_offsets[FMO_W];
        cf_pstride_nxt[i] = unsigned'(i)*hlapi_i.fm_poffsets[FMO_W];
      end
      if (chns)
      begin
        for (int i = 0; i < VSIZE; i++)
        begin
          // upper half is in channel dimension for `DINO
          cf_stride_nxt [i+VSIZE] = cf_stride_nxt[i] + hlapi_i.fm_offsets[FMO_C];
          cf_pstride_nxt[i+VSIZE] = cf_pstride_nxt[i];
        end
        // offset to next block of channels by 2 for i32
        cf_offset_nxt[CFO_C] = hlapi_i.fm_offsets[FMO_C] << 1;
      end
      else
      begin
        // offset to next block of channels
        cf_offset_nxt[CFO_C] = hlapi_i.fm_offsets[FMO_C];
      end
      cf_offset_nxt[CFO_H] = hlapi_i.fm_offsets[FMO_H];
    end : rc_PROC
  assign cf_en = hlapi_valid & hlapi_accept;

  // store (derived) configuration parameters
  // outputs: cf_stride_r, cf_pstride_r, cf_ren_r, cf_pad_lim_r, cf_buf_r
  always_ff @(posedge clk or posedge rst_a)
  begin : cf_reg_PROC
    if (rst_a == 1'b1)
    begin
      cf_stride_r   <= {STR_SZ{1'b0}};
      cf_pstride_r  <= {STR_SZ{1'b0}};
      cf_ren_r      <= '0;
      cf_padlim_r   <= '0;
      cf_buf_r      <= {BUF_SZ{1'b0}};
      cf_offset_r   <= '0;
      cf_poffset_r  <= '0;
      cf_fc_r       <= '0;
      cf_pack_r     <= pack_i16_e;
    end
    else if (cf_en)
    begin
      cf_stride_r   <= cf_stride_nxt;
      cf_pstride_r  <= cf_pstride_nxt;
      cf_ren_r      <= cf_ren_nxt;
      cf_padlim_r   <= hlapi_i.fm_padlim;
      cf_buf_r.base <= hlapi_i.fm_buf_base;
      cf_buf_r.len  <= hlapi_i.fm_buf_len;
      cf_offset_r   <= cf_offset_nxt;
      cf_poffset_r  <= hlapi_i.fm_poffsets[FMO_H];
      cf_fc_r       <= hlapi_i.conv_mode == `FC(conv_mode_fc);
      cf_pack_r     <= hlapi_i.pack_mode;
    end
  end : cf_reg_PROC

  
  //
  // iterator [grp<0>][no][ni][qd][col][row][inn]
  //
  assign i_hlapi_valid = hlapi_valid & (~pado_valid);
  assign hlapi_accept  = i_hlapi_accept & (~pado_valid);
  npu_iterator
    #(
      .N ( 7 )
      )
  u_iter_inst
    (
     .clk      ( clk               ),
     .rst_a    ( rst_a             ),
     .soft_rst ( 1'b0              ),
     .in_req   ( i_hlapi_valid     ),
     .in_ack   ( i_hlapi_accept    ),
     .in_shp   ( iter              ),
     .it_req   ( it_req            ),
     .it_ack   ( it_ack            ),
     .it_first ( it_first          ),
     .it_last  ( it_last           ),
     .it_vald  ( it_vald           )
   );


  //
  // Update scalar address, generate vector address and padding positions
  //
  // next address computation
  // outputs: ptr_nxt, padpos_nxt, cmdi_valid, cmdi_addr
  always_comb
  begin : vm_rd_cmd_PROC
    vm_addr_t       p;   // VM pointer
    vm_addr_t       a;   // VM pointer increment
    offset_t  [2:0] pp;  // Padding position
    offset_t        pa;  // Padding position row increment
    // default
    p               = ptr_r;         // pointer
    a               = '0;            // pointer increment
    pp              = padpos_r;      // padding position
    pa              = '0;            // padding position increment
    padi_data       = '0;            // no padding
    padi_data.flast = &it_last;      // last in feature-map
    padi_data.clast = &it_last[6:3]; // last in channel
    padi_data.rlast = &it_last[6:5]; // last row in column
    // current position
    cmdi_valid = it_req && padi_accept;
    casez (it_first) // [grp][no][ni][qd][col][row][inn]
    7'b11?????:
      begin
        // first data in column
        cmdi_valid    &= scalar_valid;
        p              = scalar_data.ptr;
        pp             = scalar_data.ppos;
      end
    default:
      begin
        // first data in row but not first in column
        p              = ptr_r;
        pp             = padpos_r; // padding position
      end
    endcase // case (it_first)
    // create a strided pointer and padding vector
    if (pp[1] < 0 || pp[1] > cf_padlim_r[1] ||
        pp[2] < 0 || pp[2] > cf_padlim_r[2])
    begin
      padi_data.pad |= '1;
    end
    for (int b = 0; b < NUM_FM_QUEUE; b++)
    begin : loc_SCOPE
      offset_t [3:0] cpos;
      cmdi_addr[b] = incr_vm(p, cf_stride_r[b], cf_buf_r);
      for (int i = 0; i < 4; i++)
      begin
        cpos[i]  = pp[0] + cf_pstride_r[b] + unsigned'(i);
      end
      case (cf_pack_r)
      pack_i4_e:
        begin
          cpos[0] = cpos[0];
          cpos[1] = cpos[1];
          cpos[2] = cpos[2];
          cpos[3] = cpos[3];
        end
      pack_i8_e:
        begin
          cpos[2] = cpos[1];
          cpos[3] = cpos[1];
          cpos[0] = cpos[0];
          cpos[1] = cpos[0];
        end
      default: // pack_i16_e
        begin
          cpos[0] = cpos[0];
          cpos[1] = cpos[0];
          cpos[2] = cpos[0];
          cpos[3] = cpos[0];
        end
      endcase // case (cf_pack_r)
      for (int i = 0; i < 4; i++)
      begin
        if (cpos[i] < 0 || cpos[i] > cf_padlim_r[0])
        begin
          padi_data.pad[b][i] |= 1'b1;
        end
      end
    end : loc_SCOPE
    // post increments
    casez (it_last)
    7'b1??????:
      begin
        // go to next row
        a              = cf_offset_r[CFO_H];
        pa             = cf_poffset_r[CFO_H];
      end
    default:
      begin
        // next input channel, keep padding
        a             = cf_offset_r[CFO_C];
      end
    endcase
    // increment and wrap the scalar VM pointer
    ptr_nxt       = incr_vm(p, a, cf_buf_r);
    padpos_nxt    = pp;
    padpos_nxt[1] = pp[1] + pa;
  end // block: vm_rd_cmd_PROC

  // next state
  // outputs: ptr_en, it_ack, scalar_accept, padi_valid
  always_comb
  begin : nxt_PROC
    // default outputs
    ptr_en        = 1'b0;
    it_ack        = 1'b0;
    scalar_accept = 1'b0;
    padi_valid    = 1'b0;
    if (cmdi_valid && cmdi_accept)
    begin
      // command is done
      it_ack        = 1'b1;
      padi_valid    = 1'b1;
      scalar_accept = &it_last[6:5];
      ptr_en        = 1'b1;
    end
  end : nxt_PROC

  // state
  // outputs: ptr_r, padpos_r, rdone_r
  always_ff @(posedge clk or posedge rst_a)
  begin : state_PROC
    if (rst_a == 1'b1)
    begin
      ptr_r           <= '0;
      padpos_r        <= '0;
      rdone_r         <= '0;
    end
    else
    begin
      if (ptr_en)
      begin
        ptr_r         <= ptr_nxt;
        padpos_r      <= padpos_nxt;
      end
      if (rdone_en)
      begin
        rdone_r       <= rdone_nxt;
      end
    end
  end : state_PROC


  //
  // Slice on output command
  //
  npu_slice_int
    #( .DWIDTH( NUM_FM_QUEUE*$bits(vm_addr_t) ) )
  u_slice_inst
    (
     .clk          ( clk            ),  // clock
     .rst_a        ( rst_a          ),  // asynchronous reset, active high, synchronous deassertion
     .valid_write  ( cmdi_valid     ),  // input data valid
     .accept_write ( cmdi_accept    ),  // accept input data
     .data_write   ( cmdi_addr      ),  // input data
     .valid_read   ( cmdo_valid     ),  // output data valid
     .accept_read  ( cmdo_accept    ),  // accept output data
     .data_read    ( vm_rd_cmd_addr )   // output data
     );
  assign vm_rd_cmd_valid = (cmdo_valid & padi_accept) ? cf_ren_r & ~rdone_r : '0;
  assign cmdo_accept     = ((vm_rd_cmd_valid & ~vm_rd_cmd_accept) == '0) & padi_accept;
  
  
  // next rdone state
  // outputs: rdone_en, rdone_nxt
  always_comb
  begin : done_nxt_PROC
    // default outputs
    rdone_en      = 1'b0;
    rdone_nxt     = '0;
    if (cmdo_valid)
    begin
      // command valid
      rdone_en    = 1'b1;
      if ((vm_rd_cmd_valid & vm_rd_cmd_accept) == vm_rd_cmd_valid)
      begin
        // command is done
        rdone_nxt = '0;
      end
      else
      begin
        // command is not done
        rdone_nxt = rdone_r | vm_rd_cmd_accept;
      end
    end
  end : done_nxt_PROC

  
  //
  // VM read data FIFOs
  //
// spyglass disable_block W287b
//SMD:Unconnect output
//SJ :Intentionally unconnected
  for (genvar g = 0; g < NUM_FM_QUEUE; g++)
  begin : dfifo_GEN
    npu_fifo
    #(
      .SIZE   ( D              ),
      .DWIDTH ( $bits(ixpix_t) ),
      .FRCVAL ( 1'b0           ),
      .FRCACC ( 1'b1           ) // FIFO can always accept, guarded by the padding FIFO
      )
    u_dfifo_inst
     (
      .clk          ( clk             ),
      .rst_a        ( rst_a           ),
      .valid_write  ( vm_rd_rvalid[g] ),
      .accept_write (                 ), // intentionally unconnected
      .data_write   ( vm_rd_rdata[g]  ),
      .valid_read   ( dfifo_valid[g]  ),
      .accept_read  ( fifo_accept     ),
      .data_read    ( dfifo_data[g]   )
      );
  end : dfifo_GEN
// spyglass enable_block W287b

  //
  // Pad FIFOs
  //
  npu_fifo
    #(
      .SIZE   ( D+1                ), // size needs to be one bigger than dfifo
      .DWIDTH ( $bits(stash_pad_t) ),
      .FRCVAL ( 1'b0               ),
      .FRCACC ( 1'b0               )
      )
    u_pfifo_inst
     (
      .clk          ( clk             ),
      .rst_a        ( rst_a           ),
      .valid_write  ( padi_valid      ),
      .accept_write ( padi_accept     ),
      .data_write   ( padi_data       ),
      .valid_read   ( pado_valid      ),
      .accept_read  ( fifo_accept     ),
      .data_read    ( pado_data       )
      );


  //
  // Drive output and replicate data for FC
  //
  assign vector_data.pad   = pado_data;
  generate
    if(VSIZE==8) begin: fc_PROC_V8
    assign vector_data.data  = cf_fc_r ? {dfifo_data[15:8], {8{dfifo_data[0]}}} : dfifo_data;
    end
    else begin: fc_PROC_V2
    assign vector_data.data  = cf_fc_r ? {8{dfifo_data[0]}} : dfifo_data;
    end
  endgenerate
  assign vector_valid      = dfifo_valid == cf_ren_r;
  assign fifo_accept       = vector_valid & vector_accept;

endmodule : npu_conv_stash_vector
