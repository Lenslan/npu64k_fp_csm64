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

/*
 * This module generates the write data depenency signal required by prefetching read data
 */
module npu_gtoa_prefetch_dep
  import npu_types::*;
  import npu_gtoa_types::*;
  (
   input  logic                         clk,           // clock
   input  logic                         rst_a,         // asynchronous reset, active high
   input  logic                         hlp_accept,    // new hlapi accept
   input  logic                         in_wvalid,     // input valid on a write port
   input  logic                         in_waccept,    // input accept on a write port
   output logic                         wdep           // has write dependency
   );
  // local types
  typedef enum logic [1:0] {idle_e, busy_e, done_prefetch_e} pref_state_t;
  // local wires
  logic                      state_en;
  pref_state_t               state_r;
  pref_state_t               state_nxt;

  always_comb
  begin : state_nxt_PROC
    // default outputs
    state_en      = 1'b0;
    state_nxt     = idle_e;
    wdep          = 1'b0;
    case (state_r)
    busy_e:
      begin
        // write AGU is busy for current descriptor
        // assert wdep to indicate possible data dependency
        wdep = 1'b1;
        if (in_waccept)
        begin
          state_en  = 1'b1;
          if (in_wvalid)
          begin
            state_nxt = hlp_accept ? busy_e : done_prefetch_e;
          end
          else
          begin
            state_nxt = idle_e;
          end
        end
      end
    done_prefetch_e:
      // next hlapi write command is prefetched
      // write AGU is now busy, but next hlapi read command shall be accepted (no dependency)
      begin
        if (hlp_accept)
        begin
          state_en  = 1'b1;
          state_nxt = busy_e;
        end
      end
    default: // idle_e
      // write AGU is idle
      begin
        if (in_wvalid)
        begin
          state_en  = 1'b1;
          if (hlp_accept)
          begin
            state_nxt = busy_e;
          end
          else
          begin
            state_nxt = done_prefetch_e;
          end
        end
      end
    endcase // case (state_r)
  end : state_nxt_PROC

  always_ff @(posedge clk or
              posedge rst_a)
  begin : state_reg_PROC
    if (rst_a == 1'b1)
    begin
      state_r <= idle_e;
    end
    else
    begin
      if (state_en)
      begin
        state_r <= state_nxt;
      end
    end
  end : state_reg_PROC

endmodule : npu_gtoa_prefetch_dep
