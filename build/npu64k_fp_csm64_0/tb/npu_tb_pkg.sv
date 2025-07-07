/*
 * Copyright (C) 2021-2022 Synopsys, Inc. All rights reserved.
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

`ifndef NPU_TB_PKG_INCLUDED
`define NPU_TB_PKG_INCLUDED

package npu_tb_pkg;

`define mem_access_bins \
        bins _L2_DCCM0 = {L2_DCCM0_ACCESS}; \
        bins _L2_DCCM1 = {L2_DCCM1_ACCESS}; \
        bins _GRP0_SLC0_L1_DM = {GRP0_SLC0_DM_ACCESS}; \
        bins _GRP0_SLC0_L1_AM = {GRP0_SLC0_AM_ACCESS}; \
        bins _GRP0_SLC0_L1_VM = {GRP0_SLC0_VM_ACCESS}; \
        bins _GRP0_SLC1_L1_DM = {GRP0_SLC1_DM_ACCESS}; \
        bins _GRP0_SLC1_L1_AM = {GRP0_SLC1_AM_ACCESS}; \
        bins _GRP0_SLC1_L1_VM = {GRP0_SLC1_VM_ACCESS}; \
        bins _GRP0_SLC2_L1_DM = {GRP0_SLC2_DM_ACCESS}; \
        bins _GRP0_SLC2_L1_AM = {GRP0_SLC2_AM_ACCESS}; \
        bins _GRP0_SLC2_L1_VM = {GRP0_SLC2_VM_ACCESS}; \
        bins _GRP0_SLC3_L1_DM = {GRP0_SLC3_DM_ACCESS}; \
        bins _GRP0_SLC3_L1_AM = {GRP0_SLC3_AM_ACCESS}; \
        bins _GRP0_SLC3_L1_VM = {GRP0_SLC3_VM_ACCESS}; \
        bins _GRP1_SLC0_L1_DM = {GRP1_SLC0_DM_ACCESS}; \
        bins _GRP1_SLC0_L1_AM = {GRP1_SLC0_AM_ACCESS}; \
        bins _GRP1_SLC0_L1_VM = {GRP1_SLC0_VM_ACCESS}; \
        bins _GRP1_SLC1_L1_DM = {GRP1_SLC1_DM_ACCESS}; \
        bins _GRP1_SLC1_L1_AM = {GRP1_SLC1_AM_ACCESS}; \
        bins _GRP1_SLC1_L1_VM = {GRP1_SLC1_VM_ACCESS}; \
        bins _GRP1_SLC2_L1_DM = {GRP1_SLC2_DM_ACCESS}; \
        bins _GRP1_SLC2_L1_AM = {GRP1_SLC2_AM_ACCESS}; \
        bins _GRP1_SLC2_L1_VM = {GRP1_SLC2_VM_ACCESS}; \
        bins _GRP1_SLC3_L1_DM = {GRP1_SLC3_DM_ACCESS}; \
        bins _GRP1_SLC3_L1_AM = {GRP1_SLC3_AM_ACCESS}; \
        bins _GRP1_SLC3_L1_VM = {GRP1_SLC3_VM_ACCESS}; \
        bins _GRP2_SLC0_L1_DM = {GRP2_SLC0_DM_ACCESS}; \
        bins _GRP2_SLC0_L1_AM = {GRP2_SLC0_AM_ACCESS}; \
        bins _GRP2_SLC0_L1_VM = {GRP2_SLC0_VM_ACCESS}; \
        bins _GRP2_SLC1_L1_DM = {GRP2_SLC1_DM_ACCESS}; \
        bins _GRP2_SLC1_L1_AM = {GRP2_SLC1_AM_ACCESS}; \
        bins _GRP2_SLC1_L1_VM = {GRP2_SLC1_VM_ACCESS}; \
        bins _GRP2_SLC2_L1_DM = {GRP2_SLC2_DM_ACCESS}; \
        bins _GRP2_SLC2_L1_AM = {GRP2_SLC2_AM_ACCESS}; \
        bins _GRP2_SLC2_L1_VM = {GRP2_SLC2_VM_ACCESS}; \
        bins _GRP2_SLC3_L1_DM = {GRP2_SLC3_DM_ACCESS}; \
        bins _GRP2_SLC3_L1_AM = {GRP2_SLC3_AM_ACCESS}; \
        bins _GRP2_SLC3_L1_VM = {GRP2_SLC3_VM_ACCESS}; \
        bins _GRP3_SLC0_L1_DM = {GRP3_SLC0_DM_ACCESS}; \
        bins _GRP3_SLC0_L1_AM = {GRP3_SLC0_AM_ACCESS}; \
        bins _GRP3_SLC0_L1_VM = {GRP3_SLC0_VM_ACCESS}; \
        bins _GRP3_SLC1_L1_DM = {GRP3_SLC1_DM_ACCESS}; \
        bins _GRP3_SLC1_L1_AM = {GRP3_SLC1_AM_ACCESS}; \
        bins _GRP3_SLC1_L1_VM = {GRP3_SLC1_VM_ACCESS}; \
        bins _GRP3_SLC2_L1_DM = {GRP3_SLC2_DM_ACCESS}; \
        bins _GRP3_SLC2_L1_AM = {GRP3_SLC2_AM_ACCESS}; \
        bins _GRP3_SLC2_L1_VM = {GRP3_SLC2_VM_ACCESS}; \
        bins _GRP3_SLC3_L1_DM = {GRP3_SLC3_DM_ACCESS}; \
        bins _GRP3_SLC3_L1_AM = {GRP3_SLC3_AM_ACCESS}; \
        bins _GRP3_SLC3_L1_VM = {GRP3_SLC3_VM_ACCESS}; \
        bins _GRP0_SCM = {GRP0_SCM_ACCESS}; \
        bins _GRP1_SCM = {GRP1_SCM_ACCESS}; \
        bins _GRP2_SCM = {GRP2_SCM_ACCESS}; \
        bins _GRP3_SCM = {GRP3_SCM_ACCESS}; \
        bins _NOC = {XM_ACCESS};

`define dmastu_mem_access_bins \
        bins _L2_DCCM0 = {L2_DCCM0_ACCESS}; \
        bins _L2_DCCM1 = {L2_DCCM1_ACCESS}; \
        bins _GRP0_SLC0_L1_DM = {GRP0_SLC0_DM_ACCESS}; \
        bins _GRP0_SLC0_L1_AM = {GRP0_SLC0_AM_ACCESS}; \
        bins _GRP0_SLC0_L1_VM = {GRP0_SLC0_VM_ACCESS}; \
        bins _GRP0_SLC1_L1_DM = {GRP0_SLC1_DM_ACCESS}; \
        bins _GRP0_SLC1_L1_AM = {GRP0_SLC1_AM_ACCESS}; \
        bins _GRP0_SLC1_L1_VM = {GRP0_SLC1_VM_ACCESS}; \
        bins _GRP0_SLC2_L1_DM = {GRP0_SLC2_DM_ACCESS}; \
        bins _GRP0_SLC2_L1_AM = {GRP0_SLC2_AM_ACCESS}; \
        bins _GRP0_SLC2_L1_VM = {GRP0_SLC2_VM_ACCESS}; \
        bins _GRP0_SLC3_L1_DM = {GRP0_SLC3_DM_ACCESS}; \
        bins _GRP0_SLC3_L1_AM = {GRP0_SLC3_AM_ACCESS}; \
        bins _GRP0_SLC3_L1_VM = {GRP0_SLC3_VM_ACCESS}; \
        bins _GRP1_SLC0_L1_DM = {GRP1_SLC0_DM_ACCESS}; \
        bins _GRP1_SLC0_L1_AM = {GRP1_SLC0_AM_ACCESS}; \
        bins _GRP1_SLC0_L1_VM = {GRP1_SLC0_VM_ACCESS}; \
        bins _GRP1_SLC1_L1_DM = {GRP1_SLC1_DM_ACCESS}; \
        bins _GRP1_SLC1_L1_AM = {GRP1_SLC1_AM_ACCESS}; \
        bins _GRP1_SLC1_L1_VM = {GRP1_SLC1_VM_ACCESS}; \
        bins _GRP1_SLC2_L1_DM = {GRP1_SLC2_DM_ACCESS}; \
        bins _GRP1_SLC2_L1_AM = {GRP1_SLC2_AM_ACCESS}; \
        bins _GRP1_SLC2_L1_VM = {GRP1_SLC2_VM_ACCESS}; \
        bins _GRP1_SLC3_L1_DM = {GRP1_SLC3_DM_ACCESS}; \
        bins _GRP1_SLC3_L1_AM = {GRP1_SLC3_AM_ACCESS}; \
        bins _GRP1_SLC3_L1_VM = {GRP1_SLC3_VM_ACCESS}; \
        bins _GRP2_SLC0_L1_DM = {GRP2_SLC0_DM_ACCESS}; \
        bins _GRP2_SLC0_L1_AM = {GRP2_SLC0_AM_ACCESS}; \
        bins _GRP2_SLC0_L1_VM = {GRP2_SLC0_VM_ACCESS}; \
        bins _GRP2_SLC1_L1_DM = {GRP2_SLC1_DM_ACCESS}; \
        bins _GRP2_SLC1_L1_AM = {GRP2_SLC1_AM_ACCESS}; \
        bins _GRP2_SLC1_L1_VM = {GRP2_SLC1_VM_ACCESS}; \
        bins _GRP2_SLC2_L1_DM = {GRP2_SLC2_DM_ACCESS}; \
        bins _GRP2_SLC2_L1_AM = {GRP2_SLC2_AM_ACCESS}; \
        bins _GRP2_SLC2_L1_VM = {GRP2_SLC2_VM_ACCESS}; \
        bins _GRP2_SLC3_L1_DM = {GRP2_SLC3_DM_ACCESS}; \
        bins _GRP2_SLC3_L1_AM = {GRP2_SLC3_AM_ACCESS}; \
        bins _GRP2_SLC3_L1_VM = {GRP2_SLC3_VM_ACCESS}; \
        bins _GRP3_SLC0_L1_DM = {GRP3_SLC0_DM_ACCESS}; \
        bins _GRP3_SLC0_L1_AM = {GRP3_SLC0_AM_ACCESS}; \
        bins _GRP3_SLC0_L1_VM = {GRP3_SLC0_VM_ACCESS}; \
        bins _GRP3_SLC1_L1_DM = {GRP3_SLC1_DM_ACCESS}; \
        bins _GRP3_SLC1_L1_AM = {GRP3_SLC1_AM_ACCESS}; \
        bins _GRP3_SLC1_L1_VM = {GRP3_SLC1_VM_ACCESS}; \
        bins _GRP3_SLC2_L1_DM = {GRP3_SLC2_DM_ACCESS}; \
        bins _GRP3_SLC2_L1_AM = {GRP3_SLC2_AM_ACCESS}; \
        bins _GRP3_SLC2_L1_VM = {GRP3_SLC2_VM_ACCESS}; \
        bins _GRP3_SLC3_L1_DM = {GRP3_SLC3_DM_ACCESS}; \
        bins _GRP3_SLC3_L1_AM = {GRP3_SLC3_AM_ACCESS}; \
        bins _GRP3_SLC3_L1_VM = {GRP3_SLC3_VM_ACCESS}; \
        bins _GRP0_SCM = {GRP0_SCM_ACCESS}; \
        bins _GRP1_SCM = {GRP1_SCM_ACCESS}; \
        bins _GRP2_SCM = {GRP2_SCM_ACCESS}; \
        bins _GRP3_SCM = {GRP3_SCM_ACCESS}; \
        bins _NOC = {XM_ACCESS};

  typedef enum logic [5:0] {
    XM_ACCESS                 = 6'b000001,  
    L2_DCCM0_ACCESS           = 6'b000010,
    L2_DCCM1_ACCESS           = 6'b000011,
    GRP0_SCM_ACCESS        = 4 + 0,
    GRP1_SCM_ACCESS        = 4 + 1,
    GRP2_SCM_ACCESS        = 4 + 2,
    GRP3_SCM_ACCESS        = 4 + 3,
    GRP0_SLC0_DM_ACCESS = 4 + 4 + 0*3 + 0*4*3,
    GRP0_SLC0_AM_ACCESS = 5 + 4 + 0*3 + 0*4*3,
    GRP0_SLC0_VM_ACCESS = 6 + 4 + 0*3 + 0*4*3,
    GRP0_SLC1_DM_ACCESS = 4 + 4 + 1*3 + 0*4*3,
    GRP0_SLC1_AM_ACCESS = 5 + 4 + 1*3 + 0*4*3,
    GRP0_SLC1_VM_ACCESS = 6 + 4 + 1*3 + 0*4*3,
    GRP0_SLC2_DM_ACCESS = 4 + 4 + 2*3 + 0*4*3,
    GRP0_SLC2_AM_ACCESS = 5 + 4 + 2*3 + 0*4*3,
    GRP0_SLC2_VM_ACCESS = 6 + 4 + 2*3 + 0*4*3,
    GRP0_SLC3_DM_ACCESS = 4 + 4 + 3*3 + 0*4*3,
    GRP0_SLC3_AM_ACCESS = 5 + 4 + 3*3 + 0*4*3,
    GRP0_SLC3_VM_ACCESS = 6 + 4 + 3*3 + 0*4*3,
    GRP1_SLC0_DM_ACCESS = 4 + 4 + 0*3 + 1*4*3,
    GRP1_SLC0_AM_ACCESS = 5 + 4 + 0*3 + 1*4*3,
    GRP1_SLC0_VM_ACCESS = 6 + 4 + 0*3 + 1*4*3,
    GRP1_SLC1_DM_ACCESS = 4 + 4 + 1*3 + 1*4*3,
    GRP1_SLC1_AM_ACCESS = 5 + 4 + 1*3 + 1*4*3,
    GRP1_SLC1_VM_ACCESS = 6 + 4 + 1*3 + 1*4*3,
    GRP1_SLC2_DM_ACCESS = 4 + 4 + 2*3 + 1*4*3,
    GRP1_SLC2_AM_ACCESS = 5 + 4 + 2*3 + 1*4*3,
    GRP1_SLC2_VM_ACCESS = 6 + 4 + 2*3 + 1*4*3,
    GRP1_SLC3_DM_ACCESS = 4 + 4 + 3*3 + 1*4*3,
    GRP1_SLC3_AM_ACCESS = 5 + 4 + 3*3 + 1*4*3,
    GRP1_SLC3_VM_ACCESS = 6 + 4 + 3*3 + 1*4*3,
    GRP2_SLC0_DM_ACCESS = 4 + 4 + 0*3 + 2*4*3,
    GRP2_SLC0_AM_ACCESS = 5 + 4 + 0*3 + 2*4*3,
    GRP2_SLC0_VM_ACCESS = 6 + 4 + 0*3 + 2*4*3,
    GRP2_SLC1_DM_ACCESS = 4 + 4 + 1*3 + 2*4*3,
    GRP2_SLC1_AM_ACCESS = 5 + 4 + 1*3 + 2*4*3,
    GRP2_SLC1_VM_ACCESS = 6 + 4 + 1*3 + 2*4*3,
    GRP2_SLC2_DM_ACCESS = 4 + 4 + 2*3 + 2*4*3,
    GRP2_SLC2_AM_ACCESS = 5 + 4 + 2*3 + 2*4*3,
    GRP2_SLC2_VM_ACCESS = 6 + 4 + 2*3 + 2*4*3,
    GRP2_SLC3_DM_ACCESS = 4 + 4 + 3*3 + 2*4*3,
    GRP2_SLC3_AM_ACCESS = 5 + 4 + 3*3 + 2*4*3,
    GRP2_SLC3_VM_ACCESS = 6 + 4 + 3*3 + 2*4*3,
    GRP3_SLC0_DM_ACCESS = 4 + 4 + 0*3 + 3*4*3,
    GRP3_SLC0_AM_ACCESS = 5 + 4 + 0*3 + 3*4*3,
    GRP3_SLC0_VM_ACCESS = 6 + 4 + 0*3 + 3*4*3,
    GRP3_SLC1_DM_ACCESS = 4 + 4 + 1*3 + 3*4*3,
    GRP3_SLC1_AM_ACCESS = 5 + 4 + 1*3 + 3*4*3,
    GRP3_SLC1_VM_ACCESS = 6 + 4 + 1*3 + 3*4*3,
    GRP3_SLC2_DM_ACCESS = 4 + 4 + 2*3 + 3*4*3,
    GRP3_SLC2_AM_ACCESS = 5 + 4 + 2*3 + 3*4*3,
    GRP3_SLC2_VM_ACCESS = 6 + 4 + 2*3 + 3*4*3,
    GRP3_SLC3_DM_ACCESS = 4 + 4 + 3*3 + 3*4*3,
    GRP3_SLC3_AM_ACCESS = 5 + 4 + 3*3 + 3*4*3,
    GRP3_SLC3_VM_ACCESS = 6 + 4 + 3*3 + 3*4*3,
    NO_HIT                    = 6'b000000
  } mem_acc;
  
  // get a decimal value from plusargs
  function longint get_value_from_plusargs (string args, longint default_value=0);
    longint v;
    if ($test$plusargs(args))  $value$plusargs({args, "=%d"}, v);
    else                       v = default_value;
    return v;
  endfunction

  // get a hex value from plusargs
  function longint get_hex_value_from_plusargs (string args, longint default_value=0);
    longint v;
    if ($test$plusargs(args))  $value$plusargs({args, "=%x"}, v);
    else                       v = default_value;
    return v;
  endfunction

  // set an int value from plusargs; return 1 if plusarg was passed
  function bit set_hex_value_from_plusargs (input string arg, input int dflt=0, output int x, input bit q=0);
    if ($test$plusargs(arg))  begin
      $value$plusargs({arg, "=%x"}, x);
      if(q==0) $display("set_int_value_from_plusargs returning %0x for %s plusarg", x, arg);
      return 1;
    end
    else begin
      x = dflt;
      if(q==0) $display("set_int_value_from_plusargs returning %0x default as %s plusarg not set", x, arg);
      return 0;
    end
  endfunction

  // get a string from plusargs
  function string get_str_from_plusargs (string args, string default_value="deadbeef");
    string v;
    if ($test$plusargs(args))  $value$plusargs({args, "=%s"}, v);
    else                       v = default_value;
    return v;
  endfunction

  // set an int value from plusargs; return 1 if plusarg was passed
  function bit set_int_value_from_plusargs (input string arg, input int dflt=0, output int x, input bit q=0);
    if ($test$plusargs(arg))  begin
      $value$plusargs({arg, "=%d"}, x);
      if(q==0) $display("set_int_value_from_plusargs returning %0d for %s plusarg", x, arg);
      return 1;
    end
    else begin
      x = dflt;
      if(q==0) $display("set_int_value_from_plusargs returning %0d default as %s plusarg not set", x, arg);
      return 0;
    end
  endfunction

  // set a bit value from plusargs; return 1 if plusarg was passed
  function bit set_bit_value_from_plusargs (input string arg, input bit dflt=0, output bit x);
    int dflt_int;
    int x_int;
    bit waspassed;
    dflt_int = dflt;
    waspassed = set_int_value_from_plusargs(arg, dflt_int, x_int, 1'b1);  // last arg for no printout within
    if(waspassed)
      if (x_int!=1'b1 && x_int!=1'b0 ) 
        $error("set_bit_value_from_plusargs : invalid value for bit passed in %s plusarg (%0d)", arg, x_int);
    x = x_int[0];  // returned by reference
    if(waspassed==1) $display("set_bit_value_from_plusargs returning %0d for %s plusarg", x, arg);
    if(waspassed==0) $display("set_bit_value_from_plusargs returning %0d default as %s plusarg not set", x, arg);
    return waspassed;
  endfunction

  function mem_acc mem_access_addr_decode (input logic[39:0] addr);
    mem_acc dst;
    
    logic [39:0] xm0_addr_base;
    logic [39:0] xm0_addr_size;
    logic [39:0] xm1_addr_base;
    logic [39:0] xm1_addr_size;
    logic [39:0] xm2_addr_base;
    logic [39:0] xm2_addr_size;
    logic [39:0] xm3_addr_base;
    logic [39:0] xm3_addr_size;
    
    logic [39:0] grp0_slc0_dm_base;
    logic [39:0] grp0_slc0_dm_size;
    logic [39:0] grp0_slc0_am_base;
    logic [39:0] grp0_slc0_am_size;
    logic [39:0] grp0_slc0_vm_base;
    logic [39:0] grp0_slc0_vm_size;
    logic [39:0] grp0_slc1_dm_base;
    logic [39:0] grp0_slc1_dm_size;
    logic [39:0] grp0_slc1_am_base;
    logic [39:0] grp0_slc1_am_size;
    logic [39:0] grp0_slc1_vm_base;
    logic [39:0] grp0_slc1_vm_size;
    logic [39:0] grp0_slc2_dm_base;
    logic [39:0] grp0_slc2_dm_size;
    logic [39:0] grp0_slc2_am_base;
    logic [39:0] grp0_slc2_am_size;
    logic [39:0] grp0_slc2_vm_base;
    logic [39:0] grp0_slc2_vm_size;
    logic [39:0] grp0_slc3_dm_base;
    logic [39:0] grp0_slc3_dm_size;
    logic [39:0] grp0_slc3_am_base;
    logic [39:0] grp0_slc3_am_size;
    logic [39:0] grp0_slc3_vm_base;
    logic [39:0] grp0_slc3_vm_size;
    logic [39:0] grp1_slc0_dm_base;
    logic [39:0] grp1_slc0_dm_size;
    logic [39:0] grp1_slc0_am_base;
    logic [39:0] grp1_slc0_am_size;
    logic [39:0] grp1_slc0_vm_base;
    logic [39:0] grp1_slc0_vm_size;
    logic [39:0] grp1_slc1_dm_base;
    logic [39:0] grp1_slc1_dm_size;
    logic [39:0] grp1_slc1_am_base;
    logic [39:0] grp1_slc1_am_size;
    logic [39:0] grp1_slc1_vm_base;
    logic [39:0] grp1_slc1_vm_size;
    logic [39:0] grp1_slc2_dm_base;
    logic [39:0] grp1_slc2_dm_size;
    logic [39:0] grp1_slc2_am_base;
    logic [39:0] grp1_slc2_am_size;
    logic [39:0] grp1_slc2_vm_base;
    logic [39:0] grp1_slc2_vm_size;
    logic [39:0] grp1_slc3_dm_base;
    logic [39:0] grp1_slc3_dm_size;
    logic [39:0] grp1_slc3_am_base;
    logic [39:0] grp1_slc3_am_size;
    logic [39:0] grp1_slc3_vm_base;
    logic [39:0] grp1_slc3_vm_size;
    logic [39:0] grp2_slc0_dm_base;
    logic [39:0] grp2_slc0_dm_size;
    logic [39:0] grp2_slc0_am_base;
    logic [39:0] grp2_slc0_am_size;
    logic [39:0] grp2_slc0_vm_base;
    logic [39:0] grp2_slc0_vm_size;
    logic [39:0] grp2_slc1_dm_base;
    logic [39:0] grp2_slc1_dm_size;
    logic [39:0] grp2_slc1_am_base;
    logic [39:0] grp2_slc1_am_size;
    logic [39:0] grp2_slc1_vm_base;
    logic [39:0] grp2_slc1_vm_size;
    logic [39:0] grp2_slc2_dm_base;
    logic [39:0] grp2_slc2_dm_size;
    logic [39:0] grp2_slc2_am_base;
    logic [39:0] grp2_slc2_am_size;
    logic [39:0] grp2_slc2_vm_base;
    logic [39:0] grp2_slc2_vm_size;
    logic [39:0] grp2_slc3_dm_base;
    logic [39:0] grp2_slc3_dm_size;
    logic [39:0] grp2_slc3_am_base;
    logic [39:0] grp2_slc3_am_size;
    logic [39:0] grp2_slc3_vm_base;
    logic [39:0] grp2_slc3_vm_size;
    logic [39:0] grp3_slc0_dm_base;
    logic [39:0] grp3_slc0_dm_size;
    logic [39:0] grp3_slc0_am_base;
    logic [39:0] grp3_slc0_am_size;
    logic [39:0] grp3_slc0_vm_base;
    logic [39:0] grp3_slc0_vm_size;
    logic [39:0] grp3_slc1_dm_base;
    logic [39:0] grp3_slc1_dm_size;
    logic [39:0] grp3_slc1_am_base;
    logic [39:0] grp3_slc1_am_size;
    logic [39:0] grp3_slc1_vm_base;
    logic [39:0] grp3_slc1_vm_size;
    logic [39:0] grp3_slc2_dm_base;
    logic [39:0] grp3_slc2_dm_size;
    logic [39:0] grp3_slc2_am_base;
    logic [39:0] grp3_slc2_am_size;
    logic [39:0] grp3_slc2_vm_base;
    logic [39:0] grp3_slc2_vm_size;
    logic [39:0] grp3_slc3_dm_base;
    logic [39:0] grp3_slc3_dm_size;
    logic [39:0] grp3_slc3_am_base;
    logic [39:0] grp3_slc3_am_size;
    logic [39:0] grp3_slc3_vm_base;
    logic [39:0] grp3_slc3_vm_size;
    
    logic [39:0] dccm0_base;
    logic [39:0] dccm0_size;
    logic [39:0] dccm1_base;
    logic [39:0] dccm1_size;
    logic [39:0] csm_base;
    logic [39:0] csm_size;

    xm0_addr_base = 40'h0;
    xm0_addr_size = 40'h00_8000_0000;
    xm1_addr_base = 40'h00_8000_0000;
    xm1_addr_size = 40'h00_6000_0000;
    xm2_addr_base = 40'h00_f000_0000;
    xm2_addr_size = 40'h00_1000_0000;
    xm3_addr_base = 40'h01_0000_0000;
    xm3_addr_size = 40'hff_0000_0000;

    grp0_slc0_dm_base = 40'h00_e000_0000 + 0*40'h00_0040_0000 + 0*4*40'h00_0040_0000;
    grp0_slc0_dm_size = 40'h00_0008_0000;
    grp0_slc0_am_base = 40'h00_e010_0000 + 0*40'h00_0040_0000 + 0*4*40'h00_0040_0000;
    grp0_slc0_am_size = 40'h00_0010_0000;
    grp0_slc0_vm_base = 40'h00_e020_0000 + 0*40'h00_0040_0000 + 0*4*40'h00_0040_0000;
    grp0_slc0_vm_size = 40'h00_0020_0000;
    grp0_slc1_dm_base = 40'h00_e000_0000 + 1*40'h00_0040_0000 + 0*4*40'h00_0040_0000;
    grp0_slc1_dm_size = 40'h00_0008_0000;
    grp0_slc1_am_base = 40'h00_e010_0000 + 1*40'h00_0040_0000 + 0*4*40'h00_0040_0000;
    grp0_slc1_am_size = 40'h00_0010_0000;
    grp0_slc1_vm_base = 40'h00_e020_0000 + 1*40'h00_0040_0000 + 0*4*40'h00_0040_0000;
    grp0_slc1_vm_size = 40'h00_0020_0000;
    grp0_slc2_dm_base = 40'h00_e000_0000 + 2*40'h00_0040_0000 + 0*4*40'h00_0040_0000;
    grp0_slc2_dm_size = 40'h00_0008_0000;
    grp0_slc2_am_base = 40'h00_e010_0000 + 2*40'h00_0040_0000 + 0*4*40'h00_0040_0000;
    grp0_slc2_am_size = 40'h00_0010_0000;
    grp0_slc2_vm_base = 40'h00_e020_0000 + 2*40'h00_0040_0000 + 0*4*40'h00_0040_0000;
    grp0_slc2_vm_size = 40'h00_0020_0000;
    grp0_slc3_dm_base = 40'h00_e000_0000 + 3*40'h00_0040_0000 + 0*4*40'h00_0040_0000;
    grp0_slc3_dm_size = 40'h00_0008_0000;
    grp0_slc3_am_base = 40'h00_e010_0000 + 3*40'h00_0040_0000 + 0*4*40'h00_0040_0000;
    grp0_slc3_am_size = 40'h00_0010_0000;
    grp0_slc3_vm_base = 40'h00_e020_0000 + 3*40'h00_0040_0000 + 0*4*40'h00_0040_0000;
    grp0_slc3_vm_size = 40'h00_0020_0000;
    grp1_slc0_dm_base = 40'h00_e000_0000 + 0*40'h00_0040_0000 + 1*4*40'h00_0040_0000;
    grp1_slc0_dm_size = 40'h00_0008_0000;
    grp1_slc0_am_base = 40'h00_e010_0000 + 0*40'h00_0040_0000 + 1*4*40'h00_0040_0000;
    grp1_slc0_am_size = 40'h00_0010_0000;
    grp1_slc0_vm_base = 40'h00_e020_0000 + 0*40'h00_0040_0000 + 1*4*40'h00_0040_0000;
    grp1_slc0_vm_size = 40'h00_0020_0000;
    grp1_slc1_dm_base = 40'h00_e000_0000 + 1*40'h00_0040_0000 + 1*4*40'h00_0040_0000;
    grp1_slc1_dm_size = 40'h00_0008_0000;
    grp1_slc1_am_base = 40'h00_e010_0000 + 1*40'h00_0040_0000 + 1*4*40'h00_0040_0000;
    grp1_slc1_am_size = 40'h00_0010_0000;
    grp1_slc1_vm_base = 40'h00_e020_0000 + 1*40'h00_0040_0000 + 1*4*40'h00_0040_0000;
    grp1_slc1_vm_size = 40'h00_0020_0000;
    grp1_slc2_dm_base = 40'h00_e000_0000 + 2*40'h00_0040_0000 + 1*4*40'h00_0040_0000;
    grp1_slc2_dm_size = 40'h00_0008_0000;
    grp1_slc2_am_base = 40'h00_e010_0000 + 2*40'h00_0040_0000 + 1*4*40'h00_0040_0000;
    grp1_slc2_am_size = 40'h00_0010_0000;
    grp1_slc2_vm_base = 40'h00_e020_0000 + 2*40'h00_0040_0000 + 1*4*40'h00_0040_0000;
    grp1_slc2_vm_size = 40'h00_0020_0000;
    grp1_slc3_dm_base = 40'h00_e000_0000 + 3*40'h00_0040_0000 + 1*4*40'h00_0040_0000;
    grp1_slc3_dm_size = 40'h00_0008_0000;
    grp1_slc3_am_base = 40'h00_e010_0000 + 3*40'h00_0040_0000 + 1*4*40'h00_0040_0000;
    grp1_slc3_am_size = 40'h00_0010_0000;
    grp1_slc3_vm_base = 40'h00_e020_0000 + 3*40'h00_0040_0000 + 1*4*40'h00_0040_0000;
    grp1_slc3_vm_size = 40'h00_0020_0000;
    grp2_slc0_dm_base = 40'h00_e000_0000 + 0*40'h00_0040_0000 + 2*4*40'h00_0040_0000;
    grp2_slc0_dm_size = 40'h00_0008_0000;
    grp2_slc0_am_base = 40'h00_e010_0000 + 0*40'h00_0040_0000 + 2*4*40'h00_0040_0000;
    grp2_slc0_am_size = 40'h00_0010_0000;
    grp2_slc0_vm_base = 40'h00_e020_0000 + 0*40'h00_0040_0000 + 2*4*40'h00_0040_0000;
    grp2_slc0_vm_size = 40'h00_0020_0000;
    grp2_slc1_dm_base = 40'h00_e000_0000 + 1*40'h00_0040_0000 + 2*4*40'h00_0040_0000;
    grp2_slc1_dm_size = 40'h00_0008_0000;
    grp2_slc1_am_base = 40'h00_e010_0000 + 1*40'h00_0040_0000 + 2*4*40'h00_0040_0000;
    grp2_slc1_am_size = 40'h00_0010_0000;
    grp2_slc1_vm_base = 40'h00_e020_0000 + 1*40'h00_0040_0000 + 2*4*40'h00_0040_0000;
    grp2_slc1_vm_size = 40'h00_0020_0000;
    grp2_slc2_dm_base = 40'h00_e000_0000 + 2*40'h00_0040_0000 + 2*4*40'h00_0040_0000;
    grp2_slc2_dm_size = 40'h00_0008_0000;
    grp2_slc2_am_base = 40'h00_e010_0000 + 2*40'h00_0040_0000 + 2*4*40'h00_0040_0000;
    grp2_slc2_am_size = 40'h00_0010_0000;
    grp2_slc2_vm_base = 40'h00_e020_0000 + 2*40'h00_0040_0000 + 2*4*40'h00_0040_0000;
    grp2_slc2_vm_size = 40'h00_0020_0000;
    grp2_slc3_dm_base = 40'h00_e000_0000 + 3*40'h00_0040_0000 + 2*4*40'h00_0040_0000;
    grp2_slc3_dm_size = 40'h00_0008_0000;
    grp2_slc3_am_base = 40'h00_e010_0000 + 3*40'h00_0040_0000 + 2*4*40'h00_0040_0000;
    grp2_slc3_am_size = 40'h00_0010_0000;
    grp2_slc3_vm_base = 40'h00_e020_0000 + 3*40'h00_0040_0000 + 2*4*40'h00_0040_0000;
    grp2_slc3_vm_size = 40'h00_0020_0000;
    grp3_slc0_dm_base = 40'h00_e000_0000 + 0*40'h00_0040_0000 + 3*4*40'h00_0040_0000;
    grp3_slc0_dm_size = 40'h00_0008_0000;
    grp3_slc0_am_base = 40'h00_e010_0000 + 0*40'h00_0040_0000 + 3*4*40'h00_0040_0000;
    grp3_slc0_am_size = 40'h00_0010_0000;
    grp3_slc0_vm_base = 40'h00_e020_0000 + 0*40'h00_0040_0000 + 3*4*40'h00_0040_0000;
    grp3_slc0_vm_size = 40'h00_0020_0000;
    grp3_slc1_dm_base = 40'h00_e000_0000 + 1*40'h00_0040_0000 + 3*4*40'h00_0040_0000;
    grp3_slc1_dm_size = 40'h00_0008_0000;
    grp3_slc1_am_base = 40'h00_e010_0000 + 1*40'h00_0040_0000 + 3*4*40'h00_0040_0000;
    grp3_slc1_am_size = 40'h00_0010_0000;
    grp3_slc1_vm_base = 40'h00_e020_0000 + 1*40'h00_0040_0000 + 3*4*40'h00_0040_0000;
    grp3_slc1_vm_size = 40'h00_0020_0000;
    grp3_slc2_dm_base = 40'h00_e000_0000 + 2*40'h00_0040_0000 + 3*4*40'h00_0040_0000;
    grp3_slc2_dm_size = 40'h00_0008_0000;
    grp3_slc2_am_base = 40'h00_e010_0000 + 2*40'h00_0040_0000 + 3*4*40'h00_0040_0000;
    grp3_slc2_am_size = 40'h00_0010_0000;
    grp3_slc2_vm_base = 40'h00_e020_0000 + 2*40'h00_0040_0000 + 3*4*40'h00_0040_0000;
    grp3_slc2_vm_size = 40'h00_0020_0000;
    grp3_slc3_dm_base = 40'h00_e000_0000 + 3*40'h00_0040_0000 + 3*4*40'h00_0040_0000;
    grp3_slc3_dm_size = 40'h00_0008_0000;
    grp3_slc3_am_base = 40'h00_e010_0000 + 3*40'h00_0040_0000 + 3*4*40'h00_0040_0000;
    grp3_slc3_am_size = 40'h00_0010_0000;
    grp3_slc3_vm_base = 40'h00_e020_0000 + 3*40'h00_0040_0000 + 3*4*40'h00_0040_0000;
    grp3_slc3_vm_size = 40'h00_0020_0000;

    csm_base = 40'h00_e800_0000;
    csm_size = 40'h00_0400_0000;

    dccm0_base = 40'h00_e600_0000;
    dccm0_size = 40'h00_0004_0000;
    dccm1_base = 40'h00_e604_0000;
    dccm1_size = 40'h00_0004_0000;

    if (((addr>=xm0_addr_base                 && 
        addr<(xm0_addr_base + xm0_addr_size)) ||
        (addr>=xm1_addr_base                  && 
        addr<(xm1_addr_base + xm1_addr_size)) ||
        (addr>=xm2_addr_base                  && 
        addr<(xm2_addr_base + xm2_addr_size)) ||
        (addr>=xm3_addr_base                  && 
        addr<(xm3_addr_base + xm3_addr_size)))
    ) begin
        dst = XM_ACCESS;
    end
    else if (addr>=dccm0_base        && 
        addr<(dccm0_base+dccm0_size) 
    ) begin
        dst = L2_DCCM0_ACCESS;
    end
    else if (addr>=dccm1_base        && 
        addr<(dccm1_base+dccm1_size) 
    ) begin
        dst = L2_DCCM1_ACCESS;
    end
    else if (addr>=grp0_slc0_dm_base                     && 
        addr<(grp0_slc0_dm_base+grp0_slc0_dm_size) 
    ) begin
        dst = GRP0_SLC0_DM_ACCESS;
    end
    else if (addr>=grp0_slc0_am_base                     && 
        addr<(grp0_slc0_am_base+grp0_slc0_am_size) 
    ) begin
        dst = GRP0_SLC0_AM_ACCESS;
    end
    else if (addr>=grp0_slc0_vm_base                     && 
        addr<(grp0_slc0_vm_base+grp0_slc0_vm_size) 
    ) begin
        dst = GRP0_SLC0_VM_ACCESS;
    end
    else if (addr>=grp0_slc1_dm_base                     && 
        addr<(grp0_slc1_dm_base+grp0_slc1_dm_size) 
    ) begin
        dst = GRP0_SLC1_DM_ACCESS;
    end
    else if (addr>=grp0_slc1_am_base                     && 
        addr<(grp0_slc1_am_base+grp0_slc1_am_size) 
    ) begin
        dst = GRP0_SLC1_AM_ACCESS;
    end
    else if (addr>=grp0_slc1_vm_base                     && 
        addr<(grp0_slc1_vm_base+grp0_slc1_vm_size) 
    ) begin
        dst = GRP0_SLC1_VM_ACCESS;
    end
    else if (addr>=grp0_slc2_dm_base                     && 
        addr<(grp0_slc2_dm_base+grp0_slc2_dm_size) 
    ) begin
        dst = GRP0_SLC2_DM_ACCESS;
    end
    else if (addr>=grp0_slc2_am_base                     && 
        addr<(grp0_slc2_am_base+grp0_slc2_am_size) 
    ) begin
        dst = GRP0_SLC2_AM_ACCESS;
    end
    else if (addr>=grp0_slc2_vm_base                     && 
        addr<(grp0_slc2_vm_base+grp0_slc2_vm_size) 
    ) begin
        dst = GRP0_SLC2_VM_ACCESS;
    end
    else if (addr>=grp0_slc3_dm_base                     && 
        addr<(grp0_slc3_dm_base+grp0_slc3_dm_size) 
    ) begin
        dst = GRP0_SLC3_DM_ACCESS;
    end
    else if (addr>=grp0_slc3_am_base                     && 
        addr<(grp0_slc3_am_base+grp0_slc3_am_size) 
    ) begin
        dst = GRP0_SLC3_AM_ACCESS;
    end
    else if (addr>=grp0_slc3_vm_base                     && 
        addr<(grp0_slc3_vm_base+grp0_slc3_vm_size) 
    ) begin
        dst = GRP0_SLC3_VM_ACCESS;
    end
    else if (addr>=grp1_slc0_dm_base                     && 
        addr<(grp1_slc0_dm_base+grp1_slc0_dm_size) 
    ) begin
        dst = GRP1_SLC0_DM_ACCESS;
    end
    else if (addr>=grp1_slc0_am_base                     && 
        addr<(grp1_slc0_am_base+grp1_slc0_am_size) 
    ) begin
        dst = GRP1_SLC0_AM_ACCESS;
    end
    else if (addr>=grp1_slc0_vm_base                     && 
        addr<(grp1_slc0_vm_base+grp1_slc0_vm_size) 
    ) begin
        dst = GRP1_SLC0_VM_ACCESS;
    end
    else if (addr>=grp1_slc1_dm_base                     && 
        addr<(grp1_slc1_dm_base+grp1_slc1_dm_size) 
    ) begin
        dst = GRP1_SLC1_DM_ACCESS;
    end
    else if (addr>=grp1_slc1_am_base                     && 
        addr<(grp1_slc1_am_base+grp1_slc1_am_size) 
    ) begin
        dst = GRP1_SLC1_AM_ACCESS;
    end
    else if (addr>=grp1_slc1_vm_base                     && 
        addr<(grp1_slc1_vm_base+grp1_slc1_vm_size) 
    ) begin
        dst = GRP1_SLC1_VM_ACCESS;
    end
    else if (addr>=grp1_slc2_dm_base                     && 
        addr<(grp1_slc2_dm_base+grp1_slc2_dm_size) 
    ) begin
        dst = GRP1_SLC2_DM_ACCESS;
    end
    else if (addr>=grp1_slc2_am_base                     && 
        addr<(grp1_slc2_am_base+grp1_slc2_am_size) 
    ) begin
        dst = GRP1_SLC2_AM_ACCESS;
    end
    else if (addr>=grp1_slc2_vm_base                     && 
        addr<(grp1_slc2_vm_base+grp1_slc2_vm_size) 
    ) begin
        dst = GRP1_SLC2_VM_ACCESS;
    end
    else if (addr>=grp1_slc3_dm_base                     && 
        addr<(grp1_slc3_dm_base+grp1_slc3_dm_size) 
    ) begin
        dst = GRP1_SLC3_DM_ACCESS;
    end
    else if (addr>=grp1_slc3_am_base                     && 
        addr<(grp1_slc3_am_base+grp1_slc3_am_size) 
    ) begin
        dst = GRP1_SLC3_AM_ACCESS;
    end
    else if (addr>=grp1_slc3_vm_base                     && 
        addr<(grp1_slc3_vm_base+grp1_slc3_vm_size) 
    ) begin
        dst = GRP1_SLC3_VM_ACCESS;
    end
    else if (addr>=grp2_slc0_dm_base                     && 
        addr<(grp2_slc0_dm_base+grp2_slc0_dm_size) 
    ) begin
        dst = GRP2_SLC0_DM_ACCESS;
    end
    else if (addr>=grp2_slc0_am_base                     && 
        addr<(grp2_slc0_am_base+grp2_slc0_am_size) 
    ) begin
        dst = GRP2_SLC0_AM_ACCESS;
    end
    else if (addr>=grp2_slc0_vm_base                     && 
        addr<(grp2_slc0_vm_base+grp2_slc0_vm_size) 
    ) begin
        dst = GRP2_SLC0_VM_ACCESS;
    end
    else if (addr>=grp2_slc1_dm_base                     && 
        addr<(grp2_slc1_dm_base+grp2_slc1_dm_size) 
    ) begin
        dst = GRP2_SLC1_DM_ACCESS;
    end
    else if (addr>=grp2_slc1_am_base                     && 
        addr<(grp2_slc1_am_base+grp2_slc1_am_size) 
    ) begin
        dst = GRP2_SLC1_AM_ACCESS;
    end
    else if (addr>=grp2_slc1_vm_base                     && 
        addr<(grp2_slc1_vm_base+grp2_slc1_vm_size) 
    ) begin
        dst = GRP2_SLC1_VM_ACCESS;
    end
    else if (addr>=grp2_slc2_dm_base                     && 
        addr<(grp2_slc2_dm_base+grp2_slc2_dm_size) 
    ) begin
        dst = GRP2_SLC2_DM_ACCESS;
    end
    else if (addr>=grp2_slc2_am_base                     && 
        addr<(grp2_slc2_am_base+grp2_slc2_am_size) 
    ) begin
        dst = GRP2_SLC2_AM_ACCESS;
    end
    else if (addr>=grp2_slc2_vm_base                     && 
        addr<(grp2_slc2_vm_base+grp2_slc2_vm_size) 
    ) begin
        dst = GRP2_SLC2_VM_ACCESS;
    end
    else if (addr>=grp2_slc3_dm_base                     && 
        addr<(grp2_slc3_dm_base+grp2_slc3_dm_size) 
    ) begin
        dst = GRP2_SLC3_DM_ACCESS;
    end
    else if (addr>=grp2_slc3_am_base                     && 
        addr<(grp2_slc3_am_base+grp2_slc3_am_size) 
    ) begin
        dst = GRP2_SLC3_AM_ACCESS;
    end
    else if (addr>=grp2_slc3_vm_base                     && 
        addr<(grp2_slc3_vm_base+grp2_slc3_vm_size) 
    ) begin
        dst = GRP2_SLC3_VM_ACCESS;
    end
    else if (addr>=grp3_slc0_dm_base                     && 
        addr<(grp3_slc0_dm_base+grp3_slc0_dm_size) 
    ) begin
        dst = GRP3_SLC0_DM_ACCESS;
    end
    else if (addr>=grp3_slc0_am_base                     && 
        addr<(grp3_slc0_am_base+grp3_slc0_am_size) 
    ) begin
        dst = GRP3_SLC0_AM_ACCESS;
    end
    else if (addr>=grp3_slc0_vm_base                     && 
        addr<(grp3_slc0_vm_base+grp3_slc0_vm_size) 
    ) begin
        dst = GRP3_SLC0_VM_ACCESS;
    end
    else if (addr>=grp3_slc1_dm_base                     && 
        addr<(grp3_slc1_dm_base+grp3_slc1_dm_size) 
    ) begin
        dst = GRP3_SLC1_DM_ACCESS;
    end
    else if (addr>=grp3_slc1_am_base                     && 
        addr<(grp3_slc1_am_base+grp3_slc1_am_size) 
    ) begin
        dst = GRP3_SLC1_AM_ACCESS;
    end
    else if (addr>=grp3_slc1_vm_base                     && 
        addr<(grp3_slc1_vm_base+grp3_slc1_vm_size) 
    ) begin
        dst = GRP3_SLC1_VM_ACCESS;
    end
    else if (addr>=grp3_slc2_dm_base                     && 
        addr<(grp3_slc2_dm_base+grp3_slc2_dm_size) 
    ) begin
        dst = GRP3_SLC2_DM_ACCESS;
    end
    else if (addr>=grp3_slc2_am_base                     && 
        addr<(grp3_slc2_am_base+grp3_slc2_am_size) 
    ) begin
        dst = GRP3_SLC2_AM_ACCESS;
    end
    else if (addr>=grp3_slc2_vm_base                     && 
        addr<(grp3_slc2_vm_base+grp3_slc2_vm_size) 
    ) begin
        dst = GRP3_SLC2_VM_ACCESS;
    end
    else if (addr>=grp3_slc3_dm_base                     && 
        addr<(grp3_slc3_dm_base+grp3_slc3_dm_size) 
    ) begin
        dst = GRP3_SLC3_DM_ACCESS;
    end
    else if (addr>=grp3_slc3_am_base                     && 
        addr<(grp3_slc3_am_base+grp3_slc3_am_size) 
    ) begin
        dst = GRP3_SLC3_AM_ACCESS;
    end
    else if (addr>=grp3_slc3_vm_base                     && 
        addr<(grp3_slc3_vm_base+grp3_slc3_vm_size) 
    ) begin
        dst = GRP3_SLC3_VM_ACCESS;
    end
    else if (addr>=csm_base      && 
        addr<(csm_base+csm_size) &&
        addr[16:15] == 0        
    ) begin
        dst = GRP0_SCM_ACCESS;
    end
    else if (addr>=csm_base      && 
        addr<(csm_base+csm_size) &&
        addr[16:15] == 1        
    ) begin
        dst = GRP1_SCM_ACCESS;
    end
    else if (addr>=csm_base      && 
        addr<(csm_base+csm_size) &&
        addr[16:15] == 2        
    ) begin
        dst = GRP2_SCM_ACCESS;
    end
    else if (addr>=csm_base      && 
        addr<(csm_base+csm_size) &&
        addr[16:15] == 3        
    ) begin
        dst = GRP3_SCM_ACCESS;
    end
    else
    begin
      dst = NO_HIT;
    end

  return dst;

  endfunction

endpackage

import npu_tb_pkg::*;

`endif
