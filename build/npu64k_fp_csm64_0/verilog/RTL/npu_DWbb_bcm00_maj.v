// reuse-pragma startSub BCM_FILE_REMOVAL [IncludeIf @RM_BCM00_MAJ==0 %subText]
// reuse-pragma process_ifdef standard

// reuse-pragma startSub COLLAPSE_CR_HDR [IncludeIf 0 %subText]
//
//                  (C) COPYRIGHT 2006 - 2022 SYNOPSYS, INC.
//                            ALL RIGHTS RESERVED
//
//  This software and the associated documentation are confidential and
//  proprietary to Synopsys, Inc.  Your use or disclosure of this
//  software is subject to the terms and conditions of a written
//  license agreement between you, or your company, and Synopsys, Inc.
//
//  The entire notice above must be reproduced on all authorized copies.
// reuse-pragma endSub COLLAPSE_CR_HDR
// reuse-pragma startSub [::RCE::insert_copyright] endSub
//
// reuse-pragma startSub COLLAPSE_BLOCK [IncludeIf 0 %subText]
// Filename    : DWbb_bcm00_maj.v
// Revision    : $Id: $
// Author      : Rick Kelly    2/01/06
// reuse-pragma endSub COLLAPSE_BLOCK
// Description : DWbb_bcm00_maj.v Verilog module for DWbb
//
// DesignWare IP ID: b48afb6c
// reuse-pragma startSub COLLAPSE_BLOCK [IncludeIf 0 %subText]
// DesignWare_release: 2022.12
// reuse-pragma endSub COLLAPSE_BLOCK
//
////////////////////////////////////////////////////////////////////////////////
// reuse-pragma startSub COLLAPSE_BLOCK [IncludeIf 0 %subText]
//
// ABSTRACT: Majority Vote Logic with parameter based bus WIDTH
//
//              Parameters:     Valid Values
//              ==========      ============
//              WIDTH           [ 1 to 8192 ]
//
//              Input Ports:    Size    Description
//              ===========     ====    ===========
//              a               WIDTH   First voter input
//              b               WIDTH   Second voter input
//              c               WIDTH   Third voter input
//
//              Output Ports    Size    Description
//              ============    ====    ===========
//              z               WIDTH   Majority voted output bus
//
//
// MODIFIED:
//
//   10/25/20 ZHU   Removed embedded scripts because the commands will be
//                  added by coreTools (from ct/2020.03-SP4) according to
//                  user selections
//
// reuse-pragma endSub COLLAPSE_BLOCK


// verpp-pragma preserve_ifdefs DWC_MAJORITY_VOTE_CELL_SRC
module npu_DWbb_bcm00_maj (
    a,
    b,
    c,
    z
    );

parameter integer WIDTH        = 1;  // RANGE 1 to 8192


input  [WIDTH-1:0]      a;    // 1st voter data input bus
input  [WIDTH-1:0]      b;    // 2nd voter data input bus
input  [WIDTH-1:0]      c;    // 3rd voter data input bus
output [WIDTH-1:0]      z;    // majority voted data output bus

// spyglass disable_block Ac_conv01
// SMD: Synchronized sequential element(s) converge on combinational logic
// SJ: The single-bit signals converging into sequential elements are triplicated from the same signal at the source and run through parallel paths of synchronizers with the identical number of stages.  This synchronized convergence is intentional and directly supplies combinational logic that produces a majority vote result which is immune to non-gray code transitions.
// spyglass disable_block Ac_conv02
// SMD: Synchronizers converge on combinational logic
// SJ: The single-bit signals converging into the combinational logic are triplicated from the same signal at the source and run through parallel paths of synchronizers with the identical number of stages.  This synchronized convergence is intentional as the combinational logic produces a majority vote result which is immune to non-gray code transitions.
`ifdef DWC_MAJORITY_VOTE_CELL_SRC
  `DWC_MAJORITY_VOTE_CELL_SRC
`else
  assign z = (a & b) | (a & c) | (b & c);
`endif
// spyglass enable_block Ac_conv01
// spyglass enable_block Ac_conv02

// verpp-pragma process_ifdefs DWC_MAJORITY_VOTE_CELL_SRC
endmodule
// reuse-pragma process_ifdef all_branches
// reuse-pragma endSub BCM_FILE_REMOVAL
