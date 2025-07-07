// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2013 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary 
// work of Synopsys, Inc., and is fully protected under copyright and 
// trade secret laws. You may not view, use, disclose, copy, or distribute 
// this file or any information contained herein except pursuant to a 
// valid written license from Synopsys, Inc.
//
// Certain materials incorporated herein are copyright (C) 2010 - 2011, The
// University Court of the University of Edinburgh. All Rights Reserved.
//
// The entire notice above must be reproduced on all authorized copies.
//
// Description:
// @p
//  The ?tlb module implements the micro-TLB for itlb and dtlb.
//  This is a fully associative memory with N entries and one or two lookup 
//  ports.
//  The ?tlb supports update (entry write) by parallel write of an entire
//  entry, and also supports read access (of a full entry) to support aux
//  read.
//
// @e
//
//  This .vpp source file must be pre-processed with the Verilog Pre-Processor
//  (VPP) to produce the equivalent .v file using a command such as:
//
//   vpp +q +o cpu.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"


//POST_PROCESS { prefix:"//D:", wire_prefix:"t_", edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  rst: "rst", edc: { suffix: "auto", clk: "edc_clk", rst: "rst", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_err", encode_reset: true, add_reset_sensitivity: 1 } }

//D: error_signal { name: "uitlb_err" }

module npuarc_itlb (

  ////////// General input signals ///////////////////////////////////////////
  //
  input                          clk,            // Processor clock
  input                          rst,            // Global reset
  input                          rst_init_disable_r,

  input                          clk2_en,
  input                          mmu_ready,      // jtlb initialized
  // clock control / idle status
  input                          mmu_clock_req_r,
  output                         utlb_active,

  // Enable uTLB
  input                          utlb_en_r,      // Enable TLB lookups
  output                         va_in_transl_range,

  // spyglass disable_block W240
  // SMD: input not used
  // SJ:  unused in some configs
  input                          mpu_en_r,
  // spyglass enable_block W240
  input                          lkup0_cancel,   // cpu pipe flushed (any flush)
  input                          tlb_busy,       // possible write of serializing
                                                 // mmu reg
  input                          hlt_stall,
  // debug ops not translated
  input                          debug_op,       // ld/st originated from debug

  // Shared lib
  input                          shared_en_r,    // Shared lib enable (PID)
  input [`npuarc_SASID_RANGE]           sasid_r,        // Current pid slib membership

  ////////// Interface to translation client(s): fetch or dmp ///////////////
  //
  // Request bus 0 for uTLB lookup ---------------------------------------------
  input                          lkup0_valid_r,
  input  [`npuarc_LKUP_VADDR_RANGE]     lkup0_vaddr_r,
  input  [`npuarc_PD0_ASID_RANGE]       lkup0_asid_r,

  output reg                     lkup0_stall_nxt,

  // Lookup result 
  output reg                     rslt0_valid, // includes jtlb search if nec
  output                         rslt0_match,
  output                         rslt0_multiple_match,

  output     [`npuarc_PADDR_RANGE]      rslt0_paddr,
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range:0-2
// LJ:  Some addr bits unused
  output reg [`npuarc_PADDR_RANGE]      rslt0_paddr_r,
// leda NTL_CON32 on
  output     [`npuarc_PD1_UA_RANGE]     rslt0_user_attr,
  output                         rslt0_wr_thru,
  output reg [`npuarc_PD1_PERM_RANGE]   rslt0_perm,
  output                         rslt0_cached,

  output                         rslt0_tlb_err,

  output reg                     rslt0_valid2,   // includes jtlb search if nec
  input                          rslt0_accept,


  ////////// Interface to jtlb //////////////////////////////////////////////
  //
  // Consolidated jtlb update request
  output reg                     jtlb_update_req,  // registered+2g outputs
  output reg  [`npuarc_PD0_VPN_RANGE]   jtlb_update_req_vpn,

  // jtlb response to update request
  input                          jrsp_update, 
  input                          jrsp_update_hit,
  input                          jrsp_multi_hit,
  input                          jrsp_tlb_err,

  // Entry data for update from jtlb; also used for lookups by jtlb
  input  [`npuarc_UTLB_ENTRY_RANGE]     entry_update_data, // new entry from jtlb
             
  // Inval / insert / update operations from jtlb
  input      [`npuarc_JCMD_RANGE]       jtlb_cmd_r,    // command from jtlb (aux)
  input      [`npuarc_ITLB_INDEX_RANGE] jtlb_index_r,  // Aux addr for read/write

  // Interface to read utlb entries
  output                         entry_rd_val,   // rd data valid
  output reg [`npuarc_UTLB_ENTRY_RANGE] entry_rd_data   // LR read data (entry)
);
 

////////////////////////////////////////////////////////////////////////////
// Internal Signals
////////////////////////////////////////////////////////////////////////////
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range:0-2
// LJ:  Some addr bits unused
  wire [`npuarc_PADDR_RANGE]         rslt0_paddr_a;
// leda NTL_CON32 on

  reg                         lkup0_jtlb_sel;

  reg [`npuarc_PD0_VPN_RANGE]        jtlb_update_req_vpn_r;


  wire [`npuarc_LKUP_VPN_RANGE]      lkup0_vpn_r;
  wire                        lkup_untransl_addr0_r;
  wire [`npuarc_PD1_PPN_RANGE]       rslt0_ppn;

  reg [2:0]                   lkup0_state_nxt;
  reg [2:0]                   lkup0_state_r;

  reg                         lookup0_op;
  // update request to jtlb
  reg                         jtlb_update0_req_nxt;
  reg  [`npuarc_PD0_VPN_RANGE]       jtlb_update0_req_vpn_nxt;
  reg                         jtlb_update0_req_ce;

  reg                         jtlb_update_req_r;

  reg [`npuarc_ITLB_ENTRIES_RANGE]   jcmd_inval_se;
  reg                         jcmd_insert;
  wire                        jcmd_write;

  wire                        jreq_needs_lkup;
  wire                        sasid_force_match;
 
  wire                        jrsp_match_size;
  assign jrsp_match_size    = entry_update_data[`npuarc_PCKD_PTE_SIZE];

  // lookup for insert must use promiscuous match to detect any
  // overlap with existing entries
  reg                         eager_match;

  // uTLB Update / LRU logic
  wire                        inval_entry_avail;
  wire [`npuarc_ITLB_ENTRIES_RANGE]  inval_entry_1h;
  wire [`npuarc_ITLB_ENTRIES_RANGE]  lru_entry_1h;
  reg  [`npuarc_ITLB_ENTRIES_RANGE]  entry_update_1h;

// leda NTL_CON13A off
// LMD: non driving internal net Range: ...
// LJ:  rd/wr perm bits unused, masked (pruned during synthesis)
  wire [`npuarc_UTLB_ENTRY_RANGE]    entry_rd_data_prel;   // LR read data (entry)
// leda NTL_CON13A on

//---------------------------------------------------------------------
// utlb signals
//---------------------------------------------------------------------
  wire                         req0_valid_r;
  wire [`npuarc_PD0_VPN_RANGE]        req0_vpn_r;
  wire [`npuarc_PD0_ASID_RANGE]       req0_asid_r;

  // utlb rslt outputs (raw results, before bypass)
  wire                         rsltu0_match;
  wire                         rsltu0_miss;
// leda NTL_CON13A off
// LMD: non driving internal net Range: ...
// LJ:  Unused in this instance of utlb
  wire [`npuarc_ITLB_INDEX_RANGE]     rsltu0_match_index;
// leda NTL_CON13A on
  wire                         rsltu0_match_size;
  wire                         rsltu0_multiple_match;
  
  wire [`npuarc_PD1_PPN_RANGE]        rsltu0_ppn;
  wire [`npuarc_PD1_UA_RANGE]         rsltu0_user_attr;
  wire                         rsltu0_wr_thru;
  wire [`npuarc_PD1_PERM_RANGE]       rsltu0_perm;
  wire                         rsltu0_cached;

  wire                         rslt0_match_size;

  wire                         jrsp_update0_hit;
  wire                         jrsp_update0;

  // for jcmd_insert (if no match, replace lru or invalid entry)
  reg                          rsltu0_match_r;

  // for jtlb inval and replace ops
  //--------------------------------
  wire [`npuarc_ITLB_ENTRIES_RANGE]   rsltu0_entry_match_nh;
  reg  [`npuarc_ITLB_ENTRIES_RANGE]   rsltu0_entry_match_nh_r;

  // one-hot with only a single bit set (bit with the lowest index)
  wire [`npuarc_ITLB_ENTRIES_RANGE]   rsltu0_entry_match_1h;
  wire [`npuarc_ITLB_ENTRIES_RANGE]   rsltu0_match_1h;
  reg  [`npuarc_ITLB_ENTRIES_RANGE]   rsltu0_entry_match_1h_r;
  reg  [`npuarc_ITLB_ENTRIES_RANGE]   lru_update_r; 

  wire [`npuarc_ITLB_ENTRIES_RANGE]   invalidate_entries;
  wire                         inval_utlb;  // Inval all utlb entries
  wire                         reset_lru;   // reset lru state

  // track lookup request during tlb busy period
  reg  lkup0_start;
  wire lkup_pend_set;
  wire lkup_pend_clr;
  reg  lkup_pend_r;

  wire rslt0_perm_kx;
  wire rslt0_perm_ux;


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Misc comb logic                                                        //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

assign lkup0_vpn_r  = lkup0_vaddr_r[`npuarc_LKUP_VPN_RANGE]; // vpn bits

// upper 2 GB are untranslated space
assign va_in_transl_range = ~lkup0_vpn_r[`npuarc_LKUP_VPN_MSB];

assign lkup_untransl_addr0_r = ~va_in_transl_range;

assign rslt0_tlb_err = jrsp_update & jrsp_tlb_err;

// translated (physical) address result
assign rslt0_paddr_a = (~rslt0_match || rslt0_multiple_match
                       ) ?
                         // miss, just pass through entire VA
                          {8'h0, lkup0_vaddr_r} :
                         // hit, determine VPN size, pass thru page offset
                         (rslt0_match && rslt0_match_size) ?
                           // super-page hit, wider page-offset field
                           {rslt0_ppn[`npuarc_PPN_SZ1_RANGE],
                            lkup0_vaddr_r[`npuarc_MMU_POF_SZ1_RANGE]} :
                           // normal-page hit
                           {rslt0_ppn[`npuarc_PPN_SZ0_RANGE],
                            lkup0_vaddr_r[`npuarc_MMU_POF_SZ0_RANGE]};

// pass through paddr to output in the same clock as tlb lookup result,
// hold paddr for multiple clocks (until new lookup result)
assign rslt0_paddr  = (rslt0_valid) ?
                         rslt0_paddr_a :
                         rslt0_paddr_r;

// leda G_551_1_C off
// leda NTL_RST03 off
// leda S_1C_R off
// LMD: A flipflop without reset
// LJ:  Datapath
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
always @(posedge clk)
begin: paddr_reg_PROC
  if (rslt0_valid)
  begin
    rslt0_paddr_r <= rslt0_paddr_a;
  end
end
// leda NTL_RST03 on
// leda S_1C_R on
// leda G_551_1_C on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Decode jtlb commands                                                   //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
 
// Read selected entry (indep of state)
//----------------------------------------------
assign entry_rd_val = (jtlb_cmd_r == `npuarc_JCMD_READ);


// decode jtlb ops that require lookup op
//----------------------------------------
assign jreq_needs_lkup = (jtlb_cmd_r == `npuarc_JCMD_INSERT)
                       | (jtlb_cmd_r == `npuarc_JCMD_DELETE)
                       | (jtlb_cmd_r == `npuarc_JCMD_DELETEIS)
                       ;

assign sasid_force_match = (jtlb_cmd_r == `npuarc_JCMD_DELETEIS)
                       ;

// Invalidate all uTLB entries (indep of state)
//----------------------------------------------
assign inval_utlb = (jtlb_cmd_r == `npuarc_JCMD_INVAL_ALL);

assign reset_lru  = (jtlb_cmd_r == `npuarc_JCMD_RESET_LRU)
                  | inval_utlb;


// Write indexed entry (indep of state)
//----------------------------------------------
assign jcmd_write = 1'b0;
// invalidate selected (matched) entries or all entries
assign invalidate_entries = jcmd_inval_se
                     | {`npuarc_ITLB_NUM_ENTRIES{inval_utlb}};
  

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Logic for sharing update request / response output port to jtlb        //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : jtlb_update_req_PROC
// update request to jtlb
  jtlb_update_req_vpn  = jtlb_update_req_vpn_r;

  jtlb_update_req      =  mmu_ready
                       &  jtlb_update_req_r 
                       & (~jrsp_update)
                       & (~lkup0_cancel);
end

assign jrsp_update0_hit  = jrsp_update_hit & jtlb_update_req_r;
assign jrsp_update0      = jrsp_update     & jtlb_update_req_r;


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Logic for sharing lookup input port (0) between dmp and jtlb           //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
  
// valid lookup requst to utlb generated for fetch and jtlb ops
// (1) fetch lookup only if utlb_en_r is 1 (when 0, pass vpn through to ppn)
// (2) jtlb ops are independent of utlb_en_r
assign  req0_valid_r = (  (lkup0_valid_r | lkup_pend_r)
                        & utlb_en_r
                        & (~lkup0_cancel)
                        & (~debug_op)
                        & (~lkup_untransl_addr0_r))    // (1)
                     |  jreq_needs_lkup;               // (2)


// select jtlb input for lookup : port 0
assign {req0_vpn_r, req0_asid_r}  = lkup0_jtlb_sel ? 
         {entry_update_data[`npuarc_PCKD_PTE_VPN_RANGE],      //pckd
          entry_update_data[`npuarc_PCKD_PTE_ASID_RANGE]}:
         {lkup0_vpn_r[`npuarc_PD0_VPN_RANGE], lkup0_asid_r};  //unpckd


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Mux for bypassing lookup result from jtlb to lookup port (0 or 1)      //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : rslt0_perm__PROC
  rslt0_perm = {`npuarc_PD1_PERM_WIDTH{1'b0}}; // default value, only exec perm bits used
  rslt0_perm[`npuarc_PD1_PERM_KX] = rslt0_perm_kx;
  rslt0_perm[`npuarc_PD1_PERM_UX] = rslt0_perm_ux;
end


// Bypass logic for result port 0
//
assign {rslt0_ppn,
        rslt0_user_attr,
        rslt0_wr_thru,
        rslt0_perm_kx,
        rslt0_perm_ux,
        rslt0_cached
        }  =

    // MMU disabled or debug access: pass-thru with all perms
    (~utlb_en_r | debug_op) ?
         {8'h0, lkup0_vpn_r,          // pass thru requesting vpn
          2'b00,                      // user attr
          1'b0,                       // write through
          2'b11,                      // both k, u exec permissions given
          1'b1 }:                     // Cached

    // upper 2GB, untranslated, pass-thru VA, (kernel only access)
    (lkup_untransl_addr0_r) ?
         {8'h0, lkup0_vpn_r,          // pass thru requesting vpn
          2'b00,                      // user attr
          1'b0,                       // write through
          1'b1,                       // kernel  exec perm only 
          mpu_en_r,                   // also user exec perm if mpu enabled (MPU will apply it's perms)
          1'b1 }:                     // Cached

    (jrsp_update0 & (~jrsp_update_hit)) ?
         // update miss: pass-thru orig vpn with no permissions
         {8'h0, lkup0_vpn_r,          // pass thru requesting vpn
          2'b00,                      // user attr
          1'b0,                       // write through
          2'b00,                      // no permissions given {kx,ux)
          1'b1 }:                     // Cached

    (jrsp_update0 &  jrsp_update_hit) ?
         // update hit: use ppn/perm from jtlb
         {entry_update_data[`npuarc_PCKD_PTE_PPN_RANGE],
          entry_update_data[`npuarc_PCKD_PTE_UA_RANGE],
          entry_update_data[`npuarc_PCKD_PTE_WR_THRU],
          entry_update_data[`npuarc_PCKD_PTE_PERM_KX],
          entry_update_data[`npuarc_PCKD_PTE_PERM_UX],
          entry_update_data[`npuarc_PCKD_PTE_CACHED]}:

         // No update, local utlb result
         {rsltu0_ppn,
          rsltu0_user_attr,
          rsltu0_wr_thru,
          rsltu0_perm[`npuarc_PD1_PERM_KX],
          rsltu0_perm[`npuarc_PD1_PERM_UX],
          rsltu0_cached};

// select jtlb result during update
assign rslt0_match = jrsp_update0 ? 
                        jrsp_update0_hit  : 
                       (  rsltu0_match
                       // declare match if untranslated address or tlb off
                        | lkup_untransl_addr0_r
                        | debug_op
                        | (~utlb_en_r));

// match page size for local or jtlb supplied matching entry
assign rslt0_match_size = jrsp_update0 ? jrsp_match_size :
                                             rsltu0_match_size;

// report multiple match error (occuring at jtlb or locally)
assign rslt0_multiple_match = utlb_en_r & (jrsp_update0 ? 
                                   jrsp_multi_hit : 
                                   rsltu0_multiple_match);
  
// Mask unused permission bits for aux read
// 
always @*
begin : mask_unused_perm_bits_PROC
  entry_rd_data = entry_rd_data_prel;
  entry_rd_data[`npuarc_PCKD_PTE_PERM_UW] = 1'b0;
  entry_rd_data[`npuarc_PCKD_PTE_PERM_UR] = 1'b0;
  entry_rd_data[`npuarc_PCKD_PTE_PERM_KW] = 1'b0;
  entry_rd_data[`npuarc_PCKD_PTE_PERM_KR] = 1'b0;
end


// leda W547 off
// LMD: Redundant case expression
// LJ:  Some inputs never asserted together
////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Form the write enables for Updating utlb entries                       //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
//  1. For jtlb update, if no inval entry avail, update the LRU entry
//  2. for JCMD_INSERT, if miss and if no inval entry avail, update the LRU 
//     entry
//  3. For jtlb update, if inval entry avail, update the inval entry
//     with lowest index
//  4. for JCMD_INSERT, if miss and if inval entry avail, update the inval
//     entry with lowest index
//  5. for JCMD_INSERT, if hit, update hit entry with lowest index and 
//     (elsewhere) inval other hit entries (if any)
//
// fyi: During invalidation only the valid bits of all entries are cleared.
//
always @* 
begin :  i_entry_write_PROC
  // Replace selected (lru) entry
  casez ({(jrsp_update0 & jrsp_update_hit & (~jrsp_multi_hit) & (~lkup0_cancel)),
          jcmd_insert, 
          rsltu0_match_r,  // raw port0 match ( <-jcmd )
          inval_entry_avail,
          jcmd_write
        })
    5'b1??0?,                                                    // (1)
    5'b0100?: entry_update_1h[0] = lru_entry_1h[0];            // (2)
    5'b1??1?,                                                    // (3)
    5'b0101?: entry_update_1h[0] = inval_entry_1h[0];          // (4)
    5'b011??: entry_update_1h[0] = rsltu0_entry_match_1h_r[0]; // (5)
    default:  entry_update_1h[0] = 1'b0;
  endcase
  // Replace selected (lru) entry
  casez ({(jrsp_update0 & jrsp_update_hit & (~jrsp_multi_hit) & (~lkup0_cancel)),
          jcmd_insert, 
          rsltu0_match_r,  // raw port0 match ( <-jcmd )
          inval_entry_avail,
          jcmd_write
        })
    5'b1??0?,                                                    // (1)
    5'b0100?: entry_update_1h[1] = lru_entry_1h[1];            // (2)
    5'b1??1?,                                                    // (3)
    5'b0101?: entry_update_1h[1] = inval_entry_1h[1];          // (4)
    5'b011??: entry_update_1h[1] = rsltu0_entry_match_1h_r[1]; // (5)
    default:  entry_update_1h[1] = 1'b0;
  endcase
  // Replace selected (lru) entry
  casez ({(jrsp_update0 & jrsp_update_hit & (~jrsp_multi_hit) & (~lkup0_cancel)),
          jcmd_insert, 
          rsltu0_match_r,  // raw port0 match ( <-jcmd )
          inval_entry_avail,
          jcmd_write
        })
    5'b1??0?,                                                    // (1)
    5'b0100?: entry_update_1h[2] = lru_entry_1h[2];            // (2)
    5'b1??1?,                                                    // (3)
    5'b0101?: entry_update_1h[2] = inval_entry_1h[2];          // (4)
    5'b011??: entry_update_1h[2] = rsltu0_entry_match_1h_r[2]; // (5)
    default:  entry_update_1h[2] = 1'b0;
  endcase
  // Replace selected (lru) entry
  casez ({(jrsp_update0 & jrsp_update_hit & (~jrsp_multi_hit) & (~lkup0_cancel)),
          jcmd_insert, 
          rsltu0_match_r,  // raw port0 match ( <-jcmd )
          inval_entry_avail,
          jcmd_write
        })
    5'b1??0?,                                                    // (1)
    5'b0100?: entry_update_1h[3] = lru_entry_1h[3];            // (2)
    5'b1??1?,                                                    // (3)
    5'b0101?: entry_update_1h[3] = inval_entry_1h[3];          // (4)
    5'b011??: entry_update_1h[3] = rsltu0_entry_match_1h_r[3]; // (5)
    default:  entry_update_1h[3] = 1'b0;
  endcase
end

// leda W547 on

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// States for the utlb state machine                                      //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
parameter LKUP_SM_IDLE    = 3'b000;  // No lkup or lkup/hit
parameter LKUP_SM_MISS    = 3'b001;  // update req pending to jtlb
parameter LKUP_SM_RSLT    = 3'b101;  // update req pending to jtlb
parameter LKUP_SM_INSERT  = 3'b010;  // lkup and repl hit or lru entry
parameter LKUP_SM_DELETE  = 3'b011;  // lkup and inval hit entry(ies)

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Combinational logic defining the UTLB FSM                              //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
//
//   - lookup requests (lkup*,jreq*) are early (registered at driving module)
//   - utlb lkup results (rslt*) are late signals in the same clk as request
//
//   - on hit, sm stays in idle state, simply returns results (PPN, perm...)
//     + updates lru bits
//
//   - on miss, sm goes to dmiss till updated (-> lkup_stall outputs)
//     + on jtlb miss, returns miss exception, undefined result outputs,
//       returns to idle
//     + on jhit (update/replace), jtlb result written to entry and bypassed
//       to _nxt results (before  output registers), rslt outputs are valid 
//       on next clock.
//
//   - on inval_utlb, lkup could get serviced from current entry values 
//     (entries / lru bits will be cleared at posedge) but since the jtlb cmd
//     causing the utlb invalidate (aux reg write) is serializing, all younger
//     lookups are to be discarded due to restart, so no need to service lkup
//     till after the invalidate completes (initiating restart).


// --------------------------------------------------------------------------
// LOOKUP PORT 0 (incl jtlb requests)
// --------------------------------------------------------------------------
//
always @*
begin : utlb_fsm0_PROC

  lkup0_state_nxt      = lkup0_state_r;
  lkup0_stall_nxt      = 1'b0;
  lkup0_jtlb_sel       = 1'b0; // default is ifu
  lookup0_op           = 1'b0;
  lkup0_start          = 1'b0;
  eager_match          = 1'b0;
  rslt0_valid          = 1'b0;
  rslt0_valid2         = 1'b0;

  // for jtlb related ops
  jtlb_update0_req_ce   = 1'b0;
  jtlb_update0_req_nxt      = 1'b0;
  jtlb_update0_req_vpn_nxt  = lkup0_vpn_r[`npuarc_PD0_VPN_RANGE];
  jcmd_inval_se         = `npuarc_ITLB_NUM_ENTRIES'd0;
  jcmd_insert           = 1'b0;

  
  case (lkup0_state_r)

    // default / idle state, stay here till miss or jreq_needs_lkup
    //
    LKUP_SM_IDLE:  
    begin
      lkup0_state_nxt  = LKUP_SM_IDLE;

      // give jtlb precedence over local lookups
      //
      if (  tlb_busy
          )
      begin
        // stall if busy or new entry only during req
        lkup0_stall_nxt = (lkup0_valid_r | lkup_pend_r);

        // service jtlb operation
        if (jtlb_cmd_r != `npuarc_JCMD_IDLE)
        begin
          lkup0_jtlb_sel  = 1'b1;            // select jtlb input (vpn/asid...)
          case (jtlb_cmd_r)
            `npuarc_JCMD_DELETE,
            `npuarc_JCMD_DELETEIS: 
            begin
               lookup0_op = 1'b1;
               eager_match = 1'b1;
               lkup0_state_nxt = LKUP_SM_DELETE;
             //jcmd_inval_se  = rslt0_entry_match_1h;...wait till next clk to inval (timing?)
            end
            `npuarc_JCMD_INSERT: 
            begin
               lookup0_op = 1'b1;
               eager_match = 1'b1;
               lkup0_state_nxt = LKUP_SM_INSERT;
            end
// spyglass disable_block W193 
// SMD: empty statements
// SJ:  empty default statements kept
            default: ;
// spyglass enable_block W193
          endcase
        end

      end

      // if no jtlb op and not busy
      //
      else
      if (  (lkup0_valid_r | lkup_pend_r)
          & (~lkup0_cancel)      // itlb: Don't accept new lookup if restart
         )
      begin
        lkup0_start = 1'b1;
        lookup0_op  = ~lkup_untransl_addr0_r & utlb_en_r & (~debug_op);

        // miss utlb, stall and query jtlb
        if (    rsltu0_miss 
            & (~lkup_untransl_addr0_r)
            &   utlb_en_r 
            & (~debug_op))
        begin
          lkup0_stall_nxt     = 1'b1;
          rslt0_valid         = 1'b0;
          rslt0_valid2        = 1'b0;

          lkup0_state_nxt     = LKUP_SM_MISS;
          jtlb_update0_req_nxt = 1'b1;
          jtlb_update0_req_ce = 1'b1;
        end
        else

        // hit utlb or not translated
        begin
          rslt0_valid  = 1'b1;
          rslt0_valid2 = 1'b1;
        end
      end

    end
  
    LKUP_SM_MISS:  // data lkup miss pending (wait for update)
    begin
      if (lkup0_cancel)      // itlb: abandon lookup if restart
      begin
        lkup0_state_nxt = LKUP_SM_IDLE;
      end
      else

      if (jrsp_update)
      begin
        rslt0_valid  = 1'b1;
        rslt0_valid2 = 1'b1;
        if (rslt0_accept)
          lkup0_state_nxt = LKUP_SM_IDLE;
        else
          lkup0_stall_nxt  = 1'b1; 
          lkup0_state_nxt = LKUP_SM_RSLT;
      end

      else
      begin
        // stall further fetch/lkup requests till update + 1 clk 
        // (for new entry to be written and avail for lookup)
        lkup0_stall_nxt  = 1'b1; 
        jtlb_update0_req_nxt = 1'b1;
        lkup0_state_nxt = LKUP_SM_MISS;
      end
    end
  
    LKUP_SM_RSLT:
    begin
      lkup0_stall_nxt  = 1'b1; 
      rslt0_valid  = 1'b0; // single clock cycle
      rslt0_valid2 = 1'b1; // extended
      if (rslt0_accept)
        lkup0_state_nxt = LKUP_SM_IDLE;
      else
        lkup0_state_nxt = LKUP_SM_RSLT;
    end
  
    LKUP_SM_DELETE:  // inval matching entry(ies)
    begin
      lkup0_stall_nxt = 1'b1;            // busy w/jtlb op next cycle
      lkup0_state_nxt = LKUP_SM_IDLE;
      jcmd_inval_se = rsltu0_entry_match_nh_r;
    end
  
    LKUP_SM_INSERT:  // insert new or replace matching entry(ies)
    begin
      lkup0_stall_nxt = 1'b1;            // busy w/jtlb op next cycle
      lkup0_state_nxt = LKUP_SM_IDLE;
      jcmd_insert    = 1'b1;
      jcmd_inval_se  = rsltu0_entry_match_nh_r // inval all copies of old entry except
                     & (~rsltu0_entry_match_1h_r) // the lowest index match
                     ;
    end
// spyglass disable_block W193 
// SMD: empty statements
// SJ:  empty default statements kept
    default: ;
// spyglass enable_block W193    
  endcase // case (lkup0_state_r)

end


// utlb control regs : port 0
//
always @(posedge clk or posedge rst)
begin: lkup0_ctlregs_PROC
  if (rst)
  begin
    lkup0_state_r <= 3'b0;
  end
  else
  begin
    lkup0_state_r <= lkup0_state_nxt;
  end
end // block: lkup0_ctlregs_PROC

  
// utlb update request register
//
always @(posedge clk or posedge rst)
begin: update_req_PROC
  if (rst)
  begin
    jtlb_update_req_r <= 1'b0;
  end
  else
  begin
    jtlb_update_req_r <= jtlb_update0_req_nxt;
  end
end // block: lkup0_ctlregs_PROC


// leda NTL_RST03 off
// leda S_1C_R off
// LMD: All registers must be asynchronously set or reset
// LJ:  Datapath
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
// jtlb interface update request output regs
//
always @(posedge clk)
begin: update_req_vpn_PROC
  if (jtlb_update0_req_ce)
  begin
    jtlb_update_req_vpn_r  <= jtlb_update0_req_vpn_nxt;
  end
end // block: utlb_update_PROC
// leda NTL_RST03 on
// leda S_1C_R on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01
  

// utlb / mmu active : clock request
assign utlb_active          = (lkup0_valid_r  | lkup_pend_r)
                            | (lkup0_state_r != LKUP_SM_IDLE)
                            | (jtlb_cmd_r != `npuarc_JCMD_IDLE)
                            | mmu_clock_req_r;

// Match result vector register
//
always @(posedge clk or posedge rst)
begin : lkup_rslt_vec_outreg_PROC
  if (rst)
  begin
    rsltu0_match_r          <= 1'b0;
    rsltu0_entry_match_nh_r <= `npuarc_ITLB_NUM_ENTRIES'd0;
    rsltu0_entry_match_1h_r <= `npuarc_ITLB_NUM_ENTRIES'd0;
  end
  else if (lookup0_op)
  begin
    rsltu0_match_r          <= rsltu0_match;
    rsltu0_entry_match_nh_r <= rsltu0_entry_match_nh;
    rsltu0_entry_match_1h_r <= rsltu0_entry_match_1h;
  end
end

   
// update plru in the clk after result valid (timing opt)
always @(posedge clk or posedge rst)
begin : rslt0_valid_PROC
  if (rst)
  begin
    lru_update_r            <= `npuarc_ITLB_NUM_ENTRIES'd0;
  end
  else
  begin
    lru_update_r            <= (rsltu0_match_1h    // utlb match (one-hot)
                             |  entry_update_1h);
  end
end

   
// Remember that a lookup was requested during tlb busy period
//
assign lkup_pend_set = lkup0_valid_r & ((tlb_busy & hlt_stall) | ((lkup0_state_r == LKUP_SM_RSLT) && (rslt0_accept == 1'b0)));
assign lkup_pend_clr = lkup0_cancel | lkup0_start;
wire   lkup_pend_cg0;
assign lkup_pend_cg0 = lkup_pend_clr | lkup_pend_set;


always @(posedge clk or posedge rst)
begin : lkup_pend_PROC
  if (rst)
  begin
    lkup_pend_r   <= 1'b0;
  end
  else if (lkup_pend_cg0)  // update only on clr or set
  begin
    lkup_pend_r   <= !lkup_pend_clr; // clear has priority

  end
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// LRU logic instance                                                     //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

// don't advance lru state if no result valid (preemmpted by jcmd)
assign rsltu0_match_1h = rsltu0_entry_match_1h
                       & {`npuarc_ITLB_NUM_ENTRIES{clk2_en & rslt0_valid}}
                       ;
       

npuarc_plru4 u_plru4 (
  .clk           (clk),
  .rst           (rst),
  .lru_clear     (reset_lru),
  .match_entry   (lru_update_r),     // registered lru advance
  .lru_entry     (lru_entry_1h)      // entry selected for replacement
);


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// micro-TLB instance                                                     //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
 
npuarc_uitlb u_uitlb (
  .clk                       (clk),            // Processor clock
  .rst                       (rst),            // Global reset
  .rst_init_disable_r        (rst_init_disable_r),

  .alloc_entries             (3'd4),


  //  Shared lib
  .shared_en_r               (shared_en_r),    // Shared lib enable (PID)
  .sasid_r                   (sasid_r),        // Current pid slib membership
  .sasid_force_match         (sasid_force_match),
  .eager_match               (eager_match),

  ////////// Look-up port //////////////////////////////////////////////////
  // 
  // Request  for uTLB lookup
  .req0_valid_r              (req0_valid_r),
  .req0_vpn_r                (req0_vpn_r),
  .req0_asid_r               (req0_asid_r),

  //  Lookup result
  .rslt0_match               (rsltu0_match),
  .rslt0_miss                (rsltu0_miss),
  .rslt0_match_index         (rsltu0_match_index),
  .rslt0_match_size          (rsltu0_match_size),
  .rslt0_multiple_match      (rsltu0_multiple_match),
  // for lru logic
  .rslt0_entry_match         (rsltu0_entry_match_nh),
  .rslt0_entry_match_1h      (rsltu0_entry_match_1h),

  .rslt0_ppn_out             (rsltu0_ppn),
  .rslt0_user_attr_out       (rsltu0_user_attr),
  .rslt0_wr_thru_out         (rsltu0_wr_thru),
  .rslt0_perm_out            (rsltu0_perm),
  .rslt0_cached_out          (rsltu0_cached),

  ////////// Invalidate select uTLB entries /////////////////////////////////
  .invalidate_entries        (invalidate_entries), // Invalidate select entries
  .unlock_entries            (1'b0),               // Unlock all entries

  .inval_entry_avail         (inval_entry_avail), // Current invalid entries
  .inval_entry_1h            (inval_entry_1h), // lowest index invalid entry
  ////////// Interface to read utlb entries /////////////////////////////////
  //
  .entry_rd_val              (entry_rd_val),  // read operation this cycle
  .entry_rd_addr             (jtlb_index_r),  // Aux address for read/write
  .entry_rd_data             (entry_rd_data_prel), // LR read data (entry)

  .entry_update_1h           (entry_update_1h),
  .entry_update_data         (entry_update_data)  // new entry from jtlb
);
  

endmodule // `module_name
