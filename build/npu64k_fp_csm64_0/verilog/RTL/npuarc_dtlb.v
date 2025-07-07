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

//D: error_signal { name: "udtlb_err" }

module npuarc_dtlb (

  ////////// General input signals ///////////////////////////////////////////
  //
  input                          clk,            // Processor clock
  input                          rst,            // Global reset
  input                          rst_init_disable_r,

  // Enable uTLB
  input                          utlb_en_r,      // Enable TLB lookups
  output                         x2_da0_transl,
  // spyglass disable_block W240
  // SMD: input not used
  // SJ:  unused in some configs
  input                          mpu_en_r,
  // spyglass enable_block W240
  input                          wa_restart_r,   // cpu pipe flushed (any flush)
  input                          wa_hlt_restart_r,       // WA halt restart
  input                          wa_jtlb_lookup_start_r, // flush/replay due to dtlb miss

  input                          mmu_clock_req_r,

  // Access type: user/kernel mode, pid shared bit (common to all req ports)
  input                          debug_op,       // ld/st originated from debug
  input                          kernel_mode,    // has Kernel mode privileges
  input                          access_type_inst, // instr or data access
  input                          access_type_rd, // lkup for load (or ex) op
  input                          access_type_wr, // lkup for store (or ex) op

  // Shared lib
  input                          shared_en_r,    // Shared lib enable (PID)
  input [`npuarc_SASID_RANGE]           sasid_r,        // Current pid slib membership

  ////////// Interface to translation client(s): fetch or dmp ///////////////
  //
  // Request bus 0 for uTLB lookup ---------------------------------------------
  input                          lkup0_valid_r,
  input  [`npuarc_LKUP_VADDR_RANGE]     lkup0_vaddr_r,
  input  [`npuarc_PD0_ASID_RANGE]       lkup0_asid_r,

  // Lookup result 
  output     [`npuarc_PADDR_RANGE]      rslt0_paddr,
// leda NTL_CON13A off
// LMD: non driving internal net Range: ...
// LJ:  unused page attributes (future)
  output     [`npuarc_PD1_UA_RANGE]     rslt0_user_attr,
  output                         rslt0_wr_thru,
// leda NTL_CON13A on
  output                         rslt0_cached,

  // Request bus 1 for uTLB lookup ---------------------------------------------
  input                          lkup1_valid_r,
  input  [`npuarc_LKUP_VADDR_RANGE]     lkup1_vaddr_r,
  input  [`npuarc_PD0_ASID_RANGE]       lkup1_asid_r,

  // Lookup result 
  output     [`npuarc_PADDR_RANGE]      rslt1_paddr,
// leda NTL_CON13A off
// LMD: non driving internal net Range: ...
// LJ:  unused page attributes (future)
  output     [`npuarc_PD1_UA_RANGE]     rslt1_user_attr,
  output                         rslt1_wr_thru,
// leda NTL_CON13A on
  output                         rslt1_cached,


  input                          x2_pass,
  input      [1:0]               x2_size_r,
  input                          x2_pref_r,
  output     [1:0]               dc2_dtlb_efa_mux,
  output     [1:0]               dc2_dtlb_miss,
  output                         dc2_dtlb_miss_excpn,
  output                         dc2_dtlb_ovrlp_excpn,
  output                         dc2_dtlb_protv_excpn,
  output                         dc2_dtlb_ecc_error,

  output                         utlb_active,

  ////////// Interface to jtlb //////////////////////////////////////////////
  //
  // Consolidated jtlb update request
  output reg                     jtlb_update_req,  // registered+2g output
  output reg  [`npuarc_PD0_VPN_RANGE]   jtlb_update_req_vpn,

  // jtlb response to update request
  input                          jrsp_update, 
  input                          jrsp_update_hit,
  input                          jrsp_multi_hit,
  input                          jrsp_tlb_err,

  // Entry data for update from jtlb; also used for lookups by jtlb
  input  [`npuarc_UTLB_ENTRY_RANGE]     entry_update_data, // new entry from jtlb
             
  // Inval / insert / update operations from jtlb
  input [`npuarc_JCMD_RANGE]           jtlb_cmd_r,    // command from jtlb (aux)
  input [`npuarc_DTLB_INDEX_RANGE]     jtlb_index_r,  // Aux addr for read/write
  input [7:0]         aux_memseg_r,
  // Interface to read utlb entries
  output                         entry_rd_val,   // rd data valid
  output reg [`npuarc_UTLB_ENTRY_RANGE] entry_rd_data   // LR read data (entry)
);
 

////////////////////////////////////////////////////////////////////////////
// Internal Signals
////////////////////////////////////////////////////////////////////////////


  reg                         lkup0_jtlb_sel;

  reg [`npuarc_PD0_VPN_RANGE]        jtlb_update_req_vpn_r;


  wire [`npuarc_LKUP_VPN_RANGE]      lkup0_vpn_r;
  wire                        lkup_untransl_addr0_r;

  wire                        rslt0_match;
  wire                        rslt0_multiple_match;
  wire                        rslt0_prot_viol;
  reg  [`npuarc_PD1_PERM_RANGE]      rslt0_perm;
  wire [`npuarc_PD1_PPN_RANGE]       rslt0_ppn;

  reg [1:0]                   lkup0_state_nxt;
  reg [1:0]                   lkup0_state_r;

  // update request to jtlb
  reg                         jtlb_update0_req_nxt;
  reg                         jtlb_update0_req_r;
  reg  [`npuarc_PD0_VPN_RANGE]       jtlb_update0_req_vpn_nxt;
  reg                         jtlb_update0_req_ce;

  wire [`npuarc_LKUP_VPN_RANGE]      lkup1_vpn_r;
  wire                        lkup_untransl_addr1_r;

  wire                        rslt1_match;
  wire                        rslt1_multiple_match;
  wire                        rslt1_prot_viol;
  reg  [`npuarc_PD1_PERM_RANGE]      rslt1_perm;
  wire [`npuarc_PD1_PPN_RANGE]       rslt1_ppn;

  reg [1:0]                   lkup1_state_nxt;
  reg [1:0]                   lkup1_state_r;

  // update request to jtlb
  reg                         jtlb_update1_req_nxt;
  reg                         jtlb_update1_req_r;
  reg  [`npuarc_PD0_VPN_RANGE]       jtlb_update1_req_vpn_nxt;
  reg                         jtlb_update1_req_ce;

  reg                         lookup0_op;

  reg                         jtlb_update_req_r;

  reg [`npuarc_DTLB_ENTRIES_RANGE]   jcmd_inval_se;
  reg                         jcmd_insert;
  wire                        jcmd_write;

  wire                        jrsp_update_op;
  wire                        jrsp_update_miss;
  wire                        jreq_needs_lkup;
  wire                        sasid_force_match;
 
  wire                        jrsp_match_size;
  assign jrsp_match_size    = entry_update_data[`npuarc_PCKD_PTE_SIZE];

  assign x2_da0_transl      = ~lkup_untransl_addr0_r;

  // lookup for insert must use promiscuous match to detect any
  // overlap with existing entries
  reg                         eager_match;

  // uTLB Update / LRU logic
  wire                        inval_entry_avail;
  wire [`npuarc_DTLB_ENTRIES_RANGE]  inval_entry_1h;
  wire [`npuarc_DTLB_ENTRIES_RANGE]  lru_entry_1h;
  reg  [`npuarc_DTLB_ENTRIES_RANGE]  entry_update_1h;

// leda NTL_CON13A off
// LMD: non driving internal net Range: ...
// LJ:  exec perm bits unused, masked (pruned during synthesis)
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
  wire [`npuarc_DTLB_INDEX_RANGE]     rsltu0_match_index;
// leda NTL_CON13A on
  wire                         rsltu0_match_size;
  wire                         rsltu0_multiple_match;
  
  wire [`npuarc_PD1_PPN_RANGE]        rsltu0_ppn;
  wire [`npuarc_PD1_UA_RANGE]         rsltu0_user_attr;
  wire                         rsltu0_wr_thru;
  wire [`npuarc_PD1_PERM_RANGE]       rsltu0_perm;
  wire                         rsltu0_cached;

  wire                         rslt0_match_size;

  // When an update is returned from jtlb,
  //  if hit, bypass result to rslt_* outputs while capturing the new entry, 
  //  else if miss, capture address, etc. for reporting miss exception.

// leda NTL_CON13A off
// LMD: non driving internal net Range: ...
// LJ:  Unused in logic; used by TB probe
  reg                          update0_pend;
  wire                         jrsp_update0_hit;
  wire                         jrsp_update0_miss;
  wire                         jrsp_update0;
// leda NTL_CON13A on


  wire                         req1_valid_r;
  wire [`npuarc_PD0_VPN_RANGE]        req1_vpn_r;
  wire [`npuarc_PD0_ASID_RANGE]       req1_asid_r;

  // utlb rslt outputs (raw results, before bypass)
  wire                         rsltu1_match;
  wire                         rsltu1_miss;
// leda NTL_CON13A off
// LMD: non driving internal net Range: ...
// LJ:  Unused in this instance of utlb
  wire [`npuarc_DTLB_INDEX_RANGE]     rsltu1_match_index;
// leda NTL_CON13A on
  wire                         rsltu1_match_size;
  wire                         rsltu1_multiple_match;
  
  wire [`npuarc_PD1_PPN_RANGE]        rsltu1_ppn;
  wire [`npuarc_PD1_UA_RANGE]         rsltu1_user_attr;
  wire                         rsltu1_wr_thru;
  wire [`npuarc_PD1_PERM_RANGE]       rsltu1_perm;
  wire                         rsltu1_cached;

  wire                         rslt1_match_size;

  // When an update is returned from jtlb,
  //  if hit, bypass result to rslt_* outputs while capturing the new entry, 
  //  else if miss, capture address, etc. for reporting miss exception.

// leda NTL_CON13A off
// LMD: non driving internal net Range: ...
// LJ:  Unused in logic; used by TB probe
  reg                          update1_pend;
  wire                         jrsp_update1_hit;
  wire                         jrsp_update1_miss;
  wire                         jrsp_update1;
// leda NTL_CON13A on


  // for jcmd_insert (if no match, replace lru or invalid entry)
  reg                          rslt0_valid;
  reg                          rsltu0_match_r;

  // for jtlb inval and replace ops
  //--------------------------------
  wire [`npuarc_DTLB_ENTRIES_RANGE]   rsltu0_entry_match_nh;
  reg  [`npuarc_DTLB_ENTRIES_RANGE]   rsltu0_entry_match_nh_r;

  // one-hot with only a single bit set (bit with the lowest index)
  wire [`npuarc_DTLB_ENTRIES_RANGE]   rsltu0_entry_match_1h;
  wire [`npuarc_DTLB_ENTRIES_RANGE]   rsltu0_match_1h;
  reg  [`npuarc_DTLB_ENTRIES_RANGE]   rsltu0_entry_match_1h_r;
  reg  [`npuarc_DTLB_ENTRIES_RANGE]   lru_update_r; 

// leda NTL_CON13A off
// LMD: non driving internal net Range: ...
// LJ:  Unused in logic; used by TB probe
  wire [`npuarc_DTLB_ENTRIES_RANGE]   rsltu1_entry_match;
  wire [`npuarc_DTLB_ENTRIES_RANGE]   rsltu1_entry_match_1h;
// leda NTL_CON13A on

  wire [`npuarc_DTLB_ENTRIES_RANGE]   invalidate_entries;
  wire                         inval_utlb;  // Inval all utlb entries
  wire                         reset_lru;   // reset lru state

wire                 wa_extern_restart; // wa_restart, not due to dtlb miss replay

wire                 new_update_request;

reg    [1:0]         missed_va_valid;     // valid VA excpn candidate stored in mva
wire                 missed_va_valid_set;
wire                 missed_va_valid_clr;
wire   [1:0]         missed_va_matches_lkup;

// jtlb response attributes (error condistions) carried with missed_va_valid
// (which dtlb port owned the jtlb response is remembered to determine
//  the exception fault address)
reg                  jtlb_ecc_err_excpn;
reg                  jtlb_ecc_err_port;
wire                 jtlb_ecc_err_port1;
wire                 jtlb_ecc_err_port0;

reg                  jtlb_multi_match_excpn;
reg                  jtlb_multi_match_port;
wire                 jtlb_multi_match_port1;
wire                 jtlb_multi_match_port0;

wire                 rslt_utlb_miss_excpn; // VA missed dtlb/jtlb

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Misc comb logic                                                        //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

// if lkup0 is hit and entry page size is x...and lkup1 is miss, detect false
// miss by checking addr/size/pageSize; if false miss suppress update req.
  wire               lkup1_page_cross;
  reg                lkup1_npage_cross;
  reg                lkup1_spage_cross;
  wire               rsltu1_match_prel;
  wire               rsltu1_miss_prel; 

//   wire [`PD0_VPN_RANGE]    jrsp_update_vpn;
//   assign jrsp_update_vpn = entry_update_data[`PCKD_PTE_VPN_RANGE];

// port0 result page size: rsltu0_match_size
  assign lkup1_page_cross = rsltu0_match_size ?
                              lkup1_spage_cross: 
                              lkup1_npage_cross;

  
// detect normal-page cross
//
always @*
begin : lkup1_npage_cross_PROC
  // Byte   -> never crosses
  // Half   -> crosses when [(11111)]
  // Word   -> crosses when [(111, > 00)]
  // Double -> crosses when [(11,  > 000)]
  //
  case (x2_size_r)
  2'b01:
    // Half-Word
    //
    lkup1_npage_cross = (& lkup0_vaddr_r[11:0]);
  2'b10:
    // Word
    //
    lkup1_npage_cross = (  (& lkup0_vaddr_r[11:2])
                         & (| lkup0_vaddr_r [1:0]));
  2'b11:
    // Double Word
    //
    lkup1_npage_cross = (  (& lkup0_vaddr_r[11:3])
                         & (| lkup0_vaddr_r [2:0]));
  default:
    // Byte
    //
    lkup1_npage_cross = 1'b0;
  endcase  
end

// detect super-page cross
//
always @*
begin : lkup1_spage_cross_PROC
  // Byte   -> never crosses
  // Half   -> crosses when [(11111)]
  // Word   -> crosses when [(111, > 00)]
  // Double -> crosses when [(11,  > 000)]
  //
  case (x2_size_r)
  2'b01:
    // Half-Word
    //
    lkup1_spage_cross = (& lkup0_vaddr_r[20:0]);
  2'b10:
    // Word
    //
    lkup1_spage_cross = (  (& lkup0_vaddr_r[20:2])
                         & (| lkup0_vaddr_r [1:0]));
  2'b11:
    // Double Word
    //
    lkup1_spage_cross = (  (& lkup0_vaddr_r[20:3])
                         & (| lkup0_vaddr_r [2:0]));
  default:
    // Byte
    //
    lkup1_spage_cross = 1'b0;
  endcase  
end


assign rsltu1_match  = (rsltu1_match_prel | (~lkup1_page_cross));
assign rsltu1_miss  =  (rsltu1_miss_prel &  lkup1_page_cross);

// Declare miss if either port misses
assign dc2_dtlb_miss        =   {2{utlb_en_r & (~debug_op)}}
                              & {  (~rslt1_match & lkup1_page_cross),
                                   (~rslt0_match)}
                              ;
assign dc2_dtlb_miss_excpn  = utlb_en_r & rslt_utlb_miss_excpn;

assign dc2_dtlb_ovrlp_excpn = utlb_en_r & (
                              (rslt0_multiple_match)
                            | (rslt1_multiple_match   & lkup1_page_cross)
                            | (jtlb_multi_match_excpn & (|missed_va_matches_lkup)));//& jrsp_update     );

// lookup0 is valid and it has 2bit ecc error
//
assign dc2_dtlb_ecc_error   = jtlb_ecc_err_excpn & req0_valid_r;

assign jtlb_ecc_err_port1 = jtlb_ecc_err_excpn &   jtlb_ecc_err_port;
assign jtlb_ecc_err_port0 = jtlb_ecc_err_excpn & (~jtlb_ecc_err_port);


// result 1 is valid only if result 0 is valid
//   
wire   rslt1_valid_hit;

// The following remembers there is a page cross and a port 1 hit
//
assign rslt1_valid_hit        = ~(lkup1_page_cross & (~rslt1_match));

// jtlb had a multi match excpn on port 1
//
assign jtlb_multi_match_port1 = jtlb_multi_match_excpn & missed_va_matches_lkup[1] & jtlb_multi_match_port;

// jtlb had a multi match excpn on port 0
//
assign jtlb_multi_match_port0 = jtlb_multi_match_excpn & missed_va_matches_lkup[0] & (~jtlb_multi_match_port);

assign dc2_dtlb_protv_excpn = utlb_en_r & (
                              (rslt0_match & rslt0_prot_viol & rslt1_valid_hit)
                            | (rslt0_match & rslt1_match & rslt1_prot_viol & lkup1_page_cross));

// efa_mux selects the port 0 address vs port 1 address
//    
assign dc2_dtlb_efa_mux     = {   { (rslt_utlb_miss_excpn & (~rslt1_match) & lkup1_page_cross),
                                    (rslt_utlb_miss_excpn & (~rslt0_match))
                                  }
                                | { ((rslt1_multiple_match | jtlb_multi_match_port1) & lkup1_page_cross), 
                                     (rslt0_multiple_match | jtlb_multi_match_port0)
                                  }
                                | { (jtlb_ecc_err_port1 & lkup1_page_cross), 
                                     jtlb_ecc_err_port0
                                  }
                                | { (rslt0_match & rslt1_match & rslt1_prot_viol & lkup1_page_cross),
                                    (rslt0_match & rslt0_prot_viol & rslt1_valid_hit)
                                   }
                              };


assign lkup0_vpn_r  = lkup0_vaddr_r[`npuarc_LKUP_VPN_RANGE]; // vpn bits

// upper 2 GB are untranslated space for both itlb/dtlb
assign lkup_untransl_addr0_r = lkup0_vpn_r[`npuarc_LKUP_VPN_MSB];

// Result paddr is translated PPN concat with size appropriate page offset
// (if pae, append 0 or memseg (for debug op))
assign rslt0_paddr  = (~rslt0_match || rslt0_multiple_match
                         ) ? 
                         // miss, just pass through entire VA
                          {(aux_memseg_r & {8{debug_op}}),
                          lkup0_vaddr_r} :
                         // hit, determine VPN size, pass thru page offset
                         (rslt0_match && rslt0_match_size) ?
                         // super-page hit, wider page-offset field
                         {rslt0_ppn[`npuarc_PPN_SZ1_RANGE],
                          lkup0_vaddr_r[`npuarc_MMU_POF_SZ1_RANGE]} :
                         // normal-page hit
                         {rslt0_ppn[`npuarc_PPN_SZ0_RANGE],
                          lkup0_vaddr_r[`npuarc_MMU_POF_SZ0_RANGE]};


assign lkup1_vpn_r  = lkup1_vaddr_r[`npuarc_LKUP_VPN_RANGE]; // vpn bits

// upper 2 GB are untranslated space for both itlb/dtlb
assign lkup_untransl_addr1_r = lkup1_vpn_r[`npuarc_LKUP_VPN_MSB];

// Result paddr is translated PPN concat with size appropriate page offset
// (if pae, append 0 or memseg (for debug op))
// address1 gets PA only if addr1 and addr0 are in different pages
assign rslt1_paddr  = (~((rslt1_match & lkup1_page_cross) 
                           |(rslt0_match & ~lkup1_page_cross)
                           ) 
                         | rslt1_multiple_match
                         ) ? 
                         // miss, just pass through entire VA
                          {(aux_memseg_r & {8{debug_op}}),
                          lkup1_vaddr_r} :
                         // hit, determine VPN size, pass thru page offset
                          (rslt1_match && rslt1_match_size) ?
                            // super-page hit, wider page-offset field
                            {rslt1_ppn[`npuarc_PPN_SZ1_RANGE],
                             lkup1_vaddr_r[`npuarc_MMU_POF_SZ1_RANGE]} :
                         // normal-page hit
                            {rslt1_ppn[`npuarc_PPN_SZ0_RANGE],
                             lkup1_vaddr_r[`npuarc_MMU_POF_SZ0_RANGE]};




////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Decode jtlb commands                                                   //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
 
// Read selected entry (indep of state)
//----------------------------------------------
assign entry_rd_val = (jtlb_cmd_r == `npuarc_JCMD_READ);


// decode jtlb update (write new entry) command
assign jrsp_update_miss =  jrsp_update
                        & (~jrsp_update_hit);

  
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
                     | {`npuarc_DTLB_NUM_ENTRIES{inval_utlb}};
  

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Logic for sharing update request / response output port to jtlb        //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : jtlb_update_req_PROC
// update request to jtlb
  jtlb_update_req_vpn  = jtlb_update_req_vpn_r;

  jtlb_update_req      = jtlb_update_req_r 
                       & (~jrsp_update);
end

assign jrsp_update0_hit  = jrsp_update_hit   &  jtlb_update0_req_r;
assign jrsp_update0_miss = jrsp_update_miss  &  jtlb_update0_req_r;
assign jrsp_update0      = jrsp_update       &  jtlb_update0_req_r;

assign jrsp_update1_hit  = jrsp_update_hit   &  jtlb_update1_req_r;
assign jrsp_update1_miss = jrsp_update_miss  &  jtlb_update1_req_r;
assign jrsp_update1      = jrsp_update       &  jtlb_update1_req_r;


assign jrsp_update_op = 1'b0
                         | jrsp_update0
                         | jrsp_update1
                         ;
  
////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Logic for sharing lookup input port (0) between dmp and jtlb           //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
  
// valid lookup requst to utlb generated for fetch and jtlb ops
// (1) fetch lookup only if utlb_en_r is 1 (when 0, pass vpn through to ppn)
// (2) jtlb ops are independent of utlb_en_r
assign  req0_valid_r = (lkup0_valid_r & utlb_en_r & (~debug_op)
                        & (~lkup_untransl_addr0_r))      // (1)
                     |  jreq_needs_lkup;               // (2)


// select jtlb input for lookup : port 0
assign {req0_vpn_r, req0_asid_r}  = lkup0_jtlb_sel ? 
         {entry_update_data[`npuarc_PCKD_PTE_VPN_RANGE],      //pckd
          entry_update_data[`npuarc_PCKD_PTE_ASID_RANGE]}:
         {lkup0_vpn_r[`npuarc_PD0_VPN_RANGE], lkup0_asid_r};  //unpckd

assign  req1_valid_r             =  lkup1_valid_r;
assign {req1_vpn_r, req1_asid_r} = {lkup1_vpn_r[`npuarc_PD0_VPN_RANGE], lkup1_asid_r};
  
////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Mux for bypassing lookup result from jtlb to lookup port (0 or 1)      //
//                                                                        //
////////////////////////////////////////////////////////////////////////////


  wire rslt0_perm_kr;
  wire rslt0_perm_kw;

  wire rslt0_perm_ur;
  wire rslt0_perm_uw;

always @*
begin : rslt0_perm__PROC
  rslt0_perm = {`npuarc_PD1_PERM_WIDTH{1'b0}}; // default value, only rd, wr perm bits used
  // kernel perms
  rslt0_perm[`npuarc_PD1_PERM_KR] = rslt0_perm_kr;
  rslt0_perm[`npuarc_PD1_PERM_KW] = rslt0_perm_kw;
  // user perms
  rslt0_perm[`npuarc_PD1_PERM_UR] = rslt0_perm_ur;
  rslt0_perm[`npuarc_PD1_PERM_UW] = rslt0_perm_uw;
end


// Bypass logic for result port 0
//
assign {rslt0_ppn,
        rslt0_user_attr,
        rslt0_wr_thru,
        rslt0_perm_kr,
        rslt0_perm_kw,
        rslt0_perm_ur,
        rslt0_perm_uw,
        rslt0_cached
        }  =


    // MMU disabled or debug access: pass-thru with all perms
    (~utlb_en_r | debug_op) ?
         {{aux_memseg_r & {8{debug_op}}}, lkup0_vpn_r, // pass thru requesting vpn
          2'b00,                      // user attr
          1'b0,                       // write through
          4'b1111,                    // all permissions given
          1'b1}:                      // in this case, cacheability is determined entirely in dmp

    // upper 2GB, untranslated, pass-thru VA, (kernel only access)
    (lkup_untransl_addr0_r) ?
         {{aux_memseg_r & {8{debug_op}}}, lkup0_vpn_r, // pass thru requesting vpn
          2'b00,                      // user attr
          1'b0,                       // write through
          2'b11,                      // kernel permissions given
          {2{mpu_en_r}},              // also user permissions given if mpu enabled
          1'b1}:                      // in this case, cacheability is determined entirely in dmp

    (jrsp_update0 & (~jrsp_update_hit)) ?
         // update miss: pass-thru orig vpn with no permissions
         {8'h0, lkup0_vpn_r,       // pass thru requesting vpn
          2'b00,                      // user attr
          1'b0,                       // write through
          4'b0000,                    // no permissions given
          1'b1 }:                     // Cached


    (jrsp_update0 &  jrsp_update_hit) ?
         // update hit: use ppn/perm from jtlb
         {entry_update_data[`npuarc_PCKD_PTE_PPN_RANGE],
          entry_update_data[`npuarc_PCKD_PTE_UA_RANGE],
          entry_update_data[`npuarc_PCKD_PTE_WR_THRU],
          entry_update_data[`npuarc_PCKD_PTE_PERM_KR],
          entry_update_data[`npuarc_PCKD_PTE_PERM_KW],
          entry_update_data[`npuarc_PCKD_PTE_PERM_UR],
          entry_update_data[`npuarc_PCKD_PTE_PERM_UW],
          entry_update_data[`npuarc_PCKD_PTE_CACHED]}:

         // No update, local utlb result
         {rsltu0_ppn,
          rsltu0_user_attr,
          rsltu0_wr_thru,
          rsltu0_perm[`npuarc_PD1_PERM_KR],
          rsltu0_perm[`npuarc_PD1_PERM_KW],
          rsltu0_perm[`npuarc_PD1_PERM_UR],
          rsltu0_perm[`npuarc_PD1_PERM_UW],
          rsltu0_cached};

assign rslt0_match = (  rsltu0_match
                         // declare match if untranslated address or tlb off
                         | lkup_untransl_addr0_r
                         | debug_op
                         | (~utlb_en_r));

// match page size for local or jtlb supplied matching entry
assign rslt0_match_size = jrsp_update0 ? jrsp_match_size :
                                             rsltu0_match_size;

// report multiple match error (occuring at jtlb or locally)
assign rslt0_multiple_match = jrsp_update0 ? 
                                   jrsp_multi_hit : 
                                   rsltu0_multiple_match;
  
// Indicates that the current mode (user or kernel) does not have
// exec/read/write permission for this address. (after bypass muxes)
assign rslt0_prot_viol = (~debug_op) &
        (// permission checking for instructions (ITLB,STLB)
         access_type_inst ?
          (  ( kernel_mode & (~rslt0_perm[`npuarc_PD1_PERM_KX]))
           | (~kernel_mode & (~rslt0_perm[`npuarc_PD1_PERM_UX]))
          ):
        // permission checking for data (DTLB,STLB)
          (  // kernel mode
             ( kernel_mode &  access_type_rd & (~rslt0_perm[`npuarc_PD1_PERM_KR]))
           | ( kernel_mode &  access_type_wr & (~rslt0_perm[`npuarc_PD1_PERM_KW]))
             // user mode
           | (~kernel_mode &  access_type_rd & (~rslt0_perm[`npuarc_PD1_PERM_UR]))
           | (~kernel_mode &  access_type_wr & (~rslt0_perm[`npuarc_PD1_PERM_UW]))
          )
        );


  wire rslt1_perm_kr;
  wire rslt1_perm_kw;

  wire rslt1_perm_ur;
  wire rslt1_perm_uw;

always @*
begin : rslt1_perm__PROC
  rslt1_perm = {`npuarc_PD1_PERM_WIDTH{1'b0}}; // default value, only rd, wr perm bits used
  // kernel perms
  rslt1_perm[`npuarc_PD1_PERM_KR] = rslt1_perm_kr;
  rslt1_perm[`npuarc_PD1_PERM_KW] = rslt1_perm_kw;
  // user perms
  rslt1_perm[`npuarc_PD1_PERM_UR] = rslt1_perm_ur;
  rslt1_perm[`npuarc_PD1_PERM_UW] = rslt1_perm_uw;
end


// Bypass logic for result port 1
//
assign {rslt1_ppn,
        rslt1_user_attr,
        rslt1_wr_thru,
        rslt1_perm_kr,
        rslt1_perm_kw,
        rslt1_perm_ur,
        rslt1_perm_uw,
        rslt1_cached
        }  =


    // MMU disabled or debug access: pass-thru with all perms
    (~utlb_en_r | debug_op) ?
         {{aux_memseg_r & {8{debug_op}}}, lkup1_vpn_r, // pass thru requesting vpn
          2'b00,                      // user attr
          1'b0,                       // write through
          4'b1111,                    // all permissions given
          1'b1}:                      // in this case, cacheability is determined entirely in dmp

    // upper 2GB, untranslated, pass-thru VA, (kernel only access)
    (lkup_untransl_addr1_r) ?
         {{aux_memseg_r & {8{debug_op}}}, lkup1_vpn_r, // pass thru requesting vpn
          2'b00,                      // user attr
          1'b0,                       // write through
          2'b11,                      // kernel permissions given
          {2{mpu_en_r}},              // also user permissions given if mpu enabled
          1'b1}:                      // in this case, cacheability is determined entirely in dmp

    (jrsp_update1 & (~jrsp_update_hit)) ?
         // update miss: pass-thru orig vpn with no permissions
         {8'h0, lkup1_vpn_r,       // pass thru requesting vpn
          2'b00,                      // user attr
          1'b0,                       // write through
          4'b0000,                    // no permissions given
          1'b1 }:                     // Cached


    (jrsp_update1 &  jrsp_update_hit) ?
         // update hit: use ppn/perm from jtlb
         {entry_update_data[`npuarc_PCKD_PTE_PPN_RANGE],
          entry_update_data[`npuarc_PCKD_PTE_UA_RANGE],
          entry_update_data[`npuarc_PCKD_PTE_WR_THRU],
          entry_update_data[`npuarc_PCKD_PTE_PERM_KR],
          entry_update_data[`npuarc_PCKD_PTE_PERM_KW],
          entry_update_data[`npuarc_PCKD_PTE_PERM_UR],
          entry_update_data[`npuarc_PCKD_PTE_PERM_UW],
          entry_update_data[`npuarc_PCKD_PTE_CACHED]}:

         // No update, local utlb result
         {rsltu1_ppn,
          rsltu1_user_attr,
          rsltu1_wr_thru,
          rsltu1_perm[`npuarc_PD1_PERM_KR],
          rsltu1_perm[`npuarc_PD1_PERM_KW],
          rsltu1_perm[`npuarc_PD1_PERM_UR],
          rsltu1_perm[`npuarc_PD1_PERM_UW],
          rsltu1_cached};

assign rslt1_match = (  rsltu1_match
                         // declare match if untranslated address or tlb off
                         | lkup_untransl_addr1_r
                         | debug_op
                         | (~utlb_en_r));

// match page size for local or jtlb supplied matching entry
assign rslt1_match_size = jrsp_update1 ? jrsp_match_size :
                                             rsltu1_match_size;

// report multiple match error (occuring at jtlb or locally)
assign rslt1_multiple_match = jrsp_update1 ? 
                                   jrsp_multi_hit : 
                                   rsltu1_multiple_match;
  
// Indicates that the current mode (user or kernel) does not have
// exec/read/write permission for this address. (after bypass muxes)
assign rslt1_prot_viol = (rsltu1_match_prel & (~debug_op)) &
        (// permission checking for instructions (ITLB,STLB)
         access_type_inst ?
          (  ( kernel_mode & (~rslt1_perm[`npuarc_PD1_PERM_KX]))
           | (~kernel_mode & (~rslt1_perm[`npuarc_PD1_PERM_UX]))
          ):
        // permission checking for data (DTLB,STLB)
          (  // kernel mode
             ( kernel_mode &  access_type_rd & (~rslt1_perm[`npuarc_PD1_PERM_KR]))
           | ( kernel_mode &  access_type_wr & (~rslt1_perm[`npuarc_PD1_PERM_KW]))
             // user mode
           | (~kernel_mode &  access_type_rd & (~rslt1_perm[`npuarc_PD1_PERM_UR]))
           | (~kernel_mode &  access_type_wr & (~rslt1_perm[`npuarc_PD1_PERM_UW]))
          )
        );


// Mask unused permission bits for aux read
// 
always @*
begin : mask_unused_perm_bits_PROC
  entry_rd_data = entry_rd_data_prel;
  entry_rd_data[`npuarc_PCKD_PTE_PERM_UX] = 1'b0;
  entry_rd_data[`npuarc_PCKD_PTE_PERM_KX] = 1'b0;
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
  casez ({(jrsp_update_op & jrsp_update_hit & (~jrsp_multi_hit)),
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
  casez ({(jrsp_update_op & jrsp_update_hit & (~jrsp_multi_hit)),
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
  casez ({(jrsp_update_op & jrsp_update_hit & (~jrsp_multi_hit)),
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
  casez ({(jrsp_update_op & jrsp_update_hit & (~jrsp_multi_hit)),
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
  // Replace selected (lru) entry
  casez ({(jrsp_update_op & jrsp_update_hit & (~jrsp_multi_hit)),
          jcmd_insert, 
          rsltu0_match_r,  // raw port0 match ( <-jcmd )
          inval_entry_avail,
          jcmd_write
        })
    5'b1??0?,                                                    // (1)
    5'b0100?: entry_update_1h[4] = lru_entry_1h[4];            // (2)
    5'b1??1?,                                                    // (3)
    5'b0101?: entry_update_1h[4] = inval_entry_1h[4];          // (4)
    5'b011??: entry_update_1h[4] = rsltu0_entry_match_1h_r[4]; // (5)
    default:  entry_update_1h[4] = 1'b0;
  endcase
  // Replace selected (lru) entry
  casez ({(jrsp_update_op & jrsp_update_hit & (~jrsp_multi_hit)),
          jcmd_insert, 
          rsltu0_match_r,  // raw port0 match ( <-jcmd )
          inval_entry_avail,
          jcmd_write
        })
    5'b1??0?,                                                    // (1)
    5'b0100?: entry_update_1h[5] = lru_entry_1h[5];            // (2)
    5'b1??1?,                                                    // (3)
    5'b0101?: entry_update_1h[5] = inval_entry_1h[5];          // (4)
    5'b011??: entry_update_1h[5] = rsltu0_entry_match_1h_r[5]; // (5)
    default:  entry_update_1h[5] = 1'b0;
  endcase
  // Replace selected (lru) entry
  casez ({(jrsp_update_op & jrsp_update_hit & (~jrsp_multi_hit)),
          jcmd_insert, 
          rsltu0_match_r,  // raw port0 match ( <-jcmd )
          inval_entry_avail,
          jcmd_write
        })
    5'b1??0?,                                                    // (1)
    5'b0100?: entry_update_1h[6] = lru_entry_1h[6];            // (2)
    5'b1??1?,                                                    // (3)
    5'b0101?: entry_update_1h[6] = inval_entry_1h[6];          // (4)
    5'b011??: entry_update_1h[6] = rsltu0_entry_match_1h_r[6]; // (5)
    default:  entry_update_1h[6] = 1'b0;
  endcase
  // Replace selected (lru) entry
  casez ({(jrsp_update_op & jrsp_update_hit & (~jrsp_multi_hit)),
          jcmd_insert, 
          rsltu0_match_r,  // raw port0 match ( <-jcmd )
          inval_entry_avail,
          jcmd_write
        })
    5'b1??0?,                                                    // (1)
    5'b0100?: entry_update_1h[7] = lru_entry_1h[7];            // (2)
    5'b1??1?,                                                    // (3)
    5'b0101?: entry_update_1h[7] = inval_entry_1h[7];          // (4)
    5'b011??: entry_update_1h[7] = rsltu0_entry_match_1h_r[7]; // (5)
    default:  entry_update_1h[7] = 1'b0;
  endcase
end

// leda W547 on

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// States for the utlb state machine                                      //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
parameter LKUP_SM_IDLE    = 2'b00;  // No lkup or lkup/hit
parameter LKUP_SM_MISS    = 2'b01;  // update req pending to jtlb
parameter LKUP_SM_INSERT  = 2'b10;  // lkup and repl hit or lru entry
parameter LKUP_SM_DELETE  = 2'b11;  // lkup and inval hit entry(ies)

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

  lkup0_state_nxt           = lkup0_state_r;
  lkup0_jtlb_sel            = 1'b0; // default is dmp
  lookup0_op                = 1'b0;
  eager_match               = 1'b0;
  rslt0_valid               = 1'b0;

  // for jtlb related ops
  jtlb_update0_req_ce       = 1'b0;
  jtlb_update0_req_nxt      = 1'b0;
  jtlb_update0_req_vpn_nxt  = lkup0_vpn_r[`npuarc_PD0_VPN_RANGE];
  jcmd_inval_se             = `npuarc_DTLB_NUM_ENTRIES'd0;
  jcmd_insert               = 1'b0;
  update0_pend              = 1'b0;

  
  case (lkup0_state_r)

    // default / idle state, stay here till miss or jreq_needs_lkup
    //
    LKUP_SM_IDLE:  
    begin
      lkup0_state_nxt  = LKUP_SM_IDLE;
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept
      // give jtlb precedence over local lookups
      //
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
          end
          `npuarc_JCMD_INSERT: 
          begin
             lookup0_op = 1'b1;
             eager_match = 1'b1;
             lkup0_state_nxt = LKUP_SM_INSERT;
          end
          default: ;
        endcase
      end
      // if no jtlb op and no restart
      //
      else
      if (   lkup0_valid_r & (~lkup1_state_r[0])
          & (~wa_extern_restart) ) // dtlb: No new lookup if non-dtlb restart
      begin
        lookup0_op  =   (~lkup_untransl_addr0_r) 
                      & (~debug_op)
                      & utlb_en_r; 
        
        if (  rsltu0_miss 
            & (~lkup_untransl_addr0_r)
            & (~x2_pref_r)
            & (~debug_op)
            & utlb_en_r
            & x2_pass)
        begin
          // miss
          //
          rslt0_valid          = 1'b1;

          lkup0_state_nxt      = LKUP_SM_MISS;
          jtlb_update0_req_nxt = 1'b1;
          jtlb_update0_req_ce  = 1'b1;
          update0_pend         = 1'b1;
        end
        else
        begin
          rslt0_valid          = 1'b1;
        end
      end

    end
  
    LKUP_SM_MISS:  // data lkup miss pending (wait for update)
    begin
      update0_pend = 1'b1;
     
      if (wa_extern_restart) // dtlb: abandon lookup if non-dtlb restart
      begin
        lkup0_state_nxt = LKUP_SM_IDLE;
        update0_pend    = 1'b0;
      end
      else

      if (jrsp_update)
      begin
        rslt0_valid     = 1'b0;
        lkup0_state_nxt = LKUP_SM_IDLE;
      end

      else
      begin
        // stall further fetch/lkup requests till update + 1 clk 
        // (for new entry to be written and avail for lookup)
        jtlb_update0_req_nxt = 1'b1;
        lkup0_state_nxt      = LKUP_SM_MISS;
      end
    end
  
    LKUP_SM_DELETE:  // inval matching entry(ies)
    begin
      lkup0_state_nxt = LKUP_SM_IDLE;
      jcmd_inval_se   = rsltu0_entry_match_nh_r;
    end
  
    LKUP_SM_INSERT:  // insert new or replace matching entry(ies)
    begin
      lkup0_state_nxt = LKUP_SM_IDLE;
      jcmd_insert     = 1'b1;
      jcmd_inval_se   = rsltu0_entry_match_nh_r // inval all copies of old entry except
                       & (~rsltu0_entry_match_1h_r) // the lowest index match
                       ;
    end
  
    default: ;
    
  endcase // case (lkup0_state_r)

end

// --------------------------------------------------------------------------
// LOOKUP PORT 1
// --------------------------------------------------------------------------
//
always @*
begin : utlb_fsm1_PROC

  lkup1_state_nxt           = lkup1_state_r;

  // for jtlb related ops
  jtlb_update1_req_ce       = 1'b0;
  jtlb_update1_req_nxt      = 1'b0;
  jtlb_update1_req_vpn_nxt  = lkup1_vpn_r[`npuarc_PD0_VPN_RANGE];
  update1_pend              = 1'b0;

  case (lkup1_state_r)

    // default / idle state, stay here till miss or jreq_needs_lkup
    //
    LKUP_SM_IDLE:  
    begin
      lkup1_state_nxt  = LKUP_SM_IDLE;

      if (  lkup1_valid_r 
          & utlb_en_r 
          & (~x2_pref_r) 
          & (~debug_op) 
          & (~wa_extern_restart) 
          & (~jtlb_update0_req_r) // stay idle during update0
         )
      begin
        // miss
        if (   rsltu1_miss 
            & (~lkup_untransl_addr1_r)
            & x2_pass)
        begin
          lkup1_state_nxt      = LKUP_SM_MISS;
          jtlb_update1_req_nxt = 1'b1;
          jtlb_update1_req_ce  = 1'b1;
          update1_pend         = 1'b1;
        end
      end

    end
  
    LKUP_SM_MISS:  // data lkup miss pending (wait for update)
    begin
      update1_pend = 1'b1;
      if  (  wa_extern_restart
           | jtlb_update0_req_r    // let port 0 update first
          )
      begin
        lkup1_state_nxt = LKUP_SM_IDLE;
        update1_pend = 1'b0;
      end

      // claim update only if port0 update satisfied
      else if (jrsp_update & (~jtlb_update0_req_r))
      begin
        lkup1_state_nxt = LKUP_SM_IDLE;
      end

      else
      begin
        // stall further fetch/lkup requests till update + 1 clk 
        // (for new entry to be written and avail for lookup)
        jtlb_update1_req_nxt = ~jtlb_update0_req_r;
        lkup1_state_nxt = LKUP_SM_MISS;
      end
    end
  
    default: ;
    
  endcase // case (lkup1_state_r)

end

// spyglass enable_block W193
// utlb control regs : port 0
//
always @(posedge clk or posedge rst)
begin: lkup0_ctlregs_PROC
  if (rst)
  begin
    lkup0_state_r <= 2'b0;
  end
  else
  begin
    lkup0_state_r <= lkup0_state_nxt;
  end
end // block: lkup0_ctlregs_PROC

// utlb control regs : port 1
//
always @(posedge clk or posedge rst)
begin: lkup1_ctlregs_PROC
  if (rst)
  begin
    lkup1_state_r <= 2'b0;
  end
  else
  begin
    lkup1_state_r <= lkup1_state_nxt;
  end
end // block: lkup1_ctlregs_PROC

  
// utlb update request register
//
always @(posedge clk or posedge rst)
begin: update_req_PROC
  if (rst)
  begin
    jtlb_update_req_r  <= 1'b0;
    jtlb_update0_req_r <= 1'b0;
    jtlb_update1_req_r <= 1'b0;
  end
  else
  begin
    jtlb_update_req_r  <= jtlb_update0_req_nxt | jtlb_update1_req_nxt;
    jtlb_update0_req_r <= jtlb_update0_req_nxt;
    jtlb_update1_req_r <= jtlb_update1_req_nxt;
  end
end // block: lkup2_ctlregs_PROC


// jtlb interface update request output regs
//
assign new_update_request = jtlb_update0_req_ce | jtlb_update1_req_ce;

// leda NTL_RST03 off
// leda S_1C_R off
// LMD: All registers must be asynchronously set or reset
// LJ:  Datapath
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
always @(posedge clk)
begin: update_req_vpn_PROC
  if (new_update_request)
  begin
    jtlb_update_req_vpn_r  <= jtlb_update0_req_ce ?
                                jtlb_update0_req_vpn_nxt :
                                jtlb_update1_req_vpn_nxt ;
  end
end // block: utlb_update_PROC
// leda NTL_RST03 on
// leda S_1C_R on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01
 

// Track whether an update request (VA) also missed in jtlb
//
assign missed_va_valid_set =  jrsp_update
                           & (   (~jrsp_update_hit)
                               | (jrsp_multi_hit  ) );

assign wa_extern_restart   =  wa_restart_r
                           & (~wa_jtlb_lookup_start_r);

assign missed_va_valid_clr = (    wa_extern_restart
                              & (~wa_hlt_restart_r)
                             ) | new_update_request;


assign missed_va_matches_lkup = // either lookup port
        { (~(|(jtlb_update_req_vpn_r ^ lkup1_vaddr_r[`npuarc_PD0_VPN_RANGE])) & (~lkup_untransl_addr1_r) & missed_va_valid[1]),
          (~(|(jtlb_update_req_vpn_r ^ lkup0_vaddr_r[`npuarc_PD0_VPN_RANGE])) & (~lkup_untransl_addr0_r) & missed_va_valid[0])
        }
     ;

assign rslt_utlb_miss_excpn = (| missed_va_valid)
                            & (~(jtlb_multi_match_excpn))
                            & (~(jtlb_ecc_err_excpn))
                            & (|missed_va_matches_lkup);

wire   missed_va_valid_cg0;
assign missed_va_valid_cg0 = missed_va_valid_clr | missed_va_valid_set;

always @(posedge clk or posedge rst)
begin: missed_va_valid_PROC
  if (rst)
  begin
    missed_va_valid           <= 2'h0;
    jtlb_multi_match_excpn    <= 1'b0;
    jtlb_multi_match_port     <= 1'b0;  
    jtlb_ecc_err_excpn        <= 1'b0;
    jtlb_ecc_err_port         <= 1'b0;  
  end
  else if (missed_va_valid_cg0)  // clock-enable on clear or 'set' (update)
  begin                          // (clear has priority over update)
      missed_va_valid         <= {    jtlb_update1_req_r
                                  & (~jtlb_update0_req_r),
                                      jtlb_update0_req_r
                                  }
                               & {2{!missed_va_valid_clr}};  // clr both bits on ._clr
                                                             
      jtlb_multi_match_excpn  <= jrsp_multi_hit 
                               & (!missed_va_valid_clr);
      jtlb_multi_match_port   <= (  jrsp_multi_hit 
                                  & jtlb_update1_req_r 
                                  & (~jtlb_update0_req_r)
                                 ) 
                               & (!missed_va_valid_clr);
      jtlb_ecc_err_excpn      <= jrsp_tlb_err
                               & (!missed_va_valid_clr);

      jtlb_ecc_err_port       <= (  jrsp_tlb_err
                                  & jtlb_update1_req_r 
                                  & (~jtlb_update0_req_r)
                                 ) 
                               & (!missed_va_valid_clr);

  end
end


// utlb / mmu active : clock request
assign utlb_active          = lkup0_valid_r 
                            | (lkup0_state_r != LKUP_SM_IDLE)

                            | lkup1_valid_r
                            | (lkup1_state_r != LKUP_SM_IDLE)

                            | (jtlb_cmd_r != `npuarc_JCMD_IDLE)
                            | mmu_clock_req_r;

// Match result vector registers
always @(posedge clk or posedge rst)
begin : lkup_rslt_vec_outreg_PROC
  if (rst)
  begin
    rsltu0_match_r          <= 1'b0;
    rsltu0_entry_match_nh_r <= `npuarc_DTLB_NUM_ENTRIES'd0;
    rsltu0_entry_match_1h_r <= `npuarc_DTLB_NUM_ENTRIES'd0;
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
    lru_update_r            <= `npuarc_DTLB_NUM_ENTRIES'd0;
  end
  else
  begin
    lru_update_r            <= (rsltu0_match_1h    // utlb match (one-hot)
                             |  entry_update_1h);
  end
end

   
////////////////////////////////////////////////////////////////////////////
//                                                                        //
// LRU logic instance                                                     //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
 
// don't advance lru state if no result valid (preemmpted by jcmd)
assign rsltu0_match_1h = rsltu0_entry_match_1h
                       & {`npuarc_DTLB_NUM_ENTRIES{rslt0_valid}}
                       ;

npuarc_plru8 u_plru8 (
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
 
npuarc_udtlb u_udtlb (
  .clk                          (clk),            // Processor clock
  .rst                          (rst),            // Global reset
  .rst_init_disable_r           (rst_init_disable_r),

  .alloc_entries                (4'd8),

  .shared_en_r                  (shared_en_r),    // Shared lib enable (PID)
  .sasid_r                      (sasid_r),        // Current pid slib membership
  .sasid_force_match            (sasid_force_match),
  .eager_match                  (eager_match),

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

  ////////// Look-up port //////////////////////////////////////////////////
  // 
  // Request  for uTLB lookup
  .req1_valid_r              (req1_valid_r),
  .req1_vpn_r                (req1_vpn_r),
  .req1_asid_r               (req1_asid_r),

  //  Lookup result
  .rslt1_match               (rsltu1_match_prel),
  .rslt1_miss                (rsltu1_miss_prel),
  .rslt1_match_index         (rsltu1_match_index),
  .rslt1_match_size          (rsltu1_match_size),
  .rslt1_multiple_match      (rsltu1_multiple_match),
  // for lru logic
  .rslt1_entry_match         (rsltu1_entry_match),
  .rslt1_entry_match_1h      (rsltu1_entry_match_1h),

  .rslt1_ppn_out             (rsltu1_ppn),
  .rslt1_user_attr_out       (rsltu1_user_attr),
  .rslt1_wr_thru_out         (rsltu1_wr_thru),
  .rslt1_perm_out            (rsltu1_perm),
  .rslt1_cached_out          (rsltu1_cached),

  ////////// Invalidate select uTLB entries /////////////////////////////////
  .invalidate_entries           (invalidate_entries), // Invalidate select entries
  .unlock_entries               (1'b0),               // Unlock all entries

  .inval_entry_avail            (inval_entry_avail), // Current invalid entries
  .inval_entry_1h               (inval_entry_1h), // lowest index invalid entry
  ////////// Interface to read utlb entries /////////////////////////////////
  //
  .entry_rd_val                 (entry_rd_val),  // read operation this cycle
  .entry_rd_addr                (jtlb_index_r),  // Aux address for read/write
  .entry_rd_data                (entry_rd_data_prel), // LR read data (entry)

  .entry_update_1h              (entry_update_1h),
  .entry_update_data            (entry_update_data)  // new entry from jtlb
);
  

endmodule // `module_name
