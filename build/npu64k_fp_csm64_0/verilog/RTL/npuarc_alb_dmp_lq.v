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
//----------------------------------------------------------------------------
//
// 
// 
// ALB_DMP_LQ
// 
// 
// 
// 
//
// ===========================================================================
//
// Description:
//  This module implements the Load  Queue.
//    
//  This block services load instructions that accesses external memory.  
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_lq.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"


//POST_PROCESS { prefix:"//D:", wire_prefix:"t_", edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }

//D: error_signal { name: "alb_dmp_lq_cmd_fifo_0_edc_err" }

//D: error_signal { name: "alb_dmp_lq_fifo_edc_err" }

module npuarc_alb_dmp_lq (
// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ: some bits of inputs vectors are not used
  ////////// General input signals ///////////////////////////////////////////
  //
  input                         clk,            // clock
  input                         rst_a,          // reset

  ////////// Interface to the X3 stage //////////////////////////////////////////
  //
  input                         x3_store_r,          // X3 store  
  input                         x3_pass,             // X3 pass  
  input  [`npuarc_PADDR_RANGE]         x3_mem_addr0_r,      // X3 memory address
  input  [`npuarc_PADDR_RANGE]         x3_mem_addr1_r,      // X3 memory address
  input  [`npuarc_DMP_TARGET_RANGE]    dc3_target_r,        // DC3 target
  input  [3:0]                  dc3_bank_sel_r,      // DC3 bank sel

  ////////// Interface to the DC4 (commit stage) ////////////////////////////
  //
  input                         ca_valid_r,        // CA has valid instruction
  input                         ca_pass,           // CA passing on inst
  input                         ca_load_r,         // CA load
  input                         ca_store_r,        // CA store
  input                         ca_locked_r,       // CA LLOCK/SCOND
  input                         ca_volatile_r,     // CA volatile access      
  input                         ca_strict_order_r, // CA strict order      
  input [1:0]                   ca_size_r,         // CA 00-b, 01-h, 10-w, 11-dw
  input                         ca_sex_r,          // CA sign extension
  input                         ca_user_mode_r,    // CA user mode       
  input [`npuarc_PADDR_RANGE]          ca_mem_addr0_r,    // CA memory address
  input [`npuarc_PADDR_RANGE]          ca_mem_addr1_r,    // CA memory address
  input [`npuarc_GRAD_TAG_RANGE]       ca_grad_tag, 
 
  input                         dc4_grad_req,           // Uncachd ld grad
  input [`npuarc_DMP_TARGET_RANGE]     dc4_target_r,           // DC4 memory target
  input [1:0]                   dc4_data_bank_sel_lo_r, //
  input [1:0]                   dc4_data_bank_sel_hi_r, //
  
  ////////// Interface to the result bus //////////////////////////////////////
  //
  output reg                    lq_rb_req,          // load queue req
  output reg                    lq_rb_err,          // load queue bus error
  output reg                    lq_rb_user_mode,    // privilege mode
  output reg [`npuarc_GRAD_TAG_RANGE]  lq_rb_tag,          // load queue tag
  output reg                    lq_rb_sex,          // sex
  output reg [1:0]              lq_rb_size,         // b, w, hw , dw
  output reg [`npuarc_PADDR_RANGE]     lq_rb_addr,         //
  
  input                         lq_rb_ack,          // load queue ack

  output reg [`npuarc_DOUBLE_RANGE]    lq_rb_data_even_r,  // lq even data                   
  output reg [`npuarc_DOUBLE_RANGE]    lq_rb_data_odd_r,   // lq odd data                   
  
  ////////// Interface to the BIU ///////////////////////////////////
  //
  output                        lq_mem_cmd_valid,                 
  output                        lq_mem_cmd_burst_size,                 
  output reg                    lq_mem_cmd_read,                  
  input                         lq_mem_cmd_accept,                
  output [`npuarc_PADDR_RANGE]         lq_mem_cmd_addr,   
  output reg [1:0]              lq_mem_cmd_data_size,               
  output reg                    lq_mem_cmd_lock,               
  output reg                    lq_mem_cmd_excl,
  output reg                    lq_mem_cmd_prot,               

  input                         lq_mem_rd_valid,                  
  input                         lq_mem_err_rd,                  
  input                         lq_mem_rd_excl_ok,
  output reg                    lq_mem_rd_accept,                 
  input  [`npuarc_DOUBLE_RANGE]        lq_mem_rd_data,     // 64-bit data 
  //////////  Outputs to WQ synchronization //////////////////////////////////
  // 
  output [`npuarc_DMP_FIFO_RANGE]      lq_order_ptr_1h, // LQ most recent entry
  output                        dc4_war_hazard,  // WAR hazard

  output reg                    lq_cmd_read,     // LQ command  popped
  output [`npuarc_LQ_PTR_RANGE]        lq_cmd_rd_ptr,   // LQ command read pointer

  output reg                    lq_data_retire,  // LQ data retired
  output reg [`npuarc_LQ_PTR_RANGE]    lq_data_rd_ptr,  // LQ data read pointer
  
  //////////  Inputs for LQ  synchronization ////////////////////////////////////
  //
  input [`npuarc_DMP_FIFO_RANGE]       wq_order_ptr_1h,       // Last WQ mem/per/iccm entry 
  input                         dc4_raw_hazard,        // RAW hazard
   
  input                         wq_mem_per_iccm_read,  // WQ entry processed
  input [`npuarc_WQ_PTR_RANGE]         wq_rdentry0,           // WQ processed entry
 
  input                         wq_mem_retire,         // WQ mem entry retired
  input [`npuarc_WQ_PTR_RANGE]         wq_mem_entry_id,       // WQ retired  entry
 


  ////////// Load queue status //////////////////////////////////////
  //
  output                        lq_empty_r,
  output                        lq_full_nxt
// leda NTL_CON37 on
// leda NTL_CON13C on
);


// Local Declarations

reg                       lq_load_commit_spec;
reg                       lq_fifo_push;

reg                       lq_fifo_data_pop;
wire [`npuarc_LQ_PTR_RANGE]      lq_mem_data_rd_ptr;


reg                       lq_state_r;
reg                       lq_state_nxt;
reg                       lq_state_cg0;
wire                      lq_full_r;
wire                      lq_mem_cmd_to_fifo;
wire                      lq_mem_cmd_pop;

wire                      lq_fifo_cmd_valid;  
wire                      lq_fifo_cmd_unaligned;  
wire  [`npuarc_PADDR_RANGE]      lq_fifo_cmd_addr;   
wire  [`npuarc_PADDR_RANGE]      lq_fifo_cmd_addr1; 
wire  [`npuarc_DMP_TARGET_RANGE] lq_fifo_cmd_target; 
wire                      lq_fifo_cmd_ex;
wire                      lq_fifo_cmd_llock;
wire  [1:0]               lq_fifo_cmd_data_size;
wire                      lq_fifo_cmd_user_mode;


wire  [1:0]               lq_fifo_data_size;        
wire                      lq_fifo_data_sex;         
wire                      lq_fifo_data_user_mode;         
wire  [`npuarc_PADDR_RANGE]      lq_fifo_addr;      
wire  [`npuarc_GRAD_TAG_RANGE]   lq_fifo_grad_tag; 
wire                      lq_fifo_unaligned;
wire                      lq_fifo_data_llock;
wire                      lq_mem_data_even_cg0;
wire                      lq_mem_data_odd_cg0;
wire                      lq_mem_toggle_arb_ok;
wire                      lq_mem_pass;
wire                      lq_mem_pass_err;

wire [4:0]                lq_gnt_r;

reg                       lq_pass;
reg                       lq_pass_err;

reg                       lq_rb_toggle_ok;
reg                       lq_toggle_ok;
reg                       lq_toggle;
wire [4:0]                lq_pending;

reg                       lq_rb_busy_nxt;
reg                       lq_rb_busy_r;

reg                       lq_err_nxt;
reg                       lq_err_r;


// Module definition

///////////////////////////////////////////////////////////////////////////////
// This module hides the latency of the memory subsystem by queing incoming
// loads requests without blocking the pipeline. Requests are handled 
// in order. Command and data transfers are decoupled, allowing for multiple
// outstanding transactions in the memory system, as long as it is suported
// by the external bus protocol.
/////////////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////////////
// Unaligned accesses
// 
//////////////////////////////////////////////////////////////////////////////
reg dc4_bank01_cross;
reg dc4_bank10_cross;
reg dc4_unaligned;

always @*
begin : dc4_unaligned_PROC
  //   ________________________________________________________________
  //  |       bank 1         bank 1   |       bank 0         bank 0    |
  //  |     sel_hi[1]     sel_lo[1]   |     sel_hi[0]     sel_lo[0]    |
  //  |    _________      _________   |   _________       _________    |
  //  |   |         |    |         |  |  |         |     |         |   |
  //  |   |         |    |         |  |  |         |     |         |   |
  //  |   |         |    |         |  |  |         |     |         |   |
  //  |   |<------->|    |<------->|  |  |<------->|     |<------->|   |
  //  |   |   32B   |    |   32B   |  |  |   32B   |     |   32B   |   |
  //  |   |         |    |         |  |  |         |     |         |   |
  //  |   |         |    |         |  |  |         |     |         |   |
  //  |   |_________|    |_________|  |  |_________|     |_________|   |
  //  |                               |                                |
  //  |                               |                                |
  //  |_______________________________|________________________________|
  //  
  
  dc4_bank01_cross = dc4_data_bank_sel_hi_r[0] & dc4_data_bank_sel_lo_r[1];
  dc4_bank10_cross = dc4_data_bank_sel_hi_r[1] & dc4_data_bank_sel_lo_r[0];
  
  dc4_unaligned    =  dc4_bank01_cross
                    | dc4_bank10_cross;
end

//////////////////////////////////////////////////////////////////////////////
// Combinational logic defining dc4 signals
// 
//////////////////////////////////////////////////////////////////////////////
always @*
begin : lq_fifo_push_PROC
  // Loads are pushed to the  queue when they pass the commit point and
  // they target the external memory or it is uncached (.di) load.
  // Prefetches to uncached space do not go into the load queue.
  // The following is a speculative commit, which is independent of ca_pass
  //
  lq_load_commit_spec =   ca_valid_r 
                        & ca_load_r
                        & dc4_grad_req;
  
  case (dc4_target_r)
  `npuarc_DMP_TARGET_MEM:  lq_fifo_push  = lq_load_commit_spec & (~lq_full_r);
  default:          lq_fifo_push  = 1'b0;
  endcase  
  
end



//////////////////////////////////////////////////////////////////////////////
// Module instantiation:
// The storage elements for the load queue is inside this module
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_dmp_lq_fifo u_alb_dmp_lq_fifo (


  .clk                     (clk                  ), 
  .rst_a                   (rst_a                ), 

  .x3_store_r              (x3_store_r           ),
  .x3_pass                 (x3_pass              ),
  .x3_mem_addr0_r          (x3_mem_addr0_r       ),
  .x3_mem_addr1_r          (x3_mem_addr1_r       ),
  .dc3_target_r            (dc3_target_r         ),
  .dc3_bank_sel_r          (dc3_bank_sel_r       ),

  .lq_fifo_push            (lq_fifo_push         ),
  
  .ca_pass                 (ca_pass              ),
  .ca_load_r               (ca_load_r            ),
  .ca_store_r              (ca_store_r           ),
  .ca_locked_r             (ca_locked_r          ),
  .ca_volatile_r           (ca_volatile_r        ),
  .ca_strict_order_r       (ca_strict_order_r    ),
  .ca_mem_addr0_r          (ca_mem_addr0_r       ),
  .ca_mem_addr1_r          (ca_mem_addr1_r       ),
  .ca_size_r               (ca_size_r            ),    
  .ca_sex_r                (ca_sex_r             ),    
  .ca_user_mode_r          (ca_user_mode_r       ),    
  .ca_grad_tag             (ca_grad_tag          ),    
  .dc4_target_r            (dc4_target_r         ),    
  .dc4_bank_sel_r          ({dc4_data_bank_sel_hi_r[1],
                             dc4_data_bank_sel_lo_r[1],
                             dc4_data_bank_sel_hi_r[0],
                             dc4_data_bank_sel_lo_r[0]}),    
  .dc4_unaligned           (dc4_unaligned        ), 
  
  .lq_fifo_cmd_pop         (lq_cmd_read          ),
  .lq_cmd_rd_ptr           (lq_cmd_rd_ptr        ),
  
  .lq_fifo_data_pop        (lq_fifo_data_pop     ),
  .lq_data_rd_ptr          (lq_data_rd_ptr       ),
  .lq_data_retire          (lq_data_retire       ),
  
  .lq_fifo_cmd_valid       (lq_fifo_cmd_valid    ),
  .lq_fifo_cmd_unaligned   (lq_fifo_cmd_unaligned),
  .lq_fifo_cmd_addr        (lq_fifo_cmd_addr     ),
  .lq_fifo_cmd_addr1       (lq_fifo_cmd_addr1    ),
  .lq_fifo_cmd_target      (lq_fifo_cmd_target   ),
  .lq_fifo_cmd_ex          (lq_fifo_cmd_ex       ),
  .lq_fifo_cmd_llock       (lq_fifo_cmd_llock    ),
  .lq_fifo_cmd_data_size   (lq_fifo_cmd_data_size),
  .lq_fifo_cmd_user_mode   (lq_fifo_cmd_user_mode),
  .lq_fifo_data_size       (lq_fifo_data_size    ),
  .lq_fifo_data_sex        (lq_fifo_data_sex     ),
  .lq_fifo_addr            (lq_fifo_addr         ),
  .lq_fifo_grad_tag        (lq_fifo_grad_tag     ),
  .lq_fifo_unaligned       (lq_fifo_unaligned    ),
  .lq_fifo_data_llock      (lq_fifo_data_llock   ),
  .lq_fifo_data_user_mode  (lq_fifo_data_user_mode),
  
  .lq_order_ptr_1h         (lq_order_ptr_1h      ),
  .dc4_war_hazard          (dc4_war_hazard       ),
  
  .wq_order_ptr_1h         (wq_order_ptr_1h      ),      
  .dc4_raw_hazard          (dc4_raw_hazard       ),
  .wq_cmd_read             (wq_mem_per_iccm_read ), 
  .wq_rdentry0             (wq_rdentry0          ),           
  .wq_mem_retire           (wq_mem_retire        ),         
  .wq_mem_entry_id         (wq_mem_entry_id      ),       
  .lq_fifo_empty           (lq_empty_r           ),
  .lq_fifo_full            (lq_full_r            ),
  .lq_fifo_full_nxt        (lq_full_nxt          )

);

//////////////////////////////////////////////////////////////////////////////
// Check for 1K crossing
// 
//////////////////////////////////////////////////////////////////////////////
reg  lq_fifo_cmd_1k_cross;

always @*
begin : lq_1k_cross_PROC
  // Unaligned loads may cross a 1K boundary
  //
  lq_fifo_cmd_1k_cross = (&lq_fifo_cmd_addr[9:3])
                       ;  
end

//////////////////////////////////////////////////////////////////////////////
// 
// 
//////////////////////////////////////////////////////////////////////////////
reg [1:0] lq_cmd_data_size;

always @*
begin : lq_cmd_data_size_PROC 

  // 00-b, 01-h, 10-w, 11-dw

  case (lq_fifo_cmd_data_size)
  2'b11:   lq_cmd_data_size = (lq_fifo_cmd_addr[2:0] == 3'b100) ? 2'b10 : 2'b11;
  2'b10:   lq_cmd_data_size = (lq_fifo_cmd_addr[1:0] == 2'b00)  ? 2'b10 : 2'b11;
  2'b01:   lq_cmd_data_size = (lq_fifo_cmd_addr[0]   == 1'b0)   ? 2'b01 : 2'b11;
  default: lq_cmd_data_size = 2'b00;
  endcase
end

reg  lq_mem_cmd_target;
//////////////////////////////////////////////////////////////////////////////
// @
// 
//////////////////////////////////////////////////////////////////////////////

always @*
begin : lq_mem_default_PROC
  lq_mem_cmd_data_size  = lq_cmd_data_size;
  lq_mem_cmd_read       = 1'b1;
  lq_mem_cmd_lock       = lq_fifo_cmd_ex;
  lq_mem_cmd_excl       = lq_fifo_cmd_llock;
  lq_mem_cmd_prot       = ~lq_fifo_cmd_user_mode;
  
  lq_mem_cmd_target     = (lq_fifo_cmd_target == `npuarc_DMP_TARGET_MEM);
end

//////////////////////////////////////////////////////////////////////////////
// Module instantiation
// 
//////////////////////////////////////////////////////////////////////////////
npuarc_alb_dmp_lq_port u_alb_dmp_lq_port_0 (
  .clk                     (clk                  ),  
  .rst_a                   (rst_a                ),  

  .lq_fifo_cmd_valid       (lq_fifo_cmd_valid    ),     
  .lq_fifo_cmd_addr        (lq_fifo_cmd_addr     ),      
  .lq_fifo_cmd_addr1       (lq_fifo_cmd_addr1    ),      
  .lq_fifo_cmd_target      (lq_mem_cmd_target    ),    
  .lq_fifo_cmd_unaligned   (lq_fifo_cmd_unaligned),    
  .lq_fifo_cmd_1k_cross    (lq_fifo_cmd_1k_cross ),
  .lq_fifo_empty_r         (lq_empty_r           ),

  .lq_cmd_valid            (lq_mem_cmd_valid     ),  
  .lq_cmd_addr             (lq_mem_cmd_addr      ),  
  .lq_cmd_burst_size       (lq_mem_cmd_burst_size),  
  .lq_cmd_accept           (lq_mem_cmd_accept    ), 

  .lq_cmd_to_fifo          (lq_mem_cmd_to_fifo   ),
  .lq_cmd_pop              (lq_mem_cmd_pop       ),
  
  .lq_rd_valid             (lq_mem_rd_valid      ),
  .lq_rd_excl_ok           (lq_mem_rd_excl_ok    ), 
  .lq_err_rd               (lq_mem_err_rd        ),
  .lq_rd_accept            (lq_mem_rd_accept     ),
  
  .lq_fifo_addr            (lq_fifo_addr         ),
  .lq_fifo_unaligned       (lq_fifo_unaligned    ),
  .lq_fifo_llock           (lq_fifo_data_llock   ),
  .lq_toggle_arb_ok        (lq_mem_toggle_arb_ok ),
  .lq_data_even_cg0        (lq_mem_data_even_cg0 ),
  .lq_data_odd_cg0         (lq_mem_data_odd_cg0  ),
  .lq_pass                 (lq_mem_pass          ),
  .lq_pass_err             (lq_mem_pass_err      )
);






//////////////////////////////////////////////////////////////////////////////
// Command acceptance
// 
//////////////////////////////////////////////////////////////////////////////
always @*
begin : lq_cmd_read_PROC
  // Once the command is accepted, we remove it from the lq_cmd_fifo
  //
  lq_cmd_read =   1'b0
                | lq_mem_cmd_pop
                ;
end


///////////////////////////////////////////////////////////////////////////////
// @ Popping out from each FIFO
// 
//////////////////////////////////////////////////////////////////////////////
reg lq_mem_data_pop;
reg lq_per_data_pop; 
reg lq_per2_data_pop; 
reg lq_iccm_data_pop;
reg lq_vec_mem_data_pop;

always @*
begin: lq_data_pop_PROC
  lq_mem_data_pop     = lq_fifo_data_pop & lq_gnt_r[0]; // MEM target  
  lq_per_data_pop     = lq_fifo_data_pop & lq_gnt_r[1]; // PER target  
  lq_iccm_data_pop    = lq_fifo_data_pop & lq_gnt_r[2]; // ICCM target 
  lq_vec_mem_data_pop = lq_fifo_data_pop & lq_gnt_r[3]; // VMEM target
  lq_per2_data_pop    = lq_fifo_data_pop & lq_gnt_r[4]; // PER2 target
end

//////////////////////////////////////////////////////////////////////////////
// @ FIFO that keep track of commands from the same IBP channel
//
////////////////////////////////////////////////////////////////////////////// 
wire [`npuarc_LQ_PTR_DEPTH:0] lq_mem_cmd_pending_r;

npuarc_alb_dmp_simple_fifo #(
    .DEPTH  (`npuarc_DMP_FIFO_DEPTH),  
    .DEPL2  (`npuarc_LQ_PTR_DEPTH),  
    .D_W    (`npuarc_LQ_PTR_DEPTH)  
   )
   u_alb_dmp_lq_cmd_fifo_0 (
  .clk       (clk               ),             
  .rst_a     (rst_a             ),           
  
  .push      (lq_mem_cmd_to_fifo),            
  .data_in   (lq_cmd_rd_ptr     ),         
  .pop       (lq_mem_data_pop   ),             
  
  .head      (lq_mem_data_rd_ptr)               
);

npuarc_alb_dmp_lq_cmd_track #(
    .D_W    (`npuarc_LQ_PTR_DEPTH+1)  
   )
   u_alb_dmp_lq_cmd_track_0 (
  .clk               (clk                 ),     
  .rst_a             (rst_a               ),   

  .cmd_push          (lq_mem_cmd_to_fifo  ), 
  .cmd_pop           (lq_mem_data_pop     ), 

  .cmd_pending_r     (lq_mem_cmd_pending_r)
);   






///////////////////////////////////////////////////////////////////////////////
// @ Final data read pointer
// 
//////////////////////////////////////////////////////////////////////////////
always @*
begin : lq_data_rd_ptr_PROC
  casez (lq_gnt_r)
  5'b00001:  lq_data_rd_ptr = lq_mem_data_rd_ptr;
  default: lq_data_rd_ptr   = {`npuarc_LQ_PTR_DEPTH{1'b0}};
  endcase
end

///////////////////////////////////////////////////////////////////////////////
// @ Acceptance of the read data
// 
//////////////////////////////////////////////////////////////////////////////
always @*
begin : lq_rd_accept_PROC
  // We accept the read data as long as the result bus is able to take our
  // request
  //
  lq_mem_rd_accept      = 1'b0;
  
  casez (lq_gnt_r)
  5'b00001: lq_mem_rd_accept      = ~(lq_rb_busy_r); 
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept
  default:          
    ;
  endcase
end

// spyglass enable_block W193
///////////////////////////////////////////////////////////////////////////////
// @ Asynchronous logic dertiming toggling conditions
// 
//////////////////////////////////////////////////////////////////////////////
always @*
begin : lq_toggle_PROC
  
  // Check if we can toggle the arbitration
  //
  lq_toggle_ok =  lq_rb_toggle_ok             
                & lq_mem_toggle_arb_ok
                ;

  // Toggle acceptance when we the LQ target is providing valid data and we
  // are not accepting it. 

  lq_toggle =   lq_toggle_ok
              & (  1'b0
                  | ((lq_mem_rd_valid  | lq_mem_err_rd)  & (~(lq_gnt_r[0])))
                );
end

///////////////////////////////////////////////////////////////////////////////
// @ Arbitrations
// 
//////////////////////////////////////////////////////////////////////////////

assign lq_pending[0] = (| lq_mem_cmd_pending_r);
assign lq_pending[1] = 1'b0;
assign lq_pending[2] = 1'b0;
assign lq_pending[3] = 1'b0;
assign lq_pending[4] = 1'b0;

npuarc_alb_dmp_lq_rrobin u_alb_dmp_lq_rrobin (
  .clk        (clk       ),         
  .rst_a      (rst_a     ),       

  .lq_pending (lq_pending),        
  .lq_toggle  (lq_toggle ),     
  
  .lq_gnt_r   (lq_gnt_r  )         
);


/////////////////////////////////////////////////////////////////////////////
// Clock gate enables
// 
//////////////////////////////////////////////////////////////////////////////

reg    lq_rb_data_even_cg0;
reg    lq_rb_data_odd_cg0;

always @*
begin : lq_rb_data_cg0_PROC
  lq_rb_data_even_cg0 =   1'b0
                         | lq_mem_data_even_cg0
                         ;
  
  lq_rb_data_odd_cg0 =   1'b0
                         | lq_mem_data_odd_cg0
                         ;

end

/////////////////////////////////////////////////////////////////////////////
// @
// 
//////////////////////////////////////////////////////////////////////////////
reg [`npuarc_DOUBLE_RANGE]    lq_rb_data_even_nxt;
reg [`npuarc_DOUBLE_RANGE]    lq_rb_data_odd_nxt;

always @*
begin : lq_rb_data_nxt_PROC
  lq_pass              = 1'b0;
  lq_pass_err          = 1'b0;
  lq_rb_tag            = lq_fifo_grad_tag;
  lq_rb_sex            = lq_fifo_data_sex;        
  lq_rb_size           = lq_fifo_data_size;       
  lq_rb_addr           = lq_fifo_addr;

  casez (lq_gnt_r)
  5'b00001:  
  begin
    lq_pass              = lq_mem_pass;
    lq_pass_err          = lq_mem_pass_err;
    lq_rb_data_even_nxt  = lq_mem_rd_data;
    lq_rb_data_odd_nxt   = lq_mem_rd_data;
  end
  default:          
  begin
    lq_pass              = 1'b0;
    lq_pass_err          = 1'b0;
    lq_rb_data_even_nxt  = {`npuarc_DOUBLE_SIZE{1'b0}};
    lq_rb_data_odd_nxt   = {`npuarc_DOUBLE_SIZE{1'b0}};
  end  
  endcase
end

/////////////////////////////////////////////////////////////////////////////
// @ FSM
// 
//////////////////////////////////////////////////////////////////////////////
parameter LQ_STATE_DEFAULT   = 1'b0;
parameter LQ_STATE_WAIT_ACK  = 1'b1;

always @*
begin : lq_state_nxt_PROC
  
  lq_fifo_data_pop  = 1'b0;
  
  lq_rb_busy_nxt    = lq_rb_busy_r;
  
  lq_rb_req         = lq_pass;
  lq_rb_err         = lq_pass_err;
  lq_rb_user_mode   = lq_fifo_data_user_mode;
  lq_rb_toggle_ok   = 1'b1;
  
  lq_err_nxt        = lq_err_r;
  
  lq_data_retire    = 1'b0;
  
  lq_state_cg0      = ~lq_empty_r;
  lq_state_nxt      = lq_state_r;
  
  case (lq_state_r)
  LQ_STATE_DEFAULT:
  begin
    if (lq_pass)
    begin
      // This is used to manage war hazards. There is no need to wait for the
      // result bus acknowledge for that. The load has finished and all stores
      // that may depend on it can be released.
      //
      lq_data_retire = 1'b1;
      
      if (lq_rb_ack)
      begin
        // I requested the result bus and got it right away
        //
        lq_fifo_data_pop = 1'b1;
      end
      else
      begin
        // Didnt have access to the result bus
        //
        lq_rb_toggle_ok = 1'b0;
        lq_rb_busy_nxt  = 1'b1;
        lq_err_nxt      = lq_pass_err;
        lq_state_nxt   = LQ_STATE_WAIT_ACK;
      end
    end
  end
  
  default:
  begin
    lq_data_retire    = 1'b1;
    lq_rb_req         = 1'b1;
    lq_rb_err         = lq_err_r;
    lq_rb_toggle_ok   = 1'b0;
    
    if (lq_rb_ack)
    begin
      lq_rb_toggle_ok  = 1'b1;
      lq_rb_busy_nxt   = 1'b0;
      lq_fifo_data_pop = 1'b1;
      lq_err_nxt       = 1'b0;
      lq_state_nxt     = LQ_STATE_DEFAULT;
    end
  end
  endcase
end





//////////////////////////////////////////////////////////////////////////////
// Synchronous processes
// 
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : lq_state_reg_PROC
  if (rst_a == 1'b1)
  begin
    lq_state_r    <= LQ_STATE_DEFAULT;
    lq_err_r      <= 1'b0;
    lq_rb_busy_r  <= 1'b0;
  end
  else if (lq_state_cg0)
  begin
    lq_state_r    <= lq_state_nxt;
    lq_err_r      <= lq_err_nxt;
    lq_rb_busy_r  <= lq_rb_busy_nxt;
  end
end



// leda NTL_RST03 off
// leda S_1C_R off
// LMD: A flipflop without reset
// LJ:  Datapath element, doesn't require reset
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
// KS: Conditional reset datapath when safety enabled
always @(posedge clk)
begin : lq_rb_data_even_reg_PROC
  
  if (lq_rb_data_even_cg0 == 1'b1)
  begin
    lq_rb_data_even_r <= lq_rb_data_even_nxt;
  end
end

always @(posedge clk)
begin : lq_rb_data_odd_reg_PROC
  
  if (lq_rb_data_odd_cg0 == 1'b1)
  begin
    lq_rb_data_odd_r  <= lq_rb_data_odd_nxt;
  end
end

// leda S_1C_R on
// leda NTL_RST03 on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01




endmodule // alb_dmp_lq

