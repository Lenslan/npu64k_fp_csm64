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
// ALB_DMP_EXCPN                
//                
//                
//                
//
// ===========================================================================
//
// Description:
//  This module handles the exception generation in case of bus/memory/ecc errors.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_expn.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"


//POST_PROCESS { prefix:"//D:", wire_prefix:"t_", edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 }, edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_dmp_excpn (
// leda NTL_CON13C off
// LMD: non driving port
// LJ: some inputs are not used in certain configurations
  


  ////////// General input signals /////////////////////////////////////////
  //
  input                         clk,            // clock
  input                         rst_a,          // reset
  input                         db_active_r,    // debug insn is active
  input                         idle_req,      // from the halt mgr

  ////////// Interface to the X2 stage ///////////////////////////////
  //
  input                         x2_pass,             // X2 passing on instt
  input                         x2_load_r,           // X2 load  
  input                         x2_store_r,          // X2 store
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input [`npuarc_ADDR_RANGE]           x2_mem_addr0_r,      // X2 memory address
  input [`npuarc_ADDR_RANGE]           x2_mem_addr1_r,      // X2 memory address
// spyglass enable_block W240
  input [3:0]                   dc2_bank_sel_r,      // DC2 bank
  input [`npuarc_DMP_TARGET_RANGE]     dc2_target0_r,       // DC2 memory type 
  input                         dc2_volatile_region0,// DC2 region0 volatile 
  input                         dc2_volatile_region1,// DC2 region1 volatile 

  /////////// Interface to the dtlb   ////////////////////////////////
  //
  input                         x2_cache_byp_r,
  input                         dtlb_rslt0_cached,
 

  input                         dtlb_rslt1_cached,
  input [1:0]                   dc2_dtlb_miss,
  input                         dc2_lkup1_page_cross,

  ////////// Interface to the X3 stage ///////////////////////////////
  //
  input                         x3_enable,      // X3 enable
  input                         x3_load_r,      // X3 load  
  input                         x3_store_r,     // X3 store
  input                         dc3_pref,       // ALL sorts of prefetch

  ////////// Interface to the WA stage /////////////////////////////
  //
  input                         wa_restart_r,
  input                         mem_excpn_ack_r,
  
  ////////// AUX interface //////////////////////////////////////
  //
  input [3:0]                   aux_dccm_r,      // DCCM base address 
  input [7:0]         aux_memseg_r,   //  MEMSEG register
  input                         aux_volatile_dis_r,
  ////////// X3 Exception Interface ///////////////////////////////////////////
  //
  output reg                    dc3_excpn,           // DMP excpn ()
  output reg [`npuarc_DMP_EXCPN_RANGE] dc3_excpn_type,      // exception type
  output reg [7:0]              dc3_excpn_code,      // cause code

  ////////// Bus errors ////////////////////////////////////////////////////
  //
  input                         lq_err,
  input                         lq_rb_ack,
  input                         lq_err_user_mode,
  input [`npuarc_PADDR_RANGE]          lq_err_addr,
  
  input                         wq_err_r,
  input                         wq_err_user_mode_r,
  input [`npuarc_PADDR_RANGE]          wq_err_addr_r,
  output reg                    wq_err_ack,
  
  input                         mq_rd_err,
  input                         mq_wr_err,
  input                         mq_rb_ack,
  input                         mq_err_user_mode,
  input [`npuarc_PADDR_RANGE]          mq_err_addr,
  
  input                         mq_flush_err,
  output reg                    mq_flush_err_ack,
  input [`npuarc_DC_LBUF_RANGE]        mq_flush_err_addr,
  
  input                         rf_err_req,
  input [`npuarc_DC_LBUF_RANGE]        rf_err_addr,

  input                         dc4_dccm_ecc_db_error_r,
  input                         dc4_dc_ecc_db_error_r,




  ////////// DC4 Exception Interface /////////////////////////////////////////
  //
  output reg                    iexcpn_discarded,
  output reg                    dc4_excpn,            // DMP excpn (ECC, bus err)
  output reg                    dc4_excpn_user_mode_r,// 
  output reg [`npuarc_PADDR_RANGE]     dc4_excpn_addr_r,     //    
  output reg [`npuarc_DMP_EXCPN_RANGE] dc4_excpn_type      // exception type
//  output reg [7:0]              dc4_excpn_code        // cause code

// leda NTL_CON13C on
);

// Local declarations
//

// leda NTL_CON13A off
// LMD: non driving internal net
// LJ: some variables used in certain configurations
wire                dc2_target1_iccm0;
wire                dc2_target1_iccm1;
wire                dc2_target1_dccm;
wire                dc2_target1_vec_mem;

wire                iexcpn_discarded_nxt;
wire [`npuarc_ADDR_RANGE]  dccm_physical_limit;
wire                dc2_dccm_hole0;
wire                dc2_dccm_hole1;
wire                dc2_target0_dccm;
wire                dc2_dccm_non_phys_mem;
wire                dc2_dccm_cross_target;

wire                dc2_unaligned;
wire                dc2_debug_pae40;


wire                dc2_target0_dc;
wire                dc2_target1_dc;
wire                dc2_dc_cross_target;

wire                dc2_target0_volatile_mem;
wire                dc2_target1_volatile_mem;
wire                dc2_target0_non_volatile_mem;
wire                dc2_target1_non_volatile_mem;
wire                dc2_mem_volatile_cross;

wire                dc2_target0_mem;
wire                dc2_target1_mem;

wire                mq_bus_err_rd;
wire                mq_bus_err_wr;
wire                lq_bus_err_rd;
wire                wq_bus_err_wr;

wire                dc3_cg0;
reg                 dc3_non_phys_mem_r;
reg                 dc3_cross_target_r;
reg                 dc2_mem_adv;

reg                 dc4_mem_excpn_raise;
reg                 dc4_mem_excpn_cg0;
reg                 dc4_mem_excpn_nxt;        
reg                 dc4_mem_excpn_next;        
reg                 dc4_mem_excpn_user_mode_nxt;        
reg                 dc4_mem_excpn_user_mode_next;        

reg                 dc4_mem_excpn_r; 
reg                 dc4_mem_excpn_user_mode_r; 
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg  [`npuarc_PADDR_RANGE] dc4_mem_excpn_addr_r;
reg  [`npuarc_PADDR_RANGE] dc4_mem_excpn_addr_nxt;
//leda NTL_CON32 on
// leda NTL_CON13A on
//////////////////////////////////////////////////////////////////////////////
// Asynchronous  logic defining clock gate enabled
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc2_mem_adv_PROC
  dc2_mem_adv = x2_pass & x3_enable & (x2_load_r | x2_store_r);
end

assign dc3_cg0 = dc2_mem_adv | wa_restart_r;

//////////////////////////////////////////////////////////////////////////////
// Asynchronous logic computing the target for addr1 (unaligned)               
//                                                                           
//////////////////////////////////////////////////////////////////////////////
assign dc2_debug_pae40  =    1'b0
                           | (db_active_r & (|aux_memseg_r))
                           ;                         
assign dc2_target1_dccm =  1'b0
                         | (  (x2_mem_addr1_r[31:28] == aux_dccm_r) 
                            & (~dc2_debug_pae40))
                         ;

assign dc2_target1_vec_mem =  1'b0
                           ;

assign dc2_target1_iccm0 =  1'b0
                          ;
                          
assign dc2_target1_iccm1 =  1'b0
                          ;  

assign dc2_target1_per =  1'b0 
                          ;
assign dc2_target1_per2 =  1'b0 
                          ;


assign dccm_physical_limit[27:0]    = 28'd32767; 
assign dccm_physical_limit[31:28]   = aux_dccm_r;
//////////////////////////////////////////////////////////////////////////////
//                                                                           
//////////////////////////////////////////////////////////////////////////////
// spyglass disable_block WRN_1024
// SMD: unsigned argument passed to $unsigned function call
// SJ:  arguments unsigned by default

assign dc2_dccm_hole0  =   $unsigned(x2_mem_addr0_r) 
                         > $unsigned(dccm_physical_limit);
assign dc2_dccm_hole1  =   $unsigned(x2_mem_addr1_r)
                         > $unsigned(dccm_physical_limit);
// spyglass enable_block WRN_1024

//////////////////////////////////////////////////////////////////////////////
//                                                                           
//////////////////////////////////////////////////////////////////////////////
assign dc2_unaligned      = dc2_bank_sel_r[3] & dc2_bank_sel_r[0];

assign dc2_target0_dccm   =   (dc2_target0_r == `npuarc_DMP_TARGET_DCCM)
                            & (~dc2_debug_pae40);

assign dc2_dccm_non_phys_mem =  
    (dc2_target0_dccm & dc2_dccm_hole0)
  | (dc2_target0_dccm & dc2_unaligned & dc2_dccm_hole1);
 
assign dc2_dccm_cross_target =  
   (~dc2_target0_dccm & dc2_unaligned & dc2_target1_dccm);






assign dc2_target0_mem =   1'b0
                         | (   (dc2_target0_r == `npuarc_DMP_TARGET_DC)
                            && (dc2_volatile_region0)
                            && (~aux_volatile_dis_r));

assign dc2_target1_mem  =  1'b0
                          | (   (dc2_volatile_region1)
                             && (~aux_volatile_dis_r));


assign dc2_target0_dc    =   (dc2_target0_r == `npuarc_DMP_TARGET_DC)
                          && (  (~dc2_volatile_region0)
                              | aux_volatile_dis_r)
                           ;

assign dc2_target1_dc     = (   (~dc2_volatile_region1)
                              | (aux_volatile_dis_r))
                          ;

assign dc2_dc_cross_target = 
   (dc2_target0_dc     & dc2_unaligned & (~dc2_target1_dc))
 | (dc2_target0_mem    & dc2_unaligned & (~dc2_target1_mem))
 | (   ~(|dc2_dtlb_miss)   & dc2_lkup1_page_cross & (~x2_cache_byp_r) 
     &  (dtlb_rslt0_cached ^ dtlb_rslt1_cached))
 ; 


assign dc2_target0_volatile_mem =  
     ( dc2_target0_mem |  (dc2_target0_r == `npuarc_DMP_TARGET_MEM))                        // dcache target, volatile
   & (dc2_volatile_region0)
   & (~aux_volatile_dis_r);
    
assign dc2_target1_volatile_mem =  
     ( dc2_target1_mem |  (dc2_target0_r == `npuarc_DMP_TARGET_MEM))                        // dcache target, volatile
   & (dc2_volatile_region1)
   & (~aux_volatile_dis_r);
    
assign dc2_target0_non_volatile_mem =
     (dc2_target0_mem |  (dc2_target0_r == `npuarc_DMP_TARGET_MEM))  
   & (   (~dc2_volatile_region0)
       | (aux_volatile_dis_r)); 

assign dc2_target1_non_volatile_mem =
     ( dc2_target1_mem |  (dc2_target0_r == `npuarc_DMP_TARGET_MEM))  
   & (   (~dc2_volatile_region1)
       | (aux_volatile_dis_r)); 

assign dc2_mem_volatile_cross =  
   (dc2_unaligned & dc2_target0_volatile_mem      & (~dc2_target1_volatile_mem))
 | (dc2_unaligned & dc2_target0_non_volatile_mem  & (~dc2_target1_non_volatile_mem));


//////////////////////////////////////////////////////////////////////////////
//                                                                          
//                                                                           
//////////////////////////////////////////////////////////////////////////////
assign dc2_non_phys_mem =  1'b0
                        | dc2_dccm_non_phys_mem
                         ;

assign dc2_cross_target =  dc2_mem_volatile_cross
                         | dc2_dccm_cross_target
                         | dc2_dc_cross_target
                         ;
//////////////////////////////////////////////////////////////////////////////
//                                                                          
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc3_excpn_PROC
  
  dc3_excpn =    (x3_load_r          | x3_store_r)
               & (~dc3_pref) 
               & (dc3_non_phys_mem_r | dc3_cross_target_r);
  

  casez ({dc3_non_phys_mem_r, dc3_cross_target_r})
  2'b1?:  
  begin
    dc3_excpn_type = `npuarc_DMP_MEM_ERROR;
    dc3_excpn_code = 8'h11; 
  end

  2'b01:
  begin
    dc3_excpn_type = `npuarc_DMP_MEM_ERROR;
    dc3_excpn_code = 8'h12; 
  end
  
  default:
  begin
    dc3_excpn_type = `npuarc_DMP_NO_ERROR;
    dc3_excpn_code = 8'h00;
  end  
  endcase  
end

assign mq_bus_err_rd    = 1'b0
                         | mq_rd_err
                         | mq_wr_err
                         | rf_err_req
                         ;
assign mq_bus_err_wr    =  1'b0
                         | mq_flush_err
                         ;
assign lq_bus_err_rd    = lq_err;
assign wq_bus_err_wr    = wq_err_r; 
///////////////////////////////////////////////////////////////////////////
// Bus errors                                                              
//                                                                         
///////////////////////////////////////////////////////////////////////////
always @*
begin : dc4_mem_excpn_nxt_PROC
  
  wq_err_ack                  = 1'b0;
  mq_flush_err_ack            = 1'b0;
  
  dc4_mem_excpn_raise         = 1'b0;
  dc4_mem_excpn_nxt           = 1'b0;
  dc4_mem_excpn_user_mode_nxt = dc4_mem_excpn_user_mode_r;
  dc4_mem_excpn_addr_nxt      = dc4_mem_excpn_addr_r;

  casez ({mq_bus_err_rd, 
          lq_bus_err_rd, 
          wq_bus_err_wr, 
          mq_bus_err_wr, 
          1'b0,
          1'b0,
          1'b0
        })
  7'b1??????:
  begin
    // Miss queue read error
    //
    dc4_mem_excpn_raise         = 1'b1;
    dc4_mem_excpn_nxt           = mq_rb_ack | mq_wr_err | rf_err_req;
    dc4_mem_excpn_user_mode_nxt = mq_err_user_mode;
    
    if (rf_err_req)
    begin
      dc4_mem_excpn_addr_nxt    = {`npuarc_PADDR_SIZE{1'b0}};
      dc4_mem_excpn_addr_nxt[`npuarc_DC_LBUF_RANGE]   
                                = rf_err_addr;
    end
    else
    begin
      dc4_mem_excpn_addr_nxt    = mq_err_addr;
    end
  end
  
  7'b01?????:
  begin
    // Load queue error
    //
    dc4_mem_excpn_raise         = 1'b1;
    dc4_mem_excpn_nxt           = lq_rb_ack;
    dc4_mem_excpn_user_mode_nxt = lq_err_user_mode;
    dc4_mem_excpn_addr_nxt      = lq_err_addr;
  end
  
  7'b001????:
  begin
    // Write queue error
    //
    wq_err_ack                  = 1'b1;
    
    dc4_mem_excpn_raise         = 1'b1;
    dc4_mem_excpn_nxt           = 1'b1;
    dc4_mem_excpn_user_mode_nxt = wq_err_user_mode_r;
    dc4_mem_excpn_addr_nxt      = wq_err_addr_r;
  end
  
  7'b0001???:
  begin
    // Eviction error
    //
    mq_flush_err_ack            = 1'b1;

    dc4_mem_excpn_raise         = 1'b1;
    dc4_mem_excpn_nxt           = 1'b1;
    dc4_mem_excpn_user_mode_nxt = 1'b0;  // always assume kernel mode
    dc4_mem_excpn_addr_nxt      = {`npuarc_PADDR_SIZE{1'b0}};
    dc4_mem_excpn_addr_nxt[`npuarc_DC_LBUF_RANGE]  
                                = mq_flush_err_addr;
  end
  7'b00001??:
  begin
    dc4_mem_excpn_raise         = 1'b0;
    dc4_mem_excpn_nxt           = 1'b0;
    dc4_mem_excpn_user_mode_nxt = 1'b0;
    dc4_mem_excpn_addr_nxt      = {`npuarc_PADDR_SIZE{1'b0}};
  end
  

  7'b000001?:
  begin
    dc4_mem_excpn_raise         = 1'b0;
    dc4_mem_excpn_nxt           = 1'b0;
    dc4_mem_excpn_user_mode_nxt = 1'b0;
    dc4_mem_excpn_addr_nxt      = {`npuarc_PADDR_SIZE{1'b0}};
  end

  7'b0000001:
  begin
    dc4_mem_excpn_raise         = 1'b0;
    dc4_mem_excpn_nxt           = 1'b0;
    dc4_mem_excpn_user_mode_nxt = 1'b0;
    dc4_mem_excpn_addr_nxt      = {`npuarc_PADDR_SIZE{1'b0}};
  end

// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept 
  default:;
  endcase
// spyglass enable_block W193  
  // Update memory exception state if there is not already a pending
  // memory error, or if any such pending memory exception is being
  // acknowledged in the current cycle.
  //
  // In case of idle_req from halt_mgr, the excpn could be cleared like getting an mem_excpn_ack_r
  // Though the excpn information is lost. this is done to avoid the live lock that is 
  // created between the halt bit set and dmp not being idle
  //
  dc4_mem_excpn_cg0 = (dc4_mem_excpn_raise & (~dc4_mem_excpn_r))
                     | (mem_excpn_ack_r | (dc4_excpn & idle_req))      // (1)
                     | (db_active_r & dc4_mem_excpn_r)
                     ;
end
wire   dc4_ecc_err;
assign dc4_ecc_err =   1'b0
                   | dc4_dccm_ecc_db_error_r
                   | dc4_dc_ecc_db_error_r
                   ;

assign  iexcpn_discarded_nxt = ( dc4_mem_excpn_raise & dc4_mem_excpn_r ) ? 1'b1 : (mem_excpn_ack_r ? 1'b0 : iexcpn_discarded);
always @( posedge clk or posedge rst_a )
begin
   if( rst_a == 1'b1 )
   begin
       iexcpn_discarded <= 1'b0;
   end
   else
   begin
       iexcpn_discarded <= iexcpn_discarded_nxt;
   end
end
///////////////////////////////////////////////////////////////////////////
// DC4 exceptions                                                             
//                                                                         
///////////////////////////////////////////////////////////////////////////
always @*
begin : dc4_excpn_PROC

  dc4_excpn             = dc4_mem_excpn_r  // bus error
                        | dc4_ecc_err      // ecc error 
                        ;             

  
  dc4_excpn_user_mode_r = dc4_mem_excpn_user_mode_r;
  dc4_excpn_addr_r      = dc4_mem_excpn_addr_r;
  
  dc4_excpn_type        = `npuarc_DMP_MEM_ERROR; 
  if (   dc4_ecc_err
      )
  begin
    dc4_excpn_type      = `npuarc_DMP_ECC_ERROR;
  end
end

///////////////////////////////////////////////////////////////////////////
// Synchronous process 
//
///////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : dc3_excp_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc3_non_phys_mem_r    <= 1'b0;
    dc3_cross_target_r    <= 1'b0;
  end
  else if (dc3_cg0)
  begin
      dc3_non_phys_mem_r  <= dc2_non_phys_mem & (x2_load_r | x2_store_r);
      dc3_cross_target_r  <= dc2_cross_target & (x2_load_r | x2_store_r);
  end
end

always @*
begin : dc4_mem_excpn_comb_PROC
  dc4_mem_excpn_next             = dc4_mem_excpn_r;
  dc4_mem_excpn_user_mode_next   = dc4_mem_excpn_user_mode_r;
  begin
    if (dc4_mem_excpn_cg0)
    begin
      dc4_mem_excpn_next            = dc4_mem_excpn_nxt;
      dc4_mem_excpn_user_mode_next  = dc4_mem_excpn_user_mode_nxt;
    end
  end
end

always @(posedge clk or posedge rst_a)
begin : dc4_mem_excpn_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_mem_excpn_r           <= 1'b0;
    dc4_mem_excpn_user_mode_r <= 1'b0;
  end
  else
  begin
    dc4_mem_excpn_r           <= dc4_mem_excpn_next;
    dc4_mem_excpn_user_mode_r <= dc4_mem_excpn_user_mode_next;
  end
end

// leda NTL_RST03 off
// leda S_1C_R off
// LMD: A flipflop without reset
// LJ:  Data path signals that dont require a reset
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
always @(posedge clk)
begin : dc4_mem_excpn_addr_reg_PROC
  if (dc4_mem_excpn_cg0 == 1'b1)                                
  begin                                                 
    dc4_mem_excpn_addr_r    <= dc4_mem_excpn_addr_nxt;  
  end                                                   
end
// leda S_1C_R on
// leda NTL_RST03 on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01

endmodule // alb_dmp_excpn


