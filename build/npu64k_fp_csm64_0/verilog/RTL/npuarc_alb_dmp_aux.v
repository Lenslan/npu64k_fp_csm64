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
//  #####   #    #  #####             ##    #    #  #    #
//  #    #  ##  ##  #    #           #  #   #    #   #  #
//  #    #  # ## #  #    #          #    #  #    #    ##
//  #    #  #    #  #####           ######  #    #    ##
//  #    #  #    #  #               #    #  #    #   #  #
//  #####   #    #  #      #######  #    #   ####   #    #
//
// ===========================================================================
//
// Description:
//  This module implements the DMP baseline aux register(s).
//
//  When configured with a Data Cache, this module also provides a conduit
//  for auxiliary register reads from the Data Cache auxiliary register read
//  port and credential checking interface.
//
//  When configured without a cluster auxiliary unit (CCAUX), this module
//  implements in full the auxiliary register AUX_NON_VOLATILE_LIMIT (0x5e).
//  When configured with a CCAUX unit, this module implements a shadow copy
//  of the common AUX_NON_VOLATILE_LIMIT register provided by the CCAUX unit.
//  The shadow copy is updated whenever a change in its value is detected.
//  This keeps the local copy in-sync with the global copy, with a one-cycle
//  delay. The DMP uses only the shadow copy, thereby isolating it from any
//  signal timing issues caused by propagation of the shared copy to the cores.
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"


//POST_PROCESS { prefix:"//D:", wire_prefix:"t_", edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_dmp_aux (
// leda NTL_CON13C off
// LMD: non driving port
// LJ: some bits of inputs vectors are not used
  ////////// General input signals ///////////////////////////////////////////
  //
  input                     clk,                  //  clock
  input                     rst_a,                //  reset
  input                     aux_dc_aux_busy,      //  (X3) busy
  output reg                aux_busy,             //  (X3) busy

  ////////// Interface with aux ctl ///////////////////////////////////////////
  //
  input [`npuarc_DATA_RANGE]       aux_wdata_r,          //  (WA) Aux write data

  input                     aux_ren_r,            //  (X3) Aux Reg Enable
  input [4:0]               aux_raddr_r,          //  (X3) Aux Reg Address 
  input                     aux_wen_r,            //  (WA) Aux Reg Enable
  input [4:0]               aux_waddr_r,          //  (WA) Aux Reg Address
  
  output reg [`npuarc_DATA_RANGE]  aux_rdata,            //  (X3) LR read data
  output reg                aux_illegal,          //  (X3) SR/LR illegal
  output reg                aux_k_rd,             //  (X3) needs Kernel Read
  output reg                aux_k_wr,             //  (X3) needs Kernel Write
  output reg                aux_unimpl,           //  (X3) Invalid Reg
  output reg                aux_serial_sr,        //  (X3) SR group flush pipe
  output reg                aux_strict_sr,        //  (X3) SR flush pipe
  
  input                     aux_dper_ren_r,       //  (X3) Aux Reg Enable
  input                     aux_dper_raddr_r,     //  (X3) Aux Reg Address
  input                     aux_dper_wen_r,       //  (WA) Aux Reg Enable  
  input                     aux_dper_waddr_r,     //  (WA) Aux Ref Address
  output reg [`npuarc_DATA_RANGE]  aux_dper_rdata,       //  (X3) LR read data
  output reg                aux_dper_illegal,     //  (X3) SR/LR illegal
  output reg                aux_dper_k_rd,        //  (X3) needs Kernel Read
  output reg                aux_dper_k_wr,        //  (X3) needs Kernel Write
  output reg                aux_dper_unimpl,      //  (X3) Invalid Reg
  output reg                aux_dper_serial_sr,   //  (X3) SR group flush pipe
  output reg                aux_dper_strict_sr,   //  (X3) SR flush pipe

  //////////// Mux-in info coming from dc_aux //////////////////////////// 
  //
  input [`npuarc_DATA_RANGE]       aux_dc_aux_rdata,     //  (X3) LR read data
  input                     aux_dc_aux_illegal,   //  (X3) SR/LR illegal
  input                     aux_dc_aux_k_rd,      //  (X3) needs Kernel Read
  input                     aux_dc_aux_k_wr,      //  (X3) needs Kernel Write
  input                     aux_dc_aux_unimpl,    //  (X3) Invalid Reg
  input                     aux_dc_aux_serial_sr, //  (X3) SR group flush pipe
  input                     aux_dc_aux_strict_sr, //  (X3) SR flush pipe

  //////////// Interface with DMP ////////////////////////////////////////// 
  //
  output  [3:0]             aux_dmp_dcache_attr,
  output                    aux_dmp_mem_attr,
  output reg  [3:0]         aux_volatile_base_r,
  output reg  [3:0]         aux_volatile_limit_r,
  output reg                aux_volatile_strict_r,
  output reg                aux_volatile_dis_r
// leda NTL_CON13C on
);

//!BCR { num: 94, val: 4026531842, name: "AUX_VOLATILE" }


reg  [3:0] aux_dmp_dcache_attr_r;
reg        aux_dmp_mem_attr_r;


// Local declarations.
//
reg        aux_volatile_cg0;        

reg [3:0]  aux_volatile_base_nxt;   
reg [3:0]  aux_volatile_limit_nxt;  
reg        aux_volatile_strict_nxt; 
reg        aux_volatile_dis_nxt;    


//////////////////////////////////////////////////////////////////////////////
// Reads
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : aux_read_PROC
  aux_rdata      = {`npuarc_DATA_SIZE{1'b0}};       
  aux_illegal    = 1'b0;     
  aux_k_rd       = 1'b0;        
  aux_k_wr       = 1'b0;       
  aux_unimpl     = 1'b1;      
  aux_serial_sr  = 1'b0;  
  aux_strict_sr  = 1'b0;
  aux_busy       = aux_dc_aux_busy;

// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept  
  if (aux_ren_r)
  begin
    // We have got selected
    //
    case ({7'b0000010, aux_raddr_r})
    `npuarc_DATA_UNCACHED_AUX:
    begin
      aux_rdata[31:28]  = aux_volatile_base_r; 
      aux_rdata[27:24]  = aux_volatile_limit_r; 
      aux_rdata[1]      = aux_volatile_strict_r;     
      aux_rdata[0]      = aux_volatile_dis_r;     
      aux_k_rd          = 1'b1;    
      aux_k_wr          = 1'b1;    
      aux_serial_sr     = 1'b1;  
      aux_unimpl        = 1'b0; 
    end
    
    default:
    begin
      aux_rdata        = aux_dc_aux_rdata;      
      aux_illegal      = aux_dc_aux_illegal;   
      aux_k_rd         = aux_dc_aux_k_rd;      
      aux_k_wr         = aux_dc_aux_k_wr;      
      aux_unimpl       = aux_dc_aux_unimpl;    
      aux_serial_sr    = aux_dc_aux_serial_sr; 
      aux_strict_sr    = aux_dc_aux_strict_sr; 
    end                   
    endcase   
  end
end

// spyglass enable_block W193
//////////////////////////////////////////////////////////////////////////////
// Writes
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : aux_write_PROC
  aux_volatile_cg0          = aux_wen_r & ({7'b0000010, aux_waddr_r} == `npuarc_DATA_UNCACHED_AUX);
  
  aux_volatile_base_nxt     = aux_wdata_r[31:28];
  aux_volatile_limit_nxt    = aux_wdata_r[27:24];
  aux_volatile_strict_nxt   = aux_wdata_r[1];
  aux_volatile_dis_nxt      = aux_wdata_r[0];
end


//////////////////////////////////////////////////////////////////////////////
// Synchronous processes
//
//////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin : aux_data_unc_reg_PROC
  if (rst_a == 1'b1)
  begin
    aux_volatile_base_r             <= 4'd`npuarc_AUX_VOLATILE_BASE;
    aux_volatile_limit_r            <= 4'd`npuarc_AUX_VOLATILE_LIMIT;
    aux_volatile_strict_r           <= 1'b`npuarc_AUX_VOLATILE_STRICT_ORDERING;
    aux_volatile_dis_r              <= 1'b`npuarc_AUX_VOLATILE_DISABLE;
  end
  else if (aux_volatile_cg0 == 1'b1)
  begin
    aux_volatile_base_r           <= aux_volatile_base_nxt;   
    aux_volatile_limit_r          <= aux_volatile_limit_nxt;  
    aux_volatile_strict_r         <= aux_volatile_strict_nxt; 
    aux_volatile_dis_r            <= aux_volatile_dis_nxt;    
  end
end

//////////////////////////////////////////////////////////////////////////////
// Reading from DMP_PERIPHERAL
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : aux_dper_read_PROC
  aux_dper_rdata      = {`npuarc_DATA_SIZE{1'b0}};       
  aux_dper_illegal    = 1'b0;     
  aux_dper_k_rd       = 1'b0;        
  aux_dper_k_wr       = 1'b0;       
  aux_dper_unimpl     = 1'b1;      
  aux_dper_serial_sr  = 1'b0;  
  aux_dper_strict_sr  = 1'b0;
  
  if (aux_dper_ren_r)
  begin
    // We have got selected
    //
    case ({11'b0010_0000_101 ,aux_dper_raddr_r})
    `npuarc_DATA_MEM_ATTR_AUX:
    begin
      aux_dper_rdata[4]                         = aux_dmp_mem_attr_r;

      aux_dper_rdata[3:0]                       = aux_dmp_dcache_attr_r;
      aux_dper_k_rd                             = 1'b1;    
      aux_dper_k_wr                             = 1'b1;    
      aux_dper_serial_sr                        = 1'b1;  
      aux_dper_unimpl                           = 1'b0;


//!BCR { num: 523, val: 3, name: "DATA_MEM_ATTR" }
    
    end
    
    default:
    begin
      aux_dper_rdata                            = {`npuarc_DATA_SIZE{1'b0}};       
      aux_dper_illegal                          = 1'b0;     
      aux_dper_k_rd                             = 1'b0;        
      aux_dper_k_wr                             = 1'b0;       
      aux_dper_unimpl                           = 1'b1;      
      aux_dper_serial_sr                        = 1'b0;  
      aux_dper_strict_sr                        = 1'b0;
    end
    endcase
  end
end

//////////////////////////////////////////////////////////////////////////////
// Synchronous process to implement aux_dmp_per_r register
//
//////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin : aux_dmp_per_reg_PROC
  if (rst_a == 1'b1)
  begin
    aux_dmp_mem_attr_r     <= 1'b0;
    aux_dmp_dcache_attr_r  <= 4'b0011;
  end
  else
  begin
    if (aux_dper_wen_r)
    begin
      // We have got selected
      //
      case ({11'b0010_0000_101, aux_dper_waddr_r})
      `npuarc_DATA_MEM_ATTR_AUX:
      begin
        aux_dmp_mem_attr_r    <= aux_wdata_r[4];
        aux_dmp_dcache_attr_r <= aux_wdata_r[3:0];
      end

// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept
    default: ;    
// spyglass enable_block W193  
      endcase
    end
  end
end



//////////////////////////////////////////////////////////////////////////////
//  Output assignments                                                                       //
//                                                                          
//////////////////////////////////////////////////////////////////////////////
assign aux_dmp_mem_attr     = aux_dmp_mem_attr_r;
assign  aux_dmp_dcache_attr = aux_dmp_dcache_attr_r;  

endmodule // alb_dmp_aux


