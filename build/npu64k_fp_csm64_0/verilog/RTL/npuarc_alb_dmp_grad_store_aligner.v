// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2016 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary 
// work of Synopsys, Inc., and is fully protected under copyright and 
// trade secret laws. You may not view, use, disclose, copy, or distribute 
// this file or any information contained herein except pursuant to a 
// valid written license from Synopsys, Inc.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
//                     
//                     
//   ALB_DMP_GRAD_STORE_ALIGNER                  
//                     
//                     
//                     
//
// ===========================================================================
//
// Description:
//  This module alignes the Graduating store data in accordance with the data banks. This 
//  helps in Write Queue on-the-fly alignement to always store the bank aligned
//  data.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_grad_store_aligner.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_dmp_grad_store_aligner (
// leda NTL_CON13C off
// LMD: non driving port
// LJ: some bits of inputs vectors are not used
  input                           ecc_dmp_disable,
  input [2:0]                     addr_r,

  input [`npuarc_DMP_BE_RANGE]           wq_ecc_mask_r,
  input                           wq_store_grad_match0_lo,
  input                           wq_store_grad_match0_hi,
  input                           wq_store_grad_match1_lo,
  input                           wq_store_grad_match1_hi,
  input [1:0]                     wq_grad_r,
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input [1:0]                     wq_grad_data_src_r,
// spyglass enable_block W240
  input [`npuarc_DMP_BE_RANGE]           wq_data_mask_r,

  input [`npuarc_DMP_DATA_RANGE]         wq_data_r,

  input [`npuarc_DOUBLE_RANGE]           wa_retire0_data,
  input [`npuarc_DOUBLE_RANGE]           wa_retire1_data,
  output reg [1:0]                wq_grad_prel,
  output reg [`npuarc_DMP_DATA_RANGE]   wq_wr_data   
// leda NTL_CON13C on
);

reg [`npuarc_DMP_DATA_RANGE]             wa_data_prel;
reg [`npuarc_DMP_DATA_RANGE]             wa_retire_data_prel;


reg [`npuarc_DMP_DATA_RANGE]             data_extract0;
reg [`npuarc_DMP_DATA_RANGE]             data_extract1;
wire                              store_grad_match0; 
wire                              store_grad_match1; 
reg [`npuarc_DMP_DATA_RANGE]             data_temp;

reg [`npuarc_DMP_DATA_RANGE]             wr_data0;

always @*
begin : data_temp_PROC
  //
  //
  // in case of partial gradualtion, we need to shift the data before 
  // getting data from retirement
  //
  data_temp = wq_data_r;
  
  if (~wq_data_mask_r[0])
  begin
    case(wq_data_mask_r)
    8'b1111_1110:
    begin
//      data_temp = wq_data_r << 1*8;
      data_temp = {wq_data_r[55:0], wq_data_r[63:56]};
    end
    8'b1111_1100:
    begin
//      data_temp = wq_data_r << 2*8;
      data_temp = {wq_data_r[47:0], wq_data_r[63:48]};
    end
    8'b1111_1000:
    begin
//      data_temp = wq_data_r << 3*8;
      data_temp = {wq_data_r[39:0], wq_data_r[63:40]};
    end
    8'b1111_0000:
    begin
//      data_temp = wq_data_r << 4*8;
      data_temp = {wq_data_r[31:0], wq_data_r[63:32]};
    end
    8'b1110_0000:
    begin
//      data_temp = wq_data_r << 5*8;
      data_temp = {wq_data_r[23:0], wq_data_r[63:24]};
    end
    8'b1100_0000:
    begin
//      data_temp = wq_data_r << 6*8;
      data_temp = {wq_data_r[15:0], wq_data_r[63:16]};
    end
     8'b1000_0000:
    begin
//      data_temp = wq_data_r << 7*8;
      data_temp = {wq_data_r[7:0], wq_data_r[63:8]};
    end
    default:
    begin
      data_temp = wq_data_r;
    end
    endcase    
  end
  else
  begin
    if (~ecc_dmp_disable)
    begin
      //
      // In case of ECC, consider shifting   
      casez(wq_ecc_mask_r)
      8'b????_??10:
      begin
//      data_temp = wq_data_r >> 1*8;
        data_temp = {wq_data_r[7:0], wq_data_r[63:8]};
      end
      8'b????_?100:
      begin
//      data_temp = wq_data_r >> 2*8;
        data_temp = {wq_data_r[15:0], wq_data_r[63:16]};
      end
      8'b????_1000:
      begin
//      data_temp = wq_data_r >> 3*8;
        data_temp = {wq_data_r[23:0], wq_data_r[63:24]};
      end
      8'b???1_0000:
      begin
//      data_temp = wq_data_r >> 4*8;
        data_temp = {wq_data_r[31:0], wq_data_r[63:32]};
      end
      8'b??10_0000:
      begin
//      data_temp = wq_data_r >> 5*8;
        data_temp = {wq_data_r[39:0], wq_data_r[63:40]};
      end
      8'b?100_0000:
      begin
//      data_temp = wq_data_r >> 6*8;
        data_temp = {wq_data_r[47:0], wq_data_r[63:48]};
      end
      8'b1000_0000:
      begin
//      data_temp = wq_data_r >> 7*8;
        data_temp = {wq_data_r[55:0], wq_data_r[63:56]};
      end
      default:
      begin
        data_temp = wq_data_r;
      end
      endcase    
    end
  end
end

// match in channel 0
//
//
assign store_grad_match0 = wq_store_grad_match0_hi | wq_store_grad_match0_lo;
  
//
// match in channel 1
//
assign store_grad_match1 = wq_store_grad_match1_hi | wq_store_grad_match1_lo;


always @*
begin : data_extract_PROC
  //
  //
  // This extractes the data from the retirement based on the wq_grad_data_src_r
  // if set indicates that the data is coming from upper 32 bit, otherwise lower 32 bit 
  // of the retirement
  //

  data_extract0   = {`npuarc_DMP_DATA_BITS{1'b0}};
  data_extract1   = {`npuarc_DMP_DATA_BITS{1'b0}};

  case (wq_grad_r)
  2'b01:
  begin
    //
    //
    // only graduating Lo part 
    //
    data_extract0 = wq_grad_data_src_r[0]
                  ? {data_temp[63:32], wa_retire0_data[63:32]} 
                  : {data_temp[63:32], wa_retire0_data[31:0]};

    data_extract1 = wq_grad_data_src_r[0]
                  ? {data_temp[63:32], wa_retire1_data[63:32]}
                  : {data_temp[63:32], wa_retire1_data[31:0]};
    wq_grad_prel  = 2'b00;
    wa_data_prel  = store_grad_match0
                  ? data_extract0
                  : data_extract1;    
  end

  2'b10:
  begin
    //
    //
    // only graduating Hi part
    //
  
    data_extract0 = wq_grad_data_src_r[1]
                  ? {wa_retire0_data[63:32],data_temp[31:0]}
                  : {wa_retire0_data[31:0], data_temp[31:0]};

    data_extract1 = wq_grad_data_src_r[1]
                  ? {wa_retire1_data[63:32],data_temp[31:0]}
                  : {wa_retire1_data[31:0], data_temp[31:0]};

    wq_grad_prel  = 2'b00;
    wa_data_prel  = store_grad_match0
                  ? data_extract0
                  : data_extract1;
  end

  2'b11:
  begin
    //
    //
    // Both are graduating
    //
    case ({store_grad_match1, store_grad_match0})
    2'b01:
    begin
      //
      // Channel 0 has a match
      //
      if (wq_store_grad_match0_hi == wq_store_grad_match0_lo)
      begin
        //
        // data will be coming from same tag
        //
        wq_grad_prel  = 2'b00;
        wa_data_prel  = wa_retire0_data;
      end
      else
      begin
        //
        // data will be coming from two different tags
        //
        if (wq_store_grad_match0_lo)
        begin
          //
          // lo part has a match
          //
          wq_grad_prel = {wq_grad_r[1], 1'b0};
          wa_data_prel = wq_grad_data_src_r[0] 
                       ? {data_temp[63:32], wa_retire0_data[63:32]}
                       : {data_temp[63:32], wa_retire0_data[31:0]};       
        end
        else
        begin
          //
          // hi part has a match
          //
          wq_grad_prel = {1'b0, wq_grad_r[1]};
          wa_data_prel = wq_grad_data_src_r[1] 
                       ? {wa_retire0_data[63:32], data_temp[31:0]}
                       : {wa_retire0_data[31:0],  data_temp[31:0]};
        end
      end
    end

    2'b10:
    begin
      //
      // Channel 1 has a match
      //
      if (wq_store_grad_match1_hi == wq_store_grad_match1_lo)
      begin
        //
        // data will be coming from same tag
        //
        wq_grad_prel  = 2'b00;
        wa_data_prel  = wa_retire1_data;
      end
      else
      begin
        //
        // data will be coming from two different tags
        //
        if (wq_store_grad_match1_lo)
        begin
          //
          // lo part has a match
          //
          wq_grad_prel = {wq_grad_r[1], 1'b0};
          wa_data_prel = wq_grad_data_src_r[0] 
                       ? {data_temp[63:32], wa_retire1_data[63:32]}
                       : {data_temp[63:32], wa_retire1_data[31:0]};       
        end
        else
        begin
          //
          // hi part has a match
          //
          wq_grad_prel = {1'b0, wq_grad_r[1]};
          wa_data_prel = wq_grad_data_src_r[1] 
                       ? {wa_retire1_data[63:32], data_temp[31:0]}
                       : {wa_retire1_data[31:0],  data_temp[31:0]};
        end
      end
    end

    2'b11:
    begin
      //
      // Both Channel has a match
      //
      //
      // data will be coming from two different tag
      //
      wq_grad_prel  = 2'b00;

      // Lo part
      //
      if (wq_store_grad_match0_lo)
      begin
        //
        // Channel 0 has a lo match
        //
        wa_data_prel[31:0]   = wq_grad_data_src_r[0]
                             ? wa_retire0_data[63:32]     
                             : wa_retire0_data[31:0];
      end
      else //if (wq_store_grad_match1_lo)
      begin
        //
        // Channel 1 has a lo match
        //
        wa_data_prel[31:0]   = wq_grad_data_src_r[0]
                             ? wa_retire1_data[63:32]     
                             : wa_retire1_data[31:0];
      end       
      
      // Hi Part
      //
      if (wq_store_grad_match0_hi)
      begin
        //
        // Channel 0 has a hi match
        //
        wa_data_prel[63:32]  = wq_grad_data_src_r[1]
                             ? wa_retire0_data[63:32]     
                             : wa_retire0_data[31:0];
      end
      else //if (wq_store_grad_match1_hi)
      begin
        //
        // Channel 1 has a hi match
        //
        wa_data_prel[63:32]  = wq_grad_data_src_r[1]
                             ? wa_retire1_data[63:32]     
                             : wa_retire1_data[31:0];
      end
      
    end
 
    default:
    begin
      //
      //
      wq_grad_prel  = 2'b00;
      wa_data_prel  = wa_retire0_data;
    end
    endcase
  end
  default:
  begin
    //
    //
    wq_grad_prel    = 2'b00;
    wa_data_prel    = {`npuarc_DMP_DATA_BITS{1'b0}};
  end
  endcase  
end

always @*
begin : wa_retire_data_prel_PROC
  //
  //
  // we use data_shift to align the data in case of
  // stores crossing from bank3 to bank1
  // hence we put store in to two entries in WQ.
  //
  wa_retire_data_prel = wa_data_prel;
  
  if (~wq_data_mask_r[0])
  begin
    case(wq_data_mask_r)
    8'b1111_1110:
    begin
      wa_retire_data_prel = {wa_data_prel[7:0], wa_data_prel[63:8]};
    end
    8'b1111_1100:
    begin
      wa_retire_data_prel = {wa_data_prel[15:0], wa_data_prel[63:16]};
    end
    8'b1111_1000:
    begin
      wa_retire_data_prel = {wa_data_prel[23:0], wa_data_prel[63:24]};
    end
    8'b1111_0000:
    begin
      wa_retire_data_prel = {wa_data_prel[31:0], wa_data_prel[63:32]};
    end
    8'b1110_0000:
    begin
      wa_retire_data_prel = {wa_data_prel[39:0], wa_data_prel[63:40]};
    end
    8'b1100_0000:
    begin
      wa_retire_data_prel = {wa_data_prel[47:0], wa_data_prel[63:48]};
    end
     8'b1000_0000:
    begin
      wa_retire_data_prel = {wa_data_prel[55:0], wa_data_prel[63:56]};
    end
    default:
    begin
      wa_retire_data_prel = 64'd0;
    end
    endcase    
  end
end


//////////////////////////////////////////////////////////////////////////////
//
//  Write0 data adjustment
//
//////////////////////////////////////////////////////////////////////////////
// 
// This will help in writing the data in the correct lane
//
always @*
begin : wr_data0_PROC
  if (~(&wq_ecc_mask_r) & (~ecc_dmp_disable))
  begin 
    //
    // Adjust the data according to the ECC Mask
    case (addr_r)
    3'b000:
    begin
      wr_data0      =  wa_retire_data_prel;
  //    wr_data1      =  wa_retire_data_prel;
    end
    3'b001:
    begin
      wr_data0      =  {wa_retire_data_prel[55:0], {8{1'b0}}};
  //    wr_data1      =  {{56{1'b0}}, wa_retire_data_prel[63:56]};
    end
    3'b010:
    begin
      wr_data0      =  {wa_retire_data_prel[47:0], {16{1'b0}}};
  //    wr_data1      =  {{48{1'b0}}, wa_retire_data_prel[63:48]};
    end
    3'b011:
    begin
      wr_data0      =  {wa_retire_data_prel[39:0], {24{1'b0}}};
  //    wr_data1      =  {{40{1'b0}}, wa_retire_data_prel[63:40]};
    end
    3'b100:
    begin
      wr_data0      =  wa_retire_data_prel;
  //    wr_data1      =  {{32{1'b0}}, wa_retire_data_prel[63:32]};
    end
    3'b101:
    begin
      wr_data0      =  {wa_retire_data_prel[55:0], {8{1'b0}}};   
  //    wr_data1      =  {{24{1'b0}}, wa_retire_data_prel[63:24]};
    end
    3'b110:
    begin
      wr_data0      =  {wa_retire_data_prel[47:0], {16{1'b0}}};
  //    wr_data1      =  {{16{1'b0}}, wa_retire_data_prel[63:16]};
    end
    default:   // 3'b111:
    begin
      wr_data0      =  {wa_retire_data_prel[39:0], {24{1'b0}}};
  //    wr_data1      =  {{8{1'b0}}, wa_retire_data_prel[63:8]};
    end
    endcase
  end
  else
  begin
    //
    // ECC mask is all set, then no adjustment required
    //
    wr_data0      =  wa_retire_data_prel;
  end
end

//////////////////////////////////////////////////////////////////////////////
//
// Putting the write data in the correct lane
//
//////////////////////////////////////////////////////////////////////////////
// Step (2): To write the data in the correct lane
//
always @*
begin : wq_wr_data0_data1_prel_PROC
  //
  //
  if (~ecc_dmp_disable)
  begin
    // First Byte
    //
    case (1'b1)
    wq_ecc_mask_r[0]: wq_wr_data[7:0] = wr_data0[7:0];
    default:          wq_wr_data[7:0] = wq_data_r[7:0];
    endcase
  
    // Second Byte
    //
    case (1'b1)
    wq_ecc_mask_r[1]: wq_wr_data[15:8] = wr_data0[15:8];
    default:          wq_wr_data[15:8] = wq_data_r[15:8];
    endcase
  
    // Third Byte
    //
    case (1'b1)
    wq_ecc_mask_r[2]: wq_wr_data[23:16] = wr_data0[23:16];
    default:          wq_wr_data[23:16] = wq_data_r[23:16];
    endcase

    // Fourth Byte
    //
    case (1'b1)
    wq_ecc_mask_r[3]: wq_wr_data[31:24] = wr_data0[31:24];
    default:          wq_wr_data[31:24] = wq_data_r[31:24];
    endcase

    // Fifth Byte
    //
    case (1'b1)
    wq_ecc_mask_r[4]: wq_wr_data[39:32] = wr_data0[39:32];
    default:          wq_wr_data[39:32] = wq_data_r[39:32];
    endcase
  
    // Sixth Byte
    //
    case (1'b1)
    wq_ecc_mask_r[5]: wq_wr_data[47:40] = wr_data0[47:40];
    default:          wq_wr_data[47:40] = wq_data_r[47:40];
    endcase
    
    // Seventh Byte
    //
    case (1'b1)
    wq_ecc_mask_r[6]: wq_wr_data[55:48] = wr_data0[55:48];
    default:          wq_wr_data[55:48] = wq_data_r[55:48];
    endcase
    
    // Eighth Byte
    //
    case (1'b1)
    wq_ecc_mask_r[7]: wq_wr_data[63:56] = wr_data0[63:56];
    default:          wq_wr_data[63:56] = wq_data_r[63:56];
    endcase
  end
  else
  begin
    //
    //   
    wq_wr_data = wr_data0;  
  end  
end
endmodule // alb_dmp_pre_store_aligner
