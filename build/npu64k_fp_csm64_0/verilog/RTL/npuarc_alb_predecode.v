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
// ######   ######   #######
// #     #  #     #  #
// #     #  #     #  #
// ######   ######   #####    #######
// #        #   #    #
// #        #    #   #
// #        #     #  #######
//
//
//     ######   #######   #####   #######  ######   #######
//     #     #  #        #     #  #     #  #     #  #
//     #     #  #        #        #     #  #     #  #
//     #     #  #####    #        #     #  #     #  #####
//     #     #  #        #        #     #  #     #  #
//     #     #  #        #     #  #     #  #     #  #
//     ######   #######   #####   #######  ######   #######
//
// ===========================================================================
//
// Description:
//
//  This file implements a set of instruction pre-decode tasks for the
//  ARCompact instruction set. These determine whether the instruction
//  is 16-bit or 32-bit in size, and whether it requires a LIMM.
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

// Definitions for all decode-related constants
//
`include "npuarc_decode_const.v"


module npuarc_alb_predecode (
// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ:  unused port range
  input      [31:0]             inst,             // Incoming instruction
// leda NTL_CON13C on
// leda NTL_CON37 on
  output reg                    is_16bit,         // Indicates 16-bit insn
  output reg                    is_cond_inst,     // conditional instruction


  output reg                    has_limm,         // Indicates insn has LIMM
  output reg                    limm_r0,          // Port 0 is a LIMM
  output reg                    limm_r1,          // Port 1 is a LIMM
  output reg [`npuarc_RGF_ADDR_RANGE]  rf_ra0,           // Register address src 0
  output reg [`npuarc_RGF_ADDR_RANGE]  rf_ra1,           // Register address src 1
  output reg                    rf_renb0_64,      // Port 0 is a 64-bit read
  output reg                    rf_renb1_64,      // Port 1 is a 64-bit read
  output reg                    rf_renb0,         // Read enable for port 0
  output reg                    rf_renb1          // Read enable for port 1
);
// spyglass disable_block W193
// SMD: empty statements
// SJ:  empty default statements kept and empty statements cause no problems

reg                         reg_is_64bit;       // 1 => group 5 reads 64-bits



always @*
begin : predecode_PROC

  // Initialise the local micro-code fields prior to decode
  //
  begin
    rf_ra0       = 6'd0;    // default register address, port 0
    rf_ra1       = 6'd0;    // default register address, port 1
    is_16bit     = 1'b0;    // by default instruction size is 32 bits
    has_limm     = 1'b0;    // by default inst does not have limm data
    limm_r0      = 1'b0;    // by default port 0 is not a limm data
    limm_r1      = 1'b0;    // by default port 1 is not a limm data
    rf_renb0     = 1'b0;    // by default port 0 is not a valid read
    rf_renb1     = 1'b0;    // by default port 1 is not a valid read
  end
  

  // by default port 0 is not a 64-bit read
  //
  rf_renb0_64  = 1'b0;

  // allow 64-bit source registers for major opcode groups 0x05 and 0x06
  //
  reg_is_64bit = (inst[21:20] == 2'b11); 



  // by default port 1 is not a 64-bit read
  rf_renb1_64  = 1'b0; 


  is_cond_inst = 1'b0;

                  
  case ( inst[31:27] )
  `npuarc_GRP_BRANCH_32: 
      begin
      ;
      end
  `npuarc_GRP_BL_BRCC_32: 
      begin 
        case ( inst[16] )
        1'b0: 
        begin
          if (inst[17] == 1'b0) 
          begin  // BLcc reads BLINK for cond. update
            begin
              rf_ra0   = 6'd31;
              rf_renb0 = 1'b1;
            end
            
          end 
        end
        1'b1: 
        begin
          case ( inst[4] )
          1'b0: begin
                  begin
                    rf_ra0   = { inst[14:12], inst[26:24] };
                    limm_r0  = (rf_ra0 == 6'd62);
                    rf_renb0 = ~limm_r0;
                  end
                  
                  begin
                    rf_ra1   = inst[11:6];
                    limm_r1  = (rf_ra1 == 6'd62);
                    rf_renb1 = ~limm_r1;
                  end
                  
                end
                
          1'b1: begin
                  rf_ra0   = { inst[14:12], inst[26:24] };
                  limm_r0  = (rf_ra0 == 6'd62);
                  rf_renb0 = ~limm_r0;
                end
                
          endcase
        end
        endcase
      end
  `npuarc_GRP_LOAD_32:
      begin
        begin
          rf_ra0   = { inst[14:12], inst[26:24] };
          limm_r0  = (rf_ra0 == 6'd62);
          rf_renb0 = ~limm_r0;
        end
        
      end

  `npuarc_GRP_STORE_32:
      begin
        begin
          begin
            rf_ra0   = { inst[14:12], inst[26:24] };
            limm_r0  = (rf_ra0 == 6'd62);
            rf_renb0 = ~limm_r0;
          end
          
          begin
            rf_ra1   = inst[11:6];
            limm_r1  = (rf_ra1 == 6'd62);
            rf_renb1 = ~limm_r1;
          end
          
        end
        
        if (inst[0] == 1'b1)  // if using w6 operand for store-immediate
        begin
// spyglass disable_block W415a
// SMD: signal assigned multiple times over same always block
// SJ:  overwriting default assignment
          rf_renb1 = 1'b0;    // then disable reading of register port 1
          limm_r1  = 1'b0;
// spyglass enable_block W415a
        end
        else
          rf_renb1_64 = (inst[2:1] == 2'b11); // STD stores 64-bits
      end

  `npuarc_GRP_BASECASE_32:
      begin  // Firstly, decode the operand format
        if (inst[21:19] == `npuarc_LD_RR_FMT)
        begin
         begin
           begin
             rf_ra0   = { inst[14:12], inst[26:24] };
             limm_r0  = (rf_ra0 == 6'd62);
             rf_renb0 = ~limm_r0;
           end
           
           begin
             rf_ra1   = inst[11:6];
             limm_r1  = (rf_ra1 == 6'd62);
             rf_renb1 = ~limm_r1;
           end
           
         end
         
        end 
        else
         begin
         case ( inst[23:22])
         `npuarc_REG_REG_FMT:  // REG_REG format for major opcode 0x04
            case (inst[21:16])
            // firstly all exceptions are listed
            `npuarc_LDI_OP,
            `npuarc_MOV_OP,
            `npuarc_LR_OP:     begin
                          rf_ra1   = inst[11:6];
                          limm_r1  = (rf_ra1 == 6'd62);
                          rf_renb1 = ~limm_r1;
                        end
                                  // mov or lr b,c

            `npuarc_SR_OP,
            `npuarc_TST_OP,
            `npuarc_BTST_OP,
            `npuarc_CMP_OP,
            `npuarc_RCMP_OP:   begin
                          begin
                            rf_ra0   = { inst[14:12], inst[26:24] };
                            limm_r0  = (rf_ra0 == 6'd62);
                            rf_renb0 = ~limm_r0;
                          end
                          
                          begin
                            rf_ra1   = inst[11:6];
                            limm_r1  = (rf_ra1 == 6'd62);
                            rf_renb1 = ~limm_r1;
                          end
                          
                        end
                             // source regs only

            `npuarc_BI_OP,
            `npuarc_BIH_OP:
             begin
               rf_ra1   = inst[11:6];
               limm_r1  = (rf_ra1 == 6'd62);
               rf_renb1 = ~limm_r1;
             end
             
            `npuarc_FLAG_OP: begin
                        rf_ra1   = inst[11:6];
                        limm_r1  = (rf_ra1 == 6'd62);
                        rf_renb1 = ~limm_r1;
                      end
                      

            `npuarc_JCC_OP,
            `npuarc_JCC_D_OP: begin
                        begin
                          rf_ra1   = inst[11:6];
                          limm_r1  = (rf_ra1 == 6'd62);
                          rf_renb1 = ~limm_r1;
                        end
                                    
                       end
            `npuarc_JLCC_OP,
            `npuarc_JLCC_D_OP: begin
                          begin
                            rf_ra0   = 6'd31;
                            rf_renb0 = 1'b1;
                          end
                          // read BLINK on ra0 for cond. update
                          begin
                            rf_ra1   = inst[11:6];
                            limm_r1  = (rf_ra1 == 6'd62);
                            rf_renb1 = ~limm_r1;
                          end
                                // J/JL [c]
                        end
            `npuarc_SOP_FMT:
              begin
                case (inst[5:0])
                `npuarc_ZOP_FMT:
                begin
                  case ( {inst[14:12], inst[26:24]} )
                    `npuarc_SETI_OP,
                    `npuarc_WEVT_OP,
                    `npuarc_WLFC_OP,
                    `npuarc_SLEEP_OP: begin
                                 rf_ra1   = inst[11:6];
                                 limm_r1  = (rf_ra1 == 6'd62);
                                 rf_renb1 = ~limm_r1;
                               end
                               
                    `npuarc_RTIE_OP: begin
                                rf_ra0   = 6'd29;
                                rf_renb0 = 1'b1;
                              end
                              
                    default: ;
                  endcase
                end
                `npuarc_STDC_OP:
                  begin
                  begin
                    begin
                      rf_ra1   = { inst[14:12], inst[26:24] };
                      limm_r1  = (rf_ra1 == 6'd62);
                      rf_renb1 = ~limm_r1;
                    end
                    
                    begin
                      rf_ra0   = inst[11:6];
                      limm_r0  = (rf_ra0 == 6'd62);
                      rf_renb0 = ~limm_r0;
                    end
                    
                  end
                  
                  rf_renb1_64 = 1'b1;
                  end
                `npuarc_STC_OP,
                `npuarc_EX_OP: begin
                          begin
                            rf_ra1   = { inst[14:12], inst[26:24] };
                            limm_r1  = (rf_ra1 == 6'd62);
                            rf_renb1 = ~limm_r1;
                          end
                          
                          begin
                            rf_ra0   = inst[11:6];
                            limm_r0  = (rf_ra0 == 6'd62);
                            rf_renb0 = ~limm_r0;
                          end
                          
                        end
                        
                default:   begin
                             rf_ra1   = inst[11:6];
                             limm_r1  = (rf_ra1 == 6'd62);
                             rf_renb1 = ~limm_r1;
                           end
                             // SOP b,[c|limm]
                endcase
              end
            // secondly, the default operands are extracted
            default:    begin
                          begin
                            rf_ra0   = { inst[14:12], inst[26:24] };
                            limm_r0  = (rf_ra0 == 6'd62);
                            rf_renb0 = ~limm_r0;
                          end
                          
                          begin
                            rf_ra1   = inst[11:6];
                            limm_r1  = (rf_ra1 == 6'd62);
                            rf_renb1 = ~limm_r1;
                          end
                          
                        end
                            // Generic reg-reg
            endcase

         `npuarc_REG_U6IMM_FMT:  // REG_U6IMM format for major opcode 0x04
            case (inst[21:16])
            // firstly all exceptions are listed
            `npuarc_MOV_OP,
            `npuarc_LR_OP:     ;    // mov or lr reg-u6 has no reg opds

            `npuarc_SR_OP,
            `npuarc_TST_OP,
            `npuarc_BTST_OP,
            `npuarc_CMP_OP,
            `npuarc_RCMP_OP:   begin
                          rf_ra0   = { inst[14:12], inst[26:24] };
                          limm_r0  = (rf_ra0 == 6'd62);
                          rf_renb0 = ~limm_r0;
                        end
                             // source b only

            `npuarc_LDI_OP:    ;      // LDI u6 has no src reg opds
            `npuarc_JCC_OP,
            `npuarc_JCC_D_OP:         // Jcc u6 has no src reg opds
               ;
//          `LPCC_OP,          // LP u6 has no src reg opds
            `npuarc_FLAG_OP:   ;      // flag has no src reg opds
            `npuarc_LPCC_OP:  
                  ;      // LP u6 has no src reg opds

            `npuarc_JLCC_OP,          // JL u6 reads BLINK for cond. update
            `npuarc_JLCC_D_OP: begin
                          begin
                            rf_ra0   = 6'd31;
                            rf_renb0 = 1'b1;
                          end
                          
                        end
            `npuarc_SOP_FMT:
              begin
                if (    (inst[5:0] == `npuarc_ZOP_FMT)
                     && ({inst[14:12], inst[26:24]} == `npuarc_RTIE_OP)
                   )
                  begin
                    rf_ra0   = 6'd29;
                    rf_renb0 = 1'b1;
                  end
                  
                else
                  if (   (inst[5:0] == `npuarc_EX_OP)
                      || (inst[5:0] == `npuarc_STC_OP)
                      || (inst[5:0] == `npuarc_STDC_OP)
                     )
                    begin
                    begin
                      rf_ra1   = { inst[14:12], inst[26:24] };
                      limm_r1  = (rf_ra1 == 6'd62);
                      rf_renb1 = ~limm_r1;
                    end
                    
                    rf_renb1_64 = inst[1]; // inst[1] implies SCONDD insn
                    end
              end

            // secondly, the default operands are extracted
            default:    begin
                          rf_ra0   = { inst[14:12], inst[26:24] };
                          limm_r0  = (rf_ra0 == 6'd62);
                          rf_renb0 = ~limm_r0;
                        end
                        
            endcase

         `npuarc_REG_S12IMM_FMT:  // REG_S12IMM format for major opcode 0x04
         begin
            case (inst[21:16])
            // firstly all exceptions are listed
            `npuarc_LDI_OP,
            `npuarc_MOV_OP,
            `npuarc_LR_OP:     ;   // mov or lr reg-s12 has no reg src

            `npuarc_SR_OP,
            `npuarc_TST_OP,
            `npuarc_BTST_OP:
                begin
                       begin
                         rf_ra0   = { inst[14:12], inst[26:24] };
                         limm_r0  = (rf_ra0 == 6'd62);
                         rf_renb0 = ~limm_r0;
                       end
                             // source b only
                end
            `npuarc_CMP_OP,
            `npuarc_RCMP_OP:   
                begin
                       begin
                         rf_ra0   = { inst[14:12], inst[26:24] };
                         limm_r0  = (rf_ra0 == 6'd62);
                         rf_renb0 = ~limm_r0;
                       end
                             // source b only
                end

            `npuarc_FLAG_OP:;
            `npuarc_JCC_OP,
            `npuarc_JCC_D_OP:      // J s12 has no reg opds
               ;
            `npuarc_JLCC_OP,        // JL s12 reads BLINK for cond. update
            `npuarc_JLCC_D_OP:  
                 begin
                   rf_ra0   = 6'd31;
                   rf_renb0 = 1'b1;
                 end
                 
            `npuarc_SOP_FMT:   ;     // SOP disallowed in this format
            `npuarc_LPCC_OP:        // LP s13 has no reg opds
                      ;

            // secondly, the default operands are extracted
            default:    begin
                          rf_ra0   = { inst[14:12], inst[26:24] };
                          limm_r0  = (rf_ra0 == 6'd62);
                          rf_renb0 = ~limm_r0;
                        end
                              // b-reg as src1
            endcase
         end
         
         `npuarc_REG_COND_FMT:  // REG_COND format for major opcode 0x04
            begin
            case (inst[5])
            1'b0: begin
                    begin
                      rf_ra1   = inst[11:6];
                      limm_r1  = (rf_ra1 == 6'd62);
                      rf_renb1 = ~limm_r1;
                    end
                     // c-reg as src2
                    is_cond_inst = 1'b1;
                  end
            1'b1: ;
            endcase
            case (inst[21:16])
            // firstly all exceptions are listed
            `npuarc_TST_OP,
            `npuarc_BTST_OP:   begin
                          rf_ra0   = { inst[14:12], inst[26:24] };
                          limm_r0  = (rf_ra0 == 6'd62);
                          rf_renb0 = ~limm_r0;
                        end
                              // source b only
            `npuarc_CMP_OP,
            `npuarc_RCMP_OP:   begin
                          rf_ra0   = { inst[14:12], inst[26:24] };
                          limm_r0  = (rf_ra0 == 6'd62);
                          rf_renb0 = ~limm_r0;
                        end
                              // source b only

            `npuarc_MOV_OP:    begin
                          rf_ra0   = { inst[14:12], inst[26:24] };
                          rf_renb0 = (rf_ra0 != 6'd62);
                        end
                         // b is a source if not LIMM
            
            `npuarc_LDI_OP,
            `npuarc_FLAG_OP:;
            `npuarc_JCC_OP,
            `npuarc_JCC_D_OP:       // no further src regs
               ;
            `npuarc_JLCC_OP,         // JL reads BLINK for cond. update
            `npuarc_JLCC_D_OP: 
                  begin
                    rf_ra0   = 6'd31;
                    rf_renb0 = 1'b1;
                  end
                  

            `npuarc_SOP_FMT:   ;      // SOP disallowed in this format
//          `LPCC_OP:   ;     // LPcc u6 has no reg opds
            `npuarc_LPCC_OP: 
                        ;

            // secondly, the default operands are extracted
            default:    begin
                          rf_ra0   = { inst[14:12], inst[26:24] };
                          limm_r0  = (rf_ra0 == 6'd62);
                          rf_renb0 = ~limm_r0;
                        end
                            // b-reg as src1
            // take care of Section 4.9.9.1
            endcase
            end
         endcase
         end
      end

  `npuarc_GRP_ARC_EXT1_32: ;

  `npuarc_GRP_ARC_EXT0_32:
      begin  // Firstly, decode the operand format in the same
             // way as GRP_BASECASE_32, but without the exceptional
             // formats that appear in the basecase group
             //
         case ( inst[23:22])
         `npuarc_REG_REG_FMT:      // REG_REG format for major opcode 0x04
            case (inst[21:16])
            // first specify all the exceptions
            `npuarc_SOP_FMT:   
              begin
              begin
                rf_ra1   = inst[11:6];
                limm_r1  = (rf_ra1 == 6'd62);
                rf_renb1 = ~limm_r1;
              end
                   // SOP b,[c|limm]
              end
            // secondly, the default operands are extracted
            default:    begin
                          begin
                            rf_ra0   = { inst[14:12], inst[26:24] };
                            limm_r0  = (rf_ra0 == 6'd62);
                            rf_renb0 = ~limm_r0;
                          end
                          
                          begin
                            rf_ra1   = inst[11:6];
                            limm_r1  = (rf_ra1 == 6'd62);
                            rf_renb1 = ~limm_r1;
                          end
                          
                        end
                        
            endcase

         `npuarc_REG_U6IMM_FMT:    // REG_U6IMM format for major opcode 0x04
            case (inst[21:16])
            // first specify all the exceptions
            `npuarc_SOP_FMT: ;   // no source register, only u6
            // secondly, the default operands are extracted
            default:    begin
                          rf_ra0   = { inst[14:12], inst[26:24] };
                          limm_r0  = (rf_ra0 == 6'd62);
                          rf_renb0 = ~limm_r0;
                        end
                        
            endcase

         `npuarc_REG_S12IMM_FMT:   // REG_S12IMM format for major opcode 0x04
            // case (inst[21:16])
            //   first specify all the exception
            //   (none so far)
            //   secondly, the default operands are extracted
            //   default:
            begin
              rf_ra0   = { inst[14:12], inst[26:24] };
              limm_r0  = (rf_ra0 == 6'd62);
              rf_renb0 = ~limm_r0;
            end
            
            // endcase

         `npuarc_REG_COND_FMT:     // REG_COND format for major opcode 0x04
            begin
            case (inst[5])
            1'b0: begin
                    begin
                      rf_ra1   = inst[11:6];
                      limm_r1  = (rf_ra1 == 6'd62);
                      rf_renb1 = ~limm_r1;
                    end
                     // c-reg as src2
                    is_cond_inst = 1'b1;
                  end
            1'b1: ;
            endcase
            case (inst[21:16])
            // first list all the exceptions
            // (none so far)
            // secondly, the default operands are extracted
            default:  begin 
                     begin
                       rf_ra0   = { inst[14:12], inst[26:24] };
                       limm_r0  = (rf_ra0 == 6'd62);
                       rf_renb0 = ~limm_r0;
                     end
                     
                      end
            // take care of Section 4.9.9.1
            endcase
            end
         endcase

        //==================================================================
        // If the opcode is in the range 0x30 to 0x3F, then the
        // reg_is_64bit signal is set, indicating an instruction
        // that takes 64-bit register pair operands. 
        //
        rf_renb0_64 = rf_renb0
                    & (  reg_is_64bit
                      )
                    ;
        
        //==================================================================
        // Set the rf_renb1_64 signal provide the opcode is not
        // one of DMPYHW, DMPYWHU, DMACHW or DMACWHU. These opcodes
        // all have inst[17] set to 1 and inst[19] set to 0.
        // Optionally decode major 6 opcodes
        //
        rf_renb1_64 = rf_renb1 & reg_is_64bit 
                         & (  ((inst[19] | (~inst[17])) & (~inst[28]))            // maj5 opcodes
                           );
      end

  `npuarc_GRP_USR_EXT2_32:
      begin  // Firstly, decode the operand format in the same
             // way as GRP_BASECASE_32, but without the exceptional
             // formats that appear in the basecase group
             //
         case ( inst[23:22])
         `npuarc_REG_REG_FMT:      // REG_REG format for major opcode 0x07
            case (inst[21:16])
            
              // first specify all the exceptions
              `npuarc_SOP_FMT:
                 case (inst[5:0])
              
 // [eia-sop]: 64x64
                    6'd0:
                          begin
                            rf_ra1      = inst[11:6];
                            limm_r1     = (rf_ra1 == 6'd62);
                            rf_renb1    = ~limm_r1;
                            rf_renb1_64 = rf_renb1;
                          end
 // [eia-sop]: 64x64
                    6'd1:
                          begin
                            rf_ra1      = inst[11:6];
                            limm_r1     = (rf_ra1 == 6'd62);
                            rf_renb1    = ~limm_r1;
                            rf_renb1_64 = rf_renb1;
                          end
 // [eia-sop]: 64x64
                    6'd2:
                          begin
                            rf_ra1      = inst[11:6];
                            limm_r1     = (rf_ra1 == 6'd62);
                            rf_renb1    = ~limm_r1;
                            rf_renb1_64 = rf_renb1;
                          end
 // [eia-sop]: 64x64
                    6'd3:
                          begin
                            rf_ra1      = inst[11:6];
                            limm_r1     = (rf_ra1 == 6'd62);
                            rf_renb1    = ~limm_r1;
                            rf_renb1_64 = rf_renb1;
                          end
 // [eia-sop]: 64x64
                    6'd4:
                          begin
                            rf_ra1      = inst[11:6];
                            limm_r1     = (rf_ra1 == 6'd62);
                            rf_renb1    = ~limm_r1;
                            rf_renb1_64 = rf_renb1;
                          end
 // [eia-sop]: 64x64
                    6'd5:
                          begin
                            rf_ra1      = inst[11:6];
                            limm_r1     = (rf_ra1 == 6'd62);
                            rf_renb1    = ~limm_r1;
                            rf_renb1_64 = rf_renb1;
                          end
 // [eia-sop]: 64x64
                    6'd6:
                          begin
                            rf_ra1      = inst[11:6];
                            limm_r1     = (rf_ra1 == 6'd62);
                            rf_renb1    = ~limm_r1;
                            rf_renb1_64 = rf_renb1;
                          end
                    `npuarc_ZOP_FMT:
                          begin
                            rf_ra1      = inst[11:6];
                            limm_r1     = (rf_ra1 == 6'd62);
                            rf_renb1    = ~limm_r1;
                          end
                    
                    default:;
                 endcase
              // secondly, the default operands are extracted
              default:    begin
                            begin
                              rf_ra0   = { inst[14:12], inst[26:24] };
                              limm_r0  = (rf_ra0 == 6'd62);
                              rf_renb0 = ~limm_r0;
                            end
                            
                            begin
                              rf_ra1   = inst[11:6];
                              limm_r1  = (rf_ra1 == 6'd62);
                              rf_renb1 = ~limm_r1;
                            end
                            
                          end
                          
            endcase

         `npuarc_REG_U6IMM_FMT:    // REG_U6IMM format for major opcode 0x07
            case (inst[21:16])
            // first specify all the exceptions
            `npuarc_SOP_FMT: ;   // no source register, only u6
            // secondly, the default operands are extracted
              default:    begin
                            rf_ra0   = { inst[14:12], inst[26:24] };
                            limm_r0  = (rf_ra0 == 6'd62);
                            rf_renb0 = ~limm_r0;
                          end
                          
            endcase

         `npuarc_REG_S12IMM_FMT:   // REG_S12IMM format for major opcode 0x07
            case (inst[21:16])
              // first specify all the exceptions
              `npuarc_SOP_FMT: ;   // no source register, only s12
              // secondly, the default operands are extracted
              default:    begin
                            rf_ra0   = { inst[14:12], inst[26:24] };
                            limm_r0  = (rf_ra0 == 6'd62);
                            rf_renb0 = ~limm_r0;
                          end
                          
            endcase

         `npuarc_REG_COND_FMT:     // REG_COND format for major opcode 0x07
            begin
            
              rf_ra0   = { inst[14:12], inst[26:24] };
              limm_r0  = (rf_ra0 == 6'd62);
              rf_renb0 = ~limm_r0;

              case (inst[5])  // check if instruction is conditional
                1'b0:
                  begin
                    rf_ra1   = inst[11:6];
                    limm_r1  = (rf_ra1 == 6'd62);
                    rf_renb1 = ~limm_r1;
                    is_cond_inst = 1'b1;
                  end
                1'b1:  ;
              endcase

              case (inst[21:16])
                // first specify all the exceptions
                `npuarc_SOP_FMT: ;
                // secondly, the default operands are extracted
                default:    ;
                // take care of Section 4.9.9.1
              endcase
            end

         endcase
      end

  `npuarc_GRP_ARC_EXT0_16:
      begin
        is_16bit = 1'b1;
        if (inst[18] == 0)
        begin
          begin
            rf_ra1   = { 1'b0, inst[17:16], inst[23:21] };
            limm_r1  = (rf_ra1[4:0] == 5'd30);
            rf_renb1 = ~limm_r1;
          end
          
        end  
        else
        begin
          begin
            rf_ra0   = { 1'b0, inst[17:16], inst[23:21] };
            limm_r0  = (rf_ra0[4:0] == 5'd30);
            rf_renb0 = ~limm_r0;
          end
          
        end  
      end
      
  `npuarc_GRP_ARC_EXT1_16:
      begin
      is_16bit = 1'b1;
      begin
        rf_ra0   = { 2'b00, inst[26], inst[26:24] };
        rf_renb0 = 1'b1;
      end
      
      if (inst[19] == 0)
        begin
          rf_ra1   = { 2'b00, inst[23], inst[23:21] };
          rf_renb1 = 1'b1;
        end
        
      end

  `npuarc_GRP_USR_EXT0_16:
      begin
      is_16bit = 1'b1;
      if (inst[19] == 0)
        begin
          rf_ra0   = 6'd26;     // GP register
          rf_renb0 = 1'b1;      // always read GP register
          rf_ra1   = 6'd0;      // possible store data from R0
          rf_renb1 = inst[20];  // read reg1 if st_s r0,[gp,s11]
        end
        
      end

  `npuarc_GRP_USR_EXT1_16:
      begin
      is_16bit = 1'b1;
      end

  `npuarc_GRP_LD_ADD_RR_16:
      begin
      begin
        begin
          rf_ra0   = { 2'b00, inst[26], inst[26:24] };
          rf_renb0 = 1'b1;
        end
        
        begin
          rf_ra1   = { 2'b00, inst[23], inst[23:21] };
          rf_renb1 = 1'b1;
        end
        
      end
      
      is_16bit = 1'b1;
      end

  `npuarc_GRP_ADD_SUB_SH_16:
      begin
      begin
        rf_ra0   = { 2'b00, inst[26], inst[26:24] };
        rf_renb0 = 1'b1;
      end
      
      is_16bit = 1'b1;
      end

  `npuarc_GRP_MV_CMP_ADD_16:
      begin
      is_16bit = 1'b1;
      case ( inst[20:18] )
      3'b000:  begin
                 begin
                   rf_ra0   = { 2'b00, inst[26], inst[26:24] };
                   rf_renb0 = 1'b1;
                 end
                 
                 begin
                   rf_ra1   = { 1'b0, inst[17:16], inst[23:21] };
                   limm_r1  = (rf_ra1[4:0] == 5'd30);
                   rf_renb1 = ~limm_r1;
                 end
                 
               end
                     // src1 = b, src2 = h
      3'b001:  begin
                 rf_ra0   = { 1'b0, inst[17:16], inst[23:21] };
                 limm_r0  = (rf_ra0[4:0] == 5'd30);
                 rf_renb0 = ~limm_r0;
               end
                 // src1 = h, (src2 = s3)
      3'b100:  begin
                 begin
                   rf_ra0   = { 2'b00, inst[26], inst[26:24] };
                   rf_renb0 = 1'b1;
                 end
                 
                 begin
                   rf_ra1   = { 1'b0, inst[17:16], inst[23:21] };
                   limm_r1  = (rf_ra1[4:0] == 5'd30);
                   rf_renb1 = ~limm_r1;
                 end
                 
               end
                     // src1 = b, src2 = h
      3'b101:  begin
                 rf_ra0   = { 1'b0, inst[17:16], inst[23:21] };
                 limm_r0  = (rf_ra0[4:0] == 5'd30);
                 rf_renb0 = ~limm_r0;
               end
                 // src1 = h, (src2 = s3)
      3'b111: begin
               begin
                 rf_ra0   = { 2'b00, inst[26], inst[26:24] };
                 rf_renb0 = 1'b1;
               end
                     // src1 = b, (src2 = h)
               begin
                 rf_ra1   = { 1'b0, inst[17:16], inst[23:21] };
                 limm_r1  = (rf_ra1[4:0] == 5'd30);
                 rf_renb1 = ~limm_r1;
               end
                 //
      end
      default: ;
      endcase
      end

  `npuarc_GRP_GEN_OPS_16:
      begin
      is_16bit = 1'b1;

      case ( inst[20:16] )
      5'h00: // SOPs or ZOPs
         begin
         case ( inst[23:21] )
         3'b000,
         3'b001,
         3'b010,
         3'b011,
         3'b110:  begin
                    rf_ra0   = { 2'b00, inst[26], inst[26:24] };
                    rf_renb0 = 1'b1;
                  end
                  
         3'b111:  begin
                    rf_ra1   = 6'd31;
                    rf_renb1 = inst[26]; // exclude nop_s and swi_s
                  end
                    // ZOPs
         default: ;
         endcase
         end
      5'h11,
      5'h12,
      5'h13:   begin
                 rf_ra1   = { 2'b00, inst[23], inst[23:21] };
                 rf_renb1 = 1'b1;
               end
                  // abs, not, neg: b <= op(c)
      5'h1e,
      5'h1f: ; // trap_s, brk_s and swi_s have no source registers
      default: begin
                 begin
                   rf_ra0   = { 2'b00, inst[26], inst[26:24] };
                   rf_renb0 = 1'b1;
                 end
                 
                 begin
                   rf_ra1   = { 2'b00, inst[23], inst[23:21] };
                   rf_renb1 = 1'b1;
                 end
                 
               end
               
      endcase
      end

  `npuarc_GRP_LD_WORD_16,
  `npuarc_GRP_LD_BYTE_16,
  `npuarc_GRP_LD_HALF_16,
  `npuarc_GRP_LD_HALFX_16:
      begin
      is_16bit = 1'b1;
      begin
        rf_ra0   = { 2'b00, inst[26], inst[26:24] };
        rf_renb0 = 1'b1;
      end
      
      end

  `npuarc_GRP_ST_WORD_16,
  `npuarc_GRP_ST_BYTE_16,
  `npuarc_GRP_ST_HALF_16:
      begin
      is_16bit = 1'b1;
      begin
        rf_ra0   = { 2'b00, inst[26], inst[26:24] };
        rf_renb0 = 1'b1;
      end
      
      begin
        rf_ra1   = { 2'b00, inst[23], inst[23:21] };
        rf_renb1 = 1'b1;
      end
      
      end

  `npuarc_GRP_SH_SUB_BIT_16:
      begin
      begin
        rf_ra0   = { 2'b00, inst[26], inst[26:24] };
        rf_renb0 = 1'b1;
      end
      
      is_16bit = 1'b1;
      end

  `npuarc_GRP_SP_MEM_16:
      begin

      is_16bit = 1'b1;
      begin
        rf_ra0   = 6'd28;
        rf_renb0 = 1'b1;
      end
          // SP register
      case ( inst[23:21] )
      3'd2,
      3'd3: begin
              rf_ra1   = { 2'b00, inst[26], inst[26:24] };
              rf_renb1 = 1'b1;
            end
            
      3'd7: begin
              rf_renb1 = 1'b1;
              if ( inst[20:16] == 5'd1 )
                rf_ra1 = { 2'd0, inst[26], inst[26:24] };
              else if (inst[20:16] == 5'd17)
                rf_ra1 = 6'd31;
            end
            
      default: ;
      endcase
      end

  `npuarc_GRP_GP_MEM_16:
      begin
      is_16bit = 1'b1;
      begin
        rf_ra0   = 6'd26;   // GP register
        rf_renb0 = 1'b1;    // always read GP register
      end
          // GP register
      end

  `npuarc_GRP_LD_PCL_16:
      begin
      is_16bit = 1'b1;
      begin
        rf_ra0   = 6'd63;
        rf_renb0 = 1'b1;
      end
          // PCL register
      end

  `npuarc_GRP_MV_IMM_16:
      begin
      is_16bit = 1'b1;
      end

  `npuarc_GRP_ADD_IMM_16:
      begin
      is_16bit = 1'b1;
      begin
        rf_ra0   = { 2'b00, inst[26], inst[26:24] };
        rf_renb0 = 1'b1;
      end
      
      end

  `npuarc_GRP_BRCC_S_16:
      begin
        is_16bit = 1'b1;
        begin
          rf_ra0   = { 2'b00, inst[26], inst[26:24] };
          rf_renb0 = 1'b1;
        end
        
      end

  `npuarc_GRP_BCC_S_16:
      begin
      is_16bit = 1'b1;
      end

  `npuarc_GRP_BL_S_16:
      begin
      is_16bit = 1'b1;
      end
  endcase

  has_limm = limm_r0 | limm_r1;
end
// spyglass enable_block W193

endmodule
