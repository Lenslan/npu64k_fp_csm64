#ifndef MACROS_H // {
#define MACROS_H 1
// *SYNOPSYS CONFIDENTIAL*
// 
// This is an unpublished, proprietary work of Synopsys, Inc., and is fully 
// protected under copyright and trade secret laws.  You may not view, use, 
// disclose, copy, or distribute this file or any information contained herein 
// except pursuant to a valid written license from Synopsys.
// 
// Register r26 : contains the fields required to describe the error....
//

// register 32 bits
//
//  0000.0000.0000.0000.0000.0000.0000.0000
//  -+-- -+-- ------+------- ----+---- -+--
//   |    |         |            |      |
//   |    |         |            |      +--> Error definition 
//   |    |         |            |
//   |    |         |            +---------> Part under test
//   |    |         |
//   |    |         +----------------------> Part test number
//   |    |
//   |    +--------------------------------> Test system
//   |
//   +-------------------------------------> Responsible department
//

#define TEST_RESULT_REGISTER 26

// Error definition: (3-0)
// ----------------
//    1 : passed
//    2 : warning
//    3 : failed

#define  PASSED     0x00000001
#define  WARNING    0x00000002
#define  FAILED     0x00000003

// Part under test: (11-4)
// ---------------
#define  ALL        0x00000010

// All user extensions (EIA)
// -------------------------
#define  USEREXT     0x00000FF0

// Part test number: (23-12)
// ------------
// Unused.


// Test System: (27-24)
// -----------
//    1 : assembler ARC
//    2 : C/C++ 
//    6 : NT/DOS scripts

#define  ASSEMBLER  0x01000000
#define  CPLUSPLUS  0x02000000
 
// Responsible Department: (31-28)
// ----------------
//    1 : Core
//    2 : DSP
//    3 : System eng
//    4 : EDA
//    5 : Software
//    6 : System int
//    7 : Market eng
//    8 : Peripheral

#define  CORE       0x10000000
#define  DSP        0x20000000
#define  SYS_ENG    0x30000000
#define  EDA        0x40000000
#define  SOFTWARE   0x50000000
#define  SYS_INT    0x60000000
#define  MARKET     0x70000000
#define  PERIPHERAL 0x80000000
#define  CUSTOMER   0xF0000000
        
#endif // }
