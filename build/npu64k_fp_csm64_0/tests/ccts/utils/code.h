/*************************************************************************/
/**                                                                     **/
/** Copyright (C) 2016-2018 Synopsys, Inc.                              **/
/** All Rights Reserved.                                                **/
/**                                                                     **/
/** This Synopsys software and all associated documentation are         **/
/** proprietary to Synopsys, Inc. and may only be used pursuant to the  **/
/** terms and conditions of a written license agreement with Synopsys,  **/
/** Inc. All other use, reproduction, modification, or distribution of  **/
/** this Synopsys software or the associated documentation is strictly  **/
/** prohibited.                                                         **/
/**                                                                     **/
/*************************************************************************/
#ifndef _EV_CODE_H_
#define _EV_CODE_H_

#define PASSED     0x00000001
#define WARNING    0x00000002
#define FAILED     0x00000003

#define EVTEST     0x00000200
#define CPLUSPLUS  0x02000000
#define CORE       0x10000000

static inline void arctest_failed()
{
    // ARCtest reserves R26 for the test result
    _core_write(CORE|CPLUSPLUS|0|EVTEST|FAILED, 26);
    // Set the halt bit in register STATUS32
    _flag(1);
    // Clear the pipe
    _nop();
    _nop();
    _nop();
    _nop();
}

static inline void arctest_passed()
{
    // ARCtest reserves R26 for the test result
    _core_write(CORE|CPLUSPLUS|0|EVTEST|PASSED, 26);
    // Set the halt bit in register STATUS32
    _flag(1);
    // Clear the pipe
    _nop();
    _nop();
    _nop();
    _nop();
}

#endif
