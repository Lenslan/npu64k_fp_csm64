/*************************************************************************/
/**                                                                     **/
/** Copyright (C) 2021-2022 Synopsys, Inc.                              **/
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

#include <arc/arc_reg.h>
#include "arc_cc.h"

#ifndef REG_GLOBAL_CLK_GATE_DIS
#define REG_GLOBAL_CLK_GATE_DIS 0x9A9
#endif

void disable_l1_clkg(){
  _sr(0xffffffff, REG_GLOBAL_CLK_GATE_DIS);//disable clock gating
}

void enable_core_clkg(){
  if(hasTimer0())
    _sr(0x10, REG_CONTROL0);// set field TD of CONTROL0 to enable TIMER 0 clkgating
    
  if(hasTimer1())
    _sr(0x10, REG_CONTROL1);// set field TD of CONTROL0 to enable TIMER 0 clkgating
}

void enable_l1_clkg() {
  enable_core_clkg();
  _sr(0x0,  REG_GLOBAL_CLK_GATE_DIS);//enable clock gating
}

