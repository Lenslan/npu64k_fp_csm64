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

#ifdef RTL_DPI
  #define ARC_EXEC arc_exec
#else
  #define ARC_EXEC int main
#endif

//
// boot the processor
//
ARC_EXEC() {
  // load and execute a test program
  test_program* prg = new test_program();
  // execute the test program
  prg->exec();
  // stop the simulator
  arc_exit();
}
