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

//
// boot the processor
//
void arc_exec() {
  // load and execute a test program
  npu_test* prg = new npu_test();
  // execute the test program
  prg->exec();
  // stop the simulator
  arc_exit();
}

#ifdef RTL_ARC
int main() {
  arc_exec();

  return 0;
}
#endif

#undef ARC_EXEC

