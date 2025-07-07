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
#ifndef SIM_TERMINATE
#define SIM_TERMINATE

#ifdef HOSTLINK
 #include "utils/mw_mutex.hpp"
 mutex_t hostlink_mutex;
#endif
#include "utils/npu_mem_map_define.hpp"
_Uncached volatile int user_mode_flag=0;

//set flags for TB to finish simulation
static void set_sim_finish_flag(int err, int core_id=-1) {
    int flag = (err==0) ? 0x7 : 0x6;
  #ifdef HOSTLINK
    //mutex_acquire(&hostlink_mutex);
    if (core_id>=0) {
      cout << "====== " << "core_id:" << core_id << ((err==0)?" PASS":" FAIL") << " ======" << endl;
      cout << "====== " << "core_id:" << core_id << ((err==0)?" ARC run successfully":" ARC run with error") << " ======" << endl;
    } else {
      cout << "====== " << ((err==0)?"PASS":"FAIL") << " ======" << endl;
      cout << "====== " << ((err==0)?"Host run successfully":"Host run with error") << " ======" << endl;
    }
    //_flat(1) is not mandatory for MDB debugging
    //#if (defined(TB_MDB)&&(TB_MDB>0))
    //_flag(1); //halt
    //#endif
    //mutex_release(&hostlink_mutex);
  #else
    // flag[7:5] represents sleep mode: 
    //   0x7 means simulation self-check with out error
    //   0x6 means simulation self-check with error(s)
   #ifdef RTL_ARC
    if(user_mode_flag) {
      _Uncached int *xm_p=(_Uncached int*)(NPU_HAS_L2ARC ? LC_CSM_BASE : 0);
      _llock_di(xm_p);
      _wlfc(flag<<5);
    } else{
      _sleep(flag<<5);
    }
   #else
    if(err) {
       cout << "ARC run with error(self-check failed, error idx: " << err << ")!!!" << endl;
    }
   #endif

  #endif
}

#endif
