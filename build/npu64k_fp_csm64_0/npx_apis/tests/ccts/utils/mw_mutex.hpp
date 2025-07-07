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

#ifndef __MUTEX__H
#define __MUTEX__H

#include <arc/arc_intrinsics.h>
#include <stdint.h>

// Basic mutex implementation
typedef _Uncached int mutex_t;

static inline void mutex_acquire(mutex_t* mutex){
    uint8_t cnt = 0;
    do {
        int mutexBusy = _llock_di(mutex);
        if (!mutexBusy){
            if (_scond_di(1, mutex) == 0){break;}
        }
        cnt = GET_TIMER0() % 4; // small timeout before retry
        for (int i = 0; i<cnt ; i++) {_nop();_nop();_nop();_nop();_nop();}
    } while(1);
}

static inline void mutex_release(mutex_t* mutex){
    *(mutex) = 0;
}

#endif
