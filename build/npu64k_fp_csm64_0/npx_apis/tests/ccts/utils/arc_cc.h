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
#ifndef __arc_cc_evss_h__
#define __arc_cc_evss_h__

#include <stdint.h>
#include <arc/arc_reg.h>

#ifdef __cplusplus
extern "C" {
#endif

static inline int hasRTC() {
    // returns 1 if ARC is configured with a Real-time Counter component
    unsigned timer_build = _lr(REG_TIMER_BUILD);
    return (timer_build >> 10) & 0x1;
}

static inline int hasTimer0() {
    // returns 1 if ARC is configured with Timer 0
    unsigned timer_build = _lr(REG_TIMER_BUILD);
    return (timer_build >> 8) & 0x1;
}

static inline int hasTimer1() {
    // returns 1 if ARC is configured with Timer 1
    unsigned timer_build = _lr(REG_TIMER_BUILD);
    return (timer_build >> 9) & 0x1;
}

static inline void start_cc() {
    if (hasRTC()) {
        _sr(0x1, AUX_RTC_CTRL);
    }
}

static inline void stop_cc() {
    if (hasRTC()) {
        _sr(0x0, AUX_RTC_CTRL);
    }
}

static inline void clear_cc() {
    if (hasRTC()) {
        _sr(0x3, AUX_RTC_CTRL);
    }
}

static inline uint64_t get_cc() {
    if (hasRTC()) {
        unsigned low, high, ctrl;
        while (1) {
            low = _lr(AUX_RTC_LOW);
            high = _lr(AUX_RTC_HIGH);
            // test atomicity of low and high reads
            ctrl = _lr(AUX_RTC_CTRL);
            if (ctrl >> 31) break;
        }
        return ((uint64_t) high) << 32 | (uint64_t) low;
    }
    return (uint64_t)0;
}

static inline void start_timer0 (unsigned timeout) {
                                // Bit
    unsigned ctrl = 0x5;        // [0]: generate and interrupt when done
                                // [1]: count only when running (not halted)
                                // [2]: generate a wartchdog reset signal when done

    _sr(ctrl, REG_CONTROL0);    // Configure the timer
    _sr(timeout, REG_LIMIT0);   // count up to 'timeout' limit value
    _sr(0, REG_COUNT0);         // start at 0
}

static inline void start_timer1 (unsigned timeout) {
    unsigned ctrl = 0x1;
    _sr(ctrl, REG_CONTROL1);
    _sr(timeout, REG_LIMIT1);
    _sr(0, REG_COUNT1);
}

#ifdef __cplusplus
}
#endif

#endif /* __arc_cc_evss_h__ */
