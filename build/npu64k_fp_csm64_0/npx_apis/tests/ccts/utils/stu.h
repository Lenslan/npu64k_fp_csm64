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

// Streaming Transfer Unit (STU)
#ifndef __arc_stu_h__
#define __arc_stu_h__

// STU specific AUX registers
#define PSP_AUX_STU_ENTRY_NUM          0x980
#define PSP_AUX_STU_NEXT_FREE          0x981
#define PSP_AUX_STU_NEXT_FREE_INC      0x983
#define PSP_AUX_STU_ENTRY_SELECT       0x984
#define PSP_AUX_STU_ENTRY_STAT         0x985
#define PSP_AUX_STU_BASE_L             0x986
#define PSP_AUX_STU_EVENT              0x989

// number of virtual channels in the STU. This is run-time programmable.
// Valid values are: 16, 32, 64 or 128
#define STU_NUM_CHAN 16

typedef union  {
    uint32_t data;
    struct {
        uint32_t num:8, reserved:24;
    };
} stu_free_num_aux_t;

// STU memory-mapped control register
typedef union {
    uint32_t data;
    struct {
        uint32_t sp:1, slw:2, r0:1, s_lane_id:7, r1:1, dp:1, dlw:2, d_lane_id:7, r2:2, i:1, m:1, r3:6;
    };
} stu_ctrl_t;

// Virtual channel transfer descriptors
static _Uncached volatile unsigned int _stu_desc[8*STU_NUM_CHAN] __attribute__((aligned(32)));

static inline void stu_init()
{
    for (int i=0; i<8*STU_NUM_CHAN; i++) {
        _stu_desc[i] = 0;
    }

    // initializing DMA with STU_NUM_CHAN virtual channels
    switch (STU_NUM_CHAN) {
        case 16:
            _sr(0, PSP_AUX_STU_ENTRY_NUM);
            break;
        case 32:
            _sr(1, PSP_AUX_STU_ENTRY_NUM);
            break;
        case 64:
            _sr(2, PSP_AUX_STU_ENTRY_NUM);
            break;
        case 128:
            _sr(3, PSP_AUX_STU_ENTRY_NUM);
            break;
        default:
            assert(0);
            break;
    }

    _sr((unsigned int)_stu_desc, PSP_AUX_STU_BASE_L);
}

// Simple 1D copy
static void* stu_memcpy(void *dest, const void *src, size_t n)
{
    stu_free_num_aux_t f;

    // Get ID of next free virtual channel, from 0 to STU_NUM_CHAN-1
    // Poll until a channle is free (assuming this will not take long).
    do {
        f.data = ((uint32_t) _lr(PSP_AUX_STU_NEXT_FREE));
    } while (f.num == 0x80);
    assert(f.num < STU_NUM_CHAN);
    int chan = f.num;

    // Setup 1D transfer, not using any VDSP private memory.
    // All bit fields in STU_CTRL can be set to 0 for this.
    stu_ctrl_t ctl;
    ctl.data = 0;
    _stu_desc[0*STU_NUM_CHAN + chan] = ctl.data;         // STU_CTRL
    _stu_desc[1*STU_NUM_CHAN + chan] = n-1;              // STU_SIZE (20 bits)
    _stu_desc[2*STU_NUM_CHAN + chan] = (uintptr_t) src;  // STU_SRC_L
    _stu_desc[3*STU_NUM_CHAN + chan] = (uintptr_t) dest; // STU_DES_L

    _sync();

    // Increment the virtual channel free index by 1. As a side effect, this
    // starts the transfer associated with the index returned previously by
    // the load from PSP_AUX_STU_NEXT_FREE.
    _sr(1, PSP_AUX_STU_NEXT_FREE_INC);

    // Wait for end of transfer
    _sr(chan, PSP_AUX_STU_ENTRY_SELECT);
    while (1) {
        volatile int val = _lr(PSP_AUX_STU_ENTRY_STAT);
        // TODO: sleep on the event instead of polling ...
        if ((val & 0x1F) == 0x5) break;
    }

    // Clear the event signal
    _sr(0x80000000, PSP_AUX_STU_EVENT);

    return dest;
}

#endif
