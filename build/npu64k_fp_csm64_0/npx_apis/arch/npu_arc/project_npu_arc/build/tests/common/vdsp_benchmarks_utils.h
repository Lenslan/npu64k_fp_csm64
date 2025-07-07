#ifndef __VDSP_BENCHMARKS_UTILS_H__
#define __VDSP_BENCHMARKS_UTILS_H__

#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>
#include <arc/arc_reg.h>

unsigned get_vecmem_start_address() {
    return _lr(0x544);
}

unsigned get_vecmem_size() {
    unsigned vec_build0 = _lr(0x540);
    unsigned vecmem = (vec_build0 >> 4) & 0xF;
    switch (vecmem) {
        case 6: 
            return (16*1024);
            break;
        case 7:
            return (32*1024);
            break;
        case 8:
            return (64*1024);
            break;
        case 9:
            return (128*1024);
            break;
        case 10:
            return (256*1024);
            break;
        default:
            break;
    }
    return 0;
}

void reset_vecmem() {
    void *start = (void *)get_vecmem_start_address();
    size_t size = (size_t)get_vecmem_size();
    memset(start, 0, size);
}

void disable_guardbits() {
    // disabling the VDSP accumulator guard bits by updating bit #3 of aux register VEC_CTRL
    unsigned vec_ctrl = _lr(0x546);
    vec_ctrl &= (~(1<<3));
    _sr(vec_ctrl, 0x546);
}

void enable_guardbits() {
    // enabling the VDSP accumulator guard bits by updating bit #3 of aux register VEC_CTRL
    unsigned vec_ctrl = _lr(0x546);
    vec_ctrl |= (1<<3);
    _sr(vec_ctrl, 0x546);
}

static int start_power() {
    unsigned value;
    value = _lr(0x60);
    return 1;
}

static int stop_power() {
    unsigned value;
    value = _lr(0x60);
    return 1;
}

static void startRTC() {
    _sr(0x1, AUX_RTC_CTRL);
}

static void stopRTC() {
    _sr(0x0, AUX_RTC_CTRL);
}

static void clearRTC() {
    _sr(0x3, AUX_RTC_CTRL);
}   

static uint64_t getRTC() {
    unsigned low, high, ctrl;
    while (1) {
        low = _lr(AUX_RTC_LOW);
        high = _lr(AUX_RTC_HIGH);
        // test atomicity of low and high reads
        ctrl = (uint32_t)_lr(AUX_RTC_CTRL);
        if (ctrl >> 31) break;
    }
    return ((uint64_t)high) << 32 | (uint64_t)low;
}

static int compare_images(const void *    image,
                          const void *    ref_image,
                          int             width,
                          int             height,
                          int             bpp,
                          int             invalid_border_width,
                          int *           num_diffs,
                          int *           max_diff) {
    int x, y;
    *num_diffs = 0;
    *max_diff = 0;

    assert(ref_image != NULL);
    assert(image != NULL);

    switch (bpp) {
        case 8:
            for (y=invalid_border_width; y<height-invalid_border_width; y++) {
                int line = y*width;
                for (x=invalid_border_width; x<width-invalid_border_width; x++) {
                    if (((uint8_t *)image)[line+x] != ((uint8_t *)ref_image)[line+x]) {
                        *num_diffs = *num_diffs + 1;
                        int abs_diff = abs(((uint8_t *)image)[line+x] - ((uint8_t *)ref_image)[line+x]);
                        if (abs_diff > *max_diff) *max_diff = abs_diff;
                    }
                }
            }
            break;
        case 16:
            for (y=invalid_border_width; y<height-invalid_border_width; y++) {
                int line = y*width;
                for (x=invalid_border_width; x<width-invalid_border_width; x++) {
                    if (((uint16_t *)image)[line+x] != ((uint16_t *)ref_image)[line+x]) {
                        *num_diffs = *num_diffs + 1;
                        int abs_diff = abs(((uint16_t *)image)[line+x] - ((uint16_t *)ref_image)[line+x]);
                        if (abs_diff > *max_diff) *max_diff = abs_diff;
                    }
                }
            }
            break;
        default: 
            fprintf(stderr, "ERROR: invalid bits per pixel (bpp) value\n");
            break;
    };

    return 0;
}

static void print_results(int w, int h, char *unit, char *benchmark, const char *target, uint64_t cycles, int status, int diff, int max) {
    if (status == 1) {
        fprintf(stderr, "\tNumDiff = %d; MaxDiff = %d\n", diff, max);
    }
    fprintf(stderr, "%s [%dx%d] (%s) %s: %llu cycles (%.3f cycles/%s; %.3f %s/cycle)\n", benchmark, w, h, target, (status == 0) ? "PASSED" : "FAILED", cycles, (double)cycles/(w*h), unit, (double)(w*h)/cycles, unit);
}

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
#define NUM_CHAN 16

typedef union  {
    uint32_t data;
    struct {
        uint32_t n:8, reserved:24;
    };
} stu_aux_n8_t;
typedef stu_aux_n8_t stu_aux_next_free_t;

typedef union {
    uint32_t data;
    struct {
        uint32_t sp:1, slw:2, r0:1, s_lane_id:7,
            r1:1, dp:1, dlw:2, d_lane_id:7, r2:2, i:1, m:1, r3:6;
    };
} stu_ctl_t;

// virtual channel transfer descriptors
static _Uncached volatile unsigned int stu_desc[8*NUM_CHAN] __attribute__((aligned(32))); 

static void stu_init() 
{
    for (int i=0; i<8*NUM_CHAN; i++) stu_desc[i] = 0;

    // initializing DMA with NUM_CHAN virtual channels
    switch (NUM_CHAN) {
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
    }
    _sr((unsigned int)stu_desc, PSP_AUX_STU_BASE_L);
}

static void *stu_memcpy(void *dest, const void *src, size_t n) 
{
    stu_aux_next_free_t f;
    
    // get ID of next free virtual channel, from 0 to NUM_CHAN-1
    f.data = ((uint32_t) _lr(PSP_AUX_STU_NEXT_FREE));
    assert(f.data < NUM_CHAN);
    int chan = f.n;

    stu_ctl_t ctl;
    ctl.data = 0;

    // setup 1D transfer information
    stu_desc[0*NUM_CHAN + chan] = ctl.data;
    stu_desc[1*NUM_CHAN + chan] = n-1;
    stu_desc[2*NUM_CHAN + chan] = (uintptr_t) src;
    stu_desc[3*NUM_CHAN + chan] = ((uintptr_t) dest);

    _sync();

    // increment the virtual channel free index by 1. As a side
    // effect, this starts the transfer associated with the index returned 
    // previously by _lr(PSP_AUX_STU_NEXT_FREE)
    _sr(1, PSP_AUX_STU_NEXT_FREE_INC);

    // wait for end of transfer
    _sr(chan, PSP_AUX_STU_ENTRY_SELECT);
    while (1) {
        volatile int val = _lr(PSP_AUX_STU_ENTRY_STAT);
        if ((val & 0x1F) == 0x5) break;
    }

    // clear the event signal 
    _sr(0x80000000, PSP_AUX_STU_EVENT);

    return dest;
}

#endif  /* __VDSP_BENCHMARKS_UTILS_H__ */
