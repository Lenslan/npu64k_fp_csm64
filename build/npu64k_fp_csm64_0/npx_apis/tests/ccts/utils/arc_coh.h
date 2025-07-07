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
#ifndef __arc_coh_evss_h__
#define __arc_coh_evss_h__

#include <stdint.h>
#include <assert.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef enum {
    COH_4KB = 0,
    COH_8KB,
    COH_16KB,
    COH_32KB,
    COH_64KB,
    COH_128KB,
    COH_256KB,
    COH_512KB,
    COH_1MB,
    COH_2MB,
    COH_4MB,
    COH_8MB,
    COH_16MB,
    COH_32MB,
    COH_64MB,
    COH_128MB,
    COH_256MB,
    COH_512MB,
    COH_1GB,
    COH_2GB,
    COH_4GB
} COH_SIZE;


static inline int clusterVer() {
    return (_lr(0xCF) & 0xff);
}

// returns 1 if ARC is configured with a Coherency Unit
static inline int hasCOH() {
    return 1;
    // Temprary workaround for 9001425894 : 
    //   assume the SCU with the DMA port for IOC is always present when CNN is present
    /*
    int cv = clusterVer();
    if (cv >= 5) {
        // Newer HS release (Swordfish)
        unsigned biu_build = _lr(0xE7);
        printf("CV %d : 0x%x\n", cv, biu_build);
        return (biu_build >> 12) & 0x3;
    } else {
        // HS 3.0 / 3.1 and before (Stingray)
        unsigned cluster_build = _lr(0xCF);
        printf("CV %d : 0x%x\n", cv, cluster_build);
        return (cluster_build >> 24) & 0x3;
    }
    */
}

static inline void enable_coh_snooping(const int slice) {
    if (hasCOH()) {
        // BIU_XNN_IO_0_COH_ENABLE
        _sr(0x1, 0x510 + slice * 2);
    }
}

static inline void disable_coh_snooping(const int slice) {
    if (hasCOH()) {
        // BIU_XNN_IO_0_COH_ENABLE
        _sr(0x0, 0x510 + slice * 2);
    }
}

static inline void enable_coh_partial(const int slice) {
    if (hasCOH()) {
        // BIU_XNN_IO_0_COH_PARTIAL
        _sr(0x1, 0x511 + slice * 2);
    }
}

static inline void disable_coh_partial(const int slice) {
    if (hasCOH()) {
        // BIU_XNN_IO_0_COH_PARTIAL
        _sr(0x0, 0x511 + slice * 2);
    }
}

static inline void set_coh_aperture(const int slice, uint32_t base_address, COH_SIZE size) {
    // base snooped address must be aligned on a 'size' boundary
    assert((base_address & ((1<<(((uint32_t)size)+12))-1)) == 0);
    if (hasCOH()) {
        // BIU_XNN_IO_0_COH_AP0_SIZE
        _sr((unsigned)size, 0x519 + slice * 2);
        // BIU_XNN_IO_0_COH_AP0_BASE
        _sr(base_address>>12, 0x518 + slice * 2);
    }
}

#ifdef __cplusplus
}
#endif

#endif /* __arc_coh_evss_h__ */
