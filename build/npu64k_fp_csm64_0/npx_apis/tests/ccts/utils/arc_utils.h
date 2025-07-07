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
#ifndef __arc_utils_evss_h__
#define __arc_utils_evss_h__

// Divide or round up 'a' to the closest integer which is a multipe of 'q'.
// Inputs to the macros must be positive integers
//#define DIVIDE_UP(a,q)  ( (((a)+(q)-1) / (q)) )
//#define ROUND_UP(a,q)   ( DIVIDE_UP(a,q) * (q) )
//#define DIVIDE_UP8(a)   ( (((a)+7) / 8) )
//#define ROUND_UP8(a)    ( DIVIDE_UP8(a) * 8 )
//#define DIVIDE_UP4(a)   ( (((a)+3) / 4) )
//#define ROUND_UP4(a)    ( DIVIDE_UP4(a) * 4 )
//#define DIVIDE_UP16(a)  ( (((a)+15) / 16) )
//#define ROUND_UP16(a)   ( DIVIDE_UP16(a) * 16 )

#include <stdint.h>
#include <arc/arc_reg.h>

#ifdef __cplusplus
extern "C" {
#endif

// Get the arcnum ID
//   arcnum[7:0] is located in IDENTITY[15:8]
//   IDENTITY auxiliary register is at address 0x4
static inline
unsigned int get_arcnum()
{
    return ((_lr(IDENTITY) >> 8) & 0xFF);
}

// Get the number of ARC cores in the cluster
//   num_cores[7:0] is located in CLUSTER_BUILD[15:8]
//   CLUSTER_BUILD auxiliary register is at address 0xCF
static inline
unsigned int get_numcores()
{
    return ((_lr(0xCF) >> 8) & 0xFF);
}

// Get the ARC baseline instruction set version number (ARCVER)
//   arcver[7:0] is located in IDENTITY[7:0]
//   IDENTITY auxiliary register is at address 0x4
static inline
unsigned int get_arcver()
{
    return (_lr(IDENTITY) & 0xFF);
}

// Check if ARCVER corresponds to an ARC HS processor
static inline
int is_archs()
{
    const unsigned int ver = get_arcver();
    if ((ver >= 0x50) && (ver <= 0x5F)) {
        return 1;
    }
    return 0;
}

// Check if ARCVER corresponds to an ARC EM processor
static inline
int is_arcem()
{
    const unsigned int ver = get_arcver();
    if ((ver >= 0x40) && (ver <= 0x4F)) {
        return 1;
    }
    return 0;
}

// Check if a cluster shared memory (CSM) is present in the cluster
//   CSM_BUILD register is at address 0xE5
static inline
int has_csm()
{
    return (_lr(0xE5) != 0);
}

// Returns the size of the CSM in  bytes, or 0 if no CSM is present in the cluster
//   CSM_BUILD register is at address 0xE5
static inline
unsigned int csm_size()
{
    if (!has_csm()) return 0;

    int size = (_lr(0xE5) >> 8) & 0xF;
    switch (size) {
        case 0:
            return 32*1024;
            break;
        case 1:
            return 64*1024;
            break;
        case 2:
            return 128*1024;
            break;
        case 3:
            return 256*1024;
            break;
        case 4:
            return 512*1024;
            break;
        case 5:
            return 1024*1024;
            break;
        case 6:
            return 2*1024*1024;
            break;
        case 7:
            return 4*1024*1024;
            break;
        case 8:
            return 8*1024*1024;
            break;
        default:
            break;
    }
    return 0;
}

// Return 1 if enabled, 0 if disabled
static inline
int csm_status()
{
    return _lr(0x9A0) & 0x1;
}

static inline
int csm_cur_pmode()
{
    return _lr(0x623) & 0x7; // PDM_CSM_PSTAT current mode
}

// Warning : All other ARC HS cores must have flushed their D$ of all dirty lines
// in CSM and executed a sync instruction before shutting down CSM
static inline
int csm_deepsleep(int poll)
{
    int cs = csm_cur_pmode();
    int rv = 0;
    if (cs == 0) {
        _sync();
        _sr(0x1, 0x04B); // Flush data cache
        _sync();
        _sr(0x0, 0x9A0); // Disable CSM
        _sr(0x1, 0x622); // Set PM1 in PDM_CSM_PMODE
        do {
            _nop();  _nop(); _nop(); _nop();
            poll--;
            rv = csm_cur_pmode();
        } while ((rv != 1) && (poll > 0));
    }
    return rv;
}

// Warning : All other ARC HS cores must have flushed their D$ of all dirty lines
// in CSM and executed a sync instruction before shutting down CSM
static inline
int csm_shutdown(int poll)
{
    int cs = csm_cur_pmode();
    int rv = 0;
    if ((cs == 0) || (cs == 1)) {
        if (cs == 0) {
            _sync();
            _sr(0x1, 0x04B); // Flush data cache
            _sync();
            _sr(0x0, 0x9A0); // Disable CSM
        }
        _sr(0x2, 0x622); // Set PM2 in PDM_CSM_PMODE
        do {
            _nop();  _nop(); _nop(); _nop();
            poll--;
            rv = csm_cur_pmode();
        } while ((rv != 1) && (poll > 0));
    }
    return rv;
}

static inline
int csm_power_up(int poll)
{
    int cs = csm_cur_pmode();
    if (cs != 0) {
        _sr(0x0, 0x622); // PDM_CSM_PMODE = on
        do {
            _nop();  _nop(); _nop(); _nop();
            poll--;
            cs = csm_cur_pmode();
        } while ((cs != 0) && (poll > 0));
        _sr(0x1, 0x9A0); // Enable CSM
    }
    return cs;
}

// Start power estimation flow during HDL simulation by
// reading a dummy AUX register
static inline
unsigned start_power()
{
    unsigned value;
    _sync();
    _nop();
    _nop();
    _nop();
    value = _lr(0x60);
    return value;
}

// Stop power estimation flow during HDL simulation by
// reading a dummy AUX register
static inline
unsigned stop_power()
{
    unsigned value;
    _sync();
    _nop();
    _nop();
    _nop();
    value = _lr(0x60);
    return value;
}

// Set the value of GLOBAL_CLK_GATE_DIS for L1 clock gating
//   CLUSTER_BUILD register is at address 0xCF, and bit 30 indicates clock gating present
//   GLOBAL_CLK_GATE_DIS register is at address 0x9A9. Set to 0 to enable gating
static inline
void disable_cc_clk_gate(int val)
{
    if ((_lr(0xCF) >> 30) & 0x1) {
        _sr(val, 0x9A9);
    }
}

#ifdef __cplusplus
}
#endif

#endif /* __arc_utils_evss_h__ */
