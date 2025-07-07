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

// ARConnect (a.k.a. MCIP) hardware abstraction layer

#ifndef __ARCCONNECT_HAL_h__
#define __ARCCONNECT_HAL_h__

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#include "arconnect_regs.h"

// Create a command word with its associated parameters and store it in CONNECT_AUX_CMD
static inline
void _mcip_cmd_param(const uint8_t cmd, const uint16_t param)
{
    _sr(((param<<8) | cmd), CONNECT_AUX_CMD);
}

// Write a command word as-is, typically with no paramerer
static inline
void _mcip_cmd(const uint32_t cmd)
{
    _sr(cmd, CONNECT_AUX_CMD);
}

// ----------------------------------------------------------------------------
// Query build configuration
// ----------------------------------------------------------------------------

/*
 * Returns 0 if ARConnect is not present and the value of the CONNECT_SYSTEM_BUILD which
 * will be != 0 if ARconnect exist in the system
 */
static inline
int arconnect_is_present(void)
{
    return _lr(CONNECT_SYSTEM_BUILD);
}

/*
 * Return 1 if ARConnect was configured with IDU, 0 otherwise
 */
static inline
int arconnect_has_idu(void)
{
    uint32_t sys_bld = _lr(CONNECT_SYSTEM_BUILD);
    return ((sys_bld >> 23) & 0x1);
}

/*
 * Return 1 if ARConnect was configured with ICI, 0 otherwise
 */
static inline
int arconnect_has_ici(void)
{
    uint32_t sys_bld = _lr(CONNECT_SYSTEM_BUILD);
    return ((sys_bld >> 9) & 0x1);
}

/*
 * Return 1 if ARConnect was configured with GRTC, 0 otherwise
 */
static inline
int arconnect_has_grtc(void)
{
    uint32_t sys_bld = _lr(CONNECT_SYSTEM_BUILD);
    return ((sys_bld >> 14) & 0x1);
}

/*
 * Return 1 if ARConnect was configured with semaphores, 0 otherwise
 */
static inline
int arconnect_has_sema(void)
{
    uint32_t sys_bld = _lr(CONNECT_SYSTEM_BUILD);
    return ((sys_bld >> 10) & 0x1);
}

// ----------------------------------------------------------------------------
// Who am I. This is not necessarily the same ID as arcnum for the HS
// ----------------------------------------------------------------------------

static inline
int arconnect_my_id(void)
{
    int id;
    _mcip_cmd(CONNECT_CMD_CHECK_CORE_ID);
    id = _lr(CONNECT_AUX_READBACK);
    return (id & 0x1F);
}

// ----------------------------------------------------------------------------
// IDU : Interrupt Distribution Unit
// ----------------------------------------------------------------------------

// IDU common interrupt distribution modes
#define CONNECT_CIRQ_DISTR_RR                0
#define CONNECT_CIRQ_DISTR_FIRST_ACK         1
#define CONNECT_CIRQ_DISTR_ALL_DEST          2

// IDU common interrupt triggering modes
#define CONNECT_CIRQ_TRIG_LEVEL              0
#define CONNECT_CIRQ_TRIG_EDGE               1

// Macro to help set the distribution and triggering modes in CONNECT_WDATA
#define CONNECT_CIRQ_MODE(distr, trig)       (((trig)<<4)|(distr))

// IDU common interrupt destination bitmask layout
#define CONNECT_IDU_DEST_CORE_0              0x1
#define CONNECT_IDU_DEST_CORE_1              0x2
#define CONNECT_IDU_DEST_CORE_2              0x4
#define CONNECT_IDU_DEST_CORE_3              0x8

// IDU common interrupt mask status
#define CONNECT_CIRQ_UNMASKED                0
#define CONNECT_CIRQ_MASKED                  1

// Macros to extract fields from CMD_IDU_CHECK_SOURCE when reading it
//   IS_SW   bit  [0]     : 1 if IRQ is software generated, 0 if not
//   CORE_ID bits [8:4]   : If SW generated, core ID of the ARC that generated the IRQ
//   RR_CORE bits [16:12] : Core ID selected in round robin mode (if enabled)
#define CONNECT_IDU_SOURCE_IS_SW(src)           (src & 0x1)
#define CONNECT_IDU_SOURCE_CORE_ID(src)         ((src>>4)&0x1F)
#define CONNECT_IDU_SOURCE_RR_CORE(src)         ((src>>12)&0x1F)

static inline
void arconnect_idu_disable(void)
{
    _mcip_cmd(CONNECT_CMD_IDU_DISABLE);
}

static inline
void arconnect_idu_enable(void)
{
    _mcip_cmd(CONNECT_CMD_IDU_ENABLE);
}

static inline
void arconnect_unmask_cirq(uint32_t cirq)
{
    _sr(CONNECT_CIRQ_UNMASKED, CONNECT_AUX_WDATA);
    _mcip_cmd_param(CONNECT_CMD_IDU_SET_MASK,cirq);
}

static inline
void arconnect_mask_cirq(uint32_t cirq)
{
    _sr(CONNECT_CIRQ_MASKED, CONNECT_AUX_WDATA);
    _mcip_cmd_param(CONNECT_CMD_IDU_SET_MASK,cirq);
}

static inline
void arconnect_set_cirq_mode(uint32_t cirq, uint32_t distr, uint32_t trig)
{
    _sr(CONNECT_CIRQ_MODE(distr,trig), CONNECT_AUX_WDATA);
    _mcip_cmd_param(CONNECT_CMD_IDU_SET_MODE,cirq);
}

static inline
uint32_t arconnect_get_cirq_mode(uint32_t cirq)
{
    uint32_t mode;
    _mcip_cmd_param(CONNECT_CMD_IDU_READ_MODE,cirq);
    mode = _lr(CONNECT_AUX_READBACK);
    return mode;
}

static inline
void arconnect_set_cirq_dest(uint32_t cirq, uint32_t dest_mask)
{
    /* When programmed in the all-destination distribution mode,
     * for level-triggered common interrupts triggered by the external system,
     * it is invalid to set more than one target core in its DEST register.
     */
    _sr(dest_mask, CONNECT_AUX_WDATA);
    _mcip_cmd_param(CONNECT_CMD_IDU_SET_DEST,cirq);
}

static inline
uint32_t arconnect_get_cirq_dest(uint32_t cirq)
{
    uint32_t dest_mask;
    _mcip_cmd_param(CONNECT_CMD_IDU_READ_DEST,cirq);
    dest_mask = _lr(CONNECT_AUX_READBACK);
    return (dest_mask & 0xF);
}

static inline
void arconnect_ack_cirq(uint32_t cirq)
{
    _mcip_cmd_param(CONNECT_CMD_IDU_ACK_CIRQ,cirq);
}

static inline
uint32_t arconnect_idu_is_enabled(void)
{
    uint32_t data;
    _mcip_cmd(CONNECT_CMD_IDU_READ_ENABLE);
    data = _lr(CONNECT_AUX_READBACK);
    return (data & 0x1);
}

/*
 * Each core can use the CMD_IDU_CHECK_FIRST command to check if it is
 * the first-acknowledging core to the common interrupt; if IDU is programmed
 * in the first-acknowledged mode.
 *  0 = this core is not the first-acknowledging core, or this interrupt is not
 *      programmed as a first-acknowledging mode, or there is no pending
 *      status for this interrupt.
 *  1 = this core is the first-acknowledging core, and this interrupt is
 *      programmed as a first-acknowledging mode, and this interrupt is
 *      pending.
 *
 */
static inline
uint32_t arconnect_idu_check_first(uint32_t cirq)
{
    uint32_t is_first;
    _mcip_cmd_param(CONNECT_CMD_IDU_CHECK_FIRST,cirq);
    is_first = _lr(CONNECT_AUX_READBACK);
    return (is_first & 0x1);
}

static inline
void arconnect_generate_sw_cirq(uint32_t cirq)
{
     _mcip_cmd_param(CONNECT_CMD_IDU_GEN_CIRQ,cirq);
}

/*
 * Return a bit mask specifying if the common IRQ is pending or not for each cores
 */
static inline
uint32_t arconnect_check_cirq_status(uint32_t cirq)
{
    uint32_t core_mask;
    _mcip_cmd_param(CONNECT_CMD_IDU_CHECK_STATUS,cirq);
    core_mask = _lr(CONNECT_AUX_READBACK);
    return (core_mask & 0xF);
}

// ----------------------------------------------------------------------------
// ICI : Inter-Core Interrupt Unit
// ----------------------------------------------------------------------------

#define CONNECT_ICI_MAX_SOURCES         8
#define CONNECT_ICI_BITMASK             ((1<<CONNECT_ICI_MAX_SOURCES)-1)

static inline
void arconnect_ici_gen_irq(uint32_t core_id)
{
    _mcip_cmd_param(CONNECT_CMD_INTRPT_GENERATE_IRQ,(core_id & 0x1F));
}

static inline
void arconnect_ici_gen_extern_irq(void)
{
    _mcip_cmd_param(CONNECT_CMD_INTRPT_GENERATE_IRQ,(1<<8));
}

/*
 * core_id is [0-3] for a 4 ARC core system with no CNN Engine
 * can go up to [0-7] for a 4 ARC HS + 4 CNN Engine system.
 */
static inline
void arconnect_ici_ack_irq(uint32_t core_id)
{
    _mcip_cmd_param(CONNECT_CMD_INTRPT_GENERATE_ACK,(core_id & 0x1F));
}

static inline
void arconnect_ici_ack_all_mask(uint32_t mask)
{
    _mcip_cmd_param(CONNECT_CMD_INTRPT_ACK_BIT_MASK,mask);
}


/*
 * Check if an interrupt generated is still outstanding (not acknowledged).
 * Return 1 if there is an outstanding IRQ, 0 otherwise
 */
static inline
int arconnect_ici_check_outstanding(uint32_t receiver_core_id)
{
    int status;
    _mcip_cmd_param(CONNECT_CMD_INTRPT_READ_STATUS, (receiver_core_id & 0x1F));
    status =  _lr(CONNECT_AUX_READBACK);
    return status & 0x1;
}

/*
 * Return a bit mask of all the ARC cores that are generating the interrupt
 */
static inline
uint32_t arconnect_ici_check_source(void)
{
    uint32_t source;
    _mcip_cmd(CONNECT_CMD_INTRPT_CHECK_SOURCE);
    source = _lr(CONNECT_AUX_READBACK);
    return (source & CONNECT_ICI_BITMASK);
}

/*
 * Acknowledge all the ICI source that raised an interrupt and return a bit mask
 * containing the IDs.
 * Return value of 0 means nobody raised an interrupt.
 */
static inline
uint32_t arconnect_ici_ack_all_irqs()
{
    uint32_t src_mask = arconnect_ici_check_source();
    if (src_mask != 0) {
        arconnect_ici_ack_all_mask(src_mask);
    }
    return src_mask;
/*
    uint32_t acked_src = 0;
    uint32_t src_mask = arconnect_ici_check_source();
    while (src_mask != 0) {
        if (acked_src == 0) acked_src = src_mask;
        arconnect_ici_ack_all_mask(src_mask);
        src_mask = arconnect_ici_check_source();
    }
    return acked_src;
*/
}

static inline
uint32_t arconnect_ici_ack_loop()
{
    uint32_t acked_src = 0;
    uint32_t src_mask = arconnect_ici_check_source();
    while (src_mask != 0) {
        uint32_t id_mask = 0x1;
        #pragma clang loop unroll(full)
        for (int i = 0; i < CONNECT_ICI_MAX_SOURCES; i++) {
            if (src_mask & id_mask) {
                arconnect_ici_ack_irq(i);
                acked_src |= id_mask;
            }
            id_mask <<= 1;
        }
        // loop until it is confirmed the interrupt got de-asserted
        src_mask = arconnect_ici_check_source();
    }
    return acked_src;

}

// ----------------------------------------------------------------------------
// GFRC : Global Free Running Counter (a.k.a. global real time counter / GRTC)
// ----------------------------------------------------------------------------

static inline
void arconnect_clear_gfrc(void)
{
    _mcip_cmd(CONNECT_CMD_GRTC_CLEAR);
}

static inline
uint64_t arconnect_get_gfrc(void)
{
    uint32_t low, high;
    uint64_t grtc;
    // Reading the 32 LSB of the counter also triggers a snapshot of
    // the current higher 32 bits, so they can be safely read in a
    // second step.
    _mcip_cmd(CONNECT_CMD_GRTC_READ_LO);
    low = _lr(CONNECT_AUX_READBACK);
    // Read the 32 MSB
    _mcip_cmd(CONNECT_CMD_GRTC_READ_HI);
    high = _lr(CONNECT_AUX_READBACK);
    // Return the 64bit free running counter value
    grtc = ((uint64_t)high) << 32 | (uint64_t)low;
    return grtc;
}


#ifdef __cplusplus
}
#endif

#endif /* __ARCCONNECT_HAL_h__ */
