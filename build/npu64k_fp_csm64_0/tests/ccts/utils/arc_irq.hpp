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


_Uncached volatile uint32_t irq_sync_flag = 0;

_Interrupt void timer0_handler()
{
    unsigned ctrl = _lr(REG_CONTROL0);
    irq_sync_flag = ctrl;
    ctrl &= 0xFFF7; // clear the IP bit
    _sr(ctrl, REG_CONTROL0);
    _sync();
}

// Sleep while waiting for an interrupt
static void wait_irq()
{
    irq_sync_flag = 0;
    _clri();
    while (irq_sync_flag == 0) {
        _sleep(0x1F);
        _clri();
    }
    _seti(0);
}

