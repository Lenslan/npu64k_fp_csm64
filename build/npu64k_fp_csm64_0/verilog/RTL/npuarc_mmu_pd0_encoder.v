// Library ARCv2HS-3.5.999999999
/*
 * Copyright (C) 2016-2017 Synopsys, Inc. All rights reserved.
 *
 * SYNOPSYS CONFIDENTIAL - This is an unpublished, confidential, and
 * proprietary work of Synopsys, Inc., and may be subject to patent,
 * copyright, trade secret, and other legal or contractual protection.
 * This work may be used only pursuant to the terms and conditions of a
 * written license agreement with Synopsys, Inc. All other use, reproduction,
 * distribution, or disclosure of this work is strictly prohibited.
 *
 * The entire notice above must be reproduced on all authorized copies.
 */



/*
 *************************************** MODULE INFO ***************************************************
 * Data bits: 26
 * Address bits: 0 (Address protection is enabled)
 * Fault coverage: The code can detect up to two bit errors and simultaneously corrects single bit errors.
 * All-zero and all-one protection is enabled. These faults will be detected as two-bit errors.
 * Required minimum ECC bits: 7 
 ********************************************************************************************************
 */

module npuarc_mmu_pd0_ecc_encoder(
// Module input and output ports
      input [25:0] data_in
    , output [6 :0] ecc
);

`include "npuarc_mmu_pd0_ecc_func.v"

assign ecc = mmu_pd0_ecc_enc(
             data_in    
           );
endmodule
