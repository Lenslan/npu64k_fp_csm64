/*
 * Copyright (C) 2021-2023 Synopsys, Inc. All rights reserved.
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
 * Data bits: 64
 * Address bits: 16 (Address protection is enabled)
 * Fault coverage: The code can detect up to two bit errors and simultaneously corrects single bit errors.
 * (Address errors are reported seperately) 
 * All-zero and all-one protection is enabled. These faults will be detected as two-bit errors.
 * Required minimum ECC bits: 8 
 ********************************************************************************************************
 */

module vm_ecc_1st_encoder(
// Module input and output ports
      input [63:0] data_in
    , input [15:0] address
    , output [7 :0] ecc
);

`include "vm_ecc_1st_func.sv"


assign ecc = vm_ecc_1st_enc(
             data_in
           , address
           );
endmodule
