`ifndef NPU_RDF_DEFINES_SV_INCLUDED
`define NPU_RDF_DEFINES_SV_INCLUDED

`define NPU_REPLACE_CLKGATE         1

// Clock gating cell from the library
`define CellLibraryClockGate        HDBSVT08_CKGTPLT_V5Y2_1

// 2 stages synchronization cell from the library
`define CellLibrarySync2Gate        HDBSVT08_SYNC2RBMSFQ_Y4_1

// 3 stages synchronization cell from the library
`define CellLibrarySync3Gate        HDBSVT08_SYNC3RBMSFQ_Y4_1

// Memory macro to used for VM
`define Mem_npu_vec_bank            mem_ts07n0g41p11sacrl256sa24_1024x144_bwe1_bk2_cm2_cd1_pg1_b0r0_wrapper

// Memory macro to use for AM
`define Mem_npu_acc_bank            mem_ts07n0g41p11sacrl256sa24_128x288_bwe1_bk1_cm1_cd1_pg1_b0r0_wrapper

`endif
