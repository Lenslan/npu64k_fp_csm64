`define scm_dbank_sram

`ifdef BldCfgSizeWordsExtended

  `undef BldCfgSizeWordsExtended

`endif

`ifdef SizeBitsExtended

  `undef SizeBitsExtended

`endif

`ifdef BldCfgSizeBitsDiv2

  `undef BldCfgSizeBitsDiv2

`endif

`ifdef BldCfgSizeBitsDiv4

  `undef BldCfgSizeBitsDiv4

`endif

`define scm_dbank_sram_ts07n0g41p11sadcl02ms

`define Memscm_dbank_sram mem_ts07n0g41p11sadcl02msa24_16384x137_cm8_bk8_cdtrue_bwe1_bno_rno_wrapper

`define scm_dbank_sram0

`define  nl2_scm_dbank_sram_number_of_instances  1

`ifdef bistprts

  `undef bistprts

`endif

