`define ic_data_ram

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

`define ic_data_ram_ts07n0g41p11sadcl02ms

`define Memic_data_ram mem_ts07n0g41p11sadcl02msa24_2048x78_cm4_bk2_cdtrue_bwe1_bno_rno_wrapper

`define ic_data_ram0

`define  npuarc_ic_data_ram_number_of_instances  1

`ifdef bistprts

  `undef bistprts

`endif

