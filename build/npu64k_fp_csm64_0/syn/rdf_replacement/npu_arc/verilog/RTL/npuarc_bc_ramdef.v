`define bc_ram

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

`define bc_ram_ts07n0g41p11sadcl02ms

`define Membc_ram mem_ts07n0g41p11sadcl02msa24_256x68_cm4_bk1_cdtrue_bwe1_bno_rno_wrapper

`define bc_ram0

`define  npuarc_bc_ram_number_of_instances  1

`ifdef bistprts

  `undef bistprts

`endif

