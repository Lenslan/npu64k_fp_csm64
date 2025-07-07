`define dc_tag_ram

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

`define dc_tag_ram_ts07n0g41p11sadcl02ms

`define Memdc_tag_ram mem_ts07n0g41p11sadcl02msa24_128x34_cm4_bk1_cdfalse_bwe1_bno_rno_wrapper

`define dc_tag_ram0

`define  npuarc_dc_tag_ram_number_of_instances  1

`ifdef bistprts

  `undef bistprts

`endif

