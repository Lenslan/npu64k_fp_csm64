`define mmu_ntlb_pd1_ram

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

`define mmu_ntlb_pd1_ram_ts07n0g41p11sadcl02ms

`define Memmmu_ntlb_pd1_ram mem_ts07n0g41p11sadcl02msa24_256x45_cm4_bk1_cdfalse_bwe0_bno_rno_wrapper

`define mmu_ntlb_pd1_ram0

`define  npuarc_mmu_ntlb_pd1_ram_number_of_instances  1

`ifdef bistprts

  `undef bistprts

`endif

