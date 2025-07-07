<script>
var extensions = 
  [
    {
    comment:	"no comment",
    ext_type:	2,
    gate_count:	0,
    ext_name:	"EventManager",
    xpu_num:	-1,
    permission:	"user",
    signals:	
      [
        {
        name:	"evm_event_a",
        mode:	"input",
        klass:	"Unregistered",
        MSB:	95,
        LSB:	0,
        description:	"asynchronous event inputs",
        }
      ,
        {
        name:	"evm_wakeup",
        mode:	"output",
        klass:	"Unregistered",
        MSB:	0,
        LSB:	0,
        description:	"wakup the core",
        }
      ,
        {
        name:	"evm_sleep",
        mode:	"input",
        klass:	"Unregistered",
        MSB:	0,
        LSB:	0,
        description:	"if true then core sleeps",
        }
      ,
        {
        name:	"evm_send",
        mode:	"output",
        klass:	"Unregistered",
        MSB:	63,
        LSB:	0,
        description:	"Event Send",
        }
      ,
        {
        name:	"vm_grp0_sid",
        mode:	"output",
        klass:	"Unregistered",
        MSB:	31,
        LSB:	0,
        description:	"EVT_SID register to drive SID for group0",
        }
      ,
        {
        name:	"vm_grp0_ssid",
        mode:	"output",
        klass:	"Unregistered",
        MSB:	31,
        LSB:	0,
        description:	"EVT_SSID to drive SSID group0",
        }
      ,
        {
        name:	"vm_grp1_sid",
        mode:	"output",
        klass:	"Unregistered",
        MSB:	31,
        LSB:	0,
        description:	"EVT_SID register to drive SID for group1",
        }
      ,
        {
        name:	"vm_grp1_ssid",
        mode:	"output",
        klass:	"Unregistered",
        MSB:	31,
        LSB:	0,
        description:	"EVT_SSID to drive SSID of group1",
        }
      ,
        {
        name:	"vm_grp2_sid",
        mode:	"output",
        klass:	"Unregistered",
        MSB:	31,
        LSB:	0,
        description:	"EVT_SID register to drive SID for group2",
        }
      ,
        {
        name:	"vm_grp3_sid",
        mode:	"output",
        klass:	"Unregistered",
        MSB:	31,
        LSB:	0,
        description:	"EVT_SID register to drive SID for group3",
        }
      ,
        {
        name:	"vm_grp2_ssid",
        mode:	"output",
        klass:	"Unregistered",
        MSB:	31,
        LSB:	0,
        description:	"EVT_SSID to drive SSID of group2",
        }
      ,
        {
        name:	"vm_grp3_ssid",
        mode:	"output",
        klass:	"Unregistered",
        MSB:	31,
        LSB:	0,
        description:	"EVT_SSID to drive SSID of group3",
        }
      ,
        {
        name:	"evt_vm_irq",
        mode:	"output",
        klass:	"Unregistered",
        MSB:	0,
        LSB:	0,
        description:	"IRQ send from Event Manager",
        }
      ,
        {
        name:	"evt_vm_sel",
        mode:	"output",
        klass:	"Unregistered",
        MSB:	3,
        LSB:	0,
        description:	"Current VM get selected, use to select virtual evt",
        }
      ,
      ]
    ,
    sop_insts:	
      [
        {
        inst:	"EVTMASKCHK",
        opcode:	0,
        NumberOfOperands:	"single",
        cycles:	3,
        inst_group:	"evmww",
        has_dst:	true,
        implicitCoreRead:	false,
        implicitCoreWrite:	false,
        implicitAuxRead:	false,
        implicitAuxWrite:	false,
        ext_group:	7,
        OperandSizes:	"64x64",
        src_width:	64,
        dst_width:	64,
        inst_type:	2,
        flag_setting:	true,
        blocking:	true,
        has_exception:	false,
        ext_name:	"EventManager",
        comment:	"",
        core_access:	
          [
          ]
        ,
        aux_access:	
          [
          ]
        ,
        }
      ,
        {
        inst:	"EVTMASKALL",
        opcode:	1,
        NumberOfOperands:	"single",
        cycles:	3,
        inst_group:	"evmww",
        has_dst:	true,
        implicitCoreRead:	false,
        implicitCoreWrite:	false,
        implicitAuxRead:	false,
        implicitAuxWrite:	false,
        ext_group:	7,
        OperandSizes:	"64x64",
        src_width:	64,
        dst_width:	64,
        inst_type:	2,
        flag_setting:	true,
        blocking:	true,
        has_exception:	false,
        ext_name:	"EventManager",
        comment:	"",
        core_access:	
          [
          ]
        ,
        aux_access:	
          [
          ]
        ,
        }
      ,
        {
        inst:	"EVTMASKANY",
        opcode:	2,
        NumberOfOperands:	"single",
        cycles:	3,
        inst_group:	"evmww",
        has_dst:	true,
        implicitCoreRead:	false,
        implicitCoreWrite:	false,
        implicitAuxRead:	false,
        implicitAuxWrite:	false,
        ext_group:	7,
        OperandSizes:	"64x64",
        src_width:	64,
        dst_width:	64,
        inst_type:	2,
        flag_setting:	true,
        blocking:	true,
        has_exception:	false,
        ext_name:	"EventManager",
        comment:	"",
        core_access:	
          [
          ]
        ,
        aux_access:	
          [
          ]
        ,
        }
      ,
        {
        inst:	"EVTMASKDECR",
        opcode:	3,
        NumberOfOperands:	"single",
        cycles:	3,
        inst_group:	"evmw",
        has_dst:	true,
        implicitCoreRead:	false,
        implicitCoreWrite:	false,
        implicitAuxRead:	false,
        implicitAuxWrite:	false,
        ext_group:	7,
        OperandSizes:	"64x64",
        src_width:	64,
        dst_width:	64,
        inst_type:	2,
        flag_setting:	true,
        blocking:	true,
        has_exception:	false,
        ext_name:	"EventManager",
        comment:	"",
        core_access:	
          [
          ]
        ,
        aux_access:	
          [
          ]
        ,
        }
      ,
        {
        inst:	"EVTMASKINCR",
        opcode:	4,
        NumberOfOperands:	"single",
        cycles:	3,
        inst_group:	"evmw",
        has_dst:	true,
        implicitCoreRead:	false,
        implicitCoreWrite:	false,
        implicitAuxRead:	false,
        implicitAuxWrite:	false,
        ext_group:	7,
        OperandSizes:	"64x64",
        src_width:	64,
        dst_width:	64,
        inst_type:	2,
        flag_setting:	true,
        blocking:	true,
        has_exception:	false,
        ext_name:	"EventManager",
        comment:	"",
        core_access:	
          [
          ]
        ,
        aux_access:	
          [
          ]
        ,
        }
      ,
        {
        inst:	"EVTMASKSEND",
        opcode:	5,
        NumberOfOperands:	"single",
        cycles:	3,
        inst_group:	"evm",
        has_dst:	true,
        implicitCoreRead:	false,
        implicitCoreWrite:	false,
        implicitAuxRead:	false,
        implicitAuxWrite:	false,
        ext_group:	7,
        OperandSizes:	"64x64",
        src_width:	64,
        dst_width:	64,
        inst_type:	2,
        flag_setting:	true,
        blocking:	true,
        has_exception:	false,
        ext_name:	"EventManager",
        comment:	"",
        core_access:	
          [
          ]
        ,
        aux_access:	
          [
          ]
        ,
        }
      ,
        {
        inst:	"EVTVMCHK",
        opcode:	6,
        NumberOfOperands:	"single",
        cycles:	3,
        inst_group:	"evmww",
        has_dst:	true,
        implicitCoreRead:	false,
        implicitCoreWrite:	false,
        implicitAuxRead:	false,
        implicitAuxWrite:	false,
        ext_group:	7,
        OperandSizes:	"64x64",
        src_width:	64,
        dst_width:	64,
        inst_type:	2,
        flag_setting:	true,
        blocking:	true,
        has_exception:	false,
        ext_name:	"EventManager",
        comment:	"",
        core_access:	
          [
          ]
        ,
        aux_access:	
          [
          ]
        ,
        }
      ,
      ]
    ,
    dop_insts:	
      [
      ]
    ,
    zop_insts:	
      [
      ]
    ,
    core_regs:	
      [
      ]
    ,
    aux_regs:	
      [
        {
        has_wr_out:	false,
        has_rd_out:	false,
        ar_name:	"EVT_CTRL",
        ar_num:	0xf02,
        ext_name:	"EventManager",
        user_defined:	true,
        write_only:	false,
        write_prot:	false,
        direct_write:	false,
        read_only:	false,
        comment:	"iRW ePUD",
        width:	32,
        valid_mask:	0xffffffff,
        valid_mask_in_verilog:	"32'hffffffff",
        user_specified_valid_mask:	false,
        serializing:	"last",
        instruction_access:	"read/write",
        extension_access:	"user defined",
        forwarding:	false,
        reset_value:	0,
        reset_value_in_verilog:	"32'h0",
        assembler_mode:	"r|w",
        }
      ,
        {
        has_wr_out:	false,
        has_rd_out:	false,
        ar_name:	"EVT_FILTER_LO",
        ar_num:	0xf04,
        ext_name:	"EventManager",
        user_defined:	true,
        write_only:	false,
        write_prot:	false,
        direct_write:	false,
        read_only:	false,
        comment:	"iRW ePUD",
        width:	32,
        valid_mask:	0xffffffff,
        valid_mask_in_verilog:	"32'hffffffff",
        user_specified_valid_mask:	false,
        serializing:	"last",
        instruction_access:	"read/write",
        extension_access:	"user defined",
        forwarding:	false,
        reset_value:	0,
        reset_value_in_verilog:	"32'h0",
        assembler_mode:	"r|w",
        }
      ,
        {
        has_wr_out:	false,
        has_rd_out:	false,
        ar_name:	"EVT_FILTER_HI",
        ar_num:	0xf05,
        ext_name:	"EventManager",
        user_defined:	true,
        write_only:	false,
        write_prot:	false,
        direct_write:	false,
        read_only:	false,
        comment:	"iRW ePUD",
        width:	32,
        valid_mask:	0xffffffff,
        valid_mask_in_verilog:	"32'hffffffff",
        user_specified_valid_mask:	false,
        serializing:	"last",
        instruction_access:	"read/write",
        extension_access:	"user defined",
        forwarding:	false,
        reset_value:	0,
        reset_value_in_verilog:	"32'h0",
        assembler_mode:	"r|w",
        }
      ,
        {
        has_wr_out:	false,
        has_rd_out:	false,
        ar_name:	"EVT_CNT_SEL",
        ar_num:	0xf0a,
        ext_name:	"EventManager",
        user_defined:	true,
        write_only:	false,
        write_prot:	false,
        direct_write:	false,
        read_only:	false,
        comment:	"iRW ePUD",
        width:	32,
        valid_mask:	0xffffffff,
        valid_mask_in_verilog:	"32'hffffffff",
        user_specified_valid_mask:	false,
        serializing:	"last",
        instruction_access:	"read/write",
        extension_access:	"user defined",
        forwarding:	false,
        reset_value:	0,
        reset_value_in_verilog:	"32'h0",
        assembler_mode:	"r|w",
        }
      ,
        {
        has_wr_out:	false,
        has_rd_out:	false,
        ar_name:	"EVT_CNT_VAL",
        ar_num:	0xf0b,
        ext_name:	"EventManager",
        user_defined:	true,
        write_only:	false,
        write_prot:	false,
        direct_write:	false,
        read_only:	false,
        comment:	"iRW ePUD",
        width:	32,
        valid_mask:	0xffffffff,
        valid_mask_in_verilog:	"32'hffffffff",
        user_specified_valid_mask:	false,
        serializing:	"last",
        instruction_access:	"read/write",
        extension_access:	"user defined",
        forwarding:	false,
        reset_value:	0,
        reset_value_in_verilog:	"32'h0",
        assembler_mode:	"r|w",
        }
      ,
        {
        has_wr_out:	false,
        has_rd_out:	false,
        ar_name:	"EVT_VM_SEL",
        ar_num:	0xf00,
        ext_name:	"EventManager",
        user_defined:	true,
        write_only:	false,
        write_prot:	false,
        direct_write:	false,
        read_only:	false,
        comment:	"iRW ePUD",
        width:	32,
        valid_mask:	0xffffffff,
        valid_mask_in_verilog:	"32'hffffffff",
        user_specified_valid_mask:	false,
        serializing:	"last",
        instruction_access:	"read/write",
        extension_access:	"user defined",
        forwarding:	false,
        reset_value:	0,
        reset_value_in_verilog:	"32'h0",
        assembler_mode:	"r|w",
        }
      ,
        {
        has_wr_out:	false,
        has_rd_out:	false,
        ar_name:	"EVT_VM_MAP",
        ar_num:	0xf01,
        ext_name:	"EventManager",
        user_defined:	true,
        write_only:	false,
        write_prot:	false,
        direct_write:	false,
        read_only:	false,
        comment:	"iRW ePUD",
        width:	32,
        valid_mask:	0xffffffff,
        valid_mask_in_verilog:	"32'hffffffff",
        user_specified_valid_mask:	false,
        serializing:	"last",
        instruction_access:	"read/write",
        extension_access:	"user defined",
        forwarding:	false,
        reset_value:	0,
        reset_value_in_verilog:	"32'h0",
        assembler_mode:	"r|w",
        }
      ,
        {
        has_wr_out:	false,
        has_rd_out:	false,
        ar_name:	"EVT_GRP_SEL",
        ar_num:	0xf07,
        ext_name:	"EventManager",
        user_defined:	true,
        write_only:	false,
        write_prot:	false,
        direct_write:	false,
        read_only:	false,
        comment:	"iRW ePUD",
        width:	32,
        valid_mask:	0xffffffff,
        valid_mask_in_verilog:	"32'hffffffff",
        user_specified_valid_mask:	false,
        serializing:	"last",
        instruction_access:	"read/write",
        extension_access:	"user defined",
        forwarding:	false,
        reset_value:	0,
        reset_value_in_verilog:	"32'h0",
        assembler_mode:	"r|w",
        }
      ,
        {
        has_wr_out:	false,
        has_rd_out:	false,
        ar_name:	"EVT_SID",
        ar_num:	0xf08,
        ext_name:	"EventManager",
        user_defined:	true,
        write_only:	false,
        write_prot:	false,
        direct_write:	false,
        read_only:	false,
        comment:	"iRW ePUD",
        width:	32,
        valid_mask:	0xffffffff,
        valid_mask_in_verilog:	"32'hffffffff",
        user_specified_valid_mask:	false,
        serializing:	"last",
        instruction_access:	"read/write",
        extension_access:	"user defined",
        forwarding:	false,
        reset_value:	0,
        reset_value_in_verilog:	"32'h0",
        assembler_mode:	"r|w",
        }
      ,
        {
        has_wr_out:	false,
        has_rd_out:	false,
        ar_name:	"EVT_SSID",
        ar_num:	0xf09,
        ext_name:	"EventManager",
        user_defined:	true,
        write_only:	false,
        write_prot:	false,
        direct_write:	false,
        read_only:	false,
        comment:	"iRW ePUD",
        width:	32,
        valid_mask:	0xffffffff,
        valid_mask_in_verilog:	"32'hffffffff",
        user_specified_valid_mask:	false,
        serializing:	"last",
        instruction_access:	"read/write",
        extension_access:	"user defined",
        forwarding:	false,
        reset_value:	0,
        reset_value_in_verilog:	"32'h0",
        assembler_mode:	"r|w",
        }
      ,
        {
        has_wr_out:	false,
        has_rd_out:	false,
        ar_name:	"EVT_IRQ",
        ar_num:	0xf03,
        ext_name:	"EventManager",
        user_defined:	true,
        write_only:	false,
        write_prot:	false,
        direct_write:	false,
        read_only:	false,
        comment:	"iRW ePUD",
        width:	32,
        valid_mask:	0xffffffff,
        valid_mask_in_verilog:	"32'hffffffff",
        user_specified_valid_mask:	false,
        serializing:	"last",
        instruction_access:	"read/write",
        extension_access:	"user defined",
        forwarding:	false,
        reset_value:	0,
        reset_value_in_verilog:	"32'h0",
        assembler_mode:	"r|w",
        }
      ,
      ]
    ,
    cond_codes:	
      [
      ]
    ,
    vint:	
      {
      comment:	"This is the Verilog module interface",
      user_verilog:	"foo.v",
      instruction:	true,
      flag:	true,
      prop32:	
        {
        }
      ,
      prop64:	
        {
        has:	true,
        flag:	true,
        typenz:	true,
        }
      ,
      verilog_string:	"// leda G_521_2_B off\n// LMD: use lowercase letters\n// LI: generated by AP"+
"EX\n`define COREREG_SIZE 32\n`include \"npuarc_defines.v\"\n// spyglass disable_block "+
"Reset_info09b\nmodule uxEventManager (\n// spyglass disable_block W240\n     "+
"   input          clk,\n        input          clk_ungated,\n        input  "+
"[63:0]  source1_64,\n        input  [63:0]  source2_64,\n        input  [3:0"+
"]   bflags_r_64,\n        input  [3:0]   xflags_r_64,\n        input  [5:0] "+
"  sub_opcode_64,\n        input  [63:0]  source1_64_nxt,\n        input  [63"+
":0]  source2_64_nxt,\n        input  [5:0]   sub_opcode_64_nxt,\n\n        //"+
" User-defined extension register EVT_CTRL\n        input  [31:0]  EVT_CTRL_"+
"ar_wdata,\n        input          EVT_CTRL_ar_wen,\n        output [31:0]  E"+
"VT_CTRL_ar_rdata,\n        input          EVT_CTRL_ar_ren,\n        input   "+
"       EVT_CTRL_ar_rd_cmt,\n        input          EVT_CTRL_ar_rd_abort,\n\n "+
"       // User-defined extension register EVT_FILTER_LO\n        input  [31"+
":0]  EVT_FILTER_LO_ar_wdata,\n        input          EVT_FILTER_LO_ar_wen,\n"+
"        output [31:0]  EVT_FILTER_LO_ar_rdata,\n        input          EVT_"+
"FILTER_LO_ar_ren,\n        input          EVT_FILTER_LO_ar_rd_cmt,\n        "+
"input          EVT_FILTER_LO_ar_rd_abort,\n\n        // User-defined extensi"+
"on register EVT_FILTER_HI\n        input  [31:0]  EVT_FILTER_HI_ar_wdata,\n "+
"       input          EVT_FILTER_HI_ar_wen,\n        output [31:0]  EVT_FIL"+
"TER_HI_ar_rdata,\n        input          EVT_FILTER_HI_ar_ren,\n        inpu"+
"t          EVT_FILTER_HI_ar_rd_cmt,\n        input          EVT_FILTER_HI_a"+
"r_rd_abort,\n\n        // User-defined extension register EVT_CNT_SEL\n      "+
"  input  [31:0]  EVT_CNT_SEL_ar_wdata,\n        input          EVT_CNT_SEL_"+
"ar_wen,\n        output [31:0]  EVT_CNT_SEL_ar_rdata,\n        input        "+
"  EVT_CNT_SEL_ar_ren,\n        input          EVT_CNT_SEL_ar_rd_cmt,\n      "+
"  input          EVT_CNT_SEL_ar_rd_abort,\n\n        // User-defined extensi"+
"on register EVT_CNT_VAL\n        input  [31:0]  EVT_CNT_VAL_ar_wdata,\n     "+
"   input          EVT_CNT_VAL_ar_wen,\n        output [31:0]  EVT_CNT_VAL_a"+
"r_rdata,\n        input          EVT_CNT_VAL_ar_ren,\n        input         "+
" EVT_CNT_VAL_ar_rd_cmt,\n        input          EVT_CNT_VAL_ar_rd_abort,\n\n "+
"       // User-defined extension register EVT_VM_SEL\n        input  [31:0]"+
"  EVT_VM_SEL_ar_wdata,\n        input          EVT_VM_SEL_ar_wen,\n        o"+
"utput [31:0]  EVT_VM_SEL_ar_rdata,\n        input          EVT_VM_SEL_ar_re"+
"n,\n        input          EVT_VM_SEL_ar_rd_cmt,\n        input          EVT"+
"_VM_SEL_ar_rd_abort,\n\n        // User-defined extension register EVT_VM_MA"+
"P\n        input  [31:0]  EVT_VM_MAP_ar_wdata,\n        input          EVT_V"+
"M_MAP_ar_wen,\n        output [31:0]  EVT_VM_MAP_ar_rdata,\n        input   "+
"       EVT_VM_MAP_ar_ren,\n        input          EVT_VM_MAP_ar_rd_cmt,\n   "+
"     input          EVT_VM_MAP_ar_rd_abort,\n\n        // User-defined exten"+
"sion register EVT_GRP_SEL\n        input  [31:0]  EVT_GRP_SEL_ar_wdata,\n   "+
"     input          EVT_GRP_SEL_ar_wen,\n        output [31:0]  EVT_GRP_SEL"+
"_ar_rdata,\n        input          EVT_GRP_SEL_ar_ren,\n        input       "+
"   EVT_GRP_SEL_ar_rd_cmt,\n        input          EVT_GRP_SEL_ar_rd_abort,\n"+
"\n        // User-defined extension register EVT_SID\n        input  [31:0] "+
" EVT_SID_ar_wdata,\n        input          EVT_SID_ar_wen,\n        output ["+
"31:0]  EVT_SID_ar_rdata,\n        input          EVT_SID_ar_ren,\n        in"+
"put          EVT_SID_ar_rd_cmt,\n        input          EVT_SID_ar_rd_abort"+
",\n\n        // User-defined extension register EVT_SSID\n        input  [31:"+
"0]  EVT_SSID_ar_wdata,\n        input          EVT_SSID_ar_wen,\n        out"+
"put [31:0]  EVT_SSID_ar_rdata,\n        input          EVT_SSID_ar_ren,\n   "+
"     input          EVT_SSID_ar_rd_cmt,\n        input          EVT_SSID_ar"+
"_rd_abort,\n\n        // User-defined extension register EVT_IRQ\n        inp"+
"ut  [31:0]  EVT_IRQ_ar_wdata,\n        input          EVT_IRQ_ar_wen,\n     "+
"   output [31:0]  EVT_IRQ_ar_rdata,\n        input          EVT_IRQ_ar_ren,"+
"\n        input          EVT_IRQ_ar_rd_cmt,\n        input          EVT_IRQ_"+
"ar_rd_abort,\n        input  [95:0]  evm_event_a,\n        output         ev"+
"m_wakeup,\n        input          evm_sleep,\n        output [63:0]  evm_sen"+
"d,\n        output [31:0]  vm_grp0_sid,\n        output [31:0]  vm_grp0_ssid"+
",\n        output [31:0]  vm_grp1_sid,\n        output [31:0]  vm_grp1_ssid,"+
"\n        output [31:0]  vm_grp2_sid,\n        output [31:0]  vm_grp3_sid,\n "+
"       output [31:0]  vm_grp2_ssid,\n        output [31:0]  vm_grp3_ssid,\n "+
"       output         evt_vm_irq,\n        output [3:0]   evt_vm_sel,\n     "+
"   \n        input          evmww_start,\n        input          evmww_stall"+
",\n        input          evmww_end,\n        input          evmww_start_nxt"+
",\n        input          evmww_kill,\n        input          evmww_commit,\n"+
"        input          evmww_decode,\n        output         evmww_busy,\n  "+
"      output [3:0]   evmww_bflags,\n        output [3:0]   evmww_xflags,\n  "+
"      output [63:0]  evmww_res,\n        \n        input          evmw_start"+
",\n        input          evmw_stall,\n        input          evmw_end,\n    "+
"    input          evmw_start_nxt,\n        input          evmw_kill,\n     "+
"   input          evmw_commit,\n        input          evmw_decode,\n       "+
" output         evmw_busy,\n        output [3:0]   evmw_bflags,\n        out"+
"put [3:0]   evmw_xflags,\n        output [63:0]  evmw_res,\n        \n       "+
" input          evm_start,\n        input          evm_stall,\n        input"+
"          evm_end,\n        input          evm_start_nxt,\n        input    "+
"      evm_kill,\n        input          evm_commit,\n        input          "+
"evm_decode,\n        output         evm_busy,\n        output [3:0]   evm_bf"+
"lags,\n        output [3:0]   evm_xflags,\n        output [63:0]  evm_res,\n "+
"       input          rst_a\n        );\n\n",
      }
    ,
    created_using_api:	true,
    allow_verilator:	true,
    publish_in_dot_h:	true,
    apex_template_version:	3,
    type2_alu_present:	true,
    user:	
      {
      extensions:	
        {
        s:	".set apex_eventmanager_present,1\n.extAuxRegister EVT_CTRL,0xf02,r|w\n.extAu"+
"xRegister EVT_FILTER_LO,0xf04,r|w\n.extAuxRegister EVT_FILTER_HI,0xf05,r|w\n"+
".extAuxRegister EVT_CNT_SEL,0xf0a,r|w\n.extAuxRegister EVT_CNT_VAL,0xf0b,r|"+
"w\n.extAuxRegister EVT_VM_SEL,0xf00,r|w\n.extAuxRegister EVT_VM_MAP,0xf01,r|"+
"w\n.extAuxRegister EVT_GRP_SEL,0xf07,r|w\n.extAuxRegister EVT_SID,0xf08,r|w\n"+
".extAuxRegister EVT_SSID,0xf09,r|w\n.extAuxRegister EVT_IRQ,0xf03,r|w\n.extI"+
"nstruction EVTMASKCHK,7,0,SUFFIX_FLAG,SYNTAX_2OP\n.extInstruction EVTMASKAL"+
"L,7,1,SUFFIX_FLAG,SYNTAX_2OP\n.extInstruction EVTMASKANY,7,2,SUFFIX_FLAG,SY"+
"NTAX_2OP\n.extInstruction EVTMASKDECR,7,3,SUFFIX_FLAG,SYNTAX_2OP\n.extInstru"+
"ction EVTMASKINCR,7,4,SUFFIX_FLAG,SYNTAX_2OP\n.extInstruction EVTMASKSEND,7"+
",5,SUFFIX_FLAG,SYNTAX_2OP\n.extInstruction EVTVMCHK,7,6,SUFFIX_FLAG,SYNTAX_"+
"2OP\n",
        c:	"#define APEX_EVENTMANAGER_PRESENT\t1\n\n// User extension aux register EVT_CT"+
"RL\n#define AR_EVT_CTRL 0xf02\n#pragma Aux_register(0xf02, name=>\"EVT_CTRL\")"+
"\n\n// User extension aux register EVT_FILTER_LO\n#define AR_EVT_FILTER_LO 0x"+
"f04\n#pragma Aux_register(0xf04, name=>\"EVT_FILTER_LO\")\n\n// User extension "+
"aux register EVT_FILTER_HI\n#define AR_EVT_FILTER_HI 0xf05\n#pragma Aux_regi"+
"ster(0xf05, name=>\"EVT_FILTER_HI\")\n\n// User extension aux register EVT_CNT"+
"_SEL\n#define AR_EVT_CNT_SEL 0xf0a\n#pragma Aux_register(0xf0a, name=>\"EVT_C"+
"NT_SEL\")\n\n// User extension aux register EVT_CNT_VAL\n#define AR_EVT_CNT_VA"+
"L 0xf0b\n#pragma Aux_register(0xf0b, name=>\"EVT_CNT_VAL\")\n\n// User extensio"+
"n aux register EVT_VM_SEL\n#define AR_EVT_VM_SEL 0xf00\n#pragma Aux_register"+
"(0xf00, name=>\"EVT_VM_SEL\")\n\n// User extension aux register EVT_VM_MAP\n#de"+
"fine AR_EVT_VM_MAP 0xf01\n#pragma Aux_register(0xf01, name=>\"EVT_VM_MAP\")\n\n"+
"// User extension aux register EVT_GRP_SEL\n#define AR_EVT_GRP_SEL 0xf07\n#p"+
"ragma Aux_register(0xf07, name=>\"EVT_GRP_SEL\")\n\n// User extension aux regi"+
"ster EVT_SID\n#define AR_EVT_SID 0xf08\n#pragma Aux_register(0xf08, name=>\"E"+
"VT_SID\")\n\n// User extension aux register EVT_SSID\n#define AR_EVT_SSID 0xf0"+
"9\n#pragma Aux_register(0xf09, name=>\"EVT_SSID\")\n\n// User extension aux reg"+
"ister EVT_IRQ\n#define AR_EVT_IRQ 0xf03\n#pragma Aux_register(0xf03, name=>\""+
"EVT_IRQ\")\n\n// User extension instruction EVTMASKCHK\nextern long long EVTMA"+
"SKCHK(long long);\n#pragma intrinsic(EVTMASKCHK,opcode=>7,sub_opcode=>0,blo"+
"cking_cycles=> 3)\n\n// User extension instruction EVTMASKCHK\nextern long lo"+
"ng EVTMASKCHK_f(long long);\n#pragma intrinsic(EVTMASKCHK_f,opcode=>7,sub_o"+
"pcode=>0, set_flags => 1, flags => \"zncv\",blocking_cycles=> 3)\n\n// User ex"+
"tension instruction EVTMASKALL\nextern long long EVTMASKALL(long long);\n#pr"+
"agma intrinsic(EVTMASKALL,opcode=>7,sub_opcode=>1,blocking_cycles=> 3)\n\n//"+
" User extension instruction EVTMASKALL\nextern long long EVTMASKALL_f(long "+
"long);\n#pragma intrinsic(EVTMASKALL_f,opcode=>7,sub_opcode=>1, set_flags ="+
"> 1, flags => \"zncv\",blocking_cycles=> 3)\n\n// User extension instruction E"+
"VTMASKANY\nextern long long EVTMASKANY(long long);\n#pragma intrinsic(EVTMAS"+
"KANY,opcode=>7,sub_opcode=>2,blocking_cycles=> 3)\n\n// User extension instr"+
"uction EVTMASKANY\nextern long long EVTMASKANY_f(long long);\n#pragma intrin"+
"sic(EVTMASKANY_f,opcode=>7,sub_opcode=>2, set_flags => 1, flags => \"zncv\","+
"blocking_cycles=> 3)\n\n// User extension instruction EVTMASKDECR\nextern lon"+
"g long EVTMASKDECR(long long);\n#pragma intrinsic(EVTMASKDECR,opcode=>7,sub"+
"_opcode=>3,blocking_cycles=> 3)\n\n// User extension instruction EVTMASKDECR"+
"\nextern long long EVTMASKDECR_f(long long);\n#pragma intrinsic(EVTMASKDECR_"+
"f,opcode=>7,sub_opcode=>3, set_flags => 1, flags => \"zncv\",blocking_cycles"+
"=> 3)\n\n// User extension instruction EVTMASKINCR\nextern long long EVTMASKI"+
"NCR(long long);\n#pragma intrinsic(EVTMASKINCR,opcode=>7,sub_opcode=>4,bloc"+
"king_cycles=> 3)\n\n// User extension instruction EVTMASKINCR\nextern long lo"+
"ng EVTMASKINCR_f(long long);\n#pragma intrinsic(EVTMASKINCR_f,opcode=>7,sub"+
"_opcode=>4, set_flags => 1, flags => \"zncv\",blocking_cycles=> 3)\n\n// User "+
"extension instruction EVTMASKSEND\nextern long long EVTMASKSEND(long long);"+
"\n#pragma intrinsic(EVTMASKSEND,opcode=>7,sub_opcode=>5,blocking_cycles=> 3"+
")\n\n// User extension instruction EVTMASKSEND\nextern long long EVTMASKSEND_"+
"f(long long);\n#pragma intrinsic(EVTMASKSEND_f,opcode=>7,sub_opcode=>5, set"+
"_flags => 1, flags => \"zncv\",blocking_cycles=> 3)\n\n// User extension instr"+
"uction EVTVMCHK\nextern long long EVTVMCHK(long long);\n#pragma intrinsic(EV"+
"TVMCHK,opcode=>7,sub_opcode=>6,blocking_cycles=> 3)\n\n// User extension ins"+
"truction EVTVMCHK\nextern long long EVTVMCHK_f(long long);\n#pragma intrinsi"+
"c(EVTVMCHK_f,opcode=>7,sub_opcode=>6, set_flags => 1, flags => \"zncv\",bloc"+
"king_cycles=> 3)\n",
        }
      ,
      }
    ,
    }
  ,
  ]
;

</script>
