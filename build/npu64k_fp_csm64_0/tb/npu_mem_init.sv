/*
 * Copyright (C) 2021-2022 Synopsys, Inc. All rights reserved.
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

`include "tb_defines.sv"

module npu_mem_init(input clk, input rst_a);

`ifdef TB_MSS //{
//intialize MSS memory
function void load_mss_memory();
  `ifdef ALB_MSS_FPGA_INFER_MEMORIES //{
    bit   [31:0] mem_array[bit [31:0]];
    bit   [63:0]    temp_addr;
    bit   [9:0]     bit_offset;
    int num_bytes;
    string        xm_hex;
    temp_addr = 64'h0;
    if ($value$plusargs("XM_HEX=%s", xm_hex))
    begin
        $display("Reading %s into mem_array", xm_hex);
        $readmemh(xm_hex, mem_array);

        num_bytes = 128/8; //bus data with/8
        $display(" --> INFO [TB]: Loading MSS memory");
        foreach(mem_array[i]) // i indicates for address of memory
        begin
            temp_addr = (i/num_bytes)*num_bytes;
            bit_offset = (i % num_bytes)*8;
`ifndef TB_MDB
            `MSS_MEM.mem_r[temp_addr>>4][bit_offset+:32] = mem_array[i];

            //$display("mem_array[0x%x]=0x%x",i, mem_array[i]);            
            //$display("mem[0x%x]=0x%x",i, `MSS_MEM.mem_r[i]);
`endif
        end // foreach(mem_array[i]
        $display("memory initialize completed");

        //$display("mem[0x%x]=0x%x",0, `MSS_MEM.mem_r[0]);
        //$display("mem[0x%x]=0x%x",'h0100_0000, `MSS_MEM.mem_r['h0100_0000]);
        //$display("mem[0x%x]=0x%x",'h00f0_0000, `MSS_MEM.mem_r['h00f0_0000]);
        //$display("mem[0x%x]=0x%x",'h0140_0000, `MSS_MEM.mem_r['h0140_0000]);
        //$display("mem[0x%x]=0x%x",'h0160_0001, `MSS_MEM.mem_r['h0160_0000]);
    end
    else 
    begin
        $display(" -->  [TB]: No XM loading becuase hex file is not specified, please use run option '+XM_HEX=<>'");
    end
  `endif //}
endfunction : load_mss_memory
`endif //}
//Note: this function is not used since all data/code are in MSS memory
//generate
////initialize VM banks
//function void load_vm_memory();
//   `ifndef NPU_VIC2_FIX //{
//    bit   [127:0] mem_array[bit [31:0]];
//    string        vm_hex;
//    string        hex_file_name;
//    if ($value$plusargs("VM_HEX=%s", vm_hex))
//    begin
//        $display(" --> INFO [TB]: Loading VM with 32 banks from hex file(%s)", vm_hex);
//        for(int i=0;i < 32; i++) begin
//            hex_file_name  = $sformatf("%s_%0d.hex",  vm_hex, i); 
//            $display("Reading %s into vm mem_array", hex_file_name);
//            if (i==0)  $readmemh(hex_file_name, `VM_MEM_BANK(0));
//            if (i==1)  $readmemh(hex_file_name, `VM_MEM_BANK(1));
//            if (i==2)  $readmemh(hex_file_name, `VM_MEM_BANK(2));
//            if (i==3)  $readmemh(hex_file_name, `VM_MEM_BANK(3));
//            if (i==4)  $readmemh(hex_file_name, `VM_MEM_BANK(4));
//            if (i==5)  $readmemh(hex_file_name, `VM_MEM_BANK(5));
//            if (i==6)  $readmemh(hex_file_name, `VM_MEM_BANK(6));
//            if (i==7)  $readmemh(hex_file_name, `VM_MEM_BANK(7));
//            if (i==8)  $readmemh(hex_file_name, `VM_MEM_BANK(8));
//            if (i==9)  $readmemh(hex_file_name, `VM_MEM_BANK(9));
//            if (i==10) $readmemh(hex_file_name, `VM_MEM_BANK(10));
//            if (i==11) $readmemh(hex_file_name, `VM_MEM_BANK(11));
//            if (i==12) $readmemh(hex_file_name, `VM_MEM_BANK(12));
//            if (i==13) $readmemh(hex_file_name, `VM_MEM_BANK(13));
//            if (i==14) $readmemh(hex_file_name, `VM_MEM_BANK(14));
//            if (i==15) $readmemh(hex_file_name, `VM_MEM_BANK(15));
//            //if (i==16) $readmemh(hex_file_name, `VM_MEM_BANK(16));
//            //if (i==17) $readmemh(hex_file_name, `VM_MEM_BANK(17));
//            //if (i==18) $readmemh(hex_file_name, `VM_MEM_BANK(18));
//            //if (i==19) $readmemh(hex_file_name, `VM_MEM_BANK(19));
//            //if (i==20) $readmemh(hex_file_name, `VM_MEM_BANK(20));
//            //if (i==21) $readmemh(hex_file_name, `VM_MEM_BANK(21));
//            //if (i==22) $readmemh(hex_file_name, `VM_MEM_BANK(22));
//            //if (i==23) $readmemh(hex_file_name, `VM_MEM_BANK(23));
//            //if (i==24) $readmemh(hex_file_name, `VM_MEM_BANK(24));
//            //if (i==25) $readmemh(hex_file_name, `VM_MEM_BANK(25));
//            //if (i==26) $readmemh(hex_file_name, `VM_MEM_BANK(26));
//            //if (i==27) $readmemh(hex_file_name, `VM_MEM_BANK(27));
//            //if (i==28) $readmemh(hex_file_name, `VM_MEM_BANK(28));
//            //if (i==29) $readmemh(hex_file_name, `VM_MEM_BANK(29));
//            //if (i==30) $readmemh(hex_file_name, `VM_MEM_BANK(30));
//            //if (i==31) $readmemh(hex_file_name, `VM_MEM_BANK(31));
//        end
//        $display("vm_bnk0(0x%x)=0x%x",'h00, `VM_MEM_BANK(0)['h00]);
//        $display("vm_bnk0(0x%x)=0x%x",'h100, `VM_MEM_BANK(0)['h100]);
//    end
//    else begin
//        $display(" --> INFO [TB]: No VM loading becuase hex file is not specified, use run option '+VM_HEX=<>' if needed");
//    end
//   `endif //}
//endfunction : load_vm_memory
//endgenerate

//memory initialization
initial 
begin
    @(negedge clk);
    load_mss_memory();
    //load_vm_memory();
end


endmodule: npu_mem_init
