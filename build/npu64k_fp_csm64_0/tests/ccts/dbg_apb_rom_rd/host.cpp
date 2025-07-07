#include "npu_config.hpp"
#include "host_utils.hpp"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_LINE_LENGTH 256

#ifdef __cplusplus
extern "C" {
#endif

HOST_EXEC() {
  int err_cnt = 0; 
  int host_err_cnt = 0; 
  int addr    = 0;
  int rd_data;
  int auth_data;
  // arcsync_core_rst_assert_all();
  //  TODO :  The following code Needs to be more modular 
  // ========================================================
  //  APB Slaves Data
  // ========================================================
  int total_apb_slaves = 0;           
  int     expected_value;
  // ========================================================
 

  set_expect_resp(0);
  arcsync_core_rst_dessert_all(0/*cluster id*/);
  set_intvect(0/*cluster_id*/);  
  config_npx_sys_map_all();
  if(ARCSYNC_HAS_PMU) {
    config_pmu_count(0/*cluster id*/);
  }

  // TOP ROM TABLE Entry
 for (int j =0; j <100; j++) {
  host_apb_read_int(j,0);
  rd_data = get_retd_apb();
  rd_data = rd_data & 0x0003;
  if (rd_data ==3) {
      total_apb_slaves++;
    }
    else break;
  }

 int addr_table[total_apb_slaves+1];
 int devarch[total_apb_slaves];
 int devid[total_apb_slaves][3];
 int devtype[total_apb_slaves];
 int pidr[total_apb_slaves][8];
 int cidr[total_apb_slaves][4];
 int csr[total_apb_slaves][5];

if (NPU_HAS_POWERDOMAINS == 1) {
 slc_power_down_all(0/*cluster_id*/);
 l1grp_power_down_all(0/*cluster_id*/);
 if (NPU_HAS_L2ARC) {
  l2grp_power_down_all(0/*cluster_id*/);
 }
 
 host_wait(1000);


  // Slices  & L1 & L2 in power down mode 
  // Write to Core registes through debug command and read them - should get data from all cores 
  // Unless debug is disabled using DBGEN IO port 
  for (int j = 2; j <= total_apb_slaves;j++) {
    host_apb_db_write((j << 10),0x7,1,j*10,1);
    host_apb_db_read((j << 10),0x7,5,1);
    rd_data = get_retd_apb();
  }

  // Write and Read Trace registers
  host_apb_db_write((1 << 10),0x10077,2,0x18,1); // SWE Registers
  host_apb_db_read((1 << 10),0x10077,6,1);
  rd_data = get_retd_apb();

 //// Slices & L1 &L2 in power down mode 
 //// Read Rom Table contents
 for (int j =0; j <=total_apb_slaves; j++) {
    addr = (j << 10);
    for (int i =0; i <3; i++) {
      if (j == 0) {
        host_apb_read_int(addr+0x3F0+i,0);
      }
      else {
        host_apb_read_int(addr+0x3F0+i,1);
      }
      rd_data = get_retd_apb();
      devid[j][2-i] = 0;
      if ( i == 1 && j > 1) 
        devid[j][2-i] = 8;
      if(NPU_HAS_L2ARC) if ( i == 2 && j == 2)
        devid[j][2-i] = 0x54;
      if(DUO_L2ARC) if ( i == 2 && j == 3)
        devid[j][2-i] = 0x54 | (((total_apb_slaves -3) +1) << 8) ;
      if ( i == 2 && j > (1+NPU_HAS_L2ARC+DUO_L2ARC)) 
        devid[j][2-i] = 0x54 | ((j-(1+NPU_HAS_L2ARC+DUO_L2ARC)) << 8);
      if (j==0 and rd_data != devid[j][2-i]) { //only check ROM TOP
        err_cnt++;
        printf(" Error: DEVID%d ADDR[%x] RTL %x EXP %x \n",i,addr+0x3F0+i,rd_data,devid[j][2-i]);
      }
    }
  }
 
 
if (NPU_HAS_L2ARC) {
  l2grp_power_up_all(0/*cluster_id*/);
}
 l1grp_power_up_all(0/*cluster_id*/);
 slc_power_up_all(0/*cluster_id*/);

} 

 config_npx_sys_map_all();
 if (NPU_HAS_L2ARC == 1) {
   core_run_all(0/*cluster_id*/);
 } else {
   core_run(0/*cluster_id*/,1);
 }

  // ========================================================
  //  ROM TABLE Comparision
  // ========================================================
  // TOP ROM TABLE Entry
  for (int j =0; j <total_apb_slaves+1; j++) {
    addr_table[j]  = 0;
    if ( j < total_apb_slaves) {
      addr_table[j] = addr_table[j] | 0x03;        // Setting 0th bit (Preset) and Setting 1st Bit (32 Bit)
      addr_table[j] = addr_table[j] | ((j+1) << 12); // Setting Offset
    }
    host_apb_read_int(j,0);
    rd_data = get_retd_apb();
    if (rd_data != addr_table[j]) {
      err_cnt++;
      printf(" Error: TOP TABLE ROM ENTRY ADDR[%x] RTL %x EXP %x \n",j,rd_data,addr_table[j]);
    }
  }

  // IDR 
  for (int j =0; j <=total_apb_slaves; j++) {
    addr = (j << 10);
    for (int i =0; i <1; i++) {
      host_apb_read_int(addr+0x37F+i,0);
      rd_data = get_retd_apb();
      if (rd_data != 0) {
        err_cnt++;
        printf(" Error: IDR ADDR[%x] RTL %x EXP %x \n",addr+0x37F+i,rd_data,0);
      }
    }
  }

  // ITCTRL
  for (int j =0; j <=total_apb_slaves; j++) {
    addr = (j << 10);
    for (int i =0; i <1; i++) {
      host_apb_read_int(addr+0x3C0+i,0);
      rd_data = get_retd_apb();
      if (rd_data != 0) {
        err_cnt++;
        printf(" Error: ITCTRL ADDR[%x] RTL %x EXP %x \n",addr+0x3C0+i,rd_data,0);
      }
    }
  }

  // CLAIM SET
  for (int j =0; j <=total_apb_slaves; j++) {
    addr = (j << 10);
    for (int i =0; i <2; i++) {
    host_apb_read_int(addr+0x3E8+i,0);
      rd_data = get_retd_apb();
      if (i == 0 && j == 0) expected_value = 0;
      else if (i == 1) expected_value = 0;
      else expected_value = 15;
      if (rd_data != expected_value) {
        err_cnt++;
        printf(" Error: CLAIM SET/CLR ADDR[%x] RTL %x EXP %x \n",addr+0x3E8+i,rd_data,expected_value);
      }
    }
  }

  // DEVAFF 
  for (int j =0; j <=total_apb_slaves; j++) {
    addr = (j << 10);
    for (int i =0; i <2; i++) {
      host_apb_read_int(addr+0x3EA+i,0);
      rd_data = get_retd_apb();
      if (rd_data != 0) {
        err_cnt++;
        printf(" Error: DEVAFF0/1 ADDR[%x] RTL %x EXP %x \n",addr+0x3EA+i,rd_data,0);
      }
    }
  }

  //LOCK AND STATUS 
  for (int j =0; j <=total_apb_slaves; j++) {
    addr = (j << 10);
    for (int i =0; i <2; i++) {
      host_apb_read_int(addr+0x3EC+i,0);
      rd_data = get_retd_apb();
      if (rd_data != 0) {
        err_cnt++;
        printf(" Error: LAR/LSR ADDR[%x] RTL %x EXP %x \n",addr+0x3EC+i,rd_data,0);
      }
    }
  }

  // AUTHSTATUS
  for (int j =0; j <=total_apb_slaves; j++) {
    addr = (j << 10);
    for (int i =2; i <3; i++) {
      host_apb_read_int(addr+0x3EC+i,0);
      rd_data = get_retd_apb();
      if(j == 1) auth_data = (NPU_ARC_TRACE > 0) ? 0xf : get_dbgen_niden_val(j) ;
      else auth_data = get_dbgen_niden_val(j);
      if (rd_data != auth_data) {
        err_cnt++;
        printf(" Error: AUTHSTATUS ADDR[%x] RTL %x EXP %x \n",addr+0x3EC+i,rd_data,auth_data);
      }
    }
  }

  // DEVARCH 
  for (int j =0; j <=total_apb_slaves; j++) {
    if (j == 1)      devarch[j] = (NPU_ARC_TRACE > 0) ?  0x4B100201 : 0x4B100101;
    else if (j > 1 ) devarch[j] = 0x4B100101;
    else             devarch[j] = 0x0;
    addr = (j << 10);
    for (int i =0; i <1; i++) {
      host_apb_read_int(addr+0x3EF+i,0);
      rd_data = get_retd_apb();
      if (rd_data != devarch[j]) {
        err_cnt++;
        printf(" Error: DEVARCH ADDR[%x] RTL %x EXP %x \n",addr+0x3EF+i,rd_data,devarch[j]);
      }
    }
  }

  // DEVID
  //cout << "ZY: total_apb_slaves = " << total_apb_slaves << endl;
 for (int j =0; j <=total_apb_slaves; j++) {
    addr = (j << 10);
    for (int i =0; i <3; i++) {
      host_apb_read_int(addr+0x3F0+i,0);
      rd_data = get_retd_apb();
      devid[j][2-i] = 0;
      if ( i == 1 && j > (NPU_ARC_TRACE > 0)) 
        devid[j][2-i] = 8;
      if(NPU_HAS_L2ARC) if ( i == 2 && j == (2 - (NPU_ARC_TRACE == 0))) 
        devid[j][2-i] = 0x54;
      if(DUO_L2ARC) if ( i == 2 && j == 3)
        devid[j][2-i] = 0x54 | (((total_apb_slaves -3) +1) << 8) ;
      if ( i == 2 && j > ((NPU_ARC_TRACE > 0)+NPU_HAS_L2ARC+DUO_L2ARC)) //l1arc
        devid[j][2-i] = 0x54 | ((j-((NPU_ARC_TRACE > 0)+NPU_HAS_L2ARC+DUO_L2ARC)) << 8);
      
      if (rd_data != devid[j][2-i]) {
        err_cnt++;
        printf(" Error: DEVID%d ADDR[%x] RTL %x EXP %x \n",i,addr+0x3F0+i,rd_data,devid[j][2-i]);
      }
    }
  }

  // DEVTYPE
  for (int j =0; j <=total_apb_slaves; j++) {
    addr = (j << 10);
    if ( j == 1)      devtype[j] = (NPU_ARC_TRACE > 0) ?  0x35 : 0x15;
    else if ( j >  1) devtype[j] = 0x15;
    else              devtype[j] = 0x0;
    for (int i =0; i <1; i++) {
      host_apb_read_int(addr+0x3F3+i,0);
      rd_data = get_retd_apb();
      if (rd_data != devtype[j]) {
        err_cnt++;
        printf(" Error: DEVTYPE%d ADDR[%x] RTL %x EXP %x \n",i,addr+0x3F3+i,rd_data,devtype[j]);
      }
    }
  }

  // PIDR4-7
  for (int j =0; j <=total_apb_slaves; j++) {
    addr = (j << 10);
    for (int i =0; i <4; i++) {
      if (i == 0) pidr[j][4+i] = 4;
      else        pidr[j][4+i] = 0;
      host_apb_read_int(addr+0x3F4+i,0);
      rd_data = get_retd_apb();
      if (rd_data != pidr[j][4+i]) {
        err_cnt++;
        printf(" Error: PIDR%d ADDR[%x] RTL %x EXP %x \n",i+4,addr+0x3F4+i,rd_data,pidr[j][4+i]);
      }
    }
  }

  // PIDR0-3
  for (int j =0; j <=total_apb_slaves; j++) {
    addr = (j << 10);
    for (int i =0; i <4; i++) {
      if (i == 0) pidr[j][i] = 1;
      else if (i == 1) pidr[j][i] = 0x80;
      else if (i == 2) pidr[j][i] = 0x0D;
      else             pidr[j][i] = 0x00;    
      host_apb_read_int(addr+0x3F8+i,0);
      rd_data = get_retd_apb();
      if (rd_data != pidr[j][i]) {
        err_cnt++;
        printf(" Error: PIDR%d ADDR[%x] RTL %x EXP %x \n",i,addr+0x3F8+i,rd_data,pidr[j][i]);
      }
    }
  }

  // CIDR0-3
  for (int j =0; j <=total_apb_slaves; j++) {
    addr = (j << 10);
    for (int i =0; i <4; i++) {
      if (i == 0) cidr[j][i] = 0xD;
      else if (i == 1 && j == 0) cidr[j][i] = 0x10;
      else if (i == 1 && j >  0) cidr[j][i] = 0x90;
      else if (i == 3) cidr[j][i] = 0xB1;
      else if (i == 2) cidr[j][i] = 0x05;
      host_apb_read_int(addr+0x3FC+i,0);
      rd_data = get_retd_apb();
      if (rd_data != cidr[j][i]) {
        err_cnt++;
        printf(" Error: CIDR%d ADDR[%x] RTL %x EXP %x \n",i,addr+0x3FC+i,rd_data,cidr[j][i]);
      }
    }
  }

  //CSR
  for (int j =0; j <=total_apb_slaves; j++) {
    addr = (j << 10);
    for (int i =0; i <5; i++) {
      if      (i == 0 && j == 0) csr[j][i] = 0x10;
      else if (i == 0 && j >  0) csr[j][i] = 0x90;
      else if (i == 1 && j == 0) csr[j][i] = 0x24b00005;
      else if (i == 1 && j == 1) csr[j][i] = (NPU_ARC_TRACE > 0) ?  0x84b00002 : 0x4b00001;
      else if (i == 1 && j >  1) csr[j][i] = 0x4b00001;
      else                       csr[j][i] = 0x0;
      host_apb_read_int(addr+0x100+i,0);
      rd_data = get_retd_apb();
      if (rd_data != csr[j][i]) {
        err_cnt++;
        printf(" Error: CSR%d ADDR[%x] RTL %x EXP %x \n",i,addr+0x100+i,rd_data,csr[j][i]);
      }
    }
  } 

  // Write to ROM to check slave error
  host_apb_write_int(0x0,3,1);

  // Forcing async apb clk
  set_apb_clk(1,0);
  start_async_apb_clk();
  host_wait(50);

   if (NPU_HAS_L2ARC == 1) {
     core_halt_all(0/*cluster_id*/);
   } else {
     core_halt(0/*cluster_id*/,1);
   }

  for (int i = 2; i <= 5; i++) {
    set_apb_clk(i,1);
    host_wait(50);
    // Write to Core registes through debug command and read them - should get data from all cores 
    // Unless debug is disabled using DBGEN IO port 
    for (int j = 1+NPU_ARC_TRACE; j <= total_apb_slaves;j++) {
      host_apb_db_write((j << 10),5,1,j*8,0);
      host_apb_db_read((j << 10),5,5,0);
      rd_data = get_retd_apb();

      auth_data = get_dbgen_niden_val(j);
      auth_data = auth_data & 0x3;
      if ((j*8) != rd_data && (auth_data == 3)) {
        printf(" Warning: Reading Writing Core Registers With APB Clock Divided by %x times  - Offset %x : Wr Value %x Rd Value %x From R%0d \n",i,j,j*8,rd_data,5);
        //    err_cnt++;
      }
      if (rd_data != 0 && (auth_data == 2)) {
        printf(" Error: Reading Writing Core Registers With APB Clock Divided by %x times - Offset %x - With Debug Access Disable : Wr Value %x Rd Value %x From R%0d \n",i,j,j*8,rd_data,5);
        err_cnt++;
      }
 //       addr = (j << 10);
 //       auth_data = get_dbgen_niden_val(j);
 //       auth_data = auth_data & 0x3;
 //       if(j == 1)
 //         {auth_data = 3;} ;
 //       host_apb_write_int(addr+0x3E8,0xF,0);
 //       host_apb_write_int(addr+0x3E9,0xF,0);

 //       host_apb_write_int(addr+0x3E8,0xE,0);
 //       host_apb_write_int(addr+0x3E9,0x2,0);
 //       host_apb_read_int(addr+0x3E9,0);
 //       rd_data = get_retd_apb();
 //       if(rd_data != 0xC && (auth_data == 3)){
 //         printf(" Error: Reading Writing  CLAIMTAG Registers With APB Clock Divided by %x times - Offset %x :  Rd Value %x From R%0d, expect 0xC \n",i,j,rd_data,5);
 //         err_cnt++;         };
 //       if (rd_data != 0 && (auth_data == 2)) {
 //         printf(" Error: Reading Writing CLAIMTAG Registers With APB Clock Divided by %x times - Offset %x - With Debug Access Disable  \n",i,j);
 //         err_cnt++;
 //       }   ;

    }

    // Write and Read Trace registers
    if(NPU_ARC_TRACE > 0) { 
       host_apb_db_write((1 << 10),0x0040,2,0xDEAD,0); // SWE Registers
       host_apb_db_read((1 << 10),0x0040,6,0);
       rd_data = get_retd_apb();
       if (rd_data != 0xDEAD) {
         printf(" Error: Async Clock Reading Writing Trace Register With APB Clock Divided by %x times - Offset %x : Wr Value %x Rd Value %x From %x \n",i,1,0xDEAD,rd_data,0x0040);
         err_cnt++;
       }
    }
  
 

    host_wait(50);

  }
 
   if (NPU_HAS_L2ARC == 1) {
     core_run_all(0/*cluster_id*/);
   } else {
     core_run(0/*cluster_id*/,1);
   }

  host_err_cnt = get_host_err();
  if (err_cnt || host_err_cnt) printf("Host run with errors - %x %x \n",err_cnt,host_err_cnt);
  host_exit(err_cnt + host_err_cnt);
  if (NPU_HAS_L2ARC == 1) {
    force_test_ok();
  }

  HOST_EXEC_RET;
}

#ifdef __cplusplus
}
#endif

