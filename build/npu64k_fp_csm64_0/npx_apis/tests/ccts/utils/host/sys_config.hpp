#ifndef SYS_CONFIG_UTILS
#define SYS_CONFIG_UTILS

#include "npu_defines.hpp"
#include "mem_map_defines.hpp"
#include "npu_config.hpp"
#include "host_loapi.hpp"

// config aperture_<number> for specific config port
void config_aperture(int& apidx, long long & baddr, const long long& base, const long long& size, int mst){
  int b = base >> 12; // All address are 4KB aligned, drop 12 LSB
  int s = ~(size -1) >> 12; // Turn the aperture size into a bitmask, cutting the 12 LSB
  long long bap = baddr + apidx * 4;
#ifdef HOST_CFG_DMI_LOG
  cout <<hex<< "    config aperture: apidx "<<apidx<<" @ 0x"<<bap<<" (base=0x"<<base<<", size=0x"<<size<<", mst=0x"<<mst<<")\n";
#endif
  cfg_dmi_write((long long *)(bap + 0x000), b);
  cfg_dmi_read ((long long *)(bap + 0x000));
  cfg_dmi_write((long long *)(bap + 0x080), s);
  cfg_dmi_write((long long *)(bap + 0x100), mst);
  apidx++;
}

// config apertures for L2-CSM
void cfg_csm_apertures(int& apidx, long long & baddr, const long long& base, const long long& size, int mst/*start idx*/){
  int b;
  int s = ~(size -1) >> 12;
  s = s | ((NPU_NUM_GRP-1) << (15-12));
  for(int g=0; g<NPU_NUM_GRP;g++) {
    long long bap = baddr + apidx * 4;
#ifdef HOST_CFG_DMI_LOG
    cout <<hex<< "    config aperture CSM"<<g<<" : apidx 0x"<<apidx<<" @ 0x"<<bap<<" (base=0x"<<base<<", size=0x"<<size<<", mst=0x"<<mst<<")\n";
#endif
    b = (base | (g << 15)) >> 12;
    cfg_dmi_write((long long *)(baddr + 0x000 + apidx * 4), b);
    cfg_dmi_write((long long *)(baddr + 0x080 + apidx * 4), s);
    cfg_dmi_write((long long *)(baddr + 0x100 + apidx * 4), mst+g);
    apidx++;
  }
}

// config aperture_<number> for specific config port
// the size mask is directly provided
void cfg_apert_direct(int& apidx, long long & baddr, const long long& base, const long long& size_msk, int mst){
  int b = base >> 12;
  int s = size_msk >> 12;
  long long bap = baddr + apidx * 4;
#ifdef HOST_CFG_DMI_LOG
  cout <<hex<< "    config aperture direct: apidx 0x"<<apidx<<" @ 0x"<<bap<<" (base=0x"<<base<<", size_msk=0x"<<size_msk<<", mst=0x"<<mst<<")\n";
#endif
  cfg_dmi_write((long long *)(bap + 0x000), b);
  cfg_dmi_write((long long *)(bap + 0x080), s);
  cfg_dmi_write((long long *)(bap + 0x100), mst);
  apidx++;
}

// config remap_aperture_<number> for specific config port
void cfg_reamp_aperture(int& apidx, long long & baddr, const long long& base1, const long long& size1, const long long& base2, const long long& size2, const int lsb=40){
  int b1 = base1 >> 12;
  int s1 = ~(size1 -1) >> 12;
  s1 = s1 & ((1LL<<(40-12))-1); //only care LSB bits
  long long bap1 = baddr + apidx * 4;
#ifdef HOST_CFG_DMI_LOG
  cout <<hex<< "    config remap1: apidx 0x"<<apidx<<" @ 0x"<<bap1<<" (base1=0x"<<base1<<", size1=0x"<<size1<<")\n";
#endif
  cfg_dmi_write((long long *)(bap1 + 0x000), b1);
  cfg_dmi_write((long long *)(bap1 + 0x080), s1);
  apidx++;

  int b2 = base2 >> 12;
  int s2 = ~(size2-1) >> 12;
  s2 = s2 & ((1LL<<(lsb-12))-1); //only care LSB bits
  long long bap2 = baddr + apidx * 4;
#ifdef HOST_CFG_DMI_LOG
  cout <<hex<< "    config remap2: apidx 0x"<<apidx<<" @ 0x"<<bap2<<" (base2=0x"<<base2<<", size2=0x"<<size2<<")\n";
#endif
  cfg_dmi_write((long long *)(bap2 + 0x000), b2);
  cfg_dmi_write((long long *)(bap2 + 0x080), s2);
  apidx++;
}

// config remap_aperture_<number> for specific config port
void cfg_csmreamp_aperture(int& apidx, long long & baddr, int vg=4 /*groups per virtual machine*/){
  int drop;
  switch(vg) {
    case 1 : drop = 0; break;
    case 2 : drop = 1; break;
    case 4 : drop = 2; break;
    case 8 : drop = 3; break;
  }
  long long bap = baddr + apidx * 4;
#ifdef HOST_CFG_DMI_LOG
  cout <<hex<< "    config csmremap: apidx 0x"<<apidx<<" @ 0x"<<bap<<" drop 0x" <<drop<<endl;
#endif
  cfg_dmi_write((long long *)(bap + 0x000), drop);
  apidx=apidx+2;
}

// Configure a L1 npu_group interconnect (CLN)
void config_cln_grp(int g){
  long long cfg_dmi_base=0xf0000000;
  long long baddr;
  long long saddr;
  int apidx;
  int porid;
  long long csm_addr;

    /* cln1p0_config */
    apidx=0;
    porid=0;
    baddr = cfg_dmi_base + g * 0x20000;

    /* config top matrix */
    apidx=0;
    porid=0;
    baddr = cfg_dmi_base + g * 0x20000 + 0x1000;
    csm_addr=0;
    if(g==0){
      //slice peripheral
        config_aperture(apidx, baddr, 0xe0000000, 0x01000000, 1); // aperture e000_0000 - e0ff_ffff (grp 0)
        config_aperture(apidx, baddr, 0xe1000000, 0x01000000, 2); // aperture e100_0000 - e1ff_ffff (grp 1)
        config_aperture(apidx, baddr, 0xe2000000, 0x01000000, 3); // aperture e200_0000 - e2ff_ffff (grp 2)
        config_aperture(apidx, baddr, 0xe3000000, 0x01000000, 4); // aperture e300_0000 - e3ff_ffff (grp 3)
      //STU
        config_aperture(apidx, baddr, 0xe6080000, 0x00002000, 1); // aperture e608_0000 - e608_1fff (grp 0 - stu0-1)
        config_aperture(apidx, baddr, 0xe6082000, 0x00002000, 2); // aperture e608_2000 - e608_3fff (grp 1 - stu2-3)
        config_aperture(apidx, baddr, 0xe6084000, 0x00002000, 3); // aperture e608_4000 - e608_5fff (grp 2 - stu4-5)
        config_aperture(apidx, baddr, 0xe6086000, 0x00002000, 4); // aperture e608_6000 - e608_7fff (grp 3 - stu6-7)
      //CSM
        csm_addr = LC_CSM_BASE;
        cfg_apert_direct(apidx, baddr, csm_addr, 0xfc018000, 1);
        csm_addr = LC_CSM_BASE + 0x8000;
        cfg_apert_direct(apidx, baddr, csm_addr, 0xfc018000, 2);
        csm_addr = LC_CSM_BASE + 0x10000;
        cfg_apert_direct(apidx, baddr, csm_addr, 0xfc018000, 3);
        csm_addr = LC_CSM_BASE + 0x18000;
        cfg_apert_direct(apidx, baddr, csm_addr, 0xfc018000, 4);
      //DCCM
        config_aperture(apidx, baddr, 0xe6000000, 0x00080000, 1); // aperture e600_0000 - e607_ffff -> (L2-DM)

        apidx = 14;
        config_aperture(apidx, baddr, 0x0, 0x0, 0); // others routes to  port 0, allocate to last AP to have broadcast ability
    }
    if(g==1){
      //slice peripheral
        config_aperture(apidx, baddr, 0xe0000000, 0x01000000, 2); // aperture e000_0000 - e0ff_ffff (grp 0)
        config_aperture(apidx, baddr, 0xe1000000, 0x01000000, 1); // aperture e100_0000 - e1ff_ffff (grp 1)
        config_aperture(apidx, baddr, 0xe2000000, 0x01000000, 4); // aperture e200_0000 - e2ff_ffff (grp 2)
        config_aperture(apidx, baddr, 0xe3000000, 0x01000000, 3); // aperture e300_0000 - e3ff_ffff (grp 3)
      //STU
        config_aperture(apidx, baddr, 0xe6080000, 0x00002000, 2); // aperture e608_0000 - e608_1fff (grp 0 - stu0-1)
        config_aperture(apidx, baddr, 0xe6082000, 0x00002000, 1); // aperture e608_2000 - e608_3fff (grp 1 - stu2-3)
        config_aperture(apidx, baddr, 0xe6084000, 0x00002000, 4); // aperture e608_4000 - e608_5fff (grp 2 - stu4-5)
        config_aperture(apidx, baddr, 0xe6086000, 0x00002000, 3); // aperture e608_6000 - e608_7fff (grp 3 - stu6-7)
      //CSM
        csm_addr = LC_CSM_BASE;
        cfg_apert_direct(apidx, baddr, csm_addr, 0xfc018000, 2);
        csm_addr = LC_CSM_BASE + 0x8000;
        cfg_apert_direct(apidx, baddr, csm_addr, 0xfc018000, 1);
        csm_addr = LC_CSM_BASE + 0x10000;
        cfg_apert_direct(apidx, baddr, csm_addr, 0xfc018000, 4);
        csm_addr = LC_CSM_BASE + 0x18000;
        cfg_apert_direct(apidx, baddr, csm_addr, 0xfc018000, 3);
      //DCCM
        config_aperture(apidx, baddr, 0xe6000000, 0x00080000, 1); // aperture e600_0000 - e607_ffff -> (L2-DM)

      apidx = 14;
      config_aperture(apidx, baddr, 0x0, 0x0, 0); // others routes to  port 0
    }
    if(g==2){
      //slice peripheral
        config_aperture(apidx, baddr, 0xe0000000, 0x01000000, 3); // aperture e000_0000 - e0ff_ffff (grp 0)
        config_aperture(apidx, baddr, 0xe1000000, 0x01000000, 4); // aperture e100_0000 - e1ff_ffff (grp 1)
        config_aperture(apidx, baddr, 0xe2000000, 0x01000000, 1); // aperture e200_0000 - e2ff_ffff (grp 2)
        config_aperture(apidx, baddr, 0xe3000000, 0x01000000, 2); // aperture e300_0000 - e3ff_ffff (grp 3)
      //STU
        config_aperture(apidx, baddr, 0xe6080000, 0x00002000, 3); // aperture e608_0000 - e608_1fff (grp 0 - stu0-1)
        config_aperture(apidx, baddr, 0xe6082000, 0x00002000, 4); // aperture e608_2000 - e608_3fff (grp 1 - stu2-3)
        config_aperture(apidx, baddr, 0xe6084000, 0x00002000, 1); // aperture e608_4000 - e608_5fff (grp 2 - stu4-5)
        config_aperture(apidx, baddr, 0xe6086000, 0x00002000, 2); // aperture e608_6000 - e608_7fff (grp 3 - stu6-7)
      //CSM
        csm_addr = LC_CSM_BASE;
        cfg_apert_direct(apidx, baddr, csm_addr, 0xfc018000, 3);
        csm_addr = LC_CSM_BASE + 0x8000;
        cfg_apert_direct(apidx, baddr, csm_addr, 0xfc018000, 4);
        csm_addr = LC_CSM_BASE + 0x10000;
        cfg_apert_direct(apidx, baddr, csm_addr, 0xfc018000, 1);
        csm_addr = LC_CSM_BASE + 0x18000;
        cfg_apert_direct(apidx, baddr, csm_addr, 0xfc018000, 2);
      //DCCM
        config_aperture(apidx, baddr, 0xe6000000, 0x00080000, 1); // aperture e600_0000 - e607_ffff -> (L2-DM)

      apidx = 14;
      config_aperture(apidx, baddr, 0x0, 0x0, 0); // others routes to  port 0
    }
    if(g==3){
      //slice peripheral
        config_aperture(apidx, baddr, 0xe0000000, 0x01000000, 4); // aperture e000_0000 - e0ff_ffff (grp 0)
        config_aperture(apidx, baddr, 0xe1000000, 0x01000000, 3); // aperture e100_0000 - e1ff_ffff (grp 1)
        config_aperture(apidx, baddr, 0xe2000000, 0x01000000, 2); // aperture e200_0000 - e2ff_ffff (grp 2)
        config_aperture(apidx, baddr, 0xe3000000, 0x01000000, 1); // aperture e300_0000 - e3ff_ffff (grp 3)
      //STU
        config_aperture(apidx, baddr, 0xe6080000, 0x00002000, 4); // aperture e608_0000 - e608_1fff (grp 0 - stu0-1)
        config_aperture(apidx, baddr, 0xe6082000, 0x00002000, 3); // aperture e608_2000 - e608_3fff (grp 1 - stu2-3)
        config_aperture(apidx, baddr, 0xe6084000, 0x00002000, 2); // aperture e608_4000 - e608_5fff (grp 2 - stu4-5)
        config_aperture(apidx, baddr, 0xe6086000, 0x00002000, 1); // aperture e608_6000 - e608_7fff (grp 3 - stu6-7)
      //CSM
        csm_addr = LC_CSM_BASE;
        cfg_apert_direct(apidx, baddr, csm_addr, 0xfc018000, 4);
        csm_addr = LC_CSM_BASE + 0x8000;
        cfg_apert_direct(apidx, baddr, csm_addr, 0xfc018000, 3);
        csm_addr = LC_CSM_BASE + 0x10000;
        cfg_apert_direct(apidx, baddr, csm_addr, 0xfc018000, 2);
        csm_addr = LC_CSM_BASE + 0x18000;
        cfg_apert_direct(apidx, baddr, csm_addr, 0xfc018000, 1);
      //DCCM
        config_aperture(apidx, baddr, 0xe6000000, 0x00080000, 1); // aperture e600_0000 - e607_ffff -> (L2-DM)

      apidx = 14;
      config_aperture(apidx, baddr, 0x0, 0x0, 0); // others routes to  port 0
    }

    /* config bottom matrix */
    apidx=1;
    baddr = cfg_dmi_base + g * 0x20000 + 0x2000;

    //if(NPU_CSM_SIZE == 0xc00000){
    //  //illegal case, do not map 12MB-16MB to any port
    //  cfg_apert_direct(apidx, baddr, 0xe8c00000, 0xfcc00000, 0x20); // exclude from aperture e800_0000 - ebff_ffff
    //}
    //CSM(port 0 to NPU_CSM_BANKS_PER_GRP)
    for (int m=0; m<NPU_CSM_BANKS_PER_GRP; m++) {
      //cfg_apert_direct(apidx, baddr, 0xe8000000+0x1000*m, 0xfc007000, m); // aperture e800_0000 - ebff_ffff ([14:12] for csm bank addressing)
      cfg_apert_direct(apidx, baddr, LC_CSM_BASE+0x1000*m, 0xfc007000, m);
    }
    //(port NPU_CSM_BANKS_PER_GRP)
    config_aperture(apidx, baddr, 0xe0000000+g*0x01000000, 0x01000000, NPU_CSM_BANKS_PER_GRP); // aperture e000_0000 - e0ff_ffff -> (slice peripheral)
    config_aperture(apidx, baddr, 0xe6000000, 0x00080000, NPU_CSM_BANKS_PER_GRP); // aperture e600_0000 - e607_ffff -> (L2-DM)
    config_aperture(apidx, baddr, 0xe6080000+g*0x00002000, 0x00002000, NPU_CSM_BANKS_PER_GRP); // aperture e608_0000 - e608_1fff -> (STU MMIO)
    //NOC(port NPU_CSM_BANKS_PER_GRP)
    //config_aperture(apidx, baddr, 0, 0, NPU_CSM_BANKS_PER_GRP);                   // the reste map to NoC

    /* config cln1p0_remap CSM remap*/
    /* config slice safety control */
    /* config ccm_demux */
    apidx=0;
    baddr = cfg_dmi_base + g * 0x20000 + 0x10000;
    porid=0;
    //SLICE
    for(int k=0; k<NPU_NUM_SLC_PER_GRP; k++){
      saddr = 0xe0000000 + k * 0x400000;
      config_aperture(apidx, baddr, saddr+g*0x01000000, 0x00400000, porid);
      porid++;
    }
    //STU
    for(int k=0; k<NPU_NUM_STU_PER_GRP; k++){
      saddr = 0xe6080000 + k * 0x1000;
      config_aperture(apidx, baddr, saddr+g*0x00002000, 0x00001000, porid);
      porid++;
    }
    //L2-DM
    config_aperture(apidx, baddr, 0xe6000000, 0x00080000, porid); // aperture e600_0000 - e607_ffff -> port 0(L2-DM)

}

/* config L2 group */
void config_l2_grp(){
  long long cfg_dmi_base=0xf0000000;
  long long baddr;
  int apidx;
  /* config axi matrix */
  apidx=0;
  baddr = cfg_dmi_base + 4 * 0x20000 + 0x0000;
  // l2 DM
  config_aperture(apidx, baddr, 0xe6000000, 0x00080000, NPU_NUM_GRP); // aperture e600_0000 - e607_ffff -> port 0(L2-DM)
  cfg_dmi_read((long long *)(baddr));

  for(int g=0;g<NPU_NUM_GRP;g++){
    //slice peripheral
    config_aperture(apidx, baddr, 0xe0000000+0x1000000*g, 0x01000000, g); // aperture e000_0000 - e0ff_ffff (grp $g)
    //STU MMIO
    config_aperture(apidx, baddr, 0xe6080000+0x2000*g, 0x00002000, g); // aperture e608_0000 - e608_1fff (grp 0 - stu0-1)
  }
  apidx = apidx + (4-NPU_NUM_GRP)*2;
  //CSM
  //cfg_csm_apertures(apidx, baddr, 0xe8000000, 0x4000000, 0/*start idx*/);
  cfg_csm_apertures(apidx, baddr, LC_CSM_BASE, 0x4000000, 0/*start idx*/);

  /* config cbu matrix */
  apidx=0;
  baddr = cfg_dmi_base + 4 * 0x20000 + 0x1000;
  config_aperture(apidx, baddr, 0xe6400000, 0x100000, 2);   // aperture e640_0000 - e64f_ffff -> port 2 to cfg axi
  config_aperture(apidx, baddr, 0xe0000000, 0x10000000, 0); // aperture e000_0000 - efff_ffff -> port 0 to top_matrix
  config_aperture(apidx, baddr, LC_CSM_BASE, 0x4000000, 0); // aperture CSM -> port 0 to top_matrix
  config_aperture(apidx, baddr, 0, 0, 1);                   // the rest maps to port 1 (NoC)
  cfg_dmi_read((long long *)(baddr));
  /* config dmi remap */
  apidx=0;
  baddr = cfg_dmi_base + 4 * 0x20000 + 0x2000;
  //TODO, customized by user
  /* config safety top */
  baddr = cfg_dmi_base + 4 * 0x20000 + 0x4000;
}

/* TODO: Need document
   1. how remap works
   2. aperture index for two remap modules share some aperture array(cln1p0 & slice safety)
*/
void config_remap(int g){
  long long cfg_dmi_base=0xf0000000;
  long long l2_dmi_base =0xe6400000;
  long long baddr;
  int apidx=0;

    apidx = 0;
    baddr = cfg_dmi_base + g*0x20000 + 0x3000;
    //config cln1p0 reamp
    if (NPU_NUM_GRP == 4 ) {
      cfg_csmreamp_aperture(apidx, baddr, 4);
    }
    else if (NPU_NUM_GRP == 2) {
      cfg_csmreamp_aperture(apidx, baddr, 2);
    }
    else {
      cfg_csmreamp_aperture(apidx, baddr, 1);
    }
    cfg_dmi_read((long long *)(baddr));
    
    //config sfty_ccm remap
    if(NPU_SAFETY_LEVEL >0) {
      for(int s=0;s<NPU_NUM_SLC_PER_GRP;s++){
        long long caddr = cfg_dmi_base + g*0x20000 + 0x4000 + s*0x2000;
        long long saddr = 0xe0000000 + g*0x1000000 + s*0x400000 + 0x84000;
        cfg_reamp_aperture(apidx, baddr, caddr, 0x2000, saddr, 0x2000, 13);
        cfg_dmi_read((long long *)(baddr));
        //CFG L2 Safety Remap
        caddr = l2_dmi_base + g*0x20000 + 0x4000 + s*0x2000;
        saddr = 0xe0000000 + g*0x1000000 + s*0x400000 + 0x84000;
        cfg_reamp_aperture(apidx, baddr, caddr, 0x2000, saddr, 0x2000, 13);
        //remap cfg_dmi addr to slc 0 sfty: e008_4000 - e008_5fff
        //remap cfg_dmi addr to slc 1 sfty: e048_4000 - e048_5fff
      }
    }

}

//config DMI remap
void config_dmi_reamp(const long long& base1, const long long& size1, const long long& base2, const long long& size2){
  long long cfg_dmi_base=0xf0000000;
  long long baddr;
  int apidx=0;

  baddr = cfg_dmi_base + 0x82000;
  cfg_reamp_aperture(apidx, baddr, base1, size1, base2, size2, 32);
}

void config_npx_sys_map_all(){

  //if (ARCSYNC_PMU_RESET_PMODE){
  //    l2grp_power_up_all(0/*cluster_id*/);
  //    l1grp_power_up_all(0/*cluster_id*/);
  //    slc_power_up_all(0/*cluster_id*/);
  //}

  cout << "****************************************" << endl;
  cout << "Starting to configurate system map   " << endl;
  cout << "  configuring L2 group      " << endl;
  config_l2_grp();
  for (int i=0; i<NPU_NUM_GRP; i++) {
    cout << "  configuring group " << i <<" CLN         " << endl;
    config_cln_grp(i);
    cout << "  configuring group " << i <<" remap         " << endl;
    config_remap(i);
  }
  set_sys_cfg_done();
  cout << "Configuring system map done        " << endl;
  cout << "**************************************" << endl;
}

void config_npx_sys_map(int g){
  config_cln_grp(g);
  config_remap(g);
}

#endif
