/*************************************************************************/
/**                                                                     **/
/** Copyright (C) 2021-2023 Synopsys, Inc.                              **/
/** All Rights Reserved.                                                **/
/**                                                                     **/
/** This Synopsys software and all associated documentation are         **/
/** proprietary to Synopsys, Inc. and may only be used pursuant to the  **/
/** terms and conditions of a written license agreement with Synopsys,  **/
/** Inc. All other use, reproduction, modification, or distribution of  **/
/** this Synopsys software or the associated documentation is strictly  **/
/** prohibited.                                                         **/
/**                                                                     **/
/*************************************************************************/

/*
 * npu_mli_act_lib.c
 *
 * File defining a MLI library of predefined activation functions
 *
 */

//
// channelwise reduce operations
//
void init_creduce(act_hlapi_t& h, act_bin_op_t op) {
  h.i.u.op.scl[0] = 0;
  ACT_START(h);
  // inner loop popin and add to the vr1 that will be reduced at the end of 
  // the outter loop
  ACT_INST(h, fpopin0(PALWAYS, VR0), 0);
  ACT_INST(h, fadd(PFIRST2, VR1, VR0), 4);
  // reduce and pushout at the end of the outter loop
  switch (op)
  {
  case op_add:
    ACT_INST(h, fadd(PNFIRST2, VR1, VR1, VR0), 5);
    ACT_INST(h, raddc(PLAST2, VR2, VR1), 6);
    ACT_INST(h, raddc(PLAST2, VR2, VR2), 8);
    ACT_INST(h, raddc(PLAST2, VR2, VR2), 10);
    ACT_INST(h, raddc(PLAST2, VR2, VR2), 12);
    break;
  case op_max:
    ACT_INST(h, fmax(PNFIRST2, VR1, VR1, VR0), 5);
    ACT_INST(h, rmaxc(PLAST2, VR2, VR1), 6);
    ACT_INST(h, rmaxc(PLAST2, VR2, VR2), 8);
    ACT_INST(h, rmaxc(PLAST2, VR2, VR2), 10);
    ACT_INST(h, rmaxc(PLAST2, VR2, VR2), 12);
    break;
  case op_min:
    ACT_INST(h, fmin(PNFIRST2, VR1, VR1, VR0), 5);
    ACT_INST(h, rminc(PLAST2, VR2, VR1), 6);
    ACT_INST(h, rminc(PLAST2, VR2, VR2), 8);
    ACT_INST(h, rminc(PLAST2, VR2, VR2), 10);
    ACT_INST(h, rminc(PLAST2, VR2, VR2), 12);
    break;
  case op_band:
    ACT_INST(h, band(PNFIRST2, VR1, VR1, VR0), 5);
    ACT_INST(h, randc(PLAST2, VR2, VR1), 6);
    ACT_INST(h, randc(PLAST2, VR2, VR2), 8);
    ACT_INST(h, randc(PLAST2, VR2, VR2), 10);
    ACT_INST(h, randc(PLAST2, VR2, VR2), 12);
    break;
  case op_bor:
    ACT_INST(h, bor(PNFIRST2, VR1, VR1, VR0), 5);
    ACT_INST(h, rorc(PLAST2, VR2, VR1), 6);
    ACT_INST(h, rorc(PLAST2, VR2, VR2), 8);
    ACT_INST(h, rorc(PLAST2, VR2, VR2), 10);
    ACT_INST(h, rorc(PLAST2, VR2, VR2), 12);
    break;
  default: assert(0 && "unsupported reduction operation");
  }
  ACT_INST(h, fpushout(PLAST2, VR2), 14);
  ACT_END(h);
  // end of activation program
}

//
// Mean
//
void init_mean(act_hlapi_t& h, act_alay_t l, bool fp32scl, int ch_pad) {// [NOLINT]
  switch (l) {
    case alayo16:
      h.i.u.op.scl[1] = 1*CMEAN_PER_CHAN;
      break;
    case alayo32:
      h.i.u.op.scl[1] = 2*CMEAN_PER_CHAN;
      break;
  }

  // disable channel padding on the fly, do channel pad in dedicated tapi
  if (ch_pad == -1 ) {

    ACT_START(h);
    // per tensor paramters
    ACT_INST(h, poppars(PFIRST0, SR1), 0);
    // outer loop, sr0 = 1/num
    ACT_INST(h, fadd(PFIRST0, VR7, SR0), 1); 

    unsigned int l = 2;
    // for each c, vr6 = x 
    if (fp32scl){
      ACT_INST(h, fpopin0(PALWAYS, VR4), l);
      l += 4;
      ACT_INST(h, mpy(PALWAYS, VR3, VR4, BRW0), l); //brw0 scale
      l += 4;
      ACT_INST(h, fadd(PALWAYS, VR6, VR3, BRW1), l); //brw1 bias
      l += 2;
    } else {
      ACT_INST(h, fpopin0(PALWAYS, VR6, BRW1, BRB0), l); // brw1 bias brb0 scale
      l += 4;
    }
    // if c == 0, sum = vr6 + 0 l=12 max
    ACT_INST(h, fadd(PFIRST2, VR5, VR6), l); l++;
    // else sum += vr6
    ACT_INST(h, fadd(PNFIRST2, VR5, VR5, VR6), l);  l++;

    // reduce
    ACT_INST(h, raddc(PLAST2, VR1, VR5), l);
    ACT_INST(h, raddc(PLAST2, VR1, VR1), l+2);
    ACT_INST(h, raddc(PLAST2, VR1, VR1), l+4);
    ACT_INST(h, raddc(PLAST2, VR1, VR1), l+6);

    // rv5 = rv1 * 1/num(rv7) TODO can skip mpy is num==1
    
    ACT_INST(h, mpy(PLAST2, VR3, VR1, VR7), l+8);  
    ACT_INST(h, fpushout(PLAST2, VR3), l+12);         // out=vr4
    ACT_END(h);
  // end of activation program
  } else {  // do channel padding on the fly, slower! Please use dedicated channel pad if possible
    h.i.u.op.scl[2] = ch_pad;
    h.i.u.op.scl[3] = 0;

    ACT_START(h);
    // per tensor paramters
    ACT_INST(h, poppars(PFIRST0, SR1), 0);
    
    // store from 0 to 15 in VR0, store 0's in VR2
    ACT_INST(h, strc(PFIRST0, VR0), 1);

    unsigned int l = 2;
    // for each c, vr6 = x 
    if (fp32scl){
      ACT_INST(h, fpopin0(PALWAYS, VR4), l);
      ACT_INST(h, add(PFIRST0, VR2, SR3), l+1);     // vr2=0, too much slot, fold here
      l += 4;
      ACT_INST(h, mpy(PALWAYS, VR3, VR4, BRW0), l); //brw0 scale
      // outer loop, sr0 = 1/num
      ACT_INST(h, fadd(PFIRST0, VR7, SR0), l+1); 
      l += 4;
      ACT_INST(h, fadd(PALWAYS, VR6, VR3, BRW1), l); //brw1 bias
      l += 2;
    } else {
      ACT_INST(h, fpopin0(PALWAYS, VR6, BRW1, BRB0), l); // brw1 bias brb0 scale
      ACT_INST(h, add(PFIRST0, VR2, SR3), l+1);     // vr2 = 0
        // outer loop, sr0 = 1/num
      ACT_INST(h, fadd(PFIRST0, VR7, SR0), l+2); 
      l += 4;
    }
    // Channel pad
    ACT_INST(h, gt(PLAST2, VR1, SR2, VR0), l);
    ACT_INST(h, select(PLAST2, VR6, VR6, VR2), l+2); // vr6 = vr1 > ch_pad ? vr5 : 0

    // if c == 0, sum = vr6 + 0 l=12 max
    ACT_INST(h, fadd(PFIRST2, VR5, VR6), l+4);
    // else sum += vr6
    ACT_INST(h, fadd(PNFIRST2, VR5, VR5, VR6), l+5);  


    //ACT_INST(h, fsub(PLAST2, VR5, VR5, VR6), l+6);
    l+=6; //l=20

    // reduce
    ACT_INST(h, raddc(PLAST2, VR1, VR5), l);
    ACT_INST(h, raddc(PLAST2, VR1, VR1), l+2);
    ACT_INST(h, raddc(PLAST2, VR1, VR1), l+4);
    ACT_INST(h, raddc(PLAST2, VR1, VR1), l+6);

    // rv5 = rv1 * 1/num(rv7) TODO can skip mpy is num==1
    
    ACT_INST(h, mpy(PLAST2, VR3, VR1, VR7), l+8);  
    ACT_INST(h, fpushout(PLAST2, VR3), l+12);         // out=vr4
    ACT_END(h);
    // end of activation program
  }
}

// Channel wise Mean Square Error ReduceSum((x-mean)^2)/n
void init_cmse(act_hlapi_t& h, int ch_pad) {// [NOLINT]
  h.i.u.op.scl[1] = 0;

  // no channel padding, use dedicated padding tapi
  if (ch_pad == -1) {
    ACT_START(h);
    ACT_INST(h, fpopin0(PALWAYS, VR6), 0);

    // loop0 = w*h, loop1 = c
    // outer loop, sr0 = 1/num
    // for each c, vr6 = x
    // (x-mean) * (x-mean)
    ACT_INST(h, mpy(PALWAYS, VR5, VR6, VR6), 4);

    // if c == 0, vr3 sum = 0
    ACT_INST(h, fadd(PFIRST2, VR3, VR5), 8);
    // else sum += (x-mean) * (x-mean)
    ACT_INST(h, fadd(PNFIRST2, VR3, VR3, VR5), 9);

    // reduce
    ACT_INST(h, raddc(PLAST2, VR1, VR3), 10);
    ACT_INST(h, raddc(PLAST2, VR1, VR1), 12);
    ACT_INST(h, raddc(PLAST2, VR1, VR1), 14);
    ACT_INST(h, raddc(PLAST2, VR1, VR1), 16);

    ACT_INST(h, bcc(PLAST2, VR1, VR1), 18);
    ACT_INST(h, add(PFIRST0, VR7, SR0), 20); 

    // rv4 = rv1 * 1/num(rv7) TODO can skip mpy is num==1
    ACT_INST(h, mpy(PLAST2, VR4, VR1, VR7), 22);
    ACT_INST(h, fpushout(PLAST2, VR4), 26);         // out=vr4
    ACT_END(h);
    // end of activation program
  } else { // channel padding on the fly, slower! use dedicated chn pad if possible
    h.i.u.op.scl[2] = ch_pad;
    h.i.u.op.scl[3] = 0;
    ACT_START(h);
    ACT_INST(h, strc(PFIRST0, VR0), 0);
    ACT_INST(h, fpopin0(PALWAYS, VR6), 1);
    ACT_INST(h, add(PFIRST0, VR2, SR3), 2);
    // loop0 = w*h, loop1 = c
    // outer loop, sr0 = 1/num
    // for each c, vr6 = x
    // (x-mean) * (x-mean)
    ACT_INST(h, add(PFIRST0, VR7, SR0), 4);
    ACT_INST(h, mpy(PALWAYS, VR5, VR6, VR6), 5);
    ACT_INST(h, gt(PLAST2, VR1, SR2, VR0), 6);
    // if c == 0, vr3 sum = 0
    ACT_INST(h, fadd(PFIRST2, VR3, VR5), 9);
    // else sum += (x-mean) * (x-mean)
    ACT_INST(h, fadd(PNFIRST2, VR3, VR3, VR5), 10);

    ACT_INST(h, select(PLAST2, VR5, VR2, VR5), 12);

    ACT_INST(h, fsub(PLAST2, VR3, VR3, VR5), 14);

    // reduce
    ACT_INST(h, raddc(PLAST2, VR1, VR3), 16);
    ACT_INST(h, raddc(PLAST2, VR1, VR1), 18);
    ACT_INST(h, raddc(PLAST2, VR1, VR1), 20);
    ACT_INST(h, raddc(PLAST2, VR1, VR1), 22);

    ACT_INST(h, bcc(PLAST2, VR1, VR1), 24);

    // rv4 = rv1 * 1/num(rv7) TODO can skip mpy is num==1
    ACT_INST(h, mpy(PLAST2, VR4, VR1, VR7), 26);
    ACT_INST(h, fpushout(PLAST2, VR4), 30);         // out=vr4
    ACT_END(h);
    // end of activation program
  }
}

// in0/sqrt(in1 + epsilon)
void init_add_rsqrt_scale(act_hlapi_t& h, float epsilon, bool biasdbl) {
  h.i.u.op.scl[0] = MBRSQRT_PER_CHAN;
  h.i.u.op.scl[1] = fp_e8m23_t(epsilon).data;

  ACT_START(h);
  // outer loop

  // for each tiw, pop variance^2
  ACT_INST(h, fpopin1(PFIRST2, VR2), 0);         //variances, w8c1

  // VR4 = variance^2 + epsilon
  ACT_INST(h, fadd(PFIRST2, VR4, SR1, VR2), 4);  //add epsilon

  ACT_INST(h, rsqrt0(PFIRST2, VR4), 6);          //rsqrt
  ACT_INST(h, rsqrt1(PFIRST2, VR5, VR4), 8);     //rsqrt
  ACT_INST(h, mac0(PFIRST2, VR6, VR5), 10);      //rsqrt
  ACT_INST(h, mac1(PFIRST2, VR7, VR6), 14);      //rsqrt
    // for each tic, pop x - mean
  ACT_INST(h, fpopin0(PEVEN, VR1), 16);          //x-mean, w8c16
  ACT_INST(h, fpopin0(PODD, VR5), 17);           //x-mean, w8c16

  ACT_INST(h, mpy(PEVEN, VR4, VR1, VR7), 20);    // (x-mean)*bcc(rsqrt)
  ACT_INST(h, mpy(PODD, VR0, VR5, VR7), 21);     // (x-mean)*bcc(rsqrt)

  // for each c iter, poppars.
  ACT_INST(h, poppars(PALWAYS, SR0), 22);

  ACT_INST(h, mpy(PEVEN, VR6, VR4, BRW1), 24);   // brw1 fp32 scale
  ACT_INST(h, mpy(PODD, VR2, VR0, BRW1), 25);    // brw1 fp32 scale

  if (biasdbl) {
    ACT_INST(h, fadd(PEVEN, VR4, VR6, BRH0), 28); //add bias brh0 int16
    ACT_INST(h, fadd(PODD, VR5, VR2, BRH0), 29);  //add bias brh0 int16

    ACT_INST(h, fpushout(PEVEN, VR4), 30);
    ACT_INST(h, fpushout(PODD, VR5), 31);
  } else {
    ACT_INST(h, fpushout(PEVEN, VR6, BRH0), 28);   //int8 bias and dump scale
    ACT_INST(h, fpushout(PODD, VR2, BRH0), 29);
  }
  ACT_END(h);
}


void init_bmul_scale(act_hlapi_t& h, act_alay_t l, bool biasdbl, broadcast_t brdc_f, bool spodd) {  // [NOLINT]
  // SR1 has number of per channel parameters to pop
  switch (l) {
    case alayo16:
      h.i.u.op.scl[1] = 1*BMUL_PER_CHAN;
      break;
    case alayo32:
      h.i.u.op.scl[1] = 2*BMUL_PER_CHAN;
      break;
  }

  #define PALWAYSX (spodd ? PNLAST1 : PALWAYS)

  // start of activation program
  ACT_START(h);

  // outer loop
  // get new set of per channel parameters on first iteration of inner loop
  ACT_INST(h, poppars(PFIRST1, SR1), 0);

  // first eltwise multiplication then scale
  // load input accumulator from in0 stream
  ACT_INST(h, fpopin0(PALWAYS, VR0), 2);
  // load input accumulator from in1 stream
  ACT_INST(h, fpopin1(PALWAYS, VR1), 3);
  // load input accumulator from in0 stream
  ACT_INST(h, fpopin0(PALWAYSX, VR4), 4);
  // load input accumulator from in1 stream
  ACT_INST(h, fpopin1(PALWAYSX, VR5), 5);

  int l = 6;
  // check broadcasting in w and ch dimensions for input 1
  if (brdc_f.in0_w) {
    ACT_INST(h, bcv(PALWAYS, VR0, VR0), l);
    ACT_INST(h, bcv(PALWAYSX, VR4, VR4), (l + 2));
    l += 4;
  }
  if (brdc_f.in0_c) {
    ACT_INST(h, bcc(PALWAYS, VR0, VR0), l);
    ACT_INST(h, bcc(PALWAYSX, VR4, VR4), (l + 2));
    l += 4;
  }
  // check broadcasting in w and ch dimensions for input 2
  if (brdc_f.in1_w) {
    ACT_INST(h, bcv(PALWAYS, VR1, VR1), l);
    ACT_INST(h, bcv(PALWAYSX, VR5, VR5), (l + 2));
    l += 4;
  }
  if (brdc_f.in1_c) {
    ACT_INST(h, bcc(PALWAYS, VR1, VR1), l);
    ACT_INST(h, bcc(PALWAYSX, VR5, VR5), (l + 2));
    l += 4;
  }
  // eltwise multiply
  // multiply (a[h][w][c] - zpa[c]) * (b[h][w][c] - zpb[c])
  if (l > 6) { // broadcast is used
    l -= 2;
    ACT_INST(h, mpy(PALWAYS, VR2, VR1, VR0), (l + 1));
  } else {
    ACT_INST(h, mpy(PALWAYS, VR2, VR1, VR0), l);
  }
  // multiply (a[h][w][c] - zpa[c]) * (b[h][w][c] - zpb[c])
  ACT_INST(h, mpy(PALWAYSX, VR6, VR5, VR4), (l + 2));

  
  ACT_INST(h, mpy(PALWAYS, VR3, VR2, BRW1), (l + 4));    // 32bit scl
  ACT_INST(h, mpy(PALWAYSX, VR7, VR6, BRW1), (l + 6));    // 32bit scl

  if (biasdbl) {
    ACT_INST(h, fadd(PALWAYS, VR4, VR3, BRH0), (l + 8)); //add bias brh0 int16
    ACT_INST(h, fadd(PALWAYSX, VR5, VR7, BRH0), (l + 10)); //add bias brh0 int16

    ACT_INST(h, fpushout(PALWAYS, VR4), (l + 12));
    ACT_INST(h, fpushout(PALWAYSX, VR5), (l + 14));

  } else {
    ACT_INST(h, fpushout(PALWAYS, VR3, BRH0), (l + 8));   //int8 bias and dump scale
    ACT_INST(h, fpushout(PALWAYSX, VR7, BRH0), (l + 10));   //int8 bias and dump scale
  }
  ACT_END(h);
  // end of activation program
  #undef PALWAYSX
}

/////////////////////////////////////////////////////////////////
//
// Generic binary operations with pre scaling support(floating point)
//
/////////////////////////////////////////////////////////////////

void init_binary_rr_scale_fp(
                       act_hlapi_t& h, 
                       act_bin_op_t op,
                       act_alay_t l,
                       scale_config_t scl,
                       broadcast_t brdc_f
                       ) {
  // no per channel parameters
  switch (l) {
    case alayo16:
      h.i.u.op.scl[1] = 1*SCALE_BINARY_PER_CHAN;
      break;
    case alayo32:
      h.i.u.op.scl[1] = 2*SCALE_BINARY_PER_CHAN;
      break;
  }

  act_pred_t pred_loop[] = {PFIRST0, PFIRST1, PFIRST2, PALWAYS};

  // start of activation program
  ACT_START(h);  

  unsigned int l = 0;

  if (scl.pre != scl_cfg_t::scl_none || scl.post != scl_cfg_t::scl_none) {
    assert(scl.loop_idx < 3 );
    ACT_INST(h, poppars(pred_loop[scl.loop_idx], SR1), l); l+=2;
  }

  ACT_INST(h, fpopin1(PFIRST2, VR1), l);                 l+=4;

  // check broadcasting in w and ch dimensions for input 2
  if (brdc_f.in1_w) {
    ACT_INST(h, bcv(PFIRST2, VR1, VR1), l);
    l += 2;
  }
  if (brdc_f.in1_c) {
    ACT_INST(h, bcc(PFIRST2, VR1, VR1), l);
    l += 2;
  }

  switch (scl.pre) {
    case scl_cfg_t::scl_none:
      ACT_INST(h, fpopin0(PALWAYS, VR0), l);              l+=4;
      break;
    case scl_cfg_t::scl_s8:
      ACT_INST(h, fpopin0(PALWAYS, VR0, BRB0), l);        l+=4;
      break;
    case scl_cfg_t::scl_s16:
      ACT_INST(h, fpopin0(PALWAYS, VR2), l);              l+=4;
      ACT_INST(h, mpyh(PALWAYS, VR0, VR2, BRH0), l);      l+=4;
      break;
    case scl_cfg_t::scl_sb16:
      ACT_INST(h, fpopin0(PALWAYS, VR2), l);              l+=4;
      ACT_INST(h, mpyb(PALWAYS, VR0, VR2, BRH0), l);      l+=4;
      break;
    case scl_cfg_t::scl_s32:
      ACT_INST(h, fpopin0(PALWAYS, VR2), l);              l+=4;
      ACT_INST(h, mpy(PALWAYS, VR0, VR2, BRW0), l);       l+=4;
      break;
    case scl_cfg_t::scl_b8:
      ACT_INST(h, fpopin0(PALWAYS, VR2), l);              l+=4;
      ACT_INST(h, fadd(PALWAYS, VR0, VR2, BRB0), l);      l+=2;
      break;
    case scl_cfg_t::scl_b16:
      ACT_INST(h, fpopin0(PALWAYS, VR2), l);              l+=4;
      ACT_INST(h, fadd(PALWAYS, VR0, VR2, BRH0), l);      l+=2;
      break;
    case scl_cfg_t::scl_b32:
      ACT_INST(h, fpopin0(PALWAYS, VR0, BRW0), l);        l+=4;
      break;
    case scl_cfg_t::scl_s8b32:
      ACT_INST(h, fpopin0(PALWAYS, VR0, BRW1, BRB0), l);  l+=4;
      break;
    case scl_cfg_t::scl_s16b32:
      ACT_INST(h, fpopin0(PALWAYS, VR2), l);              l+=4;
      ACT_INST(h, mpyh(PALWAYS, VR3, VR2, BRH0), l);      l+=4; // scale first and then add
      ACT_INST(h, fadd(PALWAYS, VR0, VR3, BRW1), l);      l+=2;
      break;
    case scl_cfg_t::scl_sb16b32:
      ACT_INST(h, fpopin0(PALWAYS, VR2), l);              l+=4;
      ACT_INST(h, mpyb(PALWAYS, VR3, VR2, BRH0), l);      l+=4;
      ACT_INST(h, fadd(PALWAYS, VR0, VR3, BRW1), l);      l+=2;
      break;
    case scl_cfg_t::scl_s32b32:
      ACT_INST(h, fpopin0(PALWAYS, VR2), l);              l+=4;
      ACT_INST(h, mpy(PALWAYS, VR3, VR2, BRW0), l);       l+=4;
      ACT_INST(h, fadd(PALWAYS, VR0, VR3, BRW1), l);      l+=2;
      break;
    case scl_cfg_t::scl_s8b16:
      ACT_INST(h, fpopin0(PALWAYS, VR2, BRB0), l);        l+=4;
      ACT_INST(h, fadd(PALWAYS, VR0, VR2, BRH1), l);      l+=2;
      break;
    case scl_cfg_t::scl_s16b16:
      ACT_INST(h, fpopin0(PALWAYS, VR2), l);              l+=4;
      ACT_INST(h, mpyh(PALWAYS, VR3, VR2, BRH0), l);      l+=4;
      ACT_INST(h, fadd(PALWAYS, VR0, VR3, BRH1), l);      l+=2;
      break;
    case scl_cfg_t::scl_sb16b16:
      ACT_INST(h, fpopin0(PALWAYS, VR2), l);              l+=4;
      ACT_INST(h, mpyb(PALWAYS, VR3, VR2, BRH0), l);      l+=4;
      ACT_INST(h, fadd(PALWAYS, VR0, VR3, BRH1), l);      l+=2;
      break;
    case scl_cfg_t::scl_s32b16:
      ACT_INST(h, fpopin0(PALWAYS, VR2), l);              l+=4;
      ACT_INST(h, mpy(PALWAYS, VR3, VR2, BRW0), l);       l+=4;
      ACT_INST(h, fadd(PALWAYS, VR0, VR3, BRH2), l);      l+=2;
      break;
    case scl_cfg_t::scl_s8b8:
      ACT_INST(h, fpopin0(PALWAYS, VR2, BRB0), l);        l++;
      ACT_INST(h, fadd(PALWAYS, VR0, VR3, BRB1), l);      l+=2;
      break;
    case scl_cfg_t::scl_s16b8:
      ACT_INST(h, fpopin0(PALWAYS, VR2), l);              l+=4;
      ACT_INST(h, mpyh(PALWAYS, VR3, VR2, BRH0), l);      l+=4;
      ACT_INST(h, fadd(PALWAYS, VR0, VR3, BRB2), l);      l+=2;
      break;
    case scl_cfg_t::scl_sb16b8:
      ACT_INST(h, fpopin0(PALWAYS, VR2), l);              l++;
      ACT_INST(h, mpyb(PALWAYS, VR3, VR2, BRH0), l);      l+=4;
      ACT_INST(h, fadd(PALWAYS, VR0, VR3, BRB2), l);      l+=2;
      break;
    case scl_cfg_t::scl_s32b8:
      ACT_INST(h, fpopin0(PALWAYS, VR2), l);              l+=4;
      ACT_INST(h, mpy(PALWAYS, VR3, VR2, BRW0), l);       l+=4;
      ACT_INST(h, fadd(PALWAYS, VR0, VR3, BRB4), l);      l+=2;
      break; 
  }

  // check broadcasting in w and ch dimensions for input 1
  if (brdc_f.in0_w) {
    ACT_INST(h, bcv(PALWAYS, VR0, VR0), l);
    l += 2;
  }
  if (brdc_f.in0_c) {
    ACT_INST(h, bcc(PALWAYS, VR0, VR0), l);
    l += 2;
  }

  switch (op) {
    case op_fadd:   ACT_INST(h, fadd(PALWAYS, VR2, VR0, VR1), l);   l += 2; break;
    case op_fsub:   ACT_INST(h, fsub(PALWAYS, VR2, VR0, VR1), l);   l += 2; break;
    case op_frsub:  ACT_INST(h, frsub(PALWAYS, VR2, VR0, VR1), l);  l += 2; break;
    case op_fmin:   ACT_INST(h, fmin(PALWAYS, VR2, VR0, VR1), l);   l += 2; break;
    case op_fmax:   ACT_INST(h, fmax(PALWAYS, VR2, VR0, VR1), l);   l += 2; break;
    case op_faddf:  ACT_INST(h, faddf(PALWAYS, VR2, VR0, VR1), l);  l += 2; break;
    case op_fsubf:  ACT_INST(h, fsubf(PALWAYS, VR2, VR0, VR1), l);  l += 2; break;
    case op_frsubf: ACT_INST(h, frsubf(PALWAYS, VR2, VR0, VR1), l); l += 2; break;
    case op_fminf:  ACT_INST(h, fminf(PALWAYS, VR2, VR0, VR1), l);  l += 2; break;
    case op_fmaxf:  ACT_INST(h, fmaxf(PALWAYS, VR2, VR0, VR1), l);  l += 2; break;
    case op_frelun: ACT_INST(h, frelun(PALWAYS, VR2, VR0, VR1), l); l += 2; break;
    case op_feq:    ACT_INST(h, feq(PALWAYS, VR2, VR0, VR1), l);    l += 2; break;
    case op_fneq:   ACT_INST(h, fneq(PALWAYS, VR2, VR0, VR1), l);   l += 2; break;
    case op_fgt:    ACT_INST(h, fgt(PALWAYS, VR2, VR0, VR1), l);    l += 2; break;
    case op_fgte:   ACT_INST(h, fgte(PALWAYS, VR2, VR0, VR1), l);   l += 2; break;
    case op_flt:    ACT_INST(h, flt(PALWAYS, VR2, VR0, VR1), l);    l += 2; break;
    case op_flte:   ACT_INST(h, flte(PALWAYS, VR2, VR0, VR1), l);   l += 2; break;
    case op_mpy:    ACT_INST(h, mpy(PALWAYS, VR2, VR0, VR1), l);    l += 4; break;
    case op_mpyh:   ACT_INST(h, mpyh(PALWAYS, VR2, VR0, VR1), l);   l += 4; break;
    case op_mpyb:   ACT_INST(h, mpyb(PALWAYS, VR2, VR0, VR1), l);   l += 4; break;
    default: assert(0 && "unsupported binary_rr operation");
  }

  auto out_v = VR2;
  if (op == op_feq || op == op_fneq || op == op_flt || op == op_flte || op == op_fgt || op == op_fgte) {
    ACT_INST(h, movf(PALWAYS, VR3), l); l += 2;
    out_v = VR3;
  } 

  switch (scl.post) {
    case scl_cfg_t::scl_none:
      ACT_INST(h, fpushout(PALWAYS, out_v), l);
      break;
    case scl_cfg_t::scl_s8:
      ACT_INST(h, fpushout(PALWAYS, out_v, BRB0), l);
      break;
    case scl_cfg_t::scl_s16:
      ACT_INST(h, mpyh(PALWAYS, out_v, out_v, BRH0), l);      l+=4;
      ACT_INST(h, fpushout(PALWAYS, out_v), l);      
      break;
    case scl_cfg_t::scl_sb16:
      ACT_INST(h, mpyb(PALWAYS, out_v, out_v, BRH0), l);      l+=4;
      ACT_INST(h, fpushout(PALWAYS, out_v), l);  
      break;
    case scl_cfg_t::scl_s32:
      ACT_INST(h, mpy(PALWAYS, out_v, out_v, BRW0), l);       l+=4;
      ACT_INST(h, fpushout(PALWAYS, out_v), l); 
      break;
    case scl_cfg_t::scl_b8:
      ACT_INST(h, fadd(PALWAYS, out_v, out_v, BRB0), l);      l+=2;
      ACT_INST(h, fpushout(PALWAYS, out_v), l); 
      break;
    case scl_cfg_t::scl_b16:
      ACT_INST(h, fadd(PALWAYS, out_v, out_v, BRH0), l);      l+=2;
      ACT_INST(h, fpushout(PALWAYS, out_v), l); 
      break;
    case scl_cfg_t::scl_b32:
      ACT_INST(h, fadd(PALWAYS, out_v, out_v, BRW0), l);      l+=2;
      ACT_INST(h, fpushout(PALWAYS, out_v), l); 
      break;
    case scl_cfg_t::scl_s8b32:
      assert(false && "Not support 8bit scale 32bit bias for output");
      break;
    case scl_cfg_t::scl_s16b32:
      ACT_INST(h, mpyh(PALWAYS, out_v, out_v, BRH0), l);       l+=4; // scale first and then add
      ACT_INST(h, fadd(PALWAYS, out_v, out_v, BRW1), l);       l+=2;
      ACT_INST(h, fpushout(PALWAYS, out_v), l); 
      break;
    case scl_cfg_t::scl_sb16b32:
      ACT_INST(h, mpyb(PALWAYS, out_v, out_v, BRH0), l);       l+=4;
      ACT_INST(h, fadd(PALWAYS, out_v, out_v, BRW1), l);       l+=2;
      ACT_INST(h, fpushout(PALWAYS, out_v), l); 
      break;
    case scl_cfg_t::scl_s32b32:
      ACT_INST(h, mpy(PALWAYS, out_v, out_v, BRW0), l);        l+=4;
      ACT_INST(h, fadd(PALWAYS, out_v, out_v, BRW1), l);       l+=2;
      ACT_INST(h, fpushout(PALWAYS, out_v), l); 
      break;
    case scl_cfg_t::scl_s8b16:
      ACT_INST(h, add(PALWAYS, out_v, out_v, BRH1), l);        l+=2;
      ACT_INST(h, fpushout(PALWAYS, out_v), l); 
      break;
    case scl_cfg_t::scl_s16b16:
      ACT_INST(h, mpyh(PALWAYS, out_v, out_v, BRH0), l);       l+=4;
      ACT_INST(h, add(PALWAYS, out_v, out_v, BRH1), l);        l+=2;
      ACT_INST(h, fpushout(PALWAYS, out_v), l); 
      break;
    case scl_cfg_t::scl_sb16b16:
      ACT_INST(h, mpyb(PALWAYS, out_v, out_v, BRH0), l);       l+=4;
      ACT_INST(h, add(PALWAYS, out_v, out_v, BRH1), l);        l+=2;
      ACT_INST(h, fpushout(PALWAYS, out_v), l); 
      break;
    case scl_cfg_t::scl_s32b16:
      ACT_INST(h, mpy(PALWAYS, out_v, out_v, BRW0), l);        l+=4;
      ACT_INST(h, add(PALWAYS, out_v, out_v, BRH2), l);        l+=2;
      ACT_INST(h, fpushout(PALWAYS, out_v), l); 
      break;
    case scl_cfg_t::scl_s8b8:
      ACT_INST(h, fpushout(PALWAYS, out_v, BRH0), l); 
      break;
    case scl_cfg_t::scl_s16b8:
      ACT_INST(h, mpyh(PALWAYS, out_v, out_v, BRH0), l);       l+=4;
      ACT_INST(h, add(PALWAYS, out_v, out_v, BRB2), l);        l+=2;
      ACT_INST(h, fpushout(PALWAYS, out_v), l); 
      break;
    case scl_cfg_t::scl_sb16b8:
      ACT_INST(h, mpyb(PALWAYS, out_v, out_v, BRH0), l);       l+=4;
      ACT_INST(h, add(PALWAYS, out_v, out_v, BRB2), l);        l+=2;
      ACT_INST(h, fpushout(PALWAYS, out_v), l); 
      break;
    case scl_cfg_t::scl_s32b8:
      ACT_INST(h, mpy(PALWAYS, out_v, out_v, BRW0), l);        l+=4;
      ACT_INST(h, add(PALWAYS, out_v, out_v, BRB4), l);        l+=2;
      ACT_INST(h, fpushout(PALWAYS, out_v), l); 
      break;      
  }

  ACT_END(h);
  // end of activation program
}

// W wise Mean Square Error ReduceSum((x-mean)^2)/n
void init_wmse(act_hlapi_t& h, bool useAcc, bool keepAcc) { // [NOLINT]
  // no per channel parameter
  h.i.u.op.scl[0] = useAcc ? 1 : 0;
  // start of activation program
  ACT_START(h);
  ACT_INST(h, neq(PFIRST0, VR0, SR0), 0);         // compare SR0!=0 and set flags
  ACT_INST(h, fpopin1(PFIRST2, VR1), 1);         // pop channel accumulator value into VR1
  ACT_INST(h, select(PFIRST2, VR2, VR1), 4);     // select 0 or accumulator value
  ACT_INST(h, fpopin0(PALWAYS, VR3), 5);         // pop input layer data into VR0
  ACT_INST(h, mpy(PALWAYS, VR4, VR3, VR3),8);    // power
  ACT_INST(h, fadd(PALWAYS, VR2, VR4, VR2),12);  // add with accumulator
  ACT_INST(h, raddv(PLAST2, VR6, VR2), 14);     // reduce and accumulate stage 0
  ACT_INST(h, raddv(PLAST2, VR7, VR6), 16);     // reduce and accumulate stage 1
  ACT_INST(h, raddv(PLAST2, VR3, VR7), 18);     // reduce and accumulate stage 2

  if (keepAcc) {
  // keep the intermediate output
  // bcv
    ACT_INST(h, fpushout(PLAST2, VR3), 20);      // keepAcc in AM
  } else {
    ACT_INST(h, bcv(PLAST2, VR4, VR3), 20);     // reduce and accumulate stage 2, not bcv for intermediate tile
    // final output --> divide accumulator by number of inputs
    ACT_INST(h, add(PLAST2, VR5, SR2), 22);      // broadcast scale
    ACT_INST(h, mpy(PLAST2, VR6, VR4, VR5), 24);   // 16b*16b scale
    // bcv
    ACT_INST(h, fpushout(PLAST2, VR6), 28);      // push result to AM
  }
  ACT_END(h);
  // end of activation program
}

// in0/sqrt(in1 + epsilon).broadcast(w)
void init_add_rsqrt_scale_w(act_hlapi_t& h, float epsilon, bool biasdbl) {
  h.i.u.op.scl[0] = MBRSQRTW_PER_CHAN;
  h.i.u.op.scl[1] = fp_e8m23_t(epsilon).data;

  ACT_START(h);
  // outer loop

  // for each tic, pop variance^2
  ACT_INST(h, fpopin1(PFIRST2, VR2), 0);         //variances, w8c1

  // broadcast epsilon
  ACT_INST(h, fadd(PFIRST0, VR3, SR1), 1);       //broadcast epsilon

  // VR4 = variance^2 + epsilon
  ACT_INST(h, fadd(PFIRST2, VR4, VR2, VR3), 4);  //add epsilon

  ACT_INST(h, rsqrt0(PFIRST2, VR4), 6);          //rsqrt
  ACT_INST(h, rsqrt1(PFIRST2, VR5, VR4), 8);     //rsqrt
  ACT_INST(h, mac0(PFIRST2, VR6, VR5), 10);      //rsqrt
  ACT_INST(h, mac1(PFIRST2, VR7, VR6), 14);      //rsqrt

  ACT_INST(h, poppars(PFIRST2, SR0), 15);
  
  // for each tiw, pop x - mean
  ACT_INST(h, fpopin0(PEVEN, VR1), 16);          //x-mean, w8c16
  ACT_INST(h, fpopin0(PODD, VR5), 17);           //x-mean, w8c16

  ACT_INST(h, mpy(PEVEN, VR4, VR1, VR7), 20);    // (x-mean)*bcc(rsqrt)
  ACT_INST(h, mpy(PODD, VR0, VR5, VR7), 21);     // (x-mean)*bcc(rsqrt)

  // get new set of per channel parameters on first iteration of inner loop
 
  ACT_INST(h, mpy(PEVEN, VR6, VR4, BRW1), 24);   // brw1 fp32 scale
  ACT_INST(h, mpy(PODD, VR2, VR0, BRW1), 25);    // brw1 fp32 scale

  if (biasdbl) {
    ACT_INST(h, fadd(PEVEN, VR4, VR6, BRH0), 28); //add bias brh0 int16
    ACT_INST(h, fadd(PODD, VR5, VR2, BRH0), 29);  //add bias brh0 int16

    ACT_INST(h, fpushout(PEVEN, VR4), 30);
    ACT_INST(h, fpushout(PODD, VR5), 31);
  } else {
    ACT_INST(h, fpushout(PEVEN, VR6, BRH0), 28);   //int8 bias and dump scale
    ACT_INST(h, fpushout(PODD, VR2, BRH0), 29);
  }
  ACT_END(h);
}


void init_wmean(act_hlapi_t& h, bool useAcc, bool keepAcc, act_alay_t l, bool fp32scl) {  // [NOLINT]
  // no per channel parameter
  h.i.u.op.scl[0] = useAcc ? 1 : 0;

  switch (l) {
  case alayo16:
    h.i.u.op.scl[1] = 1*WMEAN_PER_CHAN;
    break;
  case alayo32:
    h.i.u.op.scl[1] = 2*WMEAN_PER_CHAN;
    break;
}

  ACT_START(h);
  // loop0 = 1, loop1 = c loop2 = w
  ACT_INST(h, poppars(PFIRST0, SR1), 0);                 // per tensor scale
  
  // pfirst0 = 1, pfirst1 = c, pfirst2 = spatial
  // for each c popin1
  ACT_INST(h, fpopin1(PFIRST2, VR1), 1);                // pop channel accumulator value into VR1
  ACT_INST(h, neq(PFIRST0, VR0, SR0), 2);               // compare SR0!=0 and set flags, sr0 =  useAcc
  ACT_INST(h, select(PFIRST2, VR2, VR1), 4);            // select 0 or accumulator value

  int l = 6;
  // for each w popin0
  if (fp32scl){
    ACT_INST(h, fpopin0(PALWAYS, VR4), l);
    l += 4;
    ACT_INST(h, mpy(PALWAYS, VR6, VR4, BRW0), l); //brw0 scale
    l += 4;
    ACT_INST(h, fadd(PALWAYS, VR3, VR6, BRW1), l); //brw1 bias
    l += 2;
  } else {
    ACT_INST(h, fpopin0(PALWAYS, VR3, BRW1, BRB0), l);  // brw1 bias brb0 scale
    l += 4;
  }

  // for each w vr2 += in0
  ACT_INST(h, fadd(PALWAYS, VR2, VR3, VR2),l);    l+=2;  // add with accumulator

  // for each c raddv
  ACT_INST(h, raddv(PLAST2, VR4, VR2), l);        l+=2;  // reduce and accumulate stage 0
  ACT_INST(h, raddv(PLAST2, VR4, VR4), l);        l+=2;  // reduce and accumulate stage 1
  ACT_INST(h, raddv(PLAST2, VR4, VR4), l);        l+=2 ; // reduce and accumulate stage 2
  if (keepAcc) {
    // keep the intermediate output
    ACT_INST(h, fpushout(PLAST2, VR4), l);               // keepAcc in AM
  } else {
    // final output --> divide accumulator by number of inputs
    ACT_INST(h, add(PLAST2, VR5, SR2), l);        l+=2;  // broadcast scale
    ACT_INST(h, mpy(PLAST2, VR6, VR4, VR5), l);   l+=4;  // 16b*16b scale
    ACT_INST(h, fpushout(PLAST2, VR6), l);               // push result to AM
  }
  ACT_END(h);
  // end of activation program
}

void init_chan_pad(act_hlapi_t& h, int ch_pad) {
  h.i.u.op.scl[2] = ch_pad;
  h.i.u.op.scl[3] = 0;

  ACT_START(h);

  // store from 0 to 15 in VR0, store 0's in VR2
  ACT_INST(h, strc(PFIRST0, VR0), 0);

  ACT_INST(h, add(PFIRST0, VR2, SR3), 2);           // vr2=0
  ACT_INST(h, gt(PFIRST0, VR1, SR2, VR0), 4);

  ACT_INST(h, fpopin0(PALWAYS, VR6), 6);
 
  // Channel pad
  ACT_INST(h, select(PALWAYS, VR6, VR6, VR2), 10);   // vr6 = vr1 > ch_pad ? VR6 : 0

  ACT_INST(h, fpushout(PALWAYS, VR6), 12);         // out=VR6
  ACT_END(h);
  // end of activation program
}

#if 1
void init_gridsample(act_hlapi_t& h) {
  // start of activation program
  ACT_START(h);
  // only at start of C-loop
  ACT_INST(h, fpopin1(PFIRST1, VR0), 0);          // VR0 = x&y float indexes
  ACT_INST(h, ftoi(PFIRST1, VR7, VR0), 4);        // VR7 = indexes for gather
  ACT_INST(h, fract(PFIRST1, VR0, VR0), 6);       // VR0 = fraction parts
  ACT_INST(h, gather2d(PFIRST1), 7);              // start 2d-gather (uses VR7 implicitly)
  ACT_INST(h, fadd(PFIRST1, VR1, VR0), 8);        // copy VR0 to VR1
  ACT_INST(h, trnsp(PFIRST1, VR0, VR1), 10);      // transpose on VR0 and VR1
  // inner loop with some delay to compensate for gather delay
  ACT_INST(h, fpopin0(PNLAST2, VR2), 16);         // VR2 = left
  ACT_INST(h, fpopin0(PNLAST2, VR3), 18);         // VR3 = right
  // interpolate, out = left + fractx * (right - left)
  //           or out = top + fracty * (bottom - top)
  ACT_INST(h, fsub(PNLAST2, VR3, VR3, VR2), 22);  // VR3 = right (VR3) - left (VR2)
  ACT_INST(h, fsub(PLAST2, VR6, VR6, VR5), 23);   // VR6 = bottom (VR6) - top (VR5)
  ACT_INST(h, mpy(PNLAST2, VR4, VR3, VR0), 24);   // VR4 = VR3 * fractx (VR0)
  ACT_INST(h, mpy(PLAST2, VR4, VR6, VR1), 25);    // VR4 = VR6 * fracty (VR1)
  ACT_INST(h, fadd(PNLAST2, VR6, VR2), 26);       // VR6 = VR2 (copy left to VR6)
  ACT_INST(h, fadd(PLAST2, VR6, VR5), 27);        // VR6 = VR5 (copy top to VR6)
  ACT_INST(h, fadd(PFIRST2, VR5, VR4, VR6), 28);  // VR5 = VR4 + left (VR6)
  ACT_INST(h, fadd(PNFIRST2, VR6, VR4, VR6), 29); // VR6 = VR4 + left or top (VR6)
  ACT_INST(h, fpushout(PLAST2, VR6), 30);         // out = VR6
  ACT_END(h);
  // end of activation program
}
#else
void init_gridsample(act_hlapi_t& h) {
  // start of activation program
  ACT_START(h);
  // only at start of C-loop
  ACT_INST(h, fpopin1(PFIRST1, VR0), 0);          // VR0 = x&y float indexes
  ACT_INST(h, ftoi(PFIRST1, VR7, VR0), 4);        // VR7 = indexes for gather
  ACT_INST(h, fract(PFIRST1, VR0, VR0), 6);       // VR0 = fraction parts
  ACT_INST(h, gather2d(PFIRST1), 7);              // start 2d-gather (uses VR7 implicitly)
  ACT_INST(h, fadd(PFIRST1, VR1, VR0), 8);        // copy VR0 to VR1
  ACT_INST(h, trnsp(PFIRST1, VR0, VR1), 10);      // transpose on VR0 and VR1

  // inner loop with some delay to compensate for gather delay
  ACT_INST(h, fpopin0(PNLAST2, VR2), 16);         // VR2 = left
  ACT_INST(h, fpopin0(PNLAST2, VR3), 18);         // VR3 = right
  // interpolate, out = left + fractx * (right - left)
  //           or out = top + fracty * (bottom - top)
  ACT_INST(h, fsub(PNLAST2, VR3, VR3, VR2), 22);  // VR3 = right (VR3) - left (VR2)
  ACT_INST(h, fsub(PLAST2, VR3, VR6, VR5), 23);   // VR3 = bottom (VR6) - top (VR5)
  ACT_INST(h, mpy(PNLAST2, VR4, VR3, VR0), 24);   // VR4 = VR3 * fractx (VR0)
  ACT_INST(h, mpy(PLAST2, VR4, VR3, VR1), 25);    // VR4 = VR3 * fracty (VR1)
  ACT_INST(h, fadd(PLAST2, VR2, VR5), 26);        // VR2 = VR5 (copy top to VR2)
  ACT_INST(h, fadd(PFIRST2, VR5, VR4, VR2), 28);  // VR5 = VR4 + left (VR2)
  ACT_INST(h, fadd(PNFIRST2, VR6, VR4, VR2), 29); // VR6 = VR4 + left or top (VR2)
  ACT_INST(h, fpushout(PLAST2, VR6), 30);         // out = VR6
  ACT_END(h);
  // end of activation program
}

void init_gridsample(act_hlapi_t& h) {
  // start of activation program
  ACT_START(h);
  // only at start of C-loop
  ACT_INST(h, fpopin1(PFIRST1, VR0), 0);          // VR0 = x&y float indexes
  ACT_INST(h, ftoi(PFIRST1, VR7, VR0), 4);        // VR7 = indexes for gather
  ACT_INST(h, fract(PFIRST1, VR0, VR0), 6);       // VR0 = fraction parts
  ACT_INST(h, gather2d(PFIRST1), 7);              // start 2d-gather (uses VR7 implicitly)
  ACT_INST(h, fadd(PFIRST1, VR1, VR0), 8);        // copy VR0 to VR1
  ACT_INST(h, trnsp(PFIRST1, VR0, VR1), 10);      // transpose on VR0 and VR1
  ACT_INST(h, fadd(PNLAST2, VR5, VR6), 12);       // VR5 <- VR6 (copy top to VR5) (first iteration - no effect, second - copy)
  // inner loop with some delay to compensate for gather delay
  ACT_INST(h, fpopin0(PNLAST2, VR2), 18);         // VR2 = left
  ACT_INST(h, fpopin0(PNLAST2, VR3), 20);         // VR3 = right
  // interpolate, out = left + fractx * (right - left)
  //           or out = top + fracty * (bottom - top)
  ACT_INST(h, fsub(PLAST2, VR3, VR6, VR5), 23);   // VR3 = bottom (VR6) - top (VR5)
  ACT_INST(h, fsub(PNLAST2, VR3, VR3, VR2), 24);  // VR3 = right (VR3) - left (VR2)
  ACT_INST(h, mpy(PLAST2, VR4, VR3, VR1), 25);    // VR4 = VR3 * fracty (VR1)
  ACT_INST(h, mpy(PNLAST2, VR4, VR3, VR0), 26);   // VR4 = VR3 * fractx (VR0)
  ACT_INST(h, fadd(PLAST2, VR6, VR4, VR5), 29);   // VR6 = VR4 + top (VR5)
  ACT_INST(h, fadd(PNLAST2, VR6, VR4, VR2), 30);  // VR6 = VR4 + left (VR2)
  ACT_INST(h, fpushout(PLAST2, VR6), 31);         // out = VR6
  ACT_END(h);
  // end of activation program
}
#endif

//
// Prepare grid for padding
//
void init_grid_pad(act_hlapi_t& h, act_pad_t pad_type, float maxx, float maxy) {
  switch (pad_type) {
    case pad_zero:
      h.i.u.op.scl[0] = fp_e8m23_t(maxx + 2.0f).data;
      h.i.u.op.scl[1] = fp_e8m23_t(maxy + 2.0f).data;
      h.i.u.op.scl[2] = fp_e8m23_t(1.0f).data;
      break;
    case pad_edge:
      h.i.u.op.scl[0] = fp_e8m23_t(maxx).data;
      h.i.u.op.scl[1] = fp_e8m23_t(maxy).data;
      break;
    case pad_mirror:
      h.i.u.op.scl[0] = fp_e8m23_t(maxx).data;
      h.i.u.op.scl[1] = fp_e8m23_t(maxy).data;
      h.i.u.op.scl[2] = fp_e8m23_t(maxx * 2.0f).data;
      h.i.u.op.scl[3] = fp_e8m23_t(maxy * 2.0f).data;
      break;
    case pad_replic:
      h.i.u.op.scl[0] = fp_e8m23_t(maxx).data;
      h.i.u.op.scl[1] = fp_e8m23_t(maxy).data;
      h.i.u.op.scl[2] = fp_e8m23_t(maxx * 2.0f + 1.0f).data;
      h.i.u.op.scl[3] = fp_e8m23_t(maxy * 2.0f + 1.0f).data;
      break;
    default:
      assert(0 && "unsupported padding type");
  }
  // start of activation program
  ACT_START(h);
  ACT_INST(h, fpopin0(PALWAYS, VR0), 0);            // VR0 = x&y float indexes, chan 0-7 X, chan 8-15 Y
  ACT_INST(h, fadd(PFIRST0, VR2, SR0), 1);          // VR2 = MAXX
  if (maxx == maxy) { // square dictionary
    if (pad_type == pad_zero) {
      ACT_INST(h, fadd(PALWAYS, VR1, SR2, VR0), 4); // X&Y = 1.0 + X&Y
      ACT_INST(h, frelun(PALWAYS, VR3, VR1, VR2), 6);
      ACT_INST(h, fpushout(PALWAYS, VR3), 8);
    } else if (pad_type == pad_edge) {
      ACT_INST(h, frelun(PALWAYS, VR1, VR0, VR2), 4);
      ACT_INST(h, fpushout(PALWAYS, VR1), 6);
    } else {
      ACT_INST(h, fadd(PFIRST0, VR7, SR2), 2);      // VR7 = MAXX*2 or MAXX*2+1
      ACT_INST(h, trnsp(PALWAYS, VR0, VR1), 4);     // VR0 = X, VR1 = Y
      if (pad_type == pad_mirror) {
          ACT_INST(h, mirror(PALWAYS, VR0, VR0, VR2), 6);
          ACT_INST(h, mirror(PALWAYS, VR1, VR1, VR2), 8);
      } else { // pad_replic
          ACT_INST(h, replic(PALWAYS, VR0, VR0, VR2), 6);
          ACT_INST(h, replic(PALWAYS, VR1, VR1, VR2), 8);
      }
      ACT_INST(h, trnsp(PALWAYS, VR0, VR1), 10);    // transpose back
      ACT_INST(h, fpushout(PALWAYS, VR0), 12);
    }
  } else { // non-square dictionary (TODO: can be optimized for pad_zero & pad_edge cases)
    ACT_INST(h, fadd(PFIRST0, VR3, SR1), 2);        // VR3 = MAXY
    int l = 4;
    if (pad_type == pad_zero) {
      ACT_INST(h, fadd(PALWAYS, VR0, SR2, VR0), l); // X&Y = 1.0 + X&Y
      l += 2;
    }
    ACT_INST(h, trnsp(PALWAYS, VR0, VR1), l);       // VR0 = X, VR1 = Y
    switch (pad_type) {
      case pad_mirror:
        ACT_INST(h, fadd(PALWAYS, VR7, SR2), (l + 2)); // VR7 = MAXX*2
        ACT_INST(h, mirror(PALWAYS, VR0, VR0, VR2), (l + 4));
        ACT_INST(h, fadd(PALWAYS, VR7, SR3), (l + 6)); // VR7 = MAXY*2
        ACT_INST(h, mirror(PALWAYS, VR1, VR1, VR3), (l + 8));
        l += 10;
        break;
      case pad_replic:
        ACT_INST(h, fadd(PALWAYS, VR7, SR2), (l + 2)); // VR7 = MAXX*2+1
        ACT_INST(h, replic(PALWAYS, VR0, VR0, VR2), (l + 4));
        ACT_INST(h, fadd(PALWAYS, VR7, SR3), (l + 6)); // VR7 = MAXY*2+1
        ACT_INST(h, replic(PALWAYS, VR1, VR1, VR3), (l + 8));
        l += 10;
        break;
      default: // edge & zero
        ACT_INST(h, frelun(PALWAYS, VR0, VR0, VR2), (l + 2));
        ACT_INST(h, frelun(PALWAYS, VR1, VR1, VR3), (l + 4));
        l += 6;
    }
    ACT_INST(h, trnsp(PALWAYS, VR0, VR1), l);  // transpose back
    ACT_INST(h, fpushout(PALWAYS, VR0), (l + 2));
  }
  ACT_END(h);
  // end of activation program
}

//
// Bilinear interpolation of grid (gathered by iDMA)
//
void init_grid_blnr(act_hlapi_t& h, bool zerostride) {
  // start of activation program
  ACT_START(h);
  ACT_INST(h, fpopin1(PFIRST2, VR0), 0);         // VR0 = x&y float indexes
  ACT_INST(h, fpopin0(PALWAYS, VR2), 2);         // VR2 = left top
  ACT_INST(h, fpopin0(PALWAYS, VR3), 4);         // VR3 = left bottom
  if (zerostride) {
    ACT_INST(h, fract(PFIRST2, VR0, VR0), 5);    // VR0 = fraction parts (can be calculated here)
  } else {
    ACT_INST(h, bcv(PFIRST2, VR0, VR0), 5);      // VR0 = emulate stride 0 (data already fractional)
  }
  ACT_INST(h, fpopin0(PALWAYS, VR4), 6);         // VR4 = right top
  ACT_INST(h, fadd(PFIRST2, VR1, VR0), 7);       // copy VR0 to VR1
  ACT_INST(h, fpopin0(PALWAYS, VR5), 8);         // VR5 = right bottom
  ACT_INST(h, trnsp(PFIRST2, VR0, VR1), 9);      // transpose, VR0 = fractx, VR1 = fracty
  ACT_INST(h, fsub(PALWAYS, VR3, VR3, VR2), 10); // VR3 = left bottom (VR3) - left top (VR2)
  ACT_INST(h, fsub(PALWAYS, VR5, VR5, VR4), 12); // VR5 = right bottom (VR5) - right top (VR4)
  ACT_INST(h, mpy(PALWAYS, VR3, VR3, VR1), 13);  // VR3 = VR3 * fracty (VR1)
  ACT_INST(h, mpy(PALWAYS, VR5, VR5, VR1), 14);  // VR5 = VR5 * fracty (VR1)
  ACT_INST(h, fadd(PALWAYS, VR6, VR3, VR2), 16); // VR6 = VR3 + left top (VR2)
  ACT_INST(h, fadd(PALWAYS, VR7, VR5, VR4), 18); // VR7 = VR5 + right top (VR4)
  ACT_INST(h, fsub(PALWAYS, VR7, VR7, VR6), 20); // VR7 = right (VR7) - left (VR6)
  ACT_INST(h, mpy(PALWAYS, VR7, VR7, VR0), 22);  // VR7 = VR7 * fractx (VR0)
  ACT_INST(h, fadd(PALWAYS, VR7, VR7, VR6), 26); // VR7 = VR7 + left (VR6)
  ACT_INST(h, fpushout(PALWAYS, VR7), 28);       // out = VR7
  ACT_END(h);
  // end of activation program
}

//
// Make 16b int indexes for gather iDMA and 16b fractional
// weights for bilinear interpolation from 16b float grid
//
void init_grid_decomp(act_hlapi_t& h) {
  // start of activation program
  ACT_START(h);
  ACT_INST(h, fpopin0(PEVEN, VR0), 0);    // VR0 = x&y float indexes, chan 0-7 X, chan 8-15 Y
  ACT_INST(h, fpopin0(PODD, VR1), 1);     // VR1 = x&y float indexes, chan 0-7 X, chan 8-15 Y
  ACT_INST(h, fract(PEVEN, VR2, VR0), 4); // VR2 = fraction parts
  ACT_INST(h, fract(PODD, VR3, VR1), 5);  // VR3 = fraction parts
  ACT_INST(h, ftoi(PEVEN, VR4, VR0), 6);  // VR4 = int X,Y
  ACT_INST(h, ftoi(PODD, VR5, VR1), 7);   // VR5 = int X,Y
  ACT_INST(h, fpushout(PEVEN, VR2), 8);   // VR2 ->
  ACT_INST(h, fpushout(PODD, VR3), 9);    // VR3 ->
  ACT_INST(h, pushout(PEVEN, VR4), 10);   // VR4 ->
  ACT_INST(h, pushout(PODD, VR5), 11);    // VR5 ->
  ACT_END(h);
  // end of activation program
}

//
// Make 16b int indexes for gather iDMA from 16b float grid
//
void init_grid_dmaidx(act_hlapi_t& h) {
  h.i.u.op.scl[0] = 1; // SR0 = 1
  h.i.u.op.scl[1] = 0; // SR1 = 0
  // start of activation program
  ACT_START(h);
#if 1
  // Generate one index per out sample (left-top)
  ACT_INST(h, fpopin0(PEVEN, VR0), 0);    // VR0 = x&y float indexes, chan 0-7 X, chan 8-15 Y
  ACT_INST(h, fpopin0(PODD, VR1), 1);     // VR1 = x&y float indexes, chan 0-7 X, chan 8-15 Y
  ACT_INST(h, ftoi(PEVEN, VR2, VR0), 4);  // VR2 = int X,Y
  ACT_INST(h, ftoi(PODD, VR3, VR1), 5);   // VR3 = int X,Y
  ACT_INST(h, pushout(PEVEN, VR2), 6);    // VR2 ->
  ACT_INST(h, pushout(PODD, VR3), 7);     // VR3 ->
#else
  // Generate 4 indices per out sample
  ACT_INST(h, add(PFIRST0, VR0, SR0), 0);        // VR0 = 1
  ACT_INST(h, add(PFIRST0, VR1, SR1), 2);        // VR1 = 0
  ACT_INST(h, trnsp(PFIRST0, VR0, VR1), 4);      // VR0 = X{1}/Y{0}
  ACT_INST(h, add(PFIRST0, VR6, VR0), 6);        // VR6 <- VR0 (X{1}/Y{0})
  ACT_INST(h, fpopin0(PALWAYS, VR1), 7);         // VR1 = x&y float indexes, chan 0-7 X, chan 8-15 Y
  ACT_INST(h, sub(PFIRST0, VR7, SR0, VR0), 8);   // VR7 = X{0}/Y{1}
  ACT_INST(h, ftoi(PALWAYS, VR2, VR1), 10);      // VR2 = X,Y
  ACT_INST(h, pushout(PALWAYS, VR2), 12);        // VR2 ->
  ACT_INST(h, add(PALWAYS, VR3, VR6, VR2), 13);  // VR3 = X+1,Y
  ACT_INST(h, pushout(PALWAYS, VR3), 14);        // VR3 ->
  ACT_INST(h, add(PALWAYS, VR4, VR7, VR2), 15);  // VR4 = X,Y+1
  ACT_INST(h, pushout(PALWAYS, VR4), 16);        // VR4 ->
  ACT_INST(h, add(PALWAYS, VR5, VR6, VR4), 17);  // VR5 = X+1,Y+1
  ACT_INST(h, pushout(PALWAYS, VR5), 18);        // VR5 ->
#endif
  ACT_END(h);
  // end of activation program
}
