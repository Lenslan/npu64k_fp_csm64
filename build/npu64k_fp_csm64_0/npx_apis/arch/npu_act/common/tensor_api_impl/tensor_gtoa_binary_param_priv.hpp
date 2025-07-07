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

protected:
gtoa_act_params_impl_shapes shapes;  // buffer shapes
act_bin_op_t                op;      // binary operation to perform
aoffset_t                   cmax;    // number of channels
broadcast_t                 brdc_f;  // flags for broadcast in which dimension
inline void set_per_channel(aoffset_t p) {
  // multiply by number of per channel parameters
  shapes.pshape[0] = shapes.pshape[0]*p;
}
virtual void init_bin_prog(act_bin_op_t opi, broadcast_t brdc_f) = 0;
