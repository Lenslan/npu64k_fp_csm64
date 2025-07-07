
set parasitic3				"ctypical"
#set layer_map_file($parasitic3) [exec grep "^set layer_map_file" scripts/icc2_rm/rm_icc2_flat_scripts/parasitic_setup.tcl -m1 | awk {{print $3}} | sed -e  "s|\"||g" ]

if { ${TECHNOLOGY}=="16" } {

    set tluplus_file($parasitic3)  "/remote/us01dwt1p097/fab/f101-tsmc/16nm/logic/FFC/common/rules/11m/tluplus/2xa1xd3xe2y2r_mim_ut-alrdl/ver1.0p1a/typical/Tech/typical/cln16ffc_1p11m_2xa1xd3xe2y2r_mim_ut-alrdl_typical.tluplus"
    set layer_map_file($parasitic3)         "/remote/arc/arc6000/libext/stdcell/16FFC/ts16_ffc_lvt_gate_16nm_base/latest/milkyway/tlup/layers.map"

} elseif {  ${TECHNOLOGY}=="07" } {

    set tluplus_file($parasitic3)  "/remote/us01sgnfs00133/libext/stdcell/7FF/cln7_1p13m_1x1xa1ya5y2yy2r_mim_ut-alrdl_cworst.tluplus"
    set layer_map_file($parasitic3) "/remote/arc/arc6000/libext/stdcell/7FF/layers.map"

} elseif {  ${TECHNOLOGY}=="12" } {

    set tluplus_file($parasitic3)  "/remote/us01sgnfs00133/libext/stdcell/12FFC_CPODE/tlup/cln12ffc_1p11m_2xa1xd3xe2y2r_mim_ut-alrdl_cworst.tluplus"
    set layer_map_file($parasitic3) "/remote/arc/arc6000/libext/stdcell/12FFC_CPODE/tlup/layers.map"

} elseif {  ${TECHNOLOGY}=="28" } {

    set tluplus_file($parasitic3)  "/remote/arc/arc6000/libext/stdcell/28HPC/ts28_hpc_lvt_gate_30nm_hd_base/latest/milkyway/tlup/tsmc_cln28hpm_M10_7x2z_typical_0.5.tlup"
    set layer_map_file($parasitic3) "/remote/arc/arc6000/libext/stdcell/28HPC/ts28_hpc_lvt_gate_30nm_hd_base/latest/milkyway/tlup/layers.map"

} elseif {  ${TECHNOLOGY}=="GF22" } {

    set tluplus_file($parasitic3)  "/remote/us01sgnfs00133/libext/stdcell/GF22FDX/22fdsoi_10M_2Mx_6Cx_2Ix_LBthick_nominal_detailed.tluplus"
    set layer_map_file($parasitic3) "/remote/arc/arc6000/libext/stdcell/GF22FDX/layers.map"
}

#
#
#########################################
### Read parasitic files
#########################################
### Read in the TLUPlus files first.
##  Later on in the corner constraints, you can then refer to the parasitic models.
#foreach p [array name tluplus_file] {  
#	echo "RM-info : read_parasitic_tech -tlup $tluplus_file($p) -layermap $layer_map_file($p) -name $p"
#	read_parasitic_tech -tlup $tluplus_file($p) -layermap $layer_map_file($p) -name $p
#}

