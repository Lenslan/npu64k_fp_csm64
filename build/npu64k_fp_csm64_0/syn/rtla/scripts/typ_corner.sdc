
# FIXME : /scripts/syn_setup.tcl not generated anymore by RDF
set arc_typ_lib_name [exec grep "^set arc_typ_library_name" ${ARC_PRJ_DIR}/scripts/syn_setup.tcl | awk {{$1=$2=""; print $0}} | sed -e "s|\"||g"]
echo $arc_typ_lib_name

set tt_corner [exec grep "^set_operating_conditions" ${ARC_PRJ_DIR}/scripts/power_analysis.tcl  | awk {{print $2}} | sed -e "s|\"||g" ]

echo $tt_corner

set_operating_conditions -library [lindex ${arc_typ_lib_name} 0] ${tt_corner}
set_parasitic_parameters -late_spec ${parasitic3} -early_spec ${parasitic3}


