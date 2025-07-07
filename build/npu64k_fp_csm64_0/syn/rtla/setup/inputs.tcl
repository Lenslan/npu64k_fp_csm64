# Synthesis options & stragegy
puts "Info: Running script [info script]\n"

set DESIGN_NAME "npu_slice_top"
if { [info exists ::env(TOP_MODULE)] } {
  set DESIGN_NAME $::env(TOP_MODULE)
}

# Set the hier option flat/hier
set IMPLEMENTATION  "flat"

# Set the autoungroup
# FIXME: this doesn't appear to be used, conflict with RTLA_UNGROUP ??
set AUTOUNGROUP "true"

# Maximum frequency (set in the SDC)
set NPU_FMAX 1000
if { [info exists ::env(NPU_FMAX) ] } {
    set NPU_FMAX $::env(NPU_FMAX)
}

# Stop after elaboration or SDC read
set ELAB_ONLY 0
if { [info exists ::env(ELAB_ONLY) ] } {
    set ELAB_ONLY $::env(ELAB_ONLY)
}
set SDC_ONLY 0
if { [info exists ::env(SDC_ONLY) ] } {
    set SDC_ONLY $::env(SDC_ONLY)
}

# Restrict to only SVT cells, avoiding LVT
set SVT_ONLY 0
if { [info exists ::env(SVT_ONLY) ] } {
    set SVT_ONLY $::env(SVT_ONLY)
}

# Ungroud and flatten hierarchy for more optimization, hierarchical reports are hard to read
set RTLA_UNGROUP 1
if { [info exists ::env(RTLA_UNGROUP)] } {
    set RTLA_UNGROUP $::env(RTLA_UNGROUP)
}

# Clock tree synthesis
set RTLA_CTS 0
if { [info exists ::env(RTLA_CTS)] } {
    set RTLA_CTS $::env(RTLA_CTS)
}

set RTLA_LVT_RATIO -1
if { [info exists ::env(RTLA_LVT_RATIO)] } {
    set RTLA_LVT_RATIO $::env(RTLA_LVT_RATIO)
}

# Relative floorplan defined in a TCL script
set RTLA_FP_TCL "none"
if { [info exists ::env(RTLA_FP_TCL)] } {
    set RTLA_FP_TCL $::env(RTLA_FP_TCL)
}

set RTLA_PDM_UPF 0
if { [info exists ::env(RTLA_PDM_UPF)] } {
    set RTLA_PDM_UPF $::env(RTLA_PDM_UPF)
}


set RTLA_KEEP_OPEN 0
if { [info exists ::env(RTLA_KEEP_OPEN) ] } {
    set RTLA_KEEP_OPEN $::env(RTLA_KEEP_OPEN)
}


# Set the max number of cores to be used
set max_cores  "8"
if { [info exists ::env(NCORES_HOST) ] } {
    set max_cores $::env(NCORES_HOST)
}

# List the blocks to be implemented in hierarchical flow
set BLOCK_INSTANCES   ""

# Enable DMM will set_current_design_misatch_config to autofix , which will repair and fix the netlist.
set ENABLE_DMM  "false"

# Set the analysis mode to RTL_OPT or EXPLORATION
set MODE "RTL_OPT"

# Set the auto options in RTL_OPT mode
set FLOORPLAN           "auto" ; # auto, def, tcl
set FLOORPLAN_FILE      ""     ; # must speficy for def ot tcl
set UTILIZATION_RATIO   "0.60"
if { ${RTLA_FP_TCL} ne "none" } {
  set FLOORPLAN         "tcl"                ; # auto, def, tcl
  set FLOORPLAN_FILE    "${RTLA_FP_TCL}"     ; # must speficy for def ot tcl
}
puts "Info: FLOORPLAN      ${FLOORPLAN}\n"
puts "Info: FLOORPLAN_FILE ${FLOORPLAN_FILE}\n"

# Implementing the power mesh for the design, mesh is coming from ARChitect flow.
set USE_MESH false

set DFT false

# Set the below variable to constraint the pins at block-level, if left blank RTLA keeps pins at all sides
set pin_constraint_sides  "2"

# Enable register retiming
#  by default it will only happen on the fpu32 modules.
#set_optimize_registers -modules [get_modules *fpu32*]
set REGISTER_RETIME "false"

# Enable DONT USE list of cell
set ENABLE_DONT_USE true

# Try to bypass errors
set BYP_ERR false

# Define any one of the following variables for Exploration mode
set exp_aspect_ratio        [list ]
set exp_utilization         [list ]
set exp_supply_voltage      [list ]
set exp_library             [list ]

