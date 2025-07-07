current_goal lint/lint_rtl
# Lower the default violation threshold from 500 to 200 for logicDepth rule
#set_parameter  delaymax 200 
# Create a logicDepth histogram
set_goal_option addrules        LogicHist;
set_goal_option addrules        DumpHist;
set_goal_option report {LDHist moresimple}
current_goal none

current_goal cdc/cdc_verify_struct
set_parameter enable_sync yes
set_parameter enable_mux_sync recirculation
set_parameter enable_multiflop_sync yes
current_goal none

# Enable reset de-assertion synchronization check
#current_goal cdc/cdc_verify_struct
#set_goal_option addrules { Ar_resetcross01 Ar_resetcross_matrix01 }
#set_goal_option report {Clock-Reset-Detail moresimple}
#current_goal none

#current_goal constraints/sdc_check
#current_goal none
