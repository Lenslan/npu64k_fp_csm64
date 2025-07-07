puts "Info: Loading setup/setup.tcl ..."
source ./setup/setup.tcl

puts "Info: Opening library ${DESIGN_LIBRARY}"
open_lib ${DESIGN_LIBRARY} -ref_libs_for_edit

set prjblocks [get_blocks -quiet -all $DESIGN_LIBRARY:$DESIGN_NAME]
puts "Blocks available:"
foreach_in_col bl $prjblocks { puts "  [get_object_name $bl]" }

puts "Info: opening block $DESIGN_NAME"
open_block $DESIGN_NAME -ref_libs_for_edit
link_block

start_gui

