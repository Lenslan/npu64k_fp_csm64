create_port -direction in SE
create_port -direction in SI1
create_port -direction in SI2
create_port -direction in SI3
create_port -direction in SI4

create_port -direction in SI5
create_port -direction in SI6

create_port -direction out SO1
create_port -direction out SO2
create_port -direction out SO3
create_port -direction out SO4
create_port -direction out SO5
create_port -direction out SO6
create_port -direction in TM

#place_pins -self
set_dft_signal -view existing -type ScanClock -port clk -timing [list 45 55]
set_dft_signal -view existing -type Reset -port rst_a -active_state 0
set_dft_signal -view spec -type ScanDataIn -port SI1
set_dft_signal -view spec -type ScanDataIn -port SI2

set_dft_signal -view spec -type ScanDataIn -port SI3
set_dft_signal -view spec -type ScanDataIn -port SI4
set_dft_signal -view spec -type ScanDataIn -port SI5
set_dft_signal -view spec -type ScanDataIn -port SI6

set_dft_signal -view spec -type ScanEnable -port SE
set_dft_signal -view spec -type ScanDataOut -port SO1
set_dft_signal -view spec -type ScanDataOut -port SO2
set_dft_signal -view spec -type ScanDataOut -port SO3
set_dft_signal -view spec -type ScanDataOut -port SO4
set_dft_signal -view spec -type ScanDataOut -port SO5
set_dft_signal -view spec -type ScanDataOut -port SO6
set_dft_signal -type TestMode -port TM

set_scan_configuration -chain_count 4 -clock_mixing mix_clocks
#set_dft_configuration -scan_compression enable
#set_scan_compression_configuration -chain_count 6
define_test_mode Internal_scan                  -usage scan                     -encoding "TM 0 "
#define_test_mode ScanCompression_mode           -usage scan_compression         -encoding "TM 1 "
create_test_protocol
list_test_models
