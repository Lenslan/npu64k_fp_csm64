##########################################################################################
# Setup
NCONFIG           ?= nu4500.novpx
RTLA_TECH         ?= 12
export TOP_MODULE ?= npu_slice_top
TECH               = ts$(RTLA_TECH)

# source files for synthesize
export NPU_HOME_RLS
export SYN_MANIFEST ?= ${NPU_HOME_RLS}/syn/spg_manifest
# constraints
export SYN_SDC      ?= ${NPU_HOME_RLS}/syn/constraints/$(TOP_MODULE).sdc
LINT_GOALS   ?= lint/lint_rtl_enhanced,cdc/clock_reset_integrity,cdc/cdc_verify_struct,cdc/cdc_abstract,rdc/rdc_verify_struct,lint/lint_abstract
#LINT_GOALS   += dft/dft_scan_ready,dft/dft_best_practice,dft/dft_bist_ready,dft/dft_dsm_best_practice,dft/dft_dsm_random_resistance,dft/dft_abstract
export LC_SPYG_HOME      := ${NPU_HOME_RLS}/lint/spyglass_$(TOP_MODULE)
export LC_SPYG_SETUP     := $(LC_SPYG_HOME)/scripts/spyglass
# add the virtual clocks for CDC/RDC: P10019796-58225
export NPU_LINT_VIRT_CLK := 1


all: spyglass
spyglass-prep:
	cp -f ${NPU_HOME_RLS}/syn/constraints/$(TOP_MODULE).sdc ./constraints.sdc
	cd scripts/spyglass && ln -vsf ../../../../syn/constraints/sgdc/{$(TOP_MODULE)_quasi_static.sgdc,$(TOP_MODULE)_resets.sgdc,$(TOP_MODULE).sgdc} ./
	cp -f ${NPU_HOME_RLS}/config/manifest.rtl.flat ${NPU_HOME_RLS}/syn/spg_manifest
	sed -i "1i\+incdir+${NPU_HOME_RLS}/verilog/RTL" ${NPU_HOME_RLS}/syn/spg_manifest
	ls -1 ${NPU_HOME}/arch/npu_top/lint/CLKGATE_cell_model_sim.sv >> ${NPU_HOME_RLS}/syn/spg_manifest
	ln -sf ${NPU_HOME_RLS}/ram_sizes.txt $(LC_SPYG_HOME)/
	cd $(LC_SPYG_HOME) && $(LC_SPYG_SETUP)/create_stopunit.tcl
	cd $(LC_SPYG_HOME) && $(LC_SPYG_SETUP)/create_sglib.tcl
	cd $(LC_SPYG_HOME) && $(LC_SPYG_SETUP)/prepend_sglib.tcl $(LC_SPYG_SETUP)/sglib_list.f
spyglass: spyglass-prep
	cd $(LC_SPYG_HOME) && spyglass -batch -project $(LC_SPYG_SETUP)/npu.prj  -goals "$(LINT_GOALS)" | tee -i spyglass.log

spyglass-gui: spyglass-prep
	cd $(LC_SPYG_HOME) && spyglass        -project $(LC_SPYG_SETUP)/npu.prj  -goals "$(LINT_GOALS)" | tee -i spyglass.log

spyglass-debug:
	cd $(LC_SPYG_HOME) && spyglass        -project $(LC_SPYG_SETUP)/npu.prj &

