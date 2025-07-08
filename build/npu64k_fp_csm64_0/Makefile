ifeq ($(wildcard $(strip $(NPU_HOME_RLS))),)
    $(error Environment variable NPU_HOME_RLS is not defined, source the setup script)
endif
include $(NPU_HOME_RLS)/build_config.mk

NCORES            ?= ${NCORES_HOST}
LBUILD            ?= sim
BUILD             ?= ${NPU_HOME_RLS}/$(LBUILD)
NPU_RTL_SIMULATOR ?= 0
RTL_SIMULATOR     ?= $(NPU_RTL_SIMULATOR)

VERDI             ?= 1
TB_MDB            ?= 0
TB_SIM_MON        ?= 1
TB_PDM            ?= $(NPU_HAS_POWERDOMAINS)
TB_RDF            ?= 0

ARCH               = ${NPU_HOME_RLS}/arch
COMP_DEFS         :=
TOP_MODULE        ?= core_chip
export TB_MDB

# common flags
ifeq ($(TB_RDF),0)
  COMP_DEFS     += +define+ABV_ON +define+TB_MSS +define+NPU_CLN_FPGA_SRAM=0 +define+NPU_FPGA_NOT_REPLACE_CLKGATE=0
  SIM_SRC_LISTS = ${NPU_HOME_RLS}/config/manifest.flat
else
  COMP_DEFS     += +define+ABV_ON +define+TB_MSS
  SIM_SRC_LISTS = ${NPU_HOME_RLS}/config/rdf-manifest.flat
endif
SYN_SRC_LISTS = ${NPU_HOME_RLS}/syn/manifest.rtl.flat
SRC_PATHS     = +incdir+${NPU_HOME_RLS}/verilog/RTL +incdir+${NPU_HOME_RLS}/verilog +incdir+${NPU_HOME_RLS}/tb
SRC_PATHS    += +incdir+${SYNOPSYS}/dw/sim_ver -y ${SYNOPSYS}/dw/sim_ver
ifeq ($(TB_SIM_MON),1)
  COMP_DEFS   += +define+TB_SIM_MON=1
endif
ifeq ($(TB_MDB),1)
  COMP_DEFS   += +define+TB_MDB
else
  ifeq ($(TB_RDF),0)
    COMP_DEFS   += +define+FPGA_INFER_MEMORIES +define+FPGA_INFER_MEMORIES_TMP
  endif
endif
ifneq ($(VERDI),0)
  COMP_DEFS   += +define+TB_VERDI
endif
COMP_DEFS     += +define+DWC_DISABLE_CDC_METHOD_REPORTING
COMP_DEFS     += +define+SFTY_ERR_INJ_ON=1 +define+SAFETY_COMMON_ENABLE

ifeq ($(RTL_SIMULATOR),0)
#= VCS
XPROP_EN        ?= 0
VCS_COMP_OPTS    = +v2k +libext+.v+.sv -sverilog -assert svaext -full64 +vcs+lic+wait +lint=TFIPC-L -override_timescale=1ns/10ps -l vcs.log
VCS_ELAB_OPTS    = -debug_access+all -debug_region+cell+encrypt
NPU_VCS_PLI     ?= ${NPU_HOME_RLS}/lib
ifneq ($(XPROP_EN),0)
  VCS_COMP_OPTS += -xprop=${NPU_HOME_RLS}/tb/core_archipelago_xprop.cfg
endif
ifneq ($(VERDI),0)
  VCS_COMP_OPTS   += -kdb
endif
WAVE_OPTS     = +vcs+vcdpluson

ifeq ($(TB_PDM),1)
  VCS_COMP_OPTS   += +define+TB_PDM +define+UPF
  VCS_ELAB_OPTS   += -upf ${NPU_HOME_RLS}/syn/constraints/npu_top_for_vcs.upf -power_top npu_top
endif
#ifeq ($(TB_MDB),1)
  VCS_COMP_OPTS   += -P ${NPU_HOME_RLS}/tb/mdb/arc_vcs_pli_table -L $(NPU_VCS_PLI) 
#endif
VCS_COMP_OPTS += $(COMP_DEFS)
endif


ifeq ($(RTL_SIMULATOR),1)
#= Xcelium 
XC_COMP_OPTS  = -licqueue -64bit -access +rcw  -vlog_ext +.vh,.def  -sysv_ext +.svh,.sv +libext+.v+.sv -sv -override_timescale -timescale 1ns/10ps -l xc.log -dpiheader xrun_hdrs.h
XC_COMP_OPTS += -loadpli1 libarc-nc-pli-verilog:register_arc_user_tasks
XC_COMP_OPTS += $(subst +define+,-define ,$(COMP_DEFS))
XC_COMP_OPTS += $(subst +incdir+,-incdir ,$(SRC_PATHS))
XC_COMP_OPTS += -define NPU_SIM_NVCS=1
XC_SRC_LIST  := $(SIM_SRC_LISTS)
endif

ifeq ($(RTL_SIMULATOR),2)
#= ModelSim
MODELSIM_COMP_OPTS  = -64 -work worklib +acc=npr +libext+.v+.sv -sv -mfcu -override_timescale=1ns/10ps -l modelsim.log -dpiheader sv2c.h
MODELSIM_COMP_OPTS += +define+NPU_SIM_NVCS=1 $(COMP_DEFS) $(SRC_PATHS)
MODELSIM_COMP_OPTS += -suppress vlog-2720
WAVE_OPTS           = +vcs+vcdpluson
endif

# The full list of available tests are in ${NPU_HOME_RLS}/tests/ccts/cct_list.mk
CCTS      ?= all

NPU_DEV ?= 0


.PHONY: fix-manifest syn-manifest compile waves test-all

all:
	@echo "INFO: please specify a target: compile waves test"

fix-manifest: config/.manifest-fixed
config/.manifest-fixed: ${NPU_HOME_RLS}/config/manifest.rtl.flat ${NPU_HOME_RLS}/config/manifest.flat
	sed -i 's#$${NPU_HOME}/build#$${NPU_HOME_RLS}#g' $^
	touch $@

ifeq ($(RTL_SIMULATOR),0)
compile: config/.manifest-fixed
	cd $(LBUILD) && vcs -j$(NCORES) $(VCS_COMP_OPTS) $(VCS_ELAB_OPTS) $(SRC_PATHS) -f $(SIM_SRC_LISTS) -top npu_tb_top -o simv
	@echo "TB_MDB=$(TB_MDB)" > $(LBUILD)/vcs_bld.mk
	@echo "VERDI=$(VERDI)" >> $(LBUILD)/vcs_bld.mk
	@echo "TB_SIM_MON=$(TB_SIM_MON)" >> $(LBUILD)/vcs_bld.mk
waves: config/.manifest-fixed
	cd $(LBUILD) && vcs -j$(NCORES) $(VCS_COMP_OPTS) $(VCS_ELAB_OPTS)  $(WAVE_OPTS) $(SRC_PATHS) -f $(SIM_SRC_LISTS) -top npu_tb_top -o simv
	@echo "TB_MDB=$(TB_MDB)" > $(LBUILD)/vcs_bld.mk
	@echo "VERDI=$(VERDI)" >> $(LBUILD)/vcs_bld.mk
	@echo "TB_SIM_MON=$(TB_SIM_MON)" >> $(LBUILD)/vcs_bld.mk
unit-compile: config/.manifest-fixed
	cd $(LBUILD) && grep -v '\/\/' ${NPU_HOME_RLS}/config/manifest.rtl.flat | xargs -I{} vlogan -nc $(VCS_COMP_OPTS) $(SRC_PATHS) {}
endif

ifeq ($(RTL_SIMULATOR),1)
compile: config/.manifest-fixed
	@echo "COMP_OPTS   : $(COMP_OPTS)"
	@echo "XC_COMP_OPTS: $(XC_COMP_OPTS)"
	cd $(LBUILD) && xrun -c -f $(XC_SRC_LIST) $(XC_COMP_OPTS) -top npu_tb_top
waves: compile
unit-compile: config/.manifest-fixed
	cd $(LBUILD) && grep -v '\/\/' ${NPU_HOME_RLS}/config/manifest.rtl.flat | xargs -I{} xrun -compile $(XC_COMP_OPTS) {}
endif

ifeq ($(RTL_SIMULATOR),2)
compile: config/.manifest-fixed
	cd $(LBUILD) && vlog $(MODELSIM_COMP_OPTS) -f $(SIM_SRC_LISTS)
waves: compile
endif


# tests
CCT_PWR_EN ?= 0
CCT_ADV_EN ?= 0
CCT_EN     := CCT_PWR_EN=$(CCT_PWR_EN) CCT_ADV_EN=$(CCT_ADV_EN)
DUMP_SAIF  ?= 0
CCT_OPTS    = CCTS=$(CCTS) RLS=$(NPU_HOME_RLS) TB_MDB=$(TB_MDB) VERDI=$(VERDI) DUMP_SAIF=$(DUMP_SAIF) $(CCT_EN)
list-ccts:
	$(MAKE) -C ${NPU_HOME_RLS}/tests/ccts -j$(NCORES) $(CCT_OPTS) list
build-ccts:
	$(MAKE) -C ${NPU_HOME_RLS}/tests/ccts -j$(NCORES) $(CCT_OPTS) build
run-ccts:
ifeq ($(TB_MDB),0)
	$(MAKE) -C ${NPU_HOME_RLS}/tests/ccts -j$(NCORES) $(CCT_OPTS) run
	$(MAKE) -C ${NPU_HOME_RLS}/tests/ccts -j1         $(CCT_OPTS) report
else
	$(MAKE) -C ${NPU_HOME_RLS}/tests/ccts -j1         $(CCT_OPTS) run
endif
clean-ccts:
	$(MAKE) -C ${NPU_HOME_RLS}/tests/ccts -j1         $(CCT_OPTS) clean
report-ccts:
	$(MAKE) -C ${NPU_HOME_RLS}/tests/ccts -j1         $(CCT_OPTS) report

clean:
	-rm -rf $(LBUILD)/*
	-rm -rf ${NPU_HOME_RLS}/{config/.manifest-fixed,syn/.rdf-replaced}

# syn
NPU_HOME_DEV     ?= $(abspath ${NPU_HOME_RLS}/../npu)
MLIB_HOME        ?= i_dont_know
RTLA_TECH        ?= 07
ELAB_ONLY        ?= 0
SDC_ONLY         ?= 0
FMAX             ?= 1000
SYN_MANIFEST     ?= $(SYN_SRC_LISTS)
AM_VM_RAM_MACROS ?= $(MLIB_HOME)/$(NCONFIG)/npu_amvm/build_mem_ts$(RTLA_TECH)
ARC_RDF_PRJ      ?= $(MLIB_HOME)/$(NCONFIG)/npu_arc
CLN_RDF_PRJ      ?= ${NPU_HOME}/build/verilog/npu_cln_rdf
ifeq "$(MLIB_HOME)" "i_dont_know"
  CLN_RDF_LIB_PRJ  ?= ${NPU_HOME}/npu_cln_archi
else
  CLN_RDF_LIB_PRJ ?= $(MLIB_HOME)/$(NCONFIG)/npu_cln_archi
endif
VPX_RDF_PRJ      ?= $(MLIB_HOME)/$(NCONFIG)/vpx
SYN_OPTS         ?= NPU_HOME_DEV=$(NPU_HOME_DEV) TOP_MODULE=$(TOP_MODULE) RTLA_TECH=$(RTLA_TECH) FMAX=$(FMAX) ELAB_ONLY=$(ELAB_ONLY) SDC_ONLY=$(SDC_ONLY)
SYN_OPTS         += AM_VM_RAM_MACROS=$(AM_VM_RAM_MACROS) ARC_RDF_PRJ=$(ARC_RDF_PRJ) CLN_RDF_PRJ=$(CLN_RDF_PRJ) CLN_RDF_LIB_PRJ=$(CLN_RDF_LIB_PRJ)
SYN_OPTS         += VPX_RDF_PRJ=$(VPX_RDF_PRJ)
SYN_OPTS         += SYN_MANIFEST=$(SYN_MANIFEST) NPU_DEV=$(NPU_DEV)
LOCAL_MEM_LIBS   ?= $(abspath ${NPU_HOME_RLS}/../mem_mw_libs)
dc: config/.manifest-fixed syn/.rdf-replaced
	@-rm -rf syn/dc_$(TOP_MODULE)
	cp -rf syn/dc syn/dc_$(TOP_MODULE)
	cd syn/dc_$(TOP_MODULE) && find ../constraints -name "$(TOP_MODULE)*.sdc" | xargs -I{} ln -sf {} ./constraints.sdc
	cd syn/dc_$(TOP_MODULE) && make $(SYN_OPTS) LOCAL_MEM_LIBS=$(LOCAL_MEM_LIBS) all

syn-manifest replace-rdf: syn/.rdf-replaced
syn/.rdf-replaced:
	bin/restore_rdf_replacement.sh $(NCONFIG)
	touch $@

ifneq ($(NPU_DEV),0)
ARCHITT_PRJ ?=
#==Targets for Internal Development
CLK_NS := $(shell echo "scale=2; 1000 / $(FMAX)" | bc -l | awk '{printf "%-.2f",$$0}')
#CLK_NS := 10
#RDF_VCS_DEFS := +define+SYNTHESIS=1 +define+NPU_REPLACE_CLKGATE_enabled=1 +define+VIRAGE_FAST_VERILOG=1 +define+CLK_NS=$(CLK_NS)
RDF_VCS_DEFS := +define+SYNTHESIS=1 +define+NPU_REPLACE_CLKGATE_enabled=1 +define+VIRAGE_FAST_VERILOG=1 +define+CLK_NS=$(CLK_NS)
#RDF_VCS_DEFS += +define+CLK_NS=$(CLK_NS)
RDF_VCS_DEFS += +define+NPU_USE_ASIC_MEMORIES=1
RDF_VCS_DEFS += +define+FPGA_INFER_MEMORIES +define+FPGA_INFER_MEMORIES_TMP
manifest-stl: config/.manifest-fixed
	sed -i 's#\(.*npuarc_SAFETY_AINP_SYNC_STAGES\)#//\1#g' ${NPU_HOME_RLS}/verilog/RTL/npuarc_hsls_defines.v                  || true
	sed -i 's#\(.*npuarc_SAFETY_AINP_SYNC_STAGES\)#//\1#g' ${NPU_HOME_RLS}/verilog/RTL/npuarc_hsls_exported_defines.v         || true
	sed -i 's#\(.*Mem_npu_*_bank\)#//\1#g'                 ${NPU_HOME_RLS}/verilog/RTL/{npu_defines.v,npu_exported_defines.v} || true
	sed -i 's#\(.*NPU_REPLACE_CLKGATE\)#//\1#g'            ${NPU_HOME_RLS}/verilog/RTL/{npu_defines.v,npu_exported_defines.v} || true
	sed -i 's#\(.*CellLibraryClockGate\)#//\1#g'           ${NPU_HOME_RLS}/verilog/RTL/{npu_defines.v,npu_exported_defines.v} || true
	sed -i '/"npu_rdf_defines.sv"/d'                       ${NPU_HOME_RLS}/verilog/RTL/{npu_defines.v,npu_exported_defines.v} || true
	sed -i '1i \`include "npu_rdf_defines.sv"'             ${NPU_HOME_RLS}/verilog/RTL/{npu_defines.v,npu_exported_defines.v} || true
	cp -f ${NPU_HOME_RLS}/config/npu_rdf_defines.sv        ${NPU_HOME_RLS}/verilog/RTL/
	cp -f ${NPU_HOME_RLS}/config/manifest.flat                                                          $(SIM_SRC_LISTS)
	@echo ""                                                                                         >> $(SIM_SRC_LISTS)
	([[ -d ${AM_VM_RAM_MACROS} ]] && find ${AM_VM_RAM_MACROS}/*/compout/views/ -name "mem_*.v"  | grep -v 'stim\|_func\|_core\|_stub\|_netlist\|_ikos' >> $(SIM_SRC_LISTS)) || true
	([[ -d ${AM_VM_RAM_MACROS} ]] && ls ${AM_VM_RAM_MACROS}/rtl/mem_*.v                              >> $(SIM_SRC_LISTS)) || true
	([[ -d ${ARC_RDF_PRJ}      ]] && ls ${ARC_RDF_PRJ}/build/verilog/mem_*.v                         >> $(SIM_SRC_LISTS)) || true
	([[ -d ${CLN_RDF_LIB_PRJ}  ]] && ls ${CLN_RDF_LIB_PRJ}/build/verilog/mem_*.v                     >> $(SIM_SRC_LISTS)) || true
	([[ -d ${VPX_RDF_PRJ}      ]] && ls ${VPX_RDF_PRJ}/build/verilog/mem_*.v                         >> $(SIM_SRC_LISTS)) || true
	find syn/rdf_replacement -name *.*v | grep -v DWbb | xargs -I{} ln -sf ../../{} verilog/RTL/
	@echo ${NPU_HOME}/arch/npu_top/lint/CLKGATE_cell_model_sim.sv                                    >> $(SIM_SRC_LISTS)
compile-stl: manifest-stl
	cd $(LBUILD) && vcs -j$(NCORES) $(VCS_COMP_OPTS) $(VCS_ELAB_OPTS) $(RDF_VCS_DEFS) $(SRC_PATHS) -file $(SIM_SRC_LISTS) -top core_chip -o simv
waves-stl: manifest-stl
	cd $(LBUILD) && vcs -j$(NCORES) $(VCS_COMP_OPTS) $(VCS_ELAB_OPTS) $(WAVE_OPTS) $(RDF_VCS_DEFS) $(SRC_PATHS) -file $(SIM_SRC_LISTS) -top core_chip -o simv

manifest-rtla-power:config/.manifest-fixed
	sed -i 's#\(.*npuarc_SAFETY_AINP_SYNC_STAGES\)#//\1#g' ${NPU_HOME_RLS}/verilog/RTL/npuarc_hsls_defines.v                  || true
	sed -i 's#\(.*npuarc_SAFETY_AINP_SYNC_STAGES\)#//\1#g' ${NPU_HOME_RLS}/verilog/RTL/npuarc_hsls_exported_defines.v         || true
	sed -i 's#\(.*Mem_npu_*_bank\)#//\1#g'                 ${NPU_HOME_RLS}/verilog/RTL/{npu_defines.v,npu_exported_defines.v} || true
	sed -i 's#\(.*NPU_REPLACE_CLKGATE\)#//\1#g'            ${NPU_HOME_RLS}/verilog/RTL/{npu_defines.v,npu_exported_defines.v} || true
	sed -i 's#\(.*CellLibraryClockGate\)#//\1#g'           ${NPU_HOME_RLS}/verilog/RTL/{npu_defines.v,npu_exported_defines.v} || true
	sed -i '/"npu_rdf_defines.sv"/d'                       ${NPU_HOME_RLS}/verilog/RTL/{npu_defines.v,npu_exported_defines.v} || true
	sed -i '1i \`include "npu_rdf_defines.sv"'             ${NPU_HOME_RLS}/verilog/RTL/{npu_defines.v,npu_exported_defines.v} || true
	cp -f ${NPU_HOME_RLS}/config/npu_rdf_defines.sv        ${NPU_HOME_RLS}/verilog/RTL/
	cp -f ${NPU_HOME_RLS}/config/manifest.flat                                                          $(SIM_SRC_LISTS)
	@echo ""                                                                                          >> $(SIM_SRC_LISTS)
	([[ -d ${AM_VM_RAM_MACROS} ]] && ls ${AM_VM_RAM_MACROS}/*/compout/views/*/Typical*/*.v | grep -v stim  >> $(SIM_SRC_LISTS)) || true
	([[ -d ${AM_VM_RAM_MACROS} ]] && ls ${AM_VM_RAM_MACROS}/rtl/mem_*.v                               >> $(SIM_SRC_LISTS)) || true
	([[ -d ${ARC_RDF_PRJ}      ]] && ls ${ARC_RDF_PRJ}/build/verilog/mem_*.v                          >> $(SIM_SRC_LISTS)) || true
	([[ -d ${CLN_RDF_LIB_PRJ}  ]] && ls ${CLN_RDF_LIB_PRJ}/build/verilog/mem_*.v                      >> $(SIM_SRC_LISTS)) || true
	([[ -d ${VPX_RDF_PRJ}      ]] && ls ${VPX_RDF_PRJ}/build/verilog/mem_*.v                          >> $(SIM_SRC_LISTS)) || true
	#find syn/rdf_replacement -name *.*v | grep -v DWbb | xargs -I{} ln -sf ../../{} verilog/RTL/
	@echo ${NPU_HOME}/arch/npu_top/lint/CLKGATE_cell_model_sim.sv                                     >> $(SIM_SRC_LISTS)
compile-rtla-power: manifest-rtla-power
	cd $(LBUILD) && vcs -j$(NCORES) $(VCS_COMP_OPTS) $(VCS_ELAB_OPTS) $(RDF_VCS_DEFS) $(SRC_PATHS) -file $(SIM_SRC_LISTS) -top npu_tb_top -o simv
waves-rtla-power: manifest-rtla-power
	cd $(LBUILD) && vcs -j$(NCORES) $(VCS_COMP_OPTS) $(VCS_ELAB_OPTS) $(WAVE_OPTS) $(RDF_VCS_DEFS) $(SRC_PATHS) -file $(SIM_SRC_LISTS) -top npu_tb_top -o simv

#- run RTL-Architect(synthesize to PR)
rtla: config/.manifest-fixed syn/.rdf-replaced
	@-rm -rf syn/rtla_$(TOP_MODULE)
	cp -rf syn/rtla syn/rtla_$(TOP_MODULE)
	cd syn/rtla_$(TOP_MODULE) && find ../constraints -name "$(TOP_MODULE).sdc" | xargs -I{} ln -sf {} ./constraints.sdc
ifneq ($(ARCHITT_PRJ),)
	[[ -e syn/.architt-updated ]] || cp -f ${NPU_HOME}/config/$(NCONFIG)/*.sv $(ARCHITT_PRJ)/build/verilog/RTL/
	[[ -e syn/.architt-updated ]] || ${NPU_HOME}/iplib/packing/bin/ncp_patch_architt_rtl.sh $(ARCHITT_PRJ)
	touch syn/.architt-updated
endif
	cd syn/rtla_$(TOP_MODULE) && make $(SYN_OPTS) rtla
rtla-view:
	cd syn/rtla_$(TOP_MODULE) && make $(SYN_OPTS) view

rtla-power rtla_power:
	cd syn/rtla_$(TOP_MODULE) && make $(SYN_OPTS) $@

#- generate MilkyWay Libs for dc
include ${NPU_HOME_RLS}/syn/.npu_dev_mlib_paths.mk
$(LOCAL_MEM_LIBS)/.done:
	mkdir -p $(LOCAL_MEM_LIBS)
	make -C ${NPU_HOME_RLS}/syn/dc $(SYN_OPTS) LOCAL_MEM_LIBS=$(LOCAL_MEM_LIBS) dc-mw-libs
	touch $@
dc-mw-libs: $(LOCAL_MEM_LIBS)/.done

spyglass spyglass-gui spyglass-debug: config/.manifest-fixed
	@-rm -rf lint/spyglass_$(TOP_MODULE)
	cp -rf lint/spyglass lint/spyglass_$(TOP_MODULE)
	#cd lint/spyglass_$(TOP_MODULE) && cp -f ${NPU_HOME_RLS}/syn/constraints/$(TOP_MODULE).sdc ./constraints.sdc
	cd lint/spyglass_$(TOP_MODULE) && make $(SYN_OPTS) $@

#- clean up
distclean:
	-${NPU_HOME_RLS}/../npu/iplib/packing/bin/ncp_release_cleanup.sh ${NPU_HOME_RLS}
endif

