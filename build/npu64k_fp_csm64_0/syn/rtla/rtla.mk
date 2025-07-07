# Synopsys RTL Architect

##########################################################################################
#NPU_SRC_HOME  := ${NPU_HOME}
#NPU_BLD_HOME  := ${NPU_HOME}/build
RTLA_PDM_UPF   ?= 0
RTLA_LVT_RATIO ?= -1
RTLA_FP_TCL    ?= none

export ARC_RDF_PRJ AM_VM_RAM_MACROS CLN_RDF_PRJ CLN_RDF_LIB_PRJ VPX_RDF_PRJ
export RTLA_TECH TOP_MODULE
export RTLA_UNGROUP RTLA_CTS RTLA_PDM_UPF RTLA_LVT_RATIO RTLA_FP_TCL
export SYN_MANIFEST SYN_SDC ELAB_ONLY SDC_ONLY SVT_ONLY
export NPU_HOME_DEV
export DESIGN_NAME=$(TOP_MODULE)

export FMAX
export NPU_SLICE_FMAX=$(FMAX)
export NPU_CORE_FMAX=$(FMAX)
export NPU_TOP_FMAX=$(FMAX)
export CORE_ARCHIPELAGO_FMAX=$(FMAX)
export NPU_FMAX=$(FMAX)
export CLOCK_FREQ=$(FMAX)


TIMESTAMP    := $(shell date +%Y%m%d%H%M%S)
NPU_REV      := $(shell cd $(NPU_HOME) && git rev-parse --short HEAD)
NPU_DEPS_REV := $(shell cd $(NPU_DEPS) && git rev-parse --short HEAD)
REV          := $(NPU_REV)_$(NPU_DEPS_REV)
SUFFIX := _$(NCONFIG)_$(RTLA_TECH)nm_$(FMAX)Mhz
#SUFFIX := _$(NCONFIG)_$(RTLA_TECH)nm_$(FMAX)Mhz_$(REV)

LOGS_DIR  = ./logs$(SUFFIX)
export LOGS_DIR

WORK_DIR  = ./work$(SUFFIX)
export WORK_DIR

REPORTS_DIR = ./reports$(SUFFIX)
export REPORTS_DIR

## ARCv3 Cluster Network
#CLN_BLD = ${NPU_DEPS}/arcv3cln/build/${NCONFIG}
#export CLN_BLD

#RTLA_EXEC = /u/nwtnmgr/image/Q-2019.12-SP-DEV/latest/Testing/bin/rtl_shell
#RTLA_EXEC = /u/nwtnmgr/image/R-2020.09-SP3-SP4-SP5/D20210131_6210514/Testing/bin/rtl_shell
RTLA_EXEC = rtl_shell
RTLA_SETTINGS  = NPU_TOP_MODULE=$(NPU_TOP_MODULE) FMAX=$(FMAX) RTLA_TECH=$(RTLA_TECH)
RTLA_SETTINGS += ARC_RDF_PRJ=$(ARC_RDF_PRJ) AM_VM_RAM_MACROS=$(AM_VM_RAM_MACROS)
RTLA_SETTINGS += CLN_RDF_PRJ=$(CLN_RDF_PRJ) CLN_RDF_LIB_PRJ=$(CLN_RDF_LIB_PRJ) VPX_RDF_PRJ=$(VPX_RDF_PRJ)

###############################################################################

.PHONY: rtla setup run_all clean clean_all gen_manifest

help:
	@echo "Help"
	@echo "  NCONFIG = $(NCONFIG)"
	@echo "  RTLA_TECH = $(RTLA_TECH)"
	@echo "  FMAX = $(FMAX)"
	@echo "  LOGS_DIR = $(LOGS_DIR)"
	@echo "  WORK_DIR = $(WORK_DIR)"
	@echo "  REPORTS_DIR = $(REPORTS_DIR)"
	@echo "  L1ARC_RDF_PRJ = $(L1ARC_RDF_PRJ)"
	@echo "  CLN_RDF_PRJ = $(CLN_RDF_PRJ)"
	@echo "  CLN_RDF_LIB_PRJ = $(CLN_RDF_LIB_PRJ)"
	@echo "  AM_VM_RAM_MACROS = $(AM_VM_RAM_MACROS)"
	@echo ""
	@echo "Tatgets"
	@echo "  rlta"
	@echo "  rlta_power"
	@echo "  view"
	@echo "  clean"
	@echo "  clean_all"


rtla: run_all

POST_INFO ?= post_info
RUN_INFO  ?= run_info
#PRE_INFO  ?= ./pre_info
#pre-info:
#	@echo "Date            : "`date +%Y%m%d%H%M%S`                                >> $(PRE_INFO)
#	@echo "npu rev         : $(NPU_REV)"                                          >> $(PRE_INFO)
#	@echo "npu_deps rev    : $(NPU_DEPS_REV)"                                     >> $(PRE_INFO)
#	@echo "Config          : $(NCONFIG)"                                          >> $(PRE_INFO)
#	@echo "Top Module      : $(TOP_MODULE)"                                       >> $(PRE_INFO)
#	@echo "Tech            : $(RTLA_TECH)"                                        >> $(PRE_INFO)
#	@echo "FMAX(targeting) : $(FMAX)"                                             >> $(PRE_INFO)

post-info:
	@echo "Date            : "`date +%Y%m%d%H%M%S -d "$$(sed -n '1p' $(LOGS_DIR)/start.log)"`                                                                  > $(POST_INFO)
	@echo "npu rev         : $(NPU_REV)"                                                                                                                      >> $(POST_INFO)
	@echo "npu_deps rev    : $(NPU_DEPS_REV)"                                                                                                                 >> $(POST_INFO)
	@echo "Config          : $(NCONFIG)"                                                                                                                      >> $(POST_INFO)
	@echo "Top Module      : $(TOP_MODULE)"                                                                                                                   >> $(POST_INFO)
	@echo "Tech            : $(RTLA_TECH)"                                                                                                                    >> $(POST_INFO)
	@echo "FMAX(targeting) : $(FMAX)"                                                                                                                         >> $(POST_INFO)
	@echo "Run Time        : "`zcat $(REPORTS_DIR)/rtl_output.txt.gz | sed -n '/Elapsed time for this session/p' | tr -d '(hours)'  | awk '{print $$NF}'`     >> $(POST_INFO)
	@echo "Total Area      : "`sed -n '/Cell Area/p'                     $(REPORTS_DIR)/$(TOP_MODULE).report_qor.rpt | grep -v physical | awk '{print $$NF}'` >> $(POST_INFO)
	@echo "WNS_i2r         : "`sed -n '/Critical Path Slack/p'           $(REPORTS_DIR)/$(TOP_MODULE).report_qor.rpt | sed -n '1p' | awk '{print $$NF}'`      >> $(POST_INFO)
	@echo "TNS_i2r         : "`sed -n '/Total Negative Slack/p'          $(REPORTS_DIR)/$(TOP_MODULE).report_qor.rpt | sed -n '1p' | awk '{print $$NF}'`      >> $(POST_INFO)
	@echo "NVP_i2r         : "`sed -n '/No. of Violating Paths/p'        $(REPORTS_DIR)/$(TOP_MODULE).report_qor.rpt | sed -n '1p' | awk '{print $$NF}'`      >> $(POST_INFO)
	@echo "WNS_r2o         : "`sed -n '/Critical Path Slack/p'           $(REPORTS_DIR)/$(TOP_MODULE).report_qor.rpt | sed -n '2p' | awk '{print $$NF}'`      >> $(POST_INFO)
	@echo "TNS_r2o         : "`sed -n '/Total Negative Slack/p'          $(REPORTS_DIR)/$(TOP_MODULE).report_qor.rpt | sed -n '2p' | awk '{print $$NF}'`      >> $(POST_INFO)
	@echo "NVP_r2o         : "`sed -n '/No. of Violating Paths/p'        $(REPORTS_DIR)/$(TOP_MODULE).report_qor.rpt | sed -n '2p' | awk '{print $$NF}'`      >> $(POST_INFO)
	@echo "WNS_io          : "`sed -n '/Critical Path Slack/p'           $(REPORTS_DIR)/$(TOP_MODULE).report_qor.rpt | sed -n '3p' | awk '{print $$NF}'`      >> $(POST_INFO)
	@echo "TNS_io          : "`sed -n '/Total Negative Slack/p'          $(REPORTS_DIR)/$(TOP_MODULE).report_qor.rpt | sed -n '3p' | awk '{print $$NF}'`      >> $(POST_INFO)
	@echo "NVP_io          : "`sed -n '/No. of Violating Paths/p'        $(REPORTS_DIR)/$(TOP_MODULE).report_qor.rpt | sed -n '3p' | awk '{print $$NF}'`      >> $(POST_INFO)
	@echo "WNS_r2r         : "`sed -n '/Critical Path Slack/p'           $(REPORTS_DIR)/$(TOP_MODULE).report_qor.rpt | sed -n '5p' | awk '{print $$NF}'`      >> $(POST_INFO)
	@echo "TNS_r2r         : "`sed -n '/Total Negative Slack/p'          $(REPORTS_DIR)/$(TOP_MODULE).report_qor.rpt | sed -n '5p' | awk '{print $$NF}'`      >> $(POST_INFO)
	@echo "NVP_r2r         : "`sed -n '/No. of Violating Paths/p'        $(REPORTS_DIR)/$(TOP_MODULE).report_qor.rpt | sed -n '5p' | awk '{print $$NF}'`      >> $(POST_INFO)

setup:
	mkdir -p $(LOGS_DIR)
	mkdir -p $(REPORTS_DIR)
	mkdir -p $(WORK_DIR)

#IN_MANIF_SLICE := $(L1ARC_RDF_PRJ)/verilog/RTL/compile_manifest \
#		  ${NPU_HOME}/arch/npu_slice_manifest
#
## Need to include CLN files just to get the switchbox used in npu_slice_top
#IN_MANIF_TOP := $(L1ARC_RDF_PRJ)/verilog/RTL/compile_manifest \
#	        $(CLN_RDF_DIR)/compile_manifest \
#	        ${NPU_HOME}/arch/npu_slice_manifest
#
#ifeq ("$(TOP_MODULE_NAME)","npu_slice_top")
#gen_manifest: gen_manif_top
#else
#gen_manifest: gen_manif_slice
#endif
#
#gen_manif_top: $(IN_MANIF_TOP)
#	${NPU_HOME}/tools/package/manifest.py -c $(IN_MANIF_TOP) > npu_slice_top_compile_manifest
#	echo "${NPU_HOME}/arch/npu_top/RTL/npu_slice_top.sv" >> npu_slice_top_compile_manifest
#	${NPU_HOME}/tools/package/manifest.py -i -a $(IN_MANIF_TOP) > npu_slice_top_search_paths
#
#gen_manif_slice: $(IN_MANIF_SLICE)
#	${NPU_HOME}/tools/package/manifest.py -c $(IN_MANIF_SLICE) > npu_slice_compile_manifest
#	${NPU_HOME}/tools/package/manifest.py -i -a $(IN_MANIF_SLICE) > npu_slice_search_paths

#gen_manifest: $(SYN_MANIFEST)
#	find $(CLN_RDF_DIR) -name "*mem*wrapper*.v" | xargs -I{} cp -f {} $(CLN_DIR)/nl2_/verilog/RTL/
#	find $(CLN_DIR)/nl2_/verilog/RTL -name "*mem*wrapper*.v" > ${NPU_HOME}/manifest/mem_wrapper_compile_manifest
#	find $(L1ARC_RDF_PRJ) -name "*mem*wrapper*.v" | xargs -I{} cp -f {} ${NPU_DEPS}/npu_arc/project_npu_arc_base/build/verilog/RTL/
#	find  ${NPU_DEPS}/npu_arc/project_npu_arc_base/build/verilog/RTL/ -name "*mem*wrapper.v" >> ${NPU_HOME}/manifest/mem_wrapper_compile_manifest
#	cp -f ../rdf_replacement/npu_cln/* $(NPU_BLD_HOME)/src/npu_core/ncln/nl2_/verilog/RTL/
#	cp -f ../rdf_replacement/npu_arc/* $(NPU_DEPS)/npu_arc/project_npu_arc_base/build/verilog/RTL/


# Not doing a tee to $(LOGS_DIR)/rtla.log anymore since file rtl_output.txt is already created
run_all: setup
	@echo "RTLA_SETTINGS: $(RTLA_SETTINGS)"
	-rm -f $(LOGS_DIR)/*.log $(LOGS_DIR)/rtl*.txt $(WORK_DIR)/done.*
	date > $(LOGS_DIR)/start.log
	#$(RTLA_EXEC) -f ./scripts/run_all.tcl | tee $(LOGS_DIR)/rtla.log
	$(RTLA_EXEC) -f ./scripts/run_all.tcl
	date > $(LOGS_DIR)/finish.log
	#mv $(LOGS_DIR)/rtla.log $(REPORTS_DIR) && gzip $(REPORTS_DIR)/rtla.log
	$(NPU_HOME)/tools/utils/npu_git_versions.sh > $(REPORTS_DIR)/npu_git_rev.txt
	-mv rtl_output.txt $(LOGS_DIR) && gzip -c $(LOGS_DIR)/rtl_output.txt > $(REPORTS_DIR)/rtl_output.txt.gz
	-mv rtl_command.log $(LOGS_DIR)

	#cp constraints/npu_slice*sdc $(REPORTS_DIR)

rtla-power rtla_power: $(WORK_DIR)/$(TOP_MODULE).dlib
	$(RTLA_EXEC) -f ./scripts/run_power.tcl

RTLA_REPORTS_HOME ?= /slowfs/us01dwt2p863/npx/victoria/ppa
REPORTS_ID        := $(shell date +%Y%m%d%H%M%S -d "$(shell sed -n 1p $(LOGS_DIR)/start.log)")
REPORTS_NAME      := $(REPORTS_ID)_reports_$(NCONFIG)_$(TOP_MODULE)_$(RTLA_TECH)nm_$(FMAX)Mhz

.PHONY: post-info
report-results: post-info
	cat $(POST_INFO) > $(RUN_INFO)
	@echo -e "\n\n====================================================================="
	cat $(RUN_INFO)
	@echo -e "=====================================================================\n\n"
register-results:
	@echo "REPORTS_NAME: $(REPORTS_NAME)"
	@echo "REPORTS_ID:   $(REPORTS_ID)"
	-rm -rf $(RTLA_REPORTS_HOME)/$(REPORTS_NAME)
	cp -rf $(REPORTS_DIR) $(RTLA_REPORTS_HOME)/$(REPORTS_NAME)
	cat $(RUN_INFO) | awk -F: '{print $$2}' | xargs | sed 's#\s\+#,#g' > $(RTLA_REPORTS_HOME)/rtla_reports_body.tmp
	cat $(RTLA_REPORTS_HOME)/rtla_reports_body >> $(RTLA_REPORTS_HOME)/rtla_reports_body.tmp
	sort $(RTLA_REPORTS_HOME)/rtla_reports_body.tmp | uniq -u > $(RTLA_REPORTS_HOME)/rtla_reports_body
	cat $(RTLA_REPORTS_HOME)/rtla_reports_header $(RTLA_REPORTS_HOME)/rtla_reports_body > $(RTLA_REPORTS_HOME)/rtla_reports
	cat $(RTLA_REPORTS_HOME)/rtla_reports | sed 's/,/, /g'
	cd $(RTLA_REPORTS_HOME) && $(NPU_HOME)/tools/utils/gen_rtla_dashboard.py
	chmod -R 777 $(RTLA_REPORTS_HOME)/$(REPORTS_NAME)

#_tmp:
#	sort | uniq -u > $(RUN_INFO)
#	#(res=`cat $(RUN_INFO) | awk -F: '{print $$2}' | xargs | sed 's#\s\+#,#g'`; sed -i "0a $$res" $(RTLA_REPORTS_HOME)/rtla_reports_body)
#	#sort $(RTLA_REPORTS_HOME)/rtla_reports_body | uniq -u > $(RTLA_REPORTS_HOME)/rtla_reports_body.tmp
#	#mv -f $(RTLA_REPORTS_HOME)/rtla_reports_body.tmp $(RTLA_REPORTS_HOME)/rtla_reports_body
#	@-test -d $(RTLA_REPORTS_HOME)/$(REPORTS_NAME) && echo "WARNING: $(RTLA_REPORTS_HOME)/$(REPORTS_NAME) already exists, NO report copy..."
#	@test -d $(RTLA_REPORTS_HOME)/$(REPORTS_NAME) || cp -rf $(REPORTS_DIR) $(RTLA_REPORTS_HOME)/$(REPORTS_NAME)
#	@test -d $(RTLA_REPORTS_HOME)/$(REPORTS_NAME) || (res=`cat $(RUN_INFO) | awk -F: '{print $$2}' | xargs | sed 's#\s\+#,#g'`; sed -i "1a $$res" $(RTLA_REPORTS_HOME)/rtla_reports)
#	@cat $(RTLA_REPORTS_HOME)/rtla_reports | sed 's/,/ ,/g'
#	cat $(RTLA_REPORTS_HOME)/rtla_reports | sed 's/,/ ,/g' | column -t -s,

tt: setup
	date > $(LOGS_DIR)/start.log
	-rm -f $(LOGS_DIR)/rtla.log $(LOGS_DIR)/finish.log $(WORK_DIR)/done.*
	$(RTLA_EXEC) -f ./scripts/run_all.tcl | tee $(LOGS_DIR)/rtla.log
	date > $(LOGS_DIR)/finish.log
	cp $(LOGS_DIR)/rtla.log $(REPORTS_DIR)
	cp ../constraints/npu_slice*sdc $(REPORTS_DIR)

view:
	@echo "View WORK_DIR = $(WORK_DIR)"
	$(RTLA_EXEC) -f ./scripts/view_lib.tcl

clean:
	rm -f *_fm_read_verilog.tcl done*
	rm -f *compile_manifest *search_paths
	rm -rf HDL_LIBRARIES
	rm -f $(WORK_DIR)/done*
	rm -f *~

clean_all: clean
	rm -rf $(LOGS_DIR) $(WORK_DIR) $(REPORTS_DIR)
	rm -rf floorplan/ RTLA_WORKSPACE/ work_dir/ HDL_LIBRARIES/
	rm -rf rtl_command.log rtl_output.txt fusa_redundancy_cstr.sgdc .*.paths
	rm -f *.log
	rm -f default*.svf

FORCE:

