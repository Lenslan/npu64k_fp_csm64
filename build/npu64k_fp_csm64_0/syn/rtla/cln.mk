#FIXME: this Makefile build HHD CLN with ARChitect flow for RDF reuse purpose
SHELL := /bin/bash

TOP_MODULE ?= cln_core
IMPL       ?= flat
NCONFIG    ?= npu4k_vm512_csm1
LOCAL_RDF  ?=
ifeq ($(MLIB_HOME),)
  LC_CLN_RDF_LIB_PRJ ?= ${NPU_HOME}/npu_cln_archi
else
  LC_CLN_RDF_LIB_PRJ ?= $(MLIB_HOME)/$(NCONFIG)/npu_cln_archi
endif

BUILD_PRJ  ?= ${NPU_HOME}/build
CLN_PRJ_DIR?= $(LC_CLN_RDF_LIB_PRJ)
#CLN_PRJ_DIR?= $(BUILD_PRJ)/../npu_cln_archi
CLN_PRJ_DIR:= $(abspath $(CLN_PRJ_DIR))
CLN_PREFIX  = nl2_

MLV_CLN         = $(BUILD_PRJ)/verilog/npu_cln
#NPU_IPLIB_DEPS := $(shell realpath $(BUILD_PRJ)/config/$(NCONFIG))

#RDF_HOME   ?= /u/brunola/arc_src/RDF
IPLIBS         ?= $(shell grep -v '\#' ${NPU_DEPS}/p4/iplibs/v3cln_rdf.iplib_list | xargs)

CLN_PRJ_NAME := $(notdir $(CLN_PRJ_DIR))

export SNPSLMD_LICENSE_FILE := 26585@us01arclmd1:${SNPSLMD_LICENSE_FILE}

ifeq ($(strip NCORES_HOST),)
    export NCORES=4
else
    ifeq ($(shell if [ $(NCORES_HOST) -ge 8 ] ; then echo ge ; else echo lt ; fi),ge)
    export NCORES=8
  else
    export NCORES=$(NCORES_HOST)
  endif
endif

help:
	@echo "Help: iplib/packing/syn_rtla/cln.mk"
	@echo "  NCORES = $(NCORES)"
	@echo "  NPU_IPLIB_DEPS = $(NPU_IPLIB_DEPS)"
	@echo "  BUILD_PRJ = $(BUILD_PRJ)"
	@echo "  CLN_PRJ_DIR = $(CLN_PRJ_DIR)"
	@echo ""
	@echo "IPLIBS used:"
	@echo $(IPLIBS) | tr " " "\n"
	@echo ""
	@echo "From list $(NPU_IPLIB_DEPS)/iplibs.list"
	@echo ""
	@echo "Targets : build arcrams ndm syn"


build:
	-rm -rf $(CLN_PRJ_DIR)
ifneq ($(LOCAL_RDF),)
	sed -i 's#^-mem_lib_path.*#-mem_lib_path $(LOCAL_RDF)#g' $(BUILD_PRJ)/config/npu_core_ncln.txt
endif
	ARChitect2 -cl -libraries $(IPLIBS) -argument_file $(BUILD_PRJ)/config/npu_core_ncln.txt -projectpath $(CLN_PRJ_DIR)

open:
	ARChitect2 -libraries $(IPLIBS) -project $(CLN_PRJ_DIR)/${CLN_PRJ_NAME}.apr

arcrams:
	${NPU_HOME}/tools/utils/embedit_wrapper make -C $(CLN_PRJ_DIR)/build -f arcseif.makefile NCORES=$(NCORES)
	cd $(CLN_PRJ_DIR)/build && ARCrams `pwd` arcrams_lib/map_file.txt verilog vcs 5 ${CLN_PREFIX}

ndm:
	make -C $(CLN_PRJ_DIR)/build -f arcsyn.makefile synthesis rtl_opt CREATE_SCRIPTS_ONLY=true

syn:
	make -C $(CLN_PRJ_DIR)/build -f arcsyn.makefile archipelago_expand_hier_designs.log HIER_DESIGNS="alb_cpu_top cln_core"
	make -C $(CLN_PRJ_DIR)/build -j -f arcsyn.makefile synthesis NCORES=${NCORES_HOST} IMPL=$(IMPL) TOPMODULE="$(TOP_MODULE)"

# Patch the CLN created with the MLV flow with files for synthesis created with the ARChitect + RDF flow
S=${CLN_PRJ_DIR}/build/verilog/RTL
D=${MLV_CLN}_rdf/$(CLN_PREFIX)/verilog/RTL
P=$(CLN_PREFIX)
MANIF=${MLV_CLN}_rdf/compile_manifest
MEMSCM_DBANK_SRAM ?= $(shell awk '/Memscm_dbank_sram/ {print $$3}' ${S}/${P}scm_dbank_sramdef.v)
RDF_MANIF := ${MLV_CLN}_rdf/replace_rdf_manifest
patch:
	@echo "cln.mk $@ START"
	@echo "  Source = ${S}"
	@echo "  Dest   = ${D}"
	@echo "  Prefix = ${P}"
	@echo "  Manif  = ${RDF_MANIF}"
	@echo ""
	@-rm -rf ${MLV_CLN}_rdf
	rsync -av --delete ${MLV_CLN}/ ${MLV_CLN}_rdf
	touch $(RDF_MANIF)
	cp -f ${S}/${P}stdcelldef.v ${D} && echo ${D}/${P}stdcelldef.v >> $(RDF_MANIF)
	mv -n ${D}/${P}scm_dbank_sram.v ${D}/${P}scm_dbank_sram.old  ;  cp -f ${S}/${P}scm_dbank_sram.v  ${D} && echo ${D}/${P}scm_dbank_sram.v >> $(RDF_MANIF)
	mv -n ${D}/${P}clkgate.v ${D}/${P}clkgate.old  ;  cp -f ${S}/${P}clkgate.v  ${D} && echo ${D}/${P}clkgate.v >> $(RDF_MANIF)
	mv -n ${D}/${P}cln_clkgate.v ${D}/${P}cln_clkgate.old  ;  cp -f ${S}/${P}cln_clkgate.v ${D} && echo ${D}/${P}cln_clkgate.v >> $(RDF_MANIF)
	cp -vf ${S}/${P}scm_dbank_sramdef.v  ${D} && echo ${D}/${P}scm_dbank_sramdef.v >> $(RDF_MANIF)
	cp -vf ${S}/${P}synopsys_tsmc_port_mappings.v  ${D} && echo ${D}/${P}synopsys_tsmc_port_mappings.v >> $(RDF_MANIF)
	cp -vf ${S}/../$(MEMSCM_DBANK_SRAM)*  ${D}          && ls ${D}/$(MEMSCM_DBANK_SRAM)* >> $(RDF_MANIF)
	sed -i -e 's;/ncln/;/ncln_rdf/;g' ${MANIF}
	find ${D} -name '*mem*wrapper.v' -exec sh -c "echo {} >> ${MANIF}" \;
	#cp -vf ${S}/${P}defines.v  ${S}/${P}exported_defines.v  ${D} && echo -e "${D}/${P}defines.v\n${D}/${P}exported_defines.v" >> $(RDF_MANIF)
	#cp -vf ${S}/../$(shell awk '/Memscm_dbank_sram/ {print $$3}' ${S}/${P}scm_dbank_sramdef.v)*  ${D}
	@echo "cln.mk $@ DONE"

patch0:
	@-rm -rf ${MLV_CLN}_rdf
	rsync -av --delete ${MLV_CLN}/ ${MLV_CLN}_rdf
	cp -f ${S}/${P}stdcelldef.v ${D}/${P}stdcelldef.v && ([[ ! -e ${D}/${P}stdcelldef.old ]] && touch ${P}stdcelldef.old)
	mv -n ${D}/${P}scm_dbank_sram.v ${D}/${P}scm_dbank_sram.old  ;  cp -f ${S}/${P}scm_dbank_sram.v ${D}/${P}scm_dbank_sram.v && ([[ ! -e ${D}/${P}scm_dbank_sram.old ]] && touch ${D}/${P}scm_dbank_sram.old)
	mv -n ${D}/${P}clkgate.v ${D}/${P}clkgate.old  ;  cp -f ${S}/${P}clkgate.v ${D}/{${P}clkgate.v,${P}clkgate.old} && ([[ ! -e ${D}/${P}clkgate.old ]] && touch ${D}/${P}clkgate.old)
	mv -n ${D}/${P}cln_clkgate.v ${D}/${P}cln_clkgate.old  ;  cp -f ${S}/${P}cln_clkgate.v ${D} && ([[ ! -e ${D}/${P}cln_clkgate.old ]] && touch ${D}/${P}cln_clkgate.old)
	cp -vf ${S}/${P}scm_dbank_sramdef.v  ${D} && ([[ ! -e ${D}/${P}scm_dbank_sramdef.old && touch ${P}scm_dbank_sramdef.old)
	cp -vf ${S}/${P}synopsys_tsmc_port_mappings.v  ${D} && ([[ ! -e ${D}/${P}synopsys_tsmc_port_mappings.old && touch ${P}synopsys_tsmc_port_mappings.old)
	cp -vf ${S}/../$(MEMSCM_DBANK_SRAM)* ${D}/
	sed -i -e 's;/ncln/;/ncln_rdf/;g' ${MANIF}
	find ${D} -name '*mem*wrapper.v' -exec sh -c "echo {} >> ${MANIF}" \;
	#cp -vf ${S}/../$(shell awk '/Memscm_dbank_sram/ {print $$3}' ${S}/${P}scm_dbank_sramdef.v)*  ${D}
	#cp -vf ${S}/${P}defines.v  ${S}/${P}exported_defines.v  ${D}

patch1:
	@-rm -rf ${MLV_CLN}_rdf
	rsync -av --delete ${MLV_CLN}/ ${MLV_CLN}_rdf
	cp -f ${S}/${P}stdcelldef.v ${D}/${P}stdcelldef.v && cp -f ${D}/${P}stdcelldef.v ${D}/${P}stdcelldef.old
	mv -n ${D}/${P}scm_dbank_sram.v ${D}/${P}scm_dbank_sram.old  ;  cp -f ${S}/${P}scm_dbank_sram.v  ${D}
	mv -n ${D}/${P}clkgate.v ${D}/${P}clkgate.old  ;  cp -f ${S}/${P}clkgate.v  ${D}
	mv -n ${D}/${P}cln_clkgate.v ${D}/${P}cln_clkgate.old  ;  cp -f ${S}/${P}cln_clkgate.v ${D}
	cp -f ${S}/${P}scm_dbank_sramdef.v  ${D} && cp -f ${D}/${P}scm_dbank_sramdef.v  ${D}/${P}scm_dbank_sramdef.old
	#cp -f ${S}/${P}defines.v  ${S}/${P}exported_defines.v  ${D}
	cp -f ${S}/${P}synopsys_tsmc_port_mappings.v ${D} && cp -f ${D}/${P}synopsys_tsmc_port_mappings.v ${D}/${P}synopsys_tsmc_port_mappings.old
	cp -f ${S}/../$(shell awk '/Memscm_dbank_sram/ {print $$3}' ${S}/${P}scm_dbank_sramdef.v)*  ${D}
	sed -i -e 's;/npu_cln/;/npu_cln_rdf/;g' ${MANIF}
	find ${D} -name '*mem*wrapper.v' -exec sh -c "echo {} >> ${MANIF}" \;

