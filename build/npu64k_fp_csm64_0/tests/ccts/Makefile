ifneq ("$(NPU_HOME)","")
  RLS ?= ${NPU_HOME}/build
else
  ifneq ("$(NPU_HOME_RLS)","")
    RLS ?= ${NPU_HOME_RLS}
  else
    $(error "NPU_HOME / NPU_HOME_RLS are not defined")
  endif
endif
include $(RLS)/build_config.mk
include $(RLS)/tests/ccts/cct_list.mk 

export RLS
export NPU_SLICE_NUM ?= 1
export DUMP_WAVEFORM ?= 0
export DUMP_SAIF     ?= 0
export VERDI         ?= 0

SIMV      ?= $(RLS)/sim/simv
UVM_VERBOSITY ?= UVM_LOW
SIMV_OPTS ?= +UVM_VERBOSITY=$(UVM_VERBOSITY)
SIMV_OPTS += +SIM_MON_EN=1 -sv_root . -sv_lib host -ucli -do ${RLS}/tests/bin/run_npu_top.tcl

SEED      ?= 1 # Default seed set to 1
COV_SEED = $$RANDOM
COV_NAME  ?= $(shell basename $(PWD)_$(SEED))

ifeq ($(COV_EN),1)
	ifeq ($(CCT_REGR_EN),0)
		COV_RUN_OPTS = -cm_name $(COV_NAME)_$(COV_SEED) -cm line+tgl+cond+fsm+branch+assert
		SIMV_OPTS += $(COV_RUN_OPTS)
	else 
		COV_RUN_OPTS = -cm line+tgl+cond+fsm+branch+assert
		SIMV_OPTS += $(COV_RUN_OPTS)
	endif
endif

# full list of tests
COMMA        := ,
EMPTY        :=
SPACE        := $(EMPTY) $(EMPTY)
ACL_LIST     := $(CCT_ACCL)
ARC_LIST     := $(CCT_ARC)
ARCSYNC_LIST := $(CCT_ARCSYNC)
ARC_LIST     += $(ARCSYNC_LIST)
CCT_LIST     ?= $(ARC_LIST) $(ACL_LIST)
CCTS         ?= all
$ARGUMENT    ?= simv 
export REGR_OPTS 	 += $(EXP_SEED) $(REGR_COV_MRG) $(TYPE) $(WAY) $(COND)

ifeq ($(CCTS),all)
  EXP_CCTS   := $(shell echo $(CCT_LIST) | xargs)
else
  EXP_CCTS   := $(shell echo $(subst $(COMMA),$(SPACE),$(CCTS)) | xargs)
endif

RAND_SEED    ?= 0
ifneq ($(RAND_SEED),1)
	EXP_SEED := +ntb_random_seed=$(RAND_SEED)
endif

ifeq ($(CCT_REGR_EN),1)
	REGR_COV_MRG += -cm_name $(ARGUMENT) -cm line+tgl+cond+fsm+branch+assert
endif

SIMV_LOG := -l simv.log


ifeq ($(ERR_TYPE),NO_VALID) 
	TYPE := +ERR_TYPE="NO_VALID"
endif

ifeq ($(ERR_TYPE),ECC)
	TYPE := +ERR_TYPE="ECC"
ifeq ($(ERR_WAY),SB)
	WAY := +ERR_WAY="SB"
endif
ifeq ($(ERR_WAY),DB)
	WAY := +ERR_WAY="DB"
endif
ifeq ($(ERR_WAY),A0)
	WAY := +ERR_WAY="A0"
endif
ifeq ($(ERR_WAY),A1)
	WAY := +ERR_WAY="A1"
endif
endif

ifeq ($(ERR_TYPE),PARITY)
	TYPE := +ERR_TYPE="PARITY"
endif

ifeq ($(ERR_COND),INJECT_WITH_VALID)
	COND := +ERR_COND="INJECT_WITH_VALID"
endif

ifeq ($(ERR_COND),INJECT_DIRECT)
	COND := +ERR_COND="INJECT_DIRECT"
endif


ARC_HEX   := $(foreach n, $(ARC_LIST), $n.hex)
ACL_HEX   := $(foreach n, $(ACL_LIST), $n.hex)
CCT_HEX   := $(foreach n, $(EXP_CCTS), $n.hex)
CCT_RPT   := $(foreach n, $(EXP_CCTS), $n/sim.report)
CCT_CLEAN := $(foreach n, $(EXP_CCTS), clean-$(n))
CCT_HOST  := $(foreach n, $(EXP_CCTS), $n.host)
CCT_STR   := $(shell echo "$(EXP_CCTS)" | tr ' ' ',')

all:
	@echo "Please specify a target: build, run, run-all, report-all"

# Build CCT in development env
list:
	@echo "CCTS: $(CCT_STR)"

ifeq ($(TB_VIP),1)
build: $(CCT_HEX) 
else
build: $(CCT_HEX) $(CCT_HOST)
endif

NPU_MLI_TAPI_EN ?= 1
$(ARC_HEX):
	cd ${RLS}/tests/ccts/$(basename $@) && make -f ../Makefile.rtl_ccts COMPILE_ACCL=0 NPU_MLI_TAPI_EN=$(NPU_MLI_TAPI_EN) hex
$(ACL_HEX):
	cd ${RLS}/tests/ccts/$(basename $@) && make -f ../Makefile.rtl_ccts COMPILE_ACCL=1 NPU_MLI_TAPI_EN=$(NPU_MLI_TAPI_EN) hex
$(CCT_HOST):
	cd ${RLS}/tests/ccts/$(basename $@) && make -f ../Makefile.rtl_ccts host.so

# Run CCTs in release env
run: $(CCT_RPT)
$(CCT_RPT):
	cd $(dir ${RLS}/tests/ccts/$@) && make -f ../Makefile.rtl_ccts run

report:
	cd ${RLS}/tests/ccts && ${RLS}/tests/bin/cct_report.sh "$(EXP_CCTS)" "$(ARGUMENT)" "$(CCT_REGR_EN)"

clean: $(CCT_CLEAN)
$(CCT_CLEAN):
	cd ${RLS}/tests/ccts/$(patsubst clean-%,%,$@) && make -f ../Makefile.rtl_ccts clean

