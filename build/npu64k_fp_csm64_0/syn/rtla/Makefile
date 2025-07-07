##########################################################################################
# Setup
NCONFIG         ?= npu4k_vm512_csm1
FMAX            ?= 1000
RTLA_TECH       ?= 07
TOP_MODULE      ?= npu_slice_top
TECH             = ts$(RTLA_TECH)
NPU_HOME_DEV    ?= ${NPU_HOME_RLS}

# sanity elaboration check
ELAB_ONLY  ?= 0
SDC_ONLY   ?= 0

# source files for synthesize
SYN_MANIFEST ?= ${NPU_HOME_RLS}/manifest/rtl_manifest.v.flat
SYN_SDC      ?= ${NPU_HOME_RLS}/syn/rtla_$(TOP_MODULE)/constraints.sdc

# Library settings
# A(for customer) : A single directory contains all .db and .mw for memories
LOCAL_MEM_LIBS   ?= i_dont_konw
#LOCAL_MEM_LIBS   ?= /u/brunola/work/npu_dev/npu/tools/embedit_sram/build_mem_ts03/$(RTLA_TECH)

# B(for internal dev): Or seperate directories for sub-ips
# ARC HS ARChitect project with RDF configured
ARC_RDF_PRJ    ?= /u/brunola/work/npu_deps/npu_arc/rdf_project/$(TECH)_perf/npu_arc_base
VPX_RDF_PRJ    ?= /slowfs/us01dwt2p863/brunola/npu_deps/vpx/nu4500/project_rdf
# Location of AM and VM memory macros
AM_VM_RAM_MACROS ?= /u/brunola/work/npu_dev/npu/tools/embedit_sram/build_mem_ts03/$(RTLA_TECH)
# ARCv3 CLN ARChitect project with RDF configured
# NOTE: CLN_RDF_PRJ is the directory contains rdf replaced source files
#       CLN_RDF_LIB_PRJ is the directory contains rdf libraries
CLN_RDF_PRJ     ?= ${NPU_HOME_DEV}/build/src/npu_cln
CLN_RDF_LIB_PRJ ?= ${NPU_HOME_DEV}/npu_cln_archi


##########################################################################################

include rtla.mk

