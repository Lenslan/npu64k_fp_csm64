
`ifdef VPP_JS
<script>
var core_table = 
  {
  cores: 	
    [
      {
      prefix: 	"",
      define_prefix: 	"",
      arcnum: 	0,
      arcnums: 	
        []
      ,
      instances: 	
        [0,]
      ,
      }
    ,
    ]
  ,
  instances: 	
    [
      {
      type_prefix: 	"",
      define_prefix: 	"",
      signal_prefix: 	"",
      clk_prefix: 	"",
      arcnum: 	0,
      core: 	0,
      cluster_clk_gated_prefix: 	"c0",
      }
    ,
    ]
  ,
  }

</script>
`endif

// ARChitect values:
`define ARCHITECT_OS	"linux"
`define ARCHITECT_BUILD_DIRECTORY	"/mnt/jlrao/nn/npu_deps/npu_arc/project_npu_arc_se_ad1k_N64_mem_ecc_pg1/build/"
`define ARCHITECT_BUILD_DIRECTORY_WIN32	"\\mnt\\jlrao\\nn\\npu_deps\\npu_arc\\project_npu_arc_se_ad1k_N64_mem_ecc_pg1\\build\\"

// Options on component project_npu_arc_se_ad1k_N64_mem_ecc_pg1:
`define PROJECT_BUILD_HTML_DOCS	0
`define PROJECT_BUILD_TEST_CODE	1
`define PROJECT_BUILD_SCRIPTS	1
`define PROJECT_BUILD_HDL	1
`define PROJECT_COMPILE_TEST_CODE	0
`define PROJECT_GENERATE_STRUCTURAL_HDL	1
`define PROJECT_COMPILE_HDL_FOR_SIMULATION	1
`define PROJECT_BUILD_XCAM	0
`define PROJECT_RUN_ARCSYN	0
`define PROJECT_RUN_SEIF	0
`define PROJECT_RUN_ARCRAMS	0
`define PROJECT_RUN_ARCFORMAL	0
`define PROJECT_RUN_ARCPOWER	0
`define PROJECT_COMPILE_ISS_USER_EXTENSIONS	0
`define PROJECT_COMPILE_TRANSLATED_ISS_EXTENSIONS	0
`define PROJECT_COMPILE_NSIM_USER_EXTENSION	0
`define PROJECT_COMPILE_TRANSLATED_NSIM_EXTENSIONS	0

// Options on component System:
`define SYSTEM_SIM64	1
`define SYSTEM_RENAME_DEFINES	1
`define SYSTEM_EXPORT_SRAMS_TO	"none"
`define SYSTEM_COPY_PREFIX	"npuarc_"
`define SYSTEM_ALWAYS_INSTANTIATE_CORE	0

// Options on component Implementation:
`define IMPLEMENTATION_EXECUTION_TRACE_LEVEL	"stats"
`define IMPLEMENTATION_TB_TRACE	0
`define IMPLEMENTATION_UNIQUE_CLK	0
`define IMPLEMENTATION_IPXACT_INCLUDE_AUX_REGS	1
`define IMPLEMENTATION_IPXACT_DYNAMIC_AUX_REGS	1
`define IMPLEMENTATION_GENERATE_DITA_FILES	0
`define IMPLEMENTATION_ADDITIONAL_IPXACT	0
`define IMPLEMENTATION_RALF2RTL	1
`define IMPLEMENTATION_PIPEMON_INIT_BITS	4'b0011; // Enable debug instrs(0); - (0); Suppress transcript (1); enable statistics gathering (1).
`define IMPLEMENTATION_PIPEMON_TO_FILE	0
`define IMPLEMENTATION_PIPEMON_FILE_NAME	"trace.txt"

// Below is a sequence of defines of the form XXX_PRESENT
// for each VPP-based system component present in the build that wishes to
// indicate its presence.
`define NPU_PRESENT	1
`define npuarc_ARC_TRACE_PRESENT	1
`define ALB_MSS_FAB_PRESENT	1
`define ALB_MSS_CLKCTRL_PRESENT	1
`define CC_PRESENT	1
`define BIU_PRESENT	1
`define ALB_MSS_MEM_PRESENT	1

// Below are defines for every component not contained 
// within a core, using the ARChitect type to denote the component.
`define COM_ARC_HARDWARE_NPU_NPX_NPU_PRESENT	1
`define COM_ARC_HARDWARE_ARC_TRACE_PRESENT	1
`define COM_ARC_HARDWARE_ARCV2MSS_BUSFABRIC_PRESENT	1
`define COM_ARC_HARDWARE_ARCV2MSS_CLKCTRL_PRESENT	1
`define COM_ARC_HARDWARE_CC_CLUSTER_PRESENT	1
`define COM_ARC_HARDWARE_CC_BUS_INTERFACE_UNIT_PRESENT	1
`define COM_ARC_HARDWARE_HS_CPU_ISLE_PRESENT	1
`define COM_ARC_HARDWARE_IMPLEMENTATION_PRESENT	1
`define COM_ARC_HARDWARE_ARCV2MSS_SRAMCTRL_PRESENT	1

 
