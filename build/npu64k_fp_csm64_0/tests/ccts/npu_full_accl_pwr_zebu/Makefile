MYDIR := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))
	include ${NPU_HOME}/verif/common/npi/pref/TLib/conv2d/common_gen.mk
all default: clean pref hlrun rtlrun
hlrun:
	@mkdir -p vec logs Native
	make -f ${NPU_HOME}/verif/common/tensor_api/npu.mk SYSC=1 test.exe
	test.exe > logs/run_native_vec.log 2>&1
	perl $(TCONV2D)/diff.pl nvec $(VSIZE) $(ISIZE)
rtlrun:
	mkdir -p res logs
	make -f ${NPU_HOME}/verif/common/tensor_api/npu.mk RTL_DPI=1 run
	perl $(TCONV2D)/diff.pl rtl $(VSIZE) $(ISIZE)