

CFG = npu64k_fp_csm64_0
PKG = npu64k_fp_csm64_0.tar.xz

all: .install $(CFG)
	@echo "Package installed in $(CFG)/"

$(CFG):
	@echo "Decompressing $(PKG)"
	@tar xfJ $(PKG)

# Remove uneeded build artifacts
.install: .curdir
	@rm -f bcr_contents.txt rascal* vcs_run
	@rm -rf dat/ verilog/
	@touch $@

.curdir:
	@echo $(CURDIR) > $@

