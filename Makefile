ifeq ($(OS),Windows_NT)
DETECTED_OS := Windows
EXE_SUFFIX := .exe
else
UNAME_S := $(shell uname -s 2>/dev/null || echo Unknown)
ifeq ($(UNAME_S),Darwin)
DETECTED_OS := macOS
EXE_SUFFIX :=
else ifeq ($(UNAME_S),Linux)
DETECTED_OS := Linux
EXE_SUFFIX :=
else
DETECTED_OS := $(UNAME_S)
EXE_SUFFIX :=
endif
endif

PERL ?= perl$(EXE_SUFFIX)
FO_CACHE_ROOT ?= .fo-cache

GENERATED_GO_PATHS := \
	.tmp_tokenprobe.go \
	bootstrap/*.go \
	cmd/*/*.go \
	examples/*.go \
	internal/*/*.go \
	internal/*/*/*.go \
	stdlib/fo/*.go

TRANSIENT_PATHS := \
	$(FO_CACHE_ROOT) \
	.fo-build \
	.fo-build-stage \
	.cold-seed-check.* \
	.fo-build-run.* \
	.genesis-seed-check.* \
	.genesis-seed-src.* \
	.genesis-stage.debug.* \
	.seed-freeze.* \
	.seed-genesis.* \
	.seed-materialize.* \
	.seed-parity.* \
	bootstrap/bin \
	bootstrap/support \
	build/cmd \
	build/examples \
	build/fo-coldseed$(EXE_SUFFIX) \
	dist \
	seedwork

DISTCLEAN_PATHS := \
	build \
	build/fo$(EXE_SUFFIX) \
	build/fo-selfhosted$(EXE_SUFFIX) \
	build/fo-coldseed$(EXE_SUFFIX)

define PERL_REMOVE
$(PERL) -e 'use strict; use warnings; use File::Path qw(remove_tree); my %seen; for my $$pattern (@ARGV) { for my $$path (glob($$pattern)) { next if $$seen{$$path}++; if (-d $$path && !-l $$path) { remove_tree($$path); next; } unlink $$path if -e $$path || -l $$path; } }' --
endef

.PHONY: help print-os clean-cache clean-generated clean distclean

help:
	@printf '%s\n' 'Fo Make targets'
	@printf '%s\n' '  make clean       Remove caches, transient dirs, generated Go, and package build outputs'
	@printf '%s\n' '  make distclean   Also remove build/fo, build/fo-selfhosted, and the build directory'
	@printf '%s\n' '  make clean FO_CACHE_ROOT=/path/to/cache   Clean a non-default cache root'
	@printf '%s\n' '  make print-os    Show detected OS'

print-os:
	@printf '%s\n' '$(DETECTED_OS)'

clean-cache:
	@printf '%s\n' 'Cleaning cache root: $(FO_CACHE_ROOT)'
	@$(PERL_REMOVE) '$(FO_CACHE_ROOT)'

clean-generated:
	@printf '%s\n' 'Removing generated Go artifacts'
	@$(PERL_REMOVE) $(foreach path,$(GENERATED_GO_PATHS),'$(path)')

clean:
	@$(MAKE) --no-print-directory clean-cache
	@printf '%s\n' 'Removing transient build outputs'
	@$(PERL_REMOVE) $(foreach path,$(TRANSIENT_PATHS),'$(path)')
	@$(MAKE) --no-print-directory clean-generated
	@printf '%s\n' 'make clean complete on $(DETECTED_OS)'

distclean: clean
	@printf '%s\n' 'Removing compiler binaries and build directory'
	@$(PERL_REMOVE) $(foreach path,$(DISTCLEAN_PATHS),'$(path)')
	@printf '%s\n' 'make distclean complete on $(DETECTED_OS)'
