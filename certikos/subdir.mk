## Make rules for subdirectories

# The including Makefile is expected to set the following variables:
#
#	FILES		List of coq source files
#
# Additionally, the user may set the following variables:
#
#	TIMELOG		File to log compilation times to
# 	CROSSDEP	warn|ignore|rebuild
# 	SKIPDEP		Do not attempt to update the top-level .depend
#

# Figure out where we are
TOPDIR= $(dir $(CURDIR))
SUBDIR= $(notdir $(CURDIR))

# Common definitions
include $(TOPDIR)/common.mk

# Default values for parameters
CROSSDEP = warn
# TIMELOG = .timelog

# Toolchain
COQC= coqc
COQTOP= coqtop
COQDOC= coqdoc
OCAMLBUILD= ocamlbuild
COQFLAGS= $(foreach d,$(SUBDIRS),-R $(TOPDIR)$d $d)

# Local overrides for configuration variables
-include $(TOPDIR)/Makefile.config

# Hookable targets: subdir Makefiles can extend them by adding dependencies.
all: all-vo
clean: clean-vo


## Compiling Coq sources files

# Compile all of them
all-vo: $(FILES:.v=.vo)

# Compile one of them
ifeq ($(TIMELOG),)
%.vo: %.v
	@echo COQC $*
	@$(COQC) $(COQFLAGS) $*
else
# Keep a log of compilation times: if $(TIMELOG) is defined,
# we write an entry there each time we build a .vo file.
GITREV := $(shell git rev-parse --short HEAD)
GITMOD := $(shell git status --porcelain --untracked=no | grep -q . && echo +)
TIME = command time -o $@.time -f "$(GITREV)$(GITMOD):$(SUBDIR)/$< %U %S %E %P"
%.vo: %.v
	@echo COQC $*
	@$(TIME) -o $@.time $(COQC) $(COQFLAGS) $*
	@cat $@.time >> ../$(TIMELOG)
	@$(RM) $@.time
endif

# Cleanup
clean-vo:
	$(RM) $(FILES:.v=.vo) $(FILES:.v=.glob) $(FILES:.v=.vo.time)


## Out-of-date files in other subdirectories

# The way we handle out-of-date files from other subdirectories depend on the
# value of the variables $(CROSSDEP). If it is 'ignore', then we do nothing.
# If it is 'warn' (the default), we emit a warning but do not try to rebuild
# them either. If it is 'build', then we attempt to rebuild it as if it were
# one of our files.

ifeq ($(CROSSDEP),ignore)
../%.vo:
	@true
else
ifneq ($(CROSSDEP),build)
../%.vo:
	@echo "W: $@ seems out of date, you may want to rebuild"
endif
endif


## Dependency handling

# Print a list of all our .v files
.PHONY: listfiles
listfiles:
	for f in $(FILES); do \
	  echo $$f; \
	done

# The top-level Makefile will use the previous rule to build a global .depend
# file. We specialize the global .depend for our specific subdirectory.
.depend: ../.depend
	sed 's_../$(SUBDIR)/__g' $< >$@.n
	mv $@.n $@

# We want to update the toplevel .depend everytime one of our files change.
# This means we potentially rebuilt the top-level .depend every time this
# subdirectory Makefile is used. However, to rebuilt the top-level .depend,
# we in turn rely on the subdirectory Makefiles to emit their list of files as
# per the 'listfiles' target above. To address this, we skip the check whenever
# the $(SKIPDEP) variable is defined, this way the top-level Makefile can
# invoke us without causing a loop.
#
# For some reason, we need to invoke $(MAKE) with -s here; the one in the
# top-level Makefile is not sufficient and the .filelist.* files end up
# containing messages from make. This is with GNU Make 4.0 and can be
# reproduced by running 'rm .filelist.*; make -C . .depend' from the top-level
# directory. The problem disappear when we drop '-C .' or add '-s'.
#
ifndef SKIPDEP
../.depend: $(FILES)
	$(MAKE) -C .. -s .depend
endif

# If it exists, load the result.
-include .depend


## Documentation

.PHONY: documentation
documentation: html
clean: clean-html

# FIXME: we may want a global thing instead of a per-directory one, so that
# hyperlinks can take us anywhere and there is one complete set of HTML files.
html: $(FILES:.v=.vo)
	$(RM) -r $@.n
	mkdir $@.n
	$(COQDOC) -R . $(SUBDIR) --html -d $@.n --toc --utf8 $(FILES)
	$(RM) -r $@
	mv $@.n $@

.PHONY: clean-html
clean-html:
	$(RM) -r html


## Auxiliary targets

# This is similar to the corresponding target in the Compcert makefile, and is
# likewise used in our "pg" scripts.
print-includes:
	@echo '$(COQFLAGS:%="%")'
