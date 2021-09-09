# Build system for CertiKOS
#
# Although we have several components, as listed in $(SUBDIRS) below, which are
# mostly loosely-coupled,
#   * all of them mostly are built in the same way (use coqc to compile a bunch
#     of .v files into .vo files);
#   * we would like to have at least some support for cross-component
#     dependencies (and be able to rebuild only the relevant parts of another
#     component that we depend on);
#   * we don't want to modify compcert/Makefile too much, instead we would
#     prefer to use it as-is, yet integrate it as a part of our build system.
#
# The approach we take is the following. Each component has its own Makefile,
# but they can include "subdir.mk" which contains the common parts. The
# dependencies are computed by the top-level Makefile, after querying each
# subdirectory for its list of files. The resulting top-level .depend can be
# specialized for each subdirectory. This way, even sub-makes can have a global
# view of dependencies and are able to rebuild foreign files if requested.

include common.mk

default: all


## Basics

.PHONY: all documentation clean
all: _CoqProject sub-all
documentation: sub-documentation
clean: sub-clean

# This pseudo-target can be used to recurse into $(SUBDIRS)
sub-%: compcert/Makefile.config
	set -e; \
	for d in $(SUBDIRS); do \
	  $(MAKE) -C $$d $*; \
	done

# Before we can recurse into compcert/ or coqrel/, we need to configure
compcert/Makefile.config coqrel/Makefile:
	@echo "You need to run ./configure first"
	@false


## CoqProject file

# The _CoqProject file is used to communicate our Coq paths to Proof General.
# Here we generate it automatically from the mappings enumerated in common.mk
# so that they can be set in a central place.
_CoqProject: common.mk
	for l in $(foreach p,$(MAPPINGS),"-R $(p) $(subst /,.,$(p))"); do \
	  echo >> $@.n "$$l"; \
	done
	mv $@.n $@


## Dependencies

# .filelist records the list of files to be fed to coqdep.
# Since files are listed in the subdirectories' Makefiles, it needs
# to be rebuilt whenever those change.
.filelist: $(patsubst %,.filelist.%,$(SUBDIRS)) common.mk
	set -e; \
	for d in $(SUBDIRS); do \
	  sed "s_^_../$$d/_" ".filelist.$$d"; \
	done > $@.n
	mv $@.n $@

# Once we have the list, we can use coqdep to compute dependencies. Note that
# the list can sometimes contain files that do not exist yet, which is why we
# need to feed its contents through the 'wildcard' function before using them.
# We need to move to some subdirectory so that coqdep produces suitable paths.
# The redundant -R arguments tweak which versions of duplicate files are used.
.depend: .filelist $(wildcard $(shell sed 's_../__' .filelist 2>/dev/null))
	mkdir -p fakedir
	@(cd fakedir && \
	  xargs coqdep $(foreach p,$(MAPPINGS),-R ../$(p) $(subst /,.,$(p)))) \
	  <$< >$@.n 2>/dev/null
	rmdir fakedir
	mv $@.n $@

# For listing files in an individual subdirectory, we use this rule as a
# fallback default.
.filelist.%: %/Makefile
	$(MAKE) -C $* -s SKIPDEP=1 listfiles > $@.n
	mv $@.n $@

# Compcert is a special case because we don't want to tweak its Makefile.
# Instead, we extract the list from the compcert/.depend file.
.filelist.compcert: compcert/Makefile compcert/Makefile.config
	$(MAKE) -C compcert depend
	perl -e 'while(<>) {print "$$1\n" if /^(.*?\.v)o/;}' compcert/.depend \
	  | sed 's/$$(ARCH)/x86/' \
	  | sed 's/$$(VARIANT)/standard/' \
	  > $@.n
	mv $@.n $@

# Ditto w/ coqrel
.filelist.coqrel: coqrel/_CoqProject coqrel/Makefile
	csplit -f $@ $< '%^$$%1'
	mv $(@)00 $@

# Clean up dependency-related files
.PHONY: clean-dep
clean: clean-dep
clean-dep:
	$(RM) .depend .filelist $(patsubst %,.filelist.%,$(SUBDIRS))

Makefile: .depend
