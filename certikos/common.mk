## Common make definitions

# This file contains the definitions that are common to the top-level Makefile
# and those for subdirectories.

MAPPINGS= \
  compcert/common \
  compcert/cfrontend \
  compcert/lib \
  compcert/backend \
  compcert/cparser \
  compcert/flocq \
  compcert/driver \
  compcert/x86_64 \
  compcert/x86 \
  compcertx/common \
  compcertx/cfrontend \
  compcertx/backend \
  compcertx/driver \
  compcertx/x86 \
  coqrel \
  liblayers \
  tutorial \
  # \
  mcertikos \
  mcertikos/mm \

SUBDIRS= \
  $(shell for x in $(MAPPINGS); do echo $$x; done | sed 's:/.*::' | uniq)

