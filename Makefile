MKDIR := $(dir $(realpath $(firstword $(MAKEFILE_LIST))))
BASEDIR := $(PWD)

.phony: %

%:
	# cd $(MKDIR) && ocaml compiler.ml $(BASEDIR)/$@.scm > $@.s && nasm -f elf64 -o $@.o $@.s && gcc -static -m64 -o $@ $@.o && mv $@ $(BASEDIR)
	# Below we inserted the exact same line as above, only without the "mv .." which gives a warning.
	cd $(MKDIR) && ocaml compiler.ml $(BASEDIR)/$@.scm > $@.s && nasm -g -f elf64 -o $@.o $@.s && gcc -g -static -m64 -o $@ $@.o # && mv $@ $(BASEDIR)

	# used for self-testing purposes (compiles an assembly file and links it):
	# nasm -f elf64 -o $@.o $@.s && gcc -static -m64 -o $@ $@.o
