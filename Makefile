COQ_MAKEFILE := coq_makefile
MAKE := make

SRC_DIR := src
COQ_PROJECT :=_CoqProject
COQ_GENERATED_MAKEFILE := CoqMakefile

all: CoqMakefile
	$(MAKE) -f $(COQ_GENERATED_MAKEFILE)

CoqMakefile: _CoqProject
	$(COQ_MAKEFILE) -f $(COQ_PROJECT) -o $(COQ_GENERATED_MAKEFILE)

clean:
ifneq ("$(wildcard $(COQ_GENERATED_MAKEFILE))","")
	$(MAKE) -f $(COQ_GENERATED_MAKEFILE) cleanall
endif
