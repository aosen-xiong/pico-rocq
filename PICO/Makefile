# The PICO mechanization (no generics), kept from the PICO paper's artifact.
# Build: make        Check: make check        Clean: make clean
PROJECT_DIR := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))

all: CoqMakefile
	$(MAKE) -f CoqMakefile

CoqMakefile: _RocqProject
	coq_makefile -f _RocqProject -o CoqMakefile

check: all
	python3 "$(PROJECT_DIR)../scripts/check-no-axioms-admits.py" "$(PROJECT_DIR)"
	python3 "$(PROJECT_DIR)../scripts/check-public-assumptions.py" "$(PROJECT_DIR)" "$(PROJECT_DIR)public-theorems.txt"

clean:
	if [ -f CoqMakefile ]; then $(MAKE) -f CoqMakefile clean; fi
	rm -f CoqMakefile CoqMakefile.conf .CoqMakefile.d

.PHONY: all check clean
