# Generic PICO (class and method type parameters, casts).
# Build: make        Clean: make clean
all: CoqMakefile
	$(MAKE) -f CoqMakefile

CoqMakefile: _RocqProject
	coq_makefile -f _RocqProject -o CoqMakefile

clean:
	if [ -f CoqMakefile ]; then $(MAKE) -f CoqMakefile clean; fi
	rm -f CoqMakefile CoqMakefile.conf

.PHONY: all clean
