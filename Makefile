lakefile.olean: lakefile.lean
	lake update

LEAN_FILES := $(wildcard LeanGccJit/*.lean)
GCCJIT_ARGS := -O3 --gccjit-cmdopt=-ffast-math,-fno-semantic-interposition

build/bin/lean-testc: lakefile.olean $(LEAN_FILES)
	lake build lean-testc

build/tests/gccjit/%.o: tests/%.lean build/bin/lean-testc
	@mkdir -p build/tests/gccjit
	build/bin/lean-testc $(GCCJIT_ARGS) $< -o $@

build/tests/gccjit/%.exe: build/tests/gccjit/%.o
	@mkdir -p build/tests/gccjit
	leanc $< -o $@

build/tests/system/%.c: tests/%.lean 
	@mkdir -p build/tests/system
	lean $< -c $@ 

build/tests/system/%.exe: build/tests/system/%.c
	@mkdir -p build/tests
	leanc $< -o $@ -O3

test-%: tests/%.sh build/tests/system/%.exe build/tests/gccjit/%.exe
	@printf 'Testing %s\t' $*
	@bash $< build/tests/system/$*.exe build/tests/gccjit/$*.exe
	@printf 'PASS\n'

TESTS := $(patsubst tests/%.sh,test-%,$(wildcard tests/*.sh))
SYSTEM_EXES := $(patsubst tests/%.lean,build/tests/system/%.exe,$(wildcard tests/*.lean))
GCCJIT_EXES := $(patsubst tests/%.lean,build/tests/gccjit/%.exe,$(wildcard tests/*.lean))

.PHONY: test clean
.PRECIOUS: lakefile.olean build/bin/lean-testc build/tests/system/%.exe build/tests/gccjit/%.exe

all: $(SYSTEM_EXES) $(GCCJIT_EXES)
test: $(TESTS)

clean:
	lake clean