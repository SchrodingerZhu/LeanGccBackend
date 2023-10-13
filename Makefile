lakefile.olean: lakefile.lean
	lake update

build/bin/lean-testc: lakefile.olean
	lake build lean-testc

build/tests/gccjit/%.o: tests/%.lean build/bin/lean-testc
	@mkdir -p build/tests/gccjit
	build/bin/lean-testc $< $@

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
	bash $< build/tests/system/$*.exe build/tests/gccjit/$*.exe

TESTS := $(patsubst tests/%.sh,test-%,$(wildcard tests/*.sh))

.PHONY: test clean
.PRECIOUS: lakefile.olean

test: $(TESTS)

clean:
	lake clean