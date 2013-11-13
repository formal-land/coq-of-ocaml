OUTPUT = coqOfOCaml.native
TESTS_INPUT = $(wildcard tests/ex*.ml)
TESTS_OUTPUT = $(TESTS_INPUT:.ml=.vo)

default:
	ocamlbuild $(OUTPUT) -cflags -I,+compiler-libs -lflags -I,+compiler-libs,ocamlcommon.cmxa

clean:
	ocamlbuild -clean
	rm -f tests/Nex* tests/ex*.glob tests/ex*.vo

test: $(TESTS_OUTPUT)

%.v: %.ml default
	./$(OUTPUT) $< >$@

%.vo: %.v
	coqc $<
