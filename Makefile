OUTPUT = coqOfOCaml.native
TESTS_INPUT = $(wildcard tests/ex*.ml)
TESTS_OUTPUT = $(TESTS_INPUT:.ml=.vo)

default:
	ocamlbuild $(OUTPUT) -cflags -I,+compiler-libs -lflags -I,+compiler-libs,ocamlcommon.cmxa
	coqc CoqOfOCaml.v

clean:
	ocamlbuild -clean
	rm -f CoqOfOCaml.vo CoqOfOCaml.glob a.out tests/ex*.cmo tests/ex*.cmi tests/ex*.cmt tests/ex*.v tests/Nex* tests/ex*.glob tests/ex*.vo

test: $(TESTS_OUTPUT)

%.cmt: %.ml
	ocamlc -bin-annot $<

%.v: %.cmt default
	./$(OUTPUT) $< >$@

%.vo: %.v
	coqc $<