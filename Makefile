OUTPUT = coqOfOCaml.native
TESTS_INPUT = $(wildcard tests/ex*.ml)
TESTS_OUTPUT = $(TESTS_INPUT:.ml=.vo)

default:
	ocamlbuild $(OUTPUT) -lflags -I,+compiler-libs,ocamlcommon.cmxa -package smart_print,compiler-libs
	coqc CoqOfOCaml.v

clean:
	ocamlbuild -clean
	rm -f CoqOfOCaml.vo CoqOfOCaml.glob a.out tests/ex*.cmo tests/ex*.cmi tests/ex*.cmt tests/ex*.v tests/Nex* tests/ex*.glob tests/ex*.vo

test: $(TESTS_OUTPUT)

cmt: $(TESTS_INPUT:.ml=.cmt)
exp: $(TESTS_INPUT:.ml=.exp)

%.cmt: %.ml
	ocamlc -bin-annot $<

%.exp: %.cmt default
	./$(OUTPUT) -mode exp $< >$@

%.v: %.cmt default
	./$(OUTPUT) -mode coq $< >$@

%.vo: %.v
	coqc $<