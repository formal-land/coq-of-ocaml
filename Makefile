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

%.cmt: %.ml
	ocamlc -bin-annot $<

%.v: %.cmt default
	./$(OUTPUT) -monad $< >$@

%.vo: %.v
	coqc $<