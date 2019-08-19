OUTPUT = coqOfOCaml.native
TESTS_INPUT = $(wildcard tests/ex*.ml)
TESTS_OUTPUT = $(TESTS_INPUT:.ml=.vo)

default:
	ocamlbuild src/$(OUTPUT) -lflags -I,+compiler-libs,ocamlcommon.cmxa -use-ocamlfind -package compiler-libs,ppx_sexp_conv,sexplib,smart_print,str,yojson

clean:
	ocamlbuild -clean
	rm -Rf a.out tests/extraction tests/.ex*.aux tests/ex*.cmo tests/ex*.cmi tests/ex*.cmt tests/Nex* tests/ex*.glob tests/ex*.vo

test:
	ruby test.rb

cmt: $(TESTS_INPUT:.ml=.cmt)
exp: $(TESTS_INPUT:.ml=.exp)
v: $(TESTS_INPUT:.ml=.v)
vo: $(TESTS_INPUT:.ml=.vo)

%.cmt: %.ml
	ocamlc -bin-annot $<

%.exp: %.cmt default
	./$(OUTPUT) -mode exp $< >$@

%.v: %.cmt default
	./$(OUTPUT) -mode v $< >$@

%.vo: %.v
	coqc $<
