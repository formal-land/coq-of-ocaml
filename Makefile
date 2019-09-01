OUTPUT = coqOfOCaml.native
TESTS_INPUT = $(wildcard tests/ex*.ml)
TESTS_OUTPUT = $(TESTS_INPUT:.ml=.vo)

default:
	OCAMLFIND_IGNORE_DUPS_IN=`ocamlc -where`/compiler-libs ocamlbuild src/$(OUTPUT) -cflag -bin-annot -lflags -I,+compiler-libs,ocamlcommon.cmxa -use-ocamlfind -package compiler-libs,ppx_sexp_conv,sexplib,smart_print,str,yojson

clean:
	ocamlbuild -clean
	rm -Rf a.out tests/extraction tests/.*.aux tests/*.cmo tests/*.cmi tests/*.cmt tests/Nex* tests/*.glob tests/*.vo

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
