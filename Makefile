OUTPUT = _build/default/src/coqOfOCaml.exe
TESTS_INPUT = $(wildcard tests/ex*.ml)
TESTS_OUTPUT = $(TESTS_INPUT:.ml=.vo)

default:
	dune build src/coqOfOCaml.exe

watch:
	while inotifywait src/*.ml; do clear; make; done

clean:
	dune clean
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
