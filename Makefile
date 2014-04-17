OUTPUT = coqOfOCaml.native
TESTS_INPUT = $(wildcard tests/ex*.ml)
TESTS_OUTPUT = $(TESTS_INPUT:.ml=.vo)

default:
	ocamlbuild $(OUTPUT) -lflags -I,+compiler-libs,ocamlcommon.cmxa -package smart_print,compiler-libs
	coqc CoqOfOCaml.v

clean:
	ocamlbuild -clean
	rm -f CoqOfOCaml.vo CoqOfOCaml.glob a.out tests/ex*.cmo tests/ex*.cmi tests/ex*.cmt tests/Nex* tests/ex*.glob tests/ex*.vo

test: $(OUTPUT)
	ruby test.rb

cmt: $(TESTS_INPUT:.ml=.cmt)
exp: $(TESTS_INPUT:.ml=.exp)
effects: $(TESTS_INPUT:.ml=.effects)
monadise: $(TESTS_INPUT:.ml=.monadise)
interface: $(TESTS_INPUT:.ml=.interface)
v: $(TESTS_INPUT:.ml=.v)
vo: $(TESTS_INPUT:.ml=.vo)

%.cmt: %.ml
	ocamlc -bin-annot $<

%.exp: %.cmt default
	./$(OUTPUT) -mode exp $< >$@

%.effects: %.cmt default
	./$(OUTPUT) -mode effects $< >$@

%.monadise: %.cmt default
	./$(OUTPUT) -mode monadise $< >$@

%.interface: %.cmt default
	./$(OUTPUT) -mode interface $< >$@

%.v: %.cmt default
	./$(OUTPUT) -mode v $< >$@

%.vo: %.v
	coqc $<