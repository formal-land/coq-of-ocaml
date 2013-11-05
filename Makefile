default:
	ocamlbuild coqOfOCaml.native -cflags -I,+compiler-libs -lflags -I,+compiler-libs,ocamlcommon.cmxa

clean:
	ocamlbuild -clean
