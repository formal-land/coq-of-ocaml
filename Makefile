default:
	dune build src/coqOfOCaml.exe

watch:
	while inotifywait src/*.ml; do clear; make; done

clean:
	dune clean
	rm -Rf a.out tests/extraction tests/.*.aux tests/Nex* tests/*.glob tests/*.vo

test:
	ruby test.rb
