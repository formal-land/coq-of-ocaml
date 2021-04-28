default:
	dune build -p coq-of-ocaml

watch:
	while inotifywait src/*.ml; do clear; make; done

clean:
	dune clean
	rm -Rf a.out tests/extraction tests/.*.aux tests/Nex* tests/*.glob tests/*.vo* *.coverage

test:
	ruby test.rb

coverage:
	rm *.coverage || true
	ruby test.rb --with-coverage
	bisect-ppx-report html
	@echo "Outputting the coverage report in '_coverage/index.html'"
