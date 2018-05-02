all: evaluation expr miniml expr_test evaluation_test

evaluation: evaluation.ml
	ocamlbuild  evaluation.byte

expr: expr.ml
	ocamlbuild  expr.byte

miniml: miniml.ml
	ocamlbuild  miniml.byte

expr_test: expr_test.ml
	ocamlbuild  expr_test.byte

evaluation_test: evaluation_test.ml
	ocamlbuild  evaluation_test.byte

clean:
	rm -rf _build *.byte
