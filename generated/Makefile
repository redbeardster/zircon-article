# Test Isabelle-extracted OCaml code (Zircon.ml)
# Requires: ocamlfind, zarith (opam install zarith ocamlfind)

.PHONY: all test clean

OCAMLFIND ?= ocamlfind
OCAMLC = $(OCAMLFIND) ocamlc -package zarith -linkpkg

all: test_example.byte

Zircon.cmo: Zircon.ml
	$(OCAMLC) -c Zircon.ml

test_example.byte: Zircon.cmo test_example.ml
	$(OCAMLC) -o $@ Zircon.cmo test_example.ml

test: test_example.byte
	./test_example.byte

clean:
	rm -f *.cmi *.cmo *.cmx *.o test_example.byte
