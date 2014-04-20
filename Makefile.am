ACLOCAL_AMFLAGS = -I m4

bin_SCRIPTS = relts$(EXEEXT)

PACKAGES = -package ocamlgraph
LIBS     = graph.cmo -linkpkg

relts$(EXEEXT): Alt_Fernandez_modules.cmo
	$(OCAMLFIND) ocamlc $(PACKAGES) $(LIBS) $^ -o $@

.ml.cmo:
	ocamlfind ocamlc $(PACKAGES) -c $< -o $@

EXTRA_DIST = Alt_Fernandez_modules.ml

CLEANFILES = *.cmi *.cmo $(bin_SCRIPTS) *~
