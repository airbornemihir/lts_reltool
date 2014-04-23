ACLOCAL_AMFLAGS = -I m4

bin_SCRIPTS = relts$(EXEEXT)

PACKAGES = -package ocamlgraph
LIBS     = graph.cmo -linkpkg

TEST_DOT_FILES = \
test/l03.dot\
test/l04.dot\
test/l05.dot\
test/l06.dot\
test/l07.dot\
test/l08.dot\
test/l09.dot\
test/l10.dot\
test/l11.dot\
test/l12.dot\
test/l13.dot\
test/l14.dot\
test/l15.dot\
test/l16.dot\
test/l17.dot\
test/l18.dot\
test/l19.dot\
test/l20.dot\
test/l21.dot\
test/l22.dot\
test/l23.dot\
test/l24.dot\
test/l25.dot

# relts$(EXEEXT): $(TEST_DOT_FILES)

relts$(EXEEXT): Alt_Fernandez_modules.cmo
	$(OCAMLFIND) ocamlc $(PACKAGES) $(LIBS) $^ -o $@

.ml.cmo:
	ocamlfind ocamlc $(PACKAGES) -c $< -o $@

EXTRA_DIST = Alt_Fernandez_modules.ml $(TEST_DOT_FILES)

CLEANFILES = *.cmi *.cmo $(bin_SCRIPTS) *~
