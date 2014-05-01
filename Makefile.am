ACLOCAL_AMFLAGS = -I m4

check_PROGRAMS = test93$(EXEEXT) test94$(EXEEXT)

test93_SOURCES = test/test93.ml

test94_SOURCES = test/test94.ml

bin_SCRIPTS = relts$(EXEEXT) random_lts$(EXEEXT)

PACKAGES = -package ocamlgraph
LIBS     = -linkpkg

OCAMLCOMP = $(OCAMLFIND) ocamlc $(PACKAGES) -c -o $@ $^
OCAMLLINK = $(OCAMLFIND) ocamlc $(PACKAGES) $(LIBS) -o $@ $^

CXXLINK = $(CXX) $(CXXFLAGS) -o $@ $^
CXXCOMP = $(CXX) $(CXXFLAGS) -c -o $@ $^

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

relts$(EXEEXT): LTS_modules.cmo relts.cmo
	$(OCAMLLINK)

LTS_modules_test$(EXEEXT): LTS_modules.cmo LTS_modules_test.cmo
	$(OCAMLLINK)

random_lts$(EXEEXT): random_lts.o
	$(CXXLINK)

test93$(EXEEXT): LTS_modules.cmo test/test93.cmo
	$(OCAMLFIND) ocamlc $(PACKAGES) $(LIBS) $^ -o $@

test94$(EXEEXT): LTS_modules.cmo test/test94.cmo
	$(OCAMLFIND) ocamlc $(PACKAGES) $(LIBS) $^ -o $@

.ml.cmo:
	$(OCAMLCOMP)

relts.cmo: LTS_modules.cmo

.cpp.o:
	$(CXXCOMP)

TESTS = test93$(EXEEXT) test94$(EXEEXT)

EXTRA_DIST = LTS_modules.ml relts.ml random_lts.cpp LTS_modules_test.ml $(TEST_DOT_FILES)

CLEANFILES = *.cmi *.cmo *.o $(bin_SCRIPTS) *~
