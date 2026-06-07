## this Makefile, as well as the test setup in Makefile.coq.local, is copied
## from std++ (https://gitlab.mpi-sws.org/iris/stdpp)

# Forward most targets to Coq makefile (with some trick to make this phony)
%: Makefile.coq phony
	+@make -f Makefile.coq $@

all: Makefile.coq
	+@make -f Makefile.coq all
.PHONY: all

all_using_opam: Makefile.using_opam.coq
	+@make -f Makefile.using_opam.coq all
.PHONY: all

clean: Makefile.coq
	+@make -f Makefile.coq clean
	find src \( -name "*.d" -o -name "*.vo" -o -name "*.vo[sk]" -o -name "*.aux" -o -name "*.cache" -o -name "*.glob" -o -name "*.vio" \) -print -delete || true
	rm -f Makefile.coq .lia.cache
.PHONY: clean

# Create Coq Makefile.
Makefile.coq: _CoqProject Makefile
	"$(COQBIN)coq_makefile" -f _CoqProject -o Makefile.coq

Makefile.using_opam.coq: _CoqProject_using_opam Makefile
	"$(COQBIN)coq_makefile" -f _CoqProject_using_opam -o Makefile.using_opam.coq

# Some files that do *not* need to be forwarded to Makefile.coq
Makefile: ;
_CoqProject: ;
_CoqProject_using_opam: ;

# Phony wildcard targets
phony: ;
.PHONY: phony
