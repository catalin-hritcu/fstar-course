include ../../Makefile.include

all:
	$(FSTAR) Fact.fst
	$(FSTAR) Fun.fst
	$(FSTAR) Types.fst
	$(FSTAR) Purity.fst
	$(FSTAR) Divergence.fst
	$(FSTAR) DivergenceEvalClosed.fst
	$(FSTAR) Rev.fst
	$(FSTAR) AppendLength.fst
	$(FSTAR) Stack.fst
	$(FSTAR) StackClient.fst
	$(FSTAR) RefinedStackClient.fst
	$(FSTAR) RefinedStack.fst
	$(FSTAR) AbstractStack.fst
	$(FSTAR) AbstractStackClient.fst

divergence:
#	$(MAKE) -C $(ULIB_ML)
	mkdir -p out
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml Divergence.fst
	$(OCAMLOPT) out/Divergence.ml -w p -o Divergence.exe
	./Divergence.exe

clean:
	rm -dfr *~ *.exe out
