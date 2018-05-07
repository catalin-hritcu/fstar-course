include ../../Makefile.include

all:
	$(FSTAR) Heap.fsti
	$(FSTAR) Heap2.fsti
	$(FSTAR) ST.fsti
	$(FSTAR) IncrST.fst
	$(FSTAR) Incr2ST.fst
	$(FSTAR) SwapIntRefsST.fst
	$(FSTAR) SwapRefsST.fst
	$(FSTAR) CountST.fst
	$(FSTAR) FibonacciST.fst
	$(FSTAR) InvariantsST.fst

swap:
	$(MAKE) -C $(ULIB_ML)
	mkdir -p out
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml SwapIntRefsST.fst
	$(OCAMLOPT) out/SwapIntRefsST.ml -o SwapIntRefsST.exe
	./SwapIntRefsST.exe

clean:
	rm -dfr *~ *.exe out
