include ../Makefile.include

all:
	$(FSTAR) Sum.fst
	$(FSTAR) Stack.fsti
	$(FSTAR) Stack.fst
	$(FSTAR) StackClient.fst
	$(FSTAR) RefinedStackClient.fst
	$(FSTAR) SwapIntRefsST.fst
	$(FSTAR) SumST.fst
	$(FSTAR) FactorialST.fst
	$(FSTAR) InitFreezeMST.fst
	$(FSTAR) SumReify.fst
	$(FSTAR) FibonacciReify.fst
	$(FSTAR) Reader.fst

clean:
	rm -dfr *~ *.exe out
