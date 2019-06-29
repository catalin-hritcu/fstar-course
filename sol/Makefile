include ../Makefile.include

all:
	$(FSTAR) Sum.fst
	$(FSTAR) Stack.fsti
	$(FSTAR) Stack.fst
	$(FSTAR) StackClient.fst
	$(FSTAR) RefinedStack.fsti
	$(FSTAR) RefinedStack.fst
	$(FSTAR) RefinedStackClient.fst
	$(FSTAR) SumST.fst
	$(FSTAR) FactorialST.fst
	$(FSTAR) InitFreezeMST.fst
	$(FSTAR) InitFreezeArrayMST.fst
	$(FSTAR) SumReify.fst
	$(FSTAR) FibonacciReify.fst
	$(FSTAR) Reader.fst

clean:
	rm -dfr *~ *.exe out
