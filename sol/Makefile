include ../Makefile.include

all:
	$(FSTAR) Incr.fst
	$(FSTAR) Sum.fst
	$(FSTAR) RefinedStackLength.fst
	$(FSTAR) RefinedStackLengthClient.fst
	$(FSTAR) SumST.fst
	$(FSTAR) InitFreezeMST.fst

clean:
	rm -dfr *~ *.exe out
