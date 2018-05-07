# This uses Madoko (https://madoko.codeplex.com/)

deck:
	@madoko pure-fun.mdk --odir=out/pure-fun | grep -v "warning: unable to read language definition" | true
	@madoko state.mdk --odir=out/state | grep -v "warning: unable to read language definition" | true
	@madoko monotonic.mdk --odir=out/monotonic | grep -v "warning: unable to read language definition" | true
	@madoko effects.mdk --odir=out/effects | grep -v "warning: unable to read language definition" | true

clean:
	rm -f *~ css.sty madoko.css madoko.sty *math-dvi.tex *math-pdf.tex *math-dvi.final.tex *math-pdf.final.tex  *.aux *.dim *.dvi *.log *.out *.upa *.dimx *.html *.log *.pdf *.upa *.upb *.bbl *.blg .*~
	rm -dfr math
