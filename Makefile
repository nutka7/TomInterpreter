all:
	happy -gcai ParTom.y
	alex -g LexTom.x
	latex DocTom.tex; dvips DocTom.dvi -o DocTom.ps
	ghc --make TestTom.hs -o TestTom
	ghc --make Interpreter.hs -o Interpreter
clean:
	-rm -f Interpreter TestTom
	-rm -f *.log *.aux *.hi *.o *.dvi *.info
	-rm -f DocTom.ps
distclean: clean
	-rm -f DocTom.* LexTom.* ParTom.* LayoutTom.* SkelTom.* PrintTom.* TestTom.* AbsTom.* TestTom ErrM.* SharedString.* Tom.dtd XMLTom.* Makefile*

