all:
	bnfc --latex Swifty.cf
	bnfc -haskell Swifty.cf
	happy -gca ParSwifty.y
	alex -g LexSwifty.x
	ghc --make -O2 SwiftyInterpreter.hs -o SwiftyInterpreter

clean:
	-rm -f *.log *.aux *.hi *.o *.dvi *~ *.tex SwiftyInterpreter

distclean: clean
	-rm -f DocSwifty.* LexSwifty.* ParSwifty.* LayoutSwifty.* SkelSwifty.* PrintSwifty.* TestSwifty.* AbsSwifty.* TestSwifty ErrM.* SharedString.* ComposOp.* Swifty.dtd XMLSwifty.*
	

