JFLEX  = jflex 
BYACCJ = yacc -J

all: 
	$(JFLEX) term.flex
	$(BYACCJ) term.y
	echo "package fortress.theory;" >> temp1364.txt
	cat ParserVal.java >> temp1364.txt;
	mv temp1364.txt ParserVal.java
	

clean:
	rm -f TermTokenizer.java *~ *.class Parser.java ParserVal.java Lexer.java *.output

Lexer.java: term.flex
	$(JFLEX) term.flex

Parser.java: term.y
	$(BYACCJ) term.y
