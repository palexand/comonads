all:	eodf.pdf ;

eodf.pdf:	eodf.tex ;
	pdflatex eodf.tex

eodf.tex:	;
	lhs2TeX --math eodf.lhs > eodf.tex

tidy:	;
	rm -f *.aux
	rm -f *.bbl
	rm -f *.log
	rm -f *~

clean:	;
	rm -f *.aux
	rm -f *.bbl
	rm -f *.log
	rm -f *~
	rm -f eodf.tex

