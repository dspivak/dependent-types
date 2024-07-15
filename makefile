TAR = $(wildcard *.pdf)

.PHONY: all clean

all: $(TAR)

poly-universes.pdf: poly-universes.lagda.md poly-universes.tex header.tex
	pandoc poly-universes.lagda.md -o poly-universes.tex --template default.latex -H header.tex
	pdflatex poly-universes.tex

clean:
	rm -f $(TAR)