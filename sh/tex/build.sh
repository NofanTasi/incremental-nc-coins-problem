#! /bin/bash

cd ../../doc/tex

pdflatex paper.tex

mv paper.pdf ../../doc/pdf

echo ""
echo "FYI"
echo "file paper.pdf is in /doc/pdf"








