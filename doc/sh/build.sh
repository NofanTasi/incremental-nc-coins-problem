#! /bin/bash

cd ../tex

pdflatex paper.tex
pdflatex annex.tex

mv paper.pdf ../pdf
mv annex.pdf ../pdf

echo ""
echo "FYI"
echo "file paper.pdf is in /doc/pdf"
echo "file annex.pdf is in /doc/pdf"








