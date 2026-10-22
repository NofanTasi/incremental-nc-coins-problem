#! /bin/bash

cd ../tex

pdflatex paper.tex

mv paper.pdf ../pdf

echo ""
echo "FYI"
echo "file paper.pdf is in /doc/pdf"








