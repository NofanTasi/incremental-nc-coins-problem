#! /bin/bash

cd ../../doc/tex

pdflatex incremental_cyclic_report.tex

mv incremental_cyclic_report.pdf ../../bin/doc/pdf

echo ""
echo "file incremental_cyclic_report.pdf is in bin/doc/pdf"








