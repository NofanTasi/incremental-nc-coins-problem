#! /bin/bash

cd ../pdf

rm paper.pdf

echo ""
echo "FYI"
echo "removed paper.pdf from /doc/pdf"

cd ../tex

rm paper.aux
rm paper.log
rm paper.out

echo "removed .aux .log and .out files from /doc/tex"






