#! /bin/bash

cd ../../bin/doc/pdf

rm incremental_cyclic_report.pdf

echo "removed incremental_cyclic_report.pdf from bin/doc/pdf"

cd ../../../doc/tex

rm incremental_cyclic_report.aux
rm incremental_cyclic_report.log
rm incremental_cyclic_report.out

echo "removed .aux .log and .out files"






