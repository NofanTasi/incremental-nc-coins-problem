#! /bin/bash

# Define the help function
show_help() {
    echo "Usage: $(basename "$0") [options]"
    echo ""
    echo "Options:"
    echo "  -h, -help, --help        Show this help message and exit"
    echo ""
    echo "  -incremental n,          incremental nxn square"
    echo ""
    echo "  -coins n c,              (n,c)-coins solution"
    echo ""
    echo "  -incremental -v n,       incremental nxn square with verification"
    echo ""
    echo "  -coins -v n c,           (n,c)-coins solution with verification"
    echo ""
    echo "Example:"
    echo "  ./run.sh -h"
    echo "  ./run.sh -incremental 5"
    echo "  ./run.sh -coins 5 2"
    echo "  ./run.sh -incremental -v 5"
    echo "  ./run.sh -coins -v 5 2"    
}

if [[ "$1" == "-help" || "$1" == "--help" || "$1" == "-h" ]]; then
    show_help
    exit 0
fi

if [[ "$1" == "-incremental" ]]; then
    ../../bin/lean/Incremental-NC-Coins "$1" "$2"
fi

if [[ "$1" == "-coins" ]]; then
    ../../bin/lean/Incremental-NC-Coins "$1" "$2" "$3"
fi

if [[ "$1" == "-incremental" && "$2" == "-v" ]]; then
    ../../bin/lean/Incremental-NC-Coins "$1" "$2" "$3"
fi

if [[ "$1" == "-coins" && "$2" == "-v" ]]; then
    ../../bin/lean/Incremental-NC-Coins "$1" "$2" "$3" "$4"
fi

if [[ $# -eq 0 ]]; then
    echo "use ./run.sh -h for help"
fi

