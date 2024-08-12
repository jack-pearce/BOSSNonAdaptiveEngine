#!/bin/bash

if [[ $EUID -ne 0 ]]; then
    echo "This script must be run as root (with sudo)."
    exit 1
fi

cmake -DCMAKE_BUILD_TYPE=Release -DBOSS_SOURCE_REPOSITORY=/home/jcp122/repos/BOSS -DBOSS_SOURCE_BRANCH=bootstrap_load_partition -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ ..

sudo make -j 4

./deps/bin/Tests --library ./libBOSSNonAdaptiveEngine.so
