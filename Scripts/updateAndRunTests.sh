#!/bin/bash

cp ../Tests/BOSSTests.cpp ./BOSS-prefix/src/BOSS/Tests/

cmake --build . -j4

./deps/bin/Tests --library ./libBOSSNonAdaptiveEngine.so
