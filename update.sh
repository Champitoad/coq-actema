#!/usr/bin/env bash

git pull
git submodule update --recursive
cd actema-desktop
yarn run build-prover
cd ..
make clean && make update-api
make
