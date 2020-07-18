#! /bin/zsh

rm -rf build/ttc/testMutating.ttc build/ttc/testMutating.ttm
build/exec/idris2dev -o testMutating testMutating.idr
time build/exec/testMutating

