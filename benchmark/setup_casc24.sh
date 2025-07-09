#!/bin/bash
set -xe

REPO_ROOT=`git rev-parse --show-toplevel`
pushd $REPO_ROOT
mkdir -p problems/casc24
cd problems/casc24
tar xvf ../../Problems.tgz
mv Problems/* .
rmdir Problems

pushd FEQ
ln -s ../../casc29/Axioms
popd

pushd FNE
ln -s ../../casc29/Axioms
popd

pushd FNN
ln -s ../../casc29/Axioms
popd

pushd FNQ
ln -s ../../casc29/Axioms
popd

popd
