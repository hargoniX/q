#!/bin/bash
set -xe

REPO_ROOT=`git rev-parse --show-toplevel`
pushd $REPO_ROOT
cd problems/casc29
tar xvf ../../Problems.tgz
mv Problems/* .
rmdir Problems

rm -r SLH
rm -r TEQ
rm -r TFE
rm -r TFI
rm -r TFN
rm -r TNE
rm -r UEQ

pushd FEQ/FEQProblemFiles
ln -s ../../Axioms
popd

pushd FNE/FNEProblemFiles
ln -s ../../Axioms
popd

pushd FNN/FNNProblemFiles
ln -s ../../Axioms
popd

pushd FNQ/FNQProblemFiles
ln -s ../../Axioms
popd

popd
