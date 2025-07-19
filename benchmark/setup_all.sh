#!/bin/bash
set -xe

REPO_ROOT=`git rev-parse --show-toplevel`
pushd $REPO_ROOT
mkdir -p problems/tptp-full
cd problems/tptp-full
tar xvf ../../TPTP-v9.0.0.tgz
mv TPTP-v9.0.0/Problems/* .
rmdir TPTP-v9.0.0/Problems
mv TPTP-v9.0.0/Axioms .
# rm -r TPTP-v9.0.0

#rm -r SLH
#rm -r TEQ
#rm -r TFE
#rm -r TFI
#rm -r TFN
#rm -r TNE
#rm -r UEQ

# This could/should have been a function but this setup script is write once
pushd AGT
ln -s ../Axioms
popd

pushd ALG
ln -s ../Axioms
popd

pushd ANA
ln -s ../Axioms
popd

pushd ARI
ln -s ../Axioms
popd

pushd BIO
ln -s ../Axioms
popd

pushd BOO
ln -s ../Axioms
popd

pushd CAT
ln -s ../Axioms
popd

pushd COL
ln -s ../Axioms
popd

pushd COM
ln -s ../Axioms
popd

pushd CSR
ln -s ../Axioms
popd

pushd DAT
ln -s ../Axioms
popd

pushd FLD
ln -s ../Axioms
popd

pushd GEG
ln -s ../Axioms
popd

pushd GEO
ln -s ../Axioms
popd

pushd GRA
ln -s ../Axioms
popd

pushd GRP
ln -s ../Axioms
popd

pushd HAL
ln -s ../Axioms
popd

pushd HEN
ln -s ../Axioms
popd

pushd HWC
ln -s ../Axioms
popd

pushd HWV
ln -s ../Axioms
popd

pushd ITP
ln -s ../Axioms
popd

pushd KLE
ln -s ../Axioms
popd

pushd KRS
ln -s ../Axioms
popd

pushd LAT
ln -s ../Axioms
popd

pushd LCL
ln -s ../Axioms
popd

pushd LDA
ln -s ../Axioms
popd

pushd LIN
ln -s ../Axioms
popd

pushd MED
ln -s ../Axioms
popd

pushd MGT
ln -s ../Axioms
popd

pushd MSC
ln -s ../Axioms
popd

pushd MVA
ln -s ../Axioms
popd

pushd NLP
ln -s ../Axioms
popd

pushd NUM
ln -s ../Axioms
popd

pushd NUN
ln -s ../Axioms
popd

pushd PHI
ln -s ../Axioms
popd

pushd PLA
ln -s ../Axioms
popd

pushd PRD
ln -s ../Axioms
popd

pushd PRO
ln -s ../Axioms
popd

pushd PUZ
ln -s ../Axioms
popd

pushd QUA
ln -s ../Axioms
popd

pushd RAL
ln -s ../Axioms
popd

pushd REL
ln -s ../Axioms
popd

pushd RNG
ln -s ../Axioms
popd

pushd ROB
ln -s ../Axioms
popd

pushd SCT
ln -s ../Axioms
popd

pushd SET
ln -s ../Axioms
popd

pushd SEU
ln -s ../Axioms
popd

pushd SEV
ln -s ../Axioms
popd

pushd SWB
ln -s ../Axioms
popd

pushd SWC
ln -s ../Axioms
popd

pushd SWV
ln -s ../Axioms
popd

pushd SWW
ln -s ../Axioms
popd

pushd SYN
ln -s ../Axioms
popd

pushd SYO
ln -s ../Axioms
popd

pushd TOP
ln -s ../Axioms
popd

popd
