#!/bin/bash

set -xe
REPO_ROOT=`git rev-parse --show-toplevel`
pushd $REPO_ROOT > /dev/null

TARGET_DIR="problems/pelletier_cnf"
SRC_DIR="problems/pelletier_problems"
mkdir -p $TARGET_DIR
for problem in problems/pelletier_problems/*.p; do
  filename=$(basename $problem)
  ../eprover $problem --cnf &> $TARGET_DIR/$filename
done

pushd $TARGET_DIR > /dev/null
sed -i '/^#/d' *.p
popd > /dev/null
popd > /dev/null
