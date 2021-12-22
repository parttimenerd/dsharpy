#! /bin/sh

# requires the following to be installed
#   make cmake ninja-build gcc g++ flex bison libxml2-utils patch

set -e
cd "$(dirname "$0")" 
git submodule update --recursive
(cd tools/relationscutter; git pull origin master)
(cd tools/modified_cbmc; git pull origin information_flow)
(cd tools/cbmc; git pull origin develop)
(cd tools; ./build)
