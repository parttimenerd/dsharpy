#! /bin/sh

# requires the following to be installed
#   bison ccache cmake curl flex g++ g++-multilib gcc gcc-multilib git jq libboost-program-options-dev libc6-dev libgmp-dev libxml2-utils make ninja-build patch unzip wget zlib1g-dev

set -e
cd "$(dirname "$0")" 
git submodule update --recursive
(cd tools/relationscutter; git pull origin master)
(cd tools/modified_cbmc; git pull origin information_flow)
(cd tools/cbmc; git pull origin develop)
(cd tools; ./build)
