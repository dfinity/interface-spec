#!/usr/bin/env bash

#
# Build an ic portal preview using md files
#

git clone https://github.com/dfinity/portal _portal
cd _portal

git submodule update --init --remote

npm i

cp ../spec/ic-interface-spec.md ./docs/references/
cp ../spec/interface-spec-changelog.md ./docs/references/

npm run build
