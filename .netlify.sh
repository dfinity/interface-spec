#!/usr/bin/env bash

#
# Build an ic portal preview using md files
#

git clone https://github.com/dfinity/portal _portal
git submodule update --init --recursive

cd _portal
npm i

cp ../spec/ic-interface-spec.md ./docs/references/
cp ../spec/interface-spec-changelog.md ./docs/references/

npm run build
