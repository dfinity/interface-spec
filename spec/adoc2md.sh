#!/bin/bash

git show public:./index.adoc > index.adoc
sed -i "/include::/d" index.adoc

asciidoctor -a example="" -a partial="" -b docbook -a leveloffset=+1 -o index.xml index.adoc
python3 fix.py
pandoc -t gfm  --no-highlight --wrap=none -f docbook index.xml > index.md || true

sed -i "s/^ *<div class=\"\([a-z]*\)\">/:::\1/g" index.md
sed -i "s/<\/div>/:::/g" index.md
sed -i "s/“/\"/g" index.md
sed -i "s/”/\"/g" index.md
sed -i "s/’/'/g" index.md
sed -i "s/—/---/g" index.md

python3 block.py

sed -i "s/  *{.#[\_a-z-]*}\]/]/g" index.md

python3 titles.py
