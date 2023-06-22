#!/bin/bash

#git show 6f626529fcc1ebbbff79f57e49ee623d6ce3d67b:./index.adoc > index.adoc
#git show 6f626529fcc1ebbbff79f57e49ee623d6ce3d67b:./ic0.txt > ic0.txt

cp index.adoc index.adoc.tmp

sed -i "/include::[^0]*$/d" index.adoc

python3 fix.py

asciidoctor -a example="" -a partial="" -b docbook -a leveloffset=+1 -o index.xml index.adoc
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

sed -i "s/<https:\/\/sdk.dfinity.org\/>/the [developer docs](..\/home.mdx)/" index.md

sed -i "/DFINITY Foundation/d" index.md

sed -i "0,/warning/s//note/" index.md

sed -i "s/{\\\\#/{#/" index.md

sed -i "s/{attachmentsdir}/_attachments/g" index.md

echo -e "\n<Changelog/>" >> index.md

mv index.adoc.tmp index.adoc

cp index.md md-spec/ic-interface-spec.md
