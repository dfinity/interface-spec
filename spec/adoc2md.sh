#!/bin/bash

asciidoctor -a example="" -a partial="" -a IC="Internet Computer" -a proglang=Motoko -a company-id=DFINITY -b docbook -a leveloffset=+1 -o index.xml index.adoc
pandoc -t gfm  --no-highlight --wrap=none -f docbook index.xml > index.md || true
