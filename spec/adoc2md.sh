#!/bin/bash

asciidoctor -a example="" -a partial="" -b docbook -a leveloffset=+1 -o index.xml index.adoc
pandoc -t gfm  --no-highlight --wrap=none -f docbook index.xml > index.md || true
