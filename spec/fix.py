import re

tag=None

with open("index.xml", "r") as f:
  ls=f.readlines()
  with open("index.xml", "w") as g:
    for l in ls:
      m=re.search("^<section xml:id=\"(.*)\">$", l)
      if m is not None:
        tag=m.group(1)
        g.write(l)
      elif tag is not None:
        m=re.search("^<title>(.*)</title>$", l)
        assert m is not None
        if tag[0]=="_":
          g.write(l)
        else:
          g.write("<title>{} {}#{}{}</title>\n".format(m.group(1), "{", tag, "}"))
        tag=None
      else:
        g.write(l)
    g.close()
