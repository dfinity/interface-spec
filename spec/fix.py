import re

tag=None

with open("index.adoc", "r") as f:
  ls=f.readlines()
  with open("index.adoc", "w") as g:
    for l in ls:
      m=re.search("^\[#(.*)]$", l)
      if m is not None:
        tag=m.group(1)
        g.write(l)
      elif tag is not None:
        if tag[0]=="_":
          g.write(l)
        else:
          g.write("{} {}#{}{}\n".format(l[:-1], "{", tag, "}"))
        tag=None
      else:
        g.write(l)
    g.close()
