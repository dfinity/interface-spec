import re

tag=None
out=[]

with open("index.md", "r") as f:
  ls=f.readlines()
  with open("index.md", "w") as g:
    for l in ls:
      m=re.search("^-+$", l)
      if m is not None:
        out[-1] = "## " + out[-1]
      else:
        out.append(l)
    for l in out:
      g.write(l)
    g.close()
