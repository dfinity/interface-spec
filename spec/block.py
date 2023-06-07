block=False
indent=None

with open("index.md", "r") as f:
  ls=f.readlines()
  with open("index.md", "w") as g:
    for l in ls:
      if l == "<!-- -->\n":
        block = True
        g.write("```html\n")
        continue
      if block:
        if l == "\n":
          g.write(l)
        elif l[:4] == "    ":
          if indent is None:
            indent=0
            for c in l:
              if c == ' ':
                indent+=1
              else:
                break
          g.write(l[indent:])
        else:
          g.write("```\n\n")
          g.write(l)
          block = False
          indent=None
      else:
          g.write(l)
    g.close()
