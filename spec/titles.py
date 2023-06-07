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
      m=re.search("Canister hostname resolution", l)
      if m is not None:
        out=out[:-9]+["|Canister hostname resolution\n", "|--------------------------------------------\n", "| Hostname     | Canister id\n", "| `identity`   | `rdmx6-jaaaa-aaaaa-aaadq-cai`\n", "| `nns`        | `qoctq-giaaa-aaaaa-aaaea-cai`\n", "| `dscvr`      | `h5aet-waaaa-aaaab-qaamq-cai`\n", "| `personhood` | `g3wsl-eqaaa-aaaan-aaaaa-cai`\n", "|--------------------------------------------\n"]
      m=re.search("http-gateway.did", l)
      if m is not None:
        out=out[:-1]+["The following interface description, in [Candid syntax](https://github.com/dfinity/candid/blob/master/spec/Candid.md), describes the expected Canister interface. You can also [download the file]({attachmentsdir}/http-gateway.did).\n", "``` candid name= ic-interface file file=_attachments/http-gateway.did\n", "```\n"]
    for l in out:
      g.write(l)
    g.close()
