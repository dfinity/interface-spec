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
        m=re.search("^=+$", l)
        if m is not None:
          out.insert(0, "import Changelog from './_attachments/interface-spec-changelog.md';\n\n")
          out[-1] = "# " + out[-1]
        else:
          out.append(l)
      m=re.search("Canister hostname resolution", l)
      if m is not None:
        out=out[:-9]+["|Canister hostname resolution\n", "|--------------------------------------------\n", "| Hostname     | Canister id\n", "| `identity`   | `rdmx6-jaaaa-aaaaa-aaadq-cai`\n", "| `nns`        | `qoctq-giaaa-aaaaa-aaaea-cai`\n", "| `dscvr`      | `h5aet-waaaa-aaaab-qaamq-cai`\n", "| `personhood` | `g3wsl-eqaaa-aaaan-aaaaa-cai`\n", "|--------------------------------------------\n"]
      m=re.search("http-gateway.did", l)
      if m is not None:
        out=out[:-1]+["The following interface description, in [Candid syntax](https://github.com/dfinity/candid/blob/master/spec/Candid.md), describes the expected Canister interface. You can also [download the file]({attachmentsdir}/http-gateway.did).\n", "``` candid name= ic-interface file file=_attachments/http-gateway.did\n", "```\n"]
      m=re.search("ic.did", l)
      if m is not None:
        out=out[:-1]+["The [interface description](_attachments/ic.did) below, in [Candid syntax](https://github.com/dfinity/candid/blob/master/spec/Candid.md), describes the available functionality.\n", "``` candid name= ic-interface file file=_attachments/ic.did\n", "```\n"]
      m=re.search("actor Developer actor User participant", l)
      if m is not None:
        out=out[:-3] + ["```plantuml\n", "    actor Developer\n", "    actor User\n", "    participant \"Internet Computer\" as IC\n", "    participant \"Canister 1\" as Can1\n", "    Developer -> IC : /submit create canister\n", "    create Can1\n", "    IC -> Can1 : create\n", "    Developer <-- IC : canister-id=1\n", "    Developer -> IC : /submit install module\n", "    IC -> Can1 : initialize\n", "    |||\n", "    User -> IC : /submit call \"hello\"\n", "    IC -> Can1 : hello\n", "    return \"Hello world!\"\n", "    User <-- IC : \"Hello World!\"\n", "```\n", "**A typical use of the Internet Computer. (This is a simplified view; some of the arrows represent multiple interaction steps or polling.)**\n"]
      m=re.search("endif", l)
      if m is not None:
        out.append("```")
      m=re.search("This yields the following interaction diagram", l)
      if m is not None:
        out.append("```plantuml")
    for l in out:
      g.write(l)
    g.close()
