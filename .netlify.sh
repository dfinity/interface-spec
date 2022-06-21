#!/usr/bin/env bash

#
# Deploy a preview of the interface specification to netlify
#

set -e

export NP_GIT=$(which git)

wget -nv https://github.com/DavHau/nix-portable/releases/download/v009/nix-portable
chmod +x nix-portable

./nix-portable nix-build -A interface-spec default.nix

# The "result" symlink only valid inside the nix-portable sandbox, so use nix-shell
./nix-portable nix-shell -p bash --run "cp -rL result/spec/ _netlify-deploy"

chmod -R u+w _netlify-deploy
