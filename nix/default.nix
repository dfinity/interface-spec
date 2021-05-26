{ system ? builtins.currentSystem }:
let
  sourcesnix = builtins.fetchurl {
    url = https://raw.githubusercontent.com/nmattia/niv/v0.2.19/nix/sources.nix;
    sha256 = "1n92ka2rkdiib6ian6jh2b7fwvklnnwlp5yy5bv6ywm7m1y5hyfl";
  };
  nixpkgs_src = (import sourcesnix { sourcesFile = ./sources.json; inherit pkgs; }).nixpkgs;

  pkgs =
    import nixpkgs_src {
      inherit system;
      overlays = [
        (self: super: {
          sources = import sourcesnix { sourcesFile = ./sources.json; pkgs = super; };
        })
      ];
    };
in
pkgs
