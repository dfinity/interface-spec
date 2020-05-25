{ system ? builtins.currentSystem }:
(import ../default.nix {inherit system;}).public-spec
