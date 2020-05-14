{ src ? { rev = null; }, ... }:
import ./ci.nix { inherit src; }
