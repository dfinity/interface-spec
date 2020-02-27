{ src ? { rev = null; }, base ? null }:
import ./ci.nix { inherit src; }
