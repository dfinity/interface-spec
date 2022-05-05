{
  system ? builtins.currentSystem,
}:

let nixpkgs = import ./nix { inherit system; }; in
let stdenv = nixpkgs.stdenv; in
let subpath = p: import ./nix/gitSource.nix p; in

rec {
  interface-spec =
    nixpkgs.stdenv.mkDerivation {
    name = "interface-spec";
    src = subpath ./spec;
    phases = [ "unpackPhase" "buildPhase" "checkPhase" ];
    buildInputs = with nixpkgs;
      [ asciidoctor plantuml jre graphviz python cpio html-proofer cddl ];
    FONTCONFIG_FILE = nixpkgs.makeFontsConf { fontDirectories = []; };
    asciidoctor_args = [
      "-r asciidoctor-diagram"
      "-a sectanchors"
      "-a plantuml-format=svg"
      "-a ditaa-format=svg"
      "-a graphviz-format=svg"
      "-a source-highlighter=rouge"
      "-a rouge-css=style"
    ];
    buildPhase = ''
      doc_path="spec"
      mkdir -p $out/$doc_path
      asciidoctor $asciidoctor_args --failure-level WARN -v \
        -a toc2 -a toclevels=3 \
        -a example -a partial \
        -a attachmentsdir=. \
        -R $PWD -D $out/$doc_path/ index.adoc
      find . -type f -name '*.png' | cpio -pdm $out/$doc_path/
      cp *.cddl $out/$doc_path
      cp *.did $out/$doc_path
      cp *.rs $out/$doc_path

      mkdir -p $out/nix-support
      echo "report spec $out/$doc_path index.html" >> $out/nix-support/hydra-build-products
    '';

    # These ones are needed for htmlproofer
    LOCALE_ARCHIVE = nixpkgs.lib.optionalString nixpkgs.stdenv.isLinux "${nixpkgs.glibcLocales}/lib/locale/locale-archive";
    LANG = "en_US.UTF-8";
    LC_TYPE = "en_US.UTF-8";
    LANGUAGE = "en_US.UTF-8";
    doCheck = true;
    checkPhase = ''
      htmlproofer --disable-external $out/$doc_path
      if [[ ! -s $out/$doc_path/index.html ]]; then
        >&2 echo "There is no $out/$doc_path/index.html or it is empty, aborting."
        exit 1
      fi

      # also check cddl
      for file in *.cddl; do cddl $file generate 1 > /dev/null; done
    '';

  };

  # for compatibility with the deployment to https://docs.dfinity.systems/public/v
  public-spec = interface-spec;

  all-systems-go = nixpkgs.releaseTools.aggregate {
    name = "all-systems-go";
    constituents = [
      interface-spec
    ];
  };
}
