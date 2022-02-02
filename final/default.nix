with import <nixpkgs> {};

pkgs.mkShell {
    buildInputs = [ texlive.combined.scheme-full ];
}
