with import ~/nixpkgs {};
let lean = stdenv.mkDerivation rec {
  pname = "lean";
  version = "3.15.0";

  src = fetchFromGitHub {
    owner  = "leanprover-community";
    repo   = "lean";
    rev    = "v${version}";
    sha256 = "0fl8v8n53fr5qdnabici1mj3zpmjrkssx970y3q4m48s68q665v6";
  };

  nativeBuildInputs = [ cmake ];
  buildInputs = [ gmp ];
  enableParallelBuilding = true;

  preConfigure = ''
    cd src
  '';

  meta = with stdenv.lib; {
    description = "Automatic and interactive theorem prover";
    homepage    = "https://leanprover.github.io/";
    changelog   = "https://github.com/leanprover-community/lean/blob/v${version}/doc/changes.md";
    license     = licenses.asl20;
    platforms   = platforms.unix;
    maintainers = with maintainers; [ thoughtpolice gebner ];
  };
};

mathlib = stdenv.mkDerivation rec {
  pname = "mathlib";
  version = "3.10.0";
  src = fetchFromGitHub {
    owner  = "leanprover-community";
    repo   = "mathlib";
    rev    = "dbbd696dd70936cdde1b8d0079d24542be25082b";
    sha256 = "1w4zm000k3x03lcvdfhcv19jgy5kj1iv9xyd4mccnkx5haj8ja97";
  };
  buildInputs = [ lean ];
  builder = builtins.toFile "builder.sh" "
    source $stdenv/setup
    set -ex
    mkdir mathlib 
    cp -Rv $src/* mathlib
    chmod -R u+w mathlib 
    cd mathlib 
    leanpkg configure
    lean --make src 
    mkdir -p $out
    cp -R * $out
  ";
};

in pkgs.mkShell {
    buildInputs = [ texlive.combined.scheme-full lean mathlib ghc ];
    LEAN_PATH = "${lean}/lib/lean/library:${mathlib}/src";
}
