let 
  nixpkgs = builtins.fetchTarball {
    # Note: avoid Agda 2.6.4 due to https://github.com/agda/agda/issues/6654
    # name = "nixpkgs-unstable-2024-01-31";
    # url = "https://github.com/NixOS/nixpkgs/archive/5ad9903c16126a7d949101687af0aa589b1d7d3d.tar.gz";

    name = "nixpkgs-unstable-2023-07-04";
    url = "https://github.com/NixOS/nixpkgs/archive/8aeb0de93dd371d4e578f1d4e21c4ddf8a8460e0.tar.gz";
    # Hash obtained using `nix-prefetch-url --unpack <url>`
    sha256 = "04gbhh5z21flq9vxdirq1gn4cshdmq4j474amp33zh7w13nndhzi";
  };

  pkgs = import nixpkgs {};

  # Agda uses the AGDA_DIR environmental variable to determine where to load
  # default libraries from. This should have a few files in it, we only need 
  # the "defaults" files generated below.
  agdaDir = pkgs.stdenv.mkDerivation {
    name = "agdaDir";
    phases = [ "installPhase" ];
    installPhase = ''
      mkdir $out
      echo "standard-library" >> $out/defaults
    '';
  };
in
with pkgs; mkShell {
  buildInputs = [
    (agda.withPackages (ps: [
      ps.standard-library
    ]))
  ];

  LOCALE_ARCHIVE = "${glibcLocales}/lib/locale/locale-archive";

  AGDA_DIR = agdaDir;
}