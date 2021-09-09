let
  pkgs = import <nixpkgs> {};
  coq_8_6_0 = pkgs.coq_8_6.override { version = "8.6"; };
in
with pkgs;

stdenv.mkDerivation {
  name = "certikos";

  buildInputs = with ocamlPackages; [
    ocaml menhir findlib coq_8_6_0
  ];

}
