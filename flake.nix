{
  description = "A devShell example";

  inputs = {
    nixpkgs.url      = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils.url  = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
        };
        # racket-ls = import
            # ( pkgs.fetchFromGitHub
                # {
                    # owner = "jeapostrophe";
                    # repo = "racket-langserver";
                    # rev= "a1141f0871a55c036949d0bb0179fddbf86a97cd";
                    # sha256= "uaXbvVPGIUyXWpHldD999DC8c2fWOHSC+1McIeCID34=";
                # }
            # );
        # racket-format = import
            # ( pkgs.fetchFromGitHub
                # {
                    # owner = "russellw";
                    # repo = "racket-format";
                    # rev= "b3deb07903371448476e3ce5da836e53cae59456";
                    # sha256= "WWjGEakULII1V0A2RmZ6m8k07HVv3yjWeOrBspXoszE=";
                # }
            # );
      in
      with pkgs;
      {
        devShell = mkShell {
          buildInputs = [
            racket
            # racket-ls
            # racket-format
          ];

          # shellHook = ''
            # alias ls=exa
            # alias find=fd
          # '';
        };
      }
    );
}
