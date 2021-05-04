{ pkgs ? import <nixpkgs> {}}:

pkgs.mkShell {
  #RUST_SRC_PATH = pkgs.rustPlatform.rustLibSrc;
  nativeBuildInputs = [
    pkgs.niv
    pkgs.rust-analyzer
    pkgs.rustfmt
    pkgs.just
    pkgs.clippy
    pkgs.rustfmt
    pkgs.rustc
    pkgs.cargo
    pkgs.cargo-watch
    pkgs.cargo-deny
    pkgs.pre-commit
    pkgs.git # needed for pre-commit install
    #pythonEnv

    pkgs.qemu_kvm
    pkgs.gdb
    pkgs.tmux # needed for integration test
  ]; #++ vmsh.nativeBuildInputs;
  #buildInputs = vmsh.buildInputs;
  shellHook = ''
    pre-commit install
  '';
}
