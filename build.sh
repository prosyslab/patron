#!/bin/bash
set -e

export OPAMYES=1

NCPU="$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)"
OCAML_VERSION="4.13.1"
PATRON_OPAM_SWITCH=patron-"$OCAML_VERSION"
opam init --reinit --bare --no-setup

switch_exists=no
for installed_switch in $(opam switch list --short); do
  if [[ "$installed_switch" == "$PATRON_OPAM_SWITCH" ]]; then
    switch_exists=yes
    break
  fi
done

if [ "$switch_exists" = "no" ]; then
  opam switch create $PATRON_OPAM_SWITCH ocaml-base-compiler.$OCAML_VERSION
else
  opam switch $PATRON_OPAM_SWITCH
fi

eval $(SHELL=bash opam config env --switch=$PATRON_OPAM_SWITCH)

opam pin add git@github.com:prosyslab/logger.git -n
opam pin add prosys-cil git@github.com:prosyslab/cil.git -n
opam install -j $NCPU dune prosys-cil z3 core core_unix yojson logger ocamlgraph batteries ppx_compare memtrace --assume-depexts
opam install -j $NCPU ocamlformat.0.24.1 merlin ocp-index ocp-indent ocaml-lsp-server --assume-depexts  # for development
make

