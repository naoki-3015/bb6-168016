# Rocq/Coq 8.18.0 workspace toolchain (Ubuntu noble .debs extracted
# under ~/workspace/coq-toolchain; no system install).
T=$HOME/workspace/coq-toolchain
export LD_LIBRARY_PATH=$T/usr/lib/ocaml/stublibs:$T/usr/lib/ocaml:$T/usr/lib/x86_64-linux-gnu
export CAML_LD_LIBRARY_PATH=$T/usr/lib/ocaml/stublibs
export COQLIB=$T/usr/lib/ocaml/coq
export OCAMLFIND_CONF=$HOME/workspace/ocamlfind.conf
export OCAMLLIB=$T/usr/lib/ocaml
export PATH=$T/usr/bin:$PATH
