#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
test "$(uname -sm)" = 'Darwin arm64' || { echo 'This bootstrap targets macOS ARM64.' >&2; exit 1; }
mkdir -p .tools/bin perf/artifacts perf/results
if [ ! -x .tools/bin/opam ]; then
  curl -fL --retry 3 https://github.com/ocaml/opam/releases/download/2.6.1/opam-2.6.1-arm64-macos -o .tools/bin/opam
  chmod +x .tools/bin/opam
fi
echo '3e7f67bda3ba0bf72f597917b17dc337ed5a1bd48224df8b747bb35ce05c569e  .tools/bin/opam' | shasum -a 256 -c -
export OPAMROOT="$PWD/.opam-root"
export OPAMSWITCH="$PWD"
export PATH="$PWD/.tools/bin:$PATH"
export PKG_CONFIG_PATH="/opt/homebrew/opt/gmp/lib/pkgconfig${PKG_CONFIG_PATH:+:$PKG_CONFIG_PATH}"
# A newer Xcode SDK can link pipe2/dup3 weak symbols absent from the running
# macOS. Autoconf link probes otherwise accept them and Unix.pipe segfaults.
export ac_cv_func_pipe2=no
export ac_cv_func_dup3=no
if ! command -v pkgconf >/dev/null 2>&1; then
  curl -fL --retry 3 https://distfiles.ariadne.space/pkgconf/pkgconf-2.3.0.tar.xz -o .tools/pkgconf.tar.xz
  echo '3a9080ac51d03615e7c1910a0a2a8df08424892b5f13b0628a204d3fcce0ea8b  .tools/pkgconf.tar.xz' | shasum -a 256 -c -
  tar -xf .tools/pkgconf.tar.xz -C .tools
  prefix="$PWD/.tools"
  (cd .tools/pkgconf-2.3.0 && ./configure --prefix="$prefix" --disable-shared && make -j4 && make install)
fi
if ! command -v pkg-config >/dev/null 2>&1; then
  ln -s pkgconf .tools/bin/pkg-config
fi
pkg-config --exists gmp || { echo 'GMP development headers/library required.' >&2; exit 1; }
OPAM="$PWD/.tools/bin/opam"
if [ ! -f "$OPAMROOT/config" ]; then
  "$OPAM" init --bare --no-setup --disable-sandboxing -y
fi
if [ ! -d _opam/.opam-switch ]; then
  "$OPAM" switch create . 4.14.4 --no-switch -y --jobs=4
fi
if [ -f perf/toolchain.export ]; then
  "$OPAM" switch import perf/toolchain.export --assume-depexts -y --jobs=4
else
  "$OPAM" install coq.8.20.1 menhir.20231231 ocamlfind.1.9.8 --assume-depexts -y --jobs=4
fi
git submodule update --init test
"$OPAM" exec -- ./configure -prefix "$PWD/.local" aarch64-macos
"$OPAM" list --installed --columns=name,version --short > perf/results/toolchain.txt
