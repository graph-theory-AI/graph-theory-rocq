#!/usr/bin/env bash
# Make the two UNRELEASED source archives that the Dockerfile COPYs (sources/graph-theory.tar.gz,
# sources/rocq-mcp-evolve.tar.gz), each pinned by commit AND tree. Usage: fetch-sources.sh CONTEXT_DIR
# (normally this directory); it writes CONTEXT_DIR/sources/ and refuses if that already exists.
# The logic is the sealed original's (rocq92-step1-dependency-install-by-arthur recipe/fetch-sources.sh),
# with its host paths replaced by CONTEXT_DIR and a temporary work directory. Needs git, curl, gzip
# and network access to github.com. The binding identity of each source is commit + tree: an
# archive's sha256 can differ with another git or gzip version (the accepted image's archives are
# listed in README.md).
set -euo pipefail
C=${1:?usage: fetch-sources.sh CONTEXT_DIR}
S=$C/sources
[ ! -e "$S" ] || { echo "REFUSED: $S exists"; exit 1; }
W=$(mktemp -d)
trap 'rm -rf "$W"' EXIT
mkdir -p "$S"
one() {  # one NAME REPO COMMIT TREE OUT
  local g=$W/$1.git t=$W/$1.tree
  git init -q --bare "$g"
  if git -C "$g" fetch -q --no-tags "https://github.com/$2" "$3" < /dev/null; then
    [ "$(git -C "$g" rev-parse "$3^{commit}")" = "$3" ] || { echo "REFUSED: $1 commit"; exit 1; }
    [ "$(git -C "$g" rev-parse "$3^{tree}")" = "$4" ] || { echo "REFUSED: $1 tree"; exit 1; }
    git -C "$g" archive --format=tar "$3" | gzip -n -9 > "$S/$5"
    echo "SOURCE $1 via git fetch"
  else
    # f5c3e30f is no longer on a branch (PR #1 was rebased on 2026-10-05): the archive endpoint, then the tree is recomputed
    # from the extracted files and must equal TREE (a content pin as strong as the fetch).
    mkdir "$t"
    curl -fsSL "https://codeload.github.com/$2/tar.gz/$3" < /dev/null | tar -xz -C "$t" --strip-components=1
    git -C "$t" init -q && git -C "$t" add -A -f
    [ "$(git -C "$t" write-tree)" = "$4" ] || { echo "REFUSED: $1 tree of the archive"; exit 1; }
    git -C "$t" archive --format=tar "$4" | gzip -n -9 > "$S/$5"
    echo "SOURCE $1 via archive, tree verified"
  fi
  printf 'PIN %s %s commit %s tree %s\n' "$(sha256sum < "$S/$5" | cut -d' ' -f1)" "$5" "$3" "$4"
}
one graph-theory rocq-community/graph-theory 322e352b72c4ca3f153e5f80123c5020a0d40620 46c83591eb83d3b6ac81a2e1403d1d27c8abff4f graph-theory.tar.gz
one rocq-mcp-evolve LLM4Rocq/rocq-mcp-evolve f5c3e30ff366a97722f0e135e3e4de16fbd539b0 2c28dc9b757c413f80432fe42fbdf3271f22a5f7 rocq-mcp-evolve.tar.gz
exit 0
