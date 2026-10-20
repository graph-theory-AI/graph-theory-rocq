# The Rocq 9.2 proof image: recipe and identity of record

This directory is the recipe of the proof image against which the Rocq 9.2 release candidate is
checked. **It is not a claim of bit-reproducible rebuilding:** the build resolves live inputs (below),
so a rebuild is a different image.

## Identity of record

| | |
|---|---|
| tag | `graph-theory-rocq:rocq9.2-r0` |
| image Id | `sha256:d7936980007b04c241facdba3172f52cf3d37ca6e631c08581d007438fc2a2e2` |
| created | 2026-10-12T19:20:01.85302692Z |
| platform, size | linux/amd64, 2061860412 bytes, 16 layers |
| base images | `ubuntu@sha256:008173c23f95b170204355c12626cb5a965d779a7e1283b09e9cffbb1bf33ca3` (ubuntu:24.04), `node@sha256:43ac6c60b8f89723f746e8a92ce91abd5017e627ce1ddfe4238355d3a30b772c` (node:22-bookworm-slim) |

Release acceptance binds to that image Id. A rebuild from this recipe resolves the live inputs, is
expected to get a different Id, and is a NEW image. It must pass `kit/check_versions.py` ("PASS: 20
pinned package versions") and `kit/smoke.sh` before its own acceptance.

## What is pinned

- **Rocq stack** (`opam-packages.lock`, confirmed in the image by `installed-packages.txt`):
  - rocq-core 9.2.0 with rocq-stdlib 9.1.0; OCaml 5.3.0;
  - MathComp 2.6.0; mathcomp-finmap 2.2.4; mathcomp-zify 1.7.0+2.4+9.0; mathcomp-classical 1.16.0; micromega plugin 1.1.1;
  - elpi 3.7.1; rocq-elpi 3.4.0; Hierarchy Builder 1.10.3.
- **Two UNRELEASED sources**, pinned by path to archives that `fetch-sources.sh` makes. The binding identity is commit + tree; an archive's sha256 can differ with another git or gzip version.

  | package | repository | commit | tree | archive sha256 of the accepted build |
  |---|---|---|---|---|
  | coq-graph-theory dev | rocq-community/graph-theory | 322e352b72c4ca3f153e5f80123c5020a0d40620 | 46c83591eb83d3b6ac81a2e1403d1d27c8abff4f | b005e407941048a9a8571bec73f03579be90e3ceb86ea056c1e6800f218dfd3f |
  | rocq-mcp-evolve dev | LLM4Rocq/rocq-mcp-evolve | f5c3e30ff366a97722f0e135e3e4de16fbd539b0 | 2c28dc9b757c413f80432fe42fbdf3271f22a5f7 | 2ea4bd989f437583da7c1e934c4063e72cf0cb4db342ecc2ed7ff2167a871434 |

- **Tool clients in the image:** npm `@anthropic-ai/claude-code@2.1.286` and `@openai/codex@0.159.2` (Dockerfile ARGs).
- **The complete installed inventory:** `pins.tsv` (82 rows, with provenance per row) and `installed-packages.txt`.

## Live inputs (not pinned by this recipe)

- the Ubuntu apt mirror;
- the npm registry;
- the opam repositories `rocq-released` (https://rocq-prover.org/opam/released), `coq-released`
  (https://coq.inria.fr/opam/released) and `default` (https://opam.ocaml.org), by URL without a commit.
  Package versions are fixed by the lock;
- the base image tags, if the digest build arguments below are omitted.

## How to build

```sh
cd environment/rocq92
./fetch-sources.sh .        # writes sources/ (git, curl, gzip, github.com); refuses if sources/ exists
docker build --platform linux/amd64 \
  --resource memory=8g --resource cpu-quota=200000 \
  --build-arg BASE_IMAGE=ubuntu@sha256:008173c23f95b170204355c12626cb5a965d779a7e1283b09e9cffbb1bf33ca3 \
  --build-arg NODE_IMAGE=node@sha256:43ac6c60b8f89723f746e8a92ce91abd5017e627ce1ddfe4238355d3a30b772c \
  --build-arg JOBS=2 \
  -t graph-theory-rocq:rocq9.2-rebuild .
```

**Build limits.** Every RUN step calls `assert-limits.sh`, which refuses unless the build container's
`memory.max` is 8589934592 and its `cpu.max` is `200000 100000` (the `EXPECT_MEMORY_MAX` /
`EXPECT_CPU_MAX` build arguments). A builder that cannot apply `--resource` must pass matching
`--build-arg EXPECT_MEMORY_MAX=... --build-arg EXPECT_CPU_MAX=...` values, and must state that
deviation in the rebuild's record.

**Check.** In a container of the new image, run `python3 /opt/gtrocq/check_versions.py` (expect
"PASS: 20 pinned package versions") and `/opt/gtrocq/smoke.sh`.

## Run contract of the gates

The gates run each command in a container of this image with:
- `--read-only --network none --cap-drop ALL --security-opt no-new-privileges`;
- `--cpus 2` with `--memory 8g` by default (12g for the MCP server), and `--pids-limit 512`;
- a 4 GiB tmpfs at /tmp;
- the repository checkout mounted at the same path;
- the pinned `graph-conjectures` checkout mounted read-only, with `GRAPH_CONJECTURES` pointing at it
  (see the main README);
- the host user's uid and gid.

A gate receipt names the image Id it ran in.
