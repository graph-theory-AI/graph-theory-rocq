# Mac installation receipt — 23 October 2026

**PASS, with the two environment qualifications below.** A fresh opam root installed all **15 public packages and 3 compatibility wrappers** from the frozen RC. All **110 downstream examples passed**. The installed public surface is exactly **162 modules / 486 files**. All 162 `Locate Library` probes resolved inside the fresh installed prefix. The non-public import was rejected, and the installed product manifests were identical before and after the client checks.

This is Mac installation evidence, **not D-5 release acceptance**.

## Source and environment

- Commit: `3ca79221b863786b7b79c68f9a635928e8f82601`
- Tree: `dab498f2f6c58f47b8d22c22ef9a8dadcef44a7f`
- Imported bundle SHA-256: `97e4be168d5ca5a12d95087017436f83697e171de46d36761cd848579c7ec5f1`
- Native macOS 26.5.2 (25F84), Darwin 25.5.0, arm64; 16 CPUs / 128 GiB.
- opam 2.5.0; OCaml 5.3.0; Rocq core 9.2.0; stdlib 9.1.0; MathComp 2.6.0; classical 1.16.0; HB 1.10.3; elpi 3.7.1; rocq-elpi 3.4.0; finmap 2.2.4; Zify 1.7.0+2.4+9.0 for examples. Python 3.12.4; GNU Make 3.81; Apple clang 21.0.0.
- Upstream `coq-graph-theory.dev` is the UNRELEASED commit `322e352b72c4ca3f153e5f80123c5020a0d40620`, tree `46c83591eb83d3b6ac81a2e1403d1d27c8abff4f`.
- Fresh root: `/Users/lelarge/Recherche/LLM4code/graph-theory-rocq/meta/generated/mac-rc-install-2026-10-23/opam-root`; switch `rc92-install`; `--jobs=2`.

All 18 RC package source clones and the upstream graph source were checked for their exact commits, trees and clean tracked files. The isolated frozen source checkout is still clean. The original checkout, existing switches and main refs were not changed.

## What ran

The fresh root started with only 11 OCaml/compiler base packages. Dependency versions were constrained with `opam pin add --no-action --kind=version`. The whole source was pinned without installing, using `git+file://<isolated clean clone>#3ca79221b863786b7b79c68f9a635928e8f82601`. The installed set was identical before and after source pinning.

Actual opam transactions then installed `rocq-graph-theory-base`, `rocq-graph-theory-misc`, and the full 18-name package set. This exercised the frozen opam build/install commands. It was not a `make install-gate` substitute. The library-only installed set has 86 packages and its own export. The 18 root opam files passed lint; the three legacy copies were byte-equal.

The examples were copied from the frozen source to a separate downstream directory and compiled with only `-R . Downstream`, their original warning flags and `ROCQPATH=<fresh switch>/lib/coq/user-contrib`. No source-tree load path was supplied. Each source hash, command, result, timing and log hash is recorded in `downstream-clients.json` and its referenced command records.

## Recorded qualifications

1. The first base-install invocation stopped before any package build with opam exit 10: macOS metadata for `conf-python-3.9.0.0` asks Homebrew for `python@3.9`. Existing `/usr/local/bin/python3` is 3.12.4. The actual conf-package command is `python3 test.py`; its checksum-verified test passed, as did the frozen source's Python >=3.9 guard. Installation continued explicitly with `--assume-depexts`; all conf-package checks still ran and passed. No brew, sudo, source change or pin change was used. The original failed command/log and qualification are preserved.

2. `graph-theory-misc/theories/examples/ambient_shallow_minors.v` imports `mathcomp.zify`. Zify is an additional client prerequisite, absent from the public-library installation closure. After preserving the successful 86-package library inventory/export, the already approved pinned `rocq-mathcomp-zify.1.7.0+2.4+9.0` was installed. This added exactly one package and changed no existing versions. All 110 clients then passed. The example inventory/export has 87 packages.

The final environment has 68 exact matches to the prepared Mac pin inventory, 18 new RC package entries and `conf-python-3.9.0.0`. There are **zero version mismatches**. The unused compatibility package `coq-mathcomp-zify`, `memprof-limits` and `rocq-mcp-evolve` were not required by this installation/client workload and were not installed. Native platform/tool differences and all package metadata are retained.

## Timing and scope

Started `2026-10-23T12:27:39.709179+00:00`; downstream checks finished `2026-10-23T12:49:30.111320+00:00`. Wall time through downstream: **21.8 minutes**, including preparation and classification.

| Work | Seconds |
|---|---:|
| Fresh OCaml compiler | 160.620 |
| Base plus fresh dependency closure | 536.873 |
| Selected misc package | 8.248 |
| Remaining public packages and wrappers | 174.198 |
| Separate Zify example prerequisite | 21.986 |
| 110 downstream compilations, summed | 91.775 |

The immutable local Git route was exercised; the forge route awaits publication. Installing the remaining packages together does not prove each one's dependency completeness in a separate fresh switch. No source, metadata or proof fix was made.

## Evidence

`mac-install-receipt.json` is the machine-readable receipt. `SHA256SUMS` covers the compact evidence, including command records/logs, both switch exports, 87 installed package definitions, pin/source checks, the product manifests and the scripts used. `SEALED.json` binds that manifest. The archive excludes the opam root, Git checkout, and build trees; those remain locally preserved.
