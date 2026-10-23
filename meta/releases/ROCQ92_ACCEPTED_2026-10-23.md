# Rocq 9.2 accepted release — 23 October 2026

**D-5 PASS and accepted.** The published source is tagged `rocq92-accepted-2026-10-23`.
Publication fast-forwarded `main` from `806169c3fa9033f576e8bf8b2d5053f48a3951d1`
to the accepted commit; it introduced no new source or merge commit.

## Source and environment

| Binding | Value |
| --- | --- |
| Commit | `3ca79221b863786b7b79c68f9a635928e8f82601` |
| Tree | `dab498f2f6c58f47b8d22c22ef9a8dadcef44a7f` |
| Tracked-tree SHA256 | `025abfd088d170e7eb4cb3a9b3ea7841765f69b7085cfdcfa8767d96a89bf18e` |
| Linux image | `sha256:d7936980007b04c241facdba3172f52cf3d37ca6e631c08581d007438fc2a2e2` |
| KIT_C3 manifest SHA256 | `03683d09bec16c6a73f7ceec0c04723ebc8c35753d24f50e073cdafc06930c60` |
| Harness r4 SHA256 | `d19a9f015b431a7d45460e85b92aadc1b8539bca459e337d5b4c5ce3ebe39149` |

The tested stack is OCaml 5.3.0, Rocq core 9.2.0 with rocq-stdlib 9.1.0,
MathComp 2.6.0, classical 1.16.0, Hierarchy Builder 1.10.3, elpi 3.7.1,
rocq-elpi 3.4.0, finmap 2.2.4 and Zify 1.7.0+2.4+9.0.
`coq-graph-theory.dev` is the unreleased upstream commit
`322e352b72c4ca3f153e5f80123c5020a0d40620`, tree
`46c83591eb83d3b6ac81a2e1403d1d27c8abff4f`.
See the [image recipe and full inventory](../../environment/rocq92/README.md).
No Rocq 9.1 compatibility claim is made. A rebuild has its own image identity.

## The 28 stage receipts

The acceptance record is the checked **25 + 3 combination**, explicitly authorized
by the project owner. It combines 25 unchanged PASS receipts from the original run
with the three missing stages, run on a copy of its built root. Source and product
manifests matched before and after, and the original root, outputs and work area
were unchanged. No old failed receipt was rewritten, and there is no automatic
old-runner `D5_VERDICT` for this combination.

[COMBINATION.txt](rocq92-accepted-2026-10-23/COMBINATION.txt) records every stage and
its receipt hashes: **S01–S04, S05.01–S05.18, S09, S10a, S10b** (25 original
PASS receipts), then **S10c, S11 and S12** (three new PASS receipts).
The original stages cover the builds, corpus-wide assumptions, `rocqchk`, gate
commands, audit, private-prefix installation and opam lint.

| New stage | Result | Measured seconds |
| --- | --- | ---: |
| S10c, native per-directory pin scans | PASS; 18 root entries and 3 extra subdirectory entries match the predeclared sets | 22 |
| S11, `make mutation` | PASS; 12/12 mutation canaries rejected as expected, Python suites and install-gate checks passed | 2,875 |
| S12, meta suite with kernel and symlinked TMPDIR | PASS; 192 tests, no skips | 40 |

Attempt 2 ran on 23 October, 14:24:08–15:13:21 UTC, with KIT_C3 and harness r4.
It used the inherited allowance ending 16:29:50 UTC; the conditional fresh
14,400-second allowance was not used. Arthur independently approved the final
evidence at 15:18:06 UTC. Acceptance was recorded at 15:34:36 UTC under the
owner's prior conditional approval. No new fix ledger or image change was used.
Timings are shared-host measurements, within the graph-theory aggregate cap of
10 CPUs / 64 GiB. S11 ran under caps of 2 CPUs / 8 GiB and S12 under 2 CPUs / 4 GiB. These are not isolated-host benchmark results.

The [single pin comparison](rocq92-accepted-2026-10-23/pin-comparison.txt) passed
against the actual raw outputs and declared expected sets. Opam 2.1.5 lacks native
`pin scan --recursive`; R1 used labelled native scans in `base` and `digraph-theory`.
The receipt retains diagnostic wording about inserting a missing newline; the
successful attempt's raw labels already matched, and verification required no
output repair. The combination retains cosmetic `S10c''` / `KIT_C` labels;
the exact KIT_C3 and script hashes bind the executed commands.

## Fresh Mac installation

The [Mac receipt](rocq92-accepted-2026-10-23/MAC_INSTALL_RECEIPT.md) records a fresh
opam-root installation of all **15 public packages and 3 compatibility wrappers**
on macOS arm64. All **110 downstream examples** compiled against the installed
prefix only. All 162 public modules resolved there, a non-public import was
rejected, and the 486 installed files were unchanged by the checks.

Its two qualifications are retained:

1. Opam's Homebrew detection requested Python 3.9. The existing Python 3.12.4
   passed the actual conf-package test and the source's Python >=3.9 guard.
   Installation continued explicitly with `--assume-depexts`; conf checks still ran.
   No source, pin, Homebrew or system-package change was made.
2. Zify is an extra example prerequisite outside the library-only closure. After
   preserving the 86-package library inventory, the pinned
   `rocq-mathcomp-zify.1.7.0+2.4+9.0` was added, yielding 87 packages without changing
   existing versions. All clients then passed.

This receipt used the immutable local Git route. Its historical statement that
the forge route awaits publication does not claim a later forge-install test.
Publication does not claim separate fresh-switch dependency completeness for each
individual package or publication to an opam repository.

## Evidence identities

The following evidence files are byte-for-byte copies of the accepted records:

| File | SHA256 |
| --- | --- |
| [COMBINATION.txt](rocq92-accepted-2026-10-23/COMBINATION.txt) | `132c25cf3981e8348dd0c5a70eb7a1632103bd35d538ef222ba39e7cc3e01b68` |
| [pin-comparison.txt](rocq92-accepted-2026-10-23/pin-comparison.txt) | `ab42f87db550ece7b5fcca5186d95273dba9cac09b26343315d52c2136125ed2` |
| [MAC_INSTALL_RECEIPT.md](rocq92-accepted-2026-10-23/MAC_INSTALL_RECEIPT.md) | `4c8eab2369a290d69dc9e1e00fb765edf6948825eccbb5287127ca6384bb9983` |

The complete combination packet's manifest is
`65c5be9c94c30dc706066edf60c8230e47a0d908916c5f3e984ab300c896e3e0`;
the successful pin-comparison packet's manifest is
`927072c0fdfb075add66b4a3ff014990fbc9884b849a4d4e6b159a3ab3f10ad5`;
the Mac packet's manifest is
`6cbcdf9bb8733b2950ee041a2d9bdbba1f0e3ae39aa7e914b25d50148e0aad26`.
The original acceptance record SHA256 is
`d7c898797b9b8217cb3298812ed6645ea941a51c114138e3a187396fcd8540f6`.
Full logs, manifests, immutable source products and historical failed attempts
remain preserved in the project evidence stores; this receipt indexes them and
publishes the compact records above.

## CI and follow-up scope

The publication triggered [the new audit and meta-kernel CI run](https://github.com/graph-theory-AI/graph-theory-rocq/actions/runs/40022203882).
The Ubuntu runner's first locked-stack installation is a separate environment
execution. A runner or infrastructure failure is classified as a follow-up;
D-5 remains the acceptance record. CI success is not asserted by this receipt.

This documentation commit changes no proof, project file, Makefile, opam metadata
or meta tooling. README.md is read by the audit's headline check
(`meta/report_corpus_status.py`, lines 472–483); its headline counts are unchanged,
and `python3 meta/report_corpus_status.py --check --edge-legs` passed on this head.
The change lands under the owner's explicit authorization of this follow-up PR.
The already proved `ck_conj1_delta7` theorem is now described accurately in both
READMEs; its dedicated registration and receipt are subsequent mathematics work.
