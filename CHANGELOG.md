# Changelog

## Rocq 9.2 accepted source release — 2026-10-23

- Published the exact D-5-accepted commit `3ca79221b863786b7b79c68f9a635928e8f82601`
  as `rocq92-accepted-2026-10-23`, by a fast-forward of `main`.
- Validated the Rocq 9.2 stack, corpus builds and checks, 12 mutation canaries,
  meta suites, native per-directory pin scans and public-library installation.
  The acceptance is the checked 25 + 3 combination. A fresh Mac opam installation
  and all 110 downstream examples passed with the recorded Python and Zify qualifications.
- Updated the supported environment and corrected the Cheng–Keevash k = 7
  documentation: `ck_conj1_delta7` and its explicit-path corollary are already proved.

See the [release receipt](meta/releases/ROCQ92_ACCEPTED_2026-10-23.md) for exact
bindings, evidence hashes and scope. This release claims no Rocq 9.1 support
and is not an opam-repository release.
