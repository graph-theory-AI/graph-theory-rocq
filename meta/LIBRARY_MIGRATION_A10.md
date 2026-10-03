# Library Migration A10: Incidence Degree

Batch A family A10, on the private baseline `a54026d` (A9 record `ce0f8c2` plus the reviewed ClassicalLemmas
source tooling `ff6b3f6`). Registry `meta/library_primitives/incidence-degree.json`; spec, hashes and per-row
certificates: `meta/migration_reports/incidence_degree.{spec.json,md}`; API contracts are in the Rocq doc comments.

- **Contract.** `GTBase.incidence.incidence_degree F v := #|[set e in F | v \in e]|` counts the members of an
  arbitrary finite family on an arbitrary `finType`, with no edge, uniformity or nonemptiness premise. Six
  corpus copies (X36, X84, X37, X38, X6, X73) and the public Hypergraph `hg_degree` and ClassicalLemmas `edeg`
  convert to it. X108's degree inside `W` is the canonical count of the explicitly restricted family
  `[set e in E | e \subset W]` (a proved equality, zero outside `W`). `GTBase.common.incidence_degree_edges`
  gives `#|N(v)|` at `E(G)`.
- **Packaging.** `incidence.v` is MathComp-only. ClassicalLemmas maps `GTBase` and the root Makefile now has
  `classical-lemmas: base`. Only `edeg_setD`'s unfolding changed (`rewrite /edeg /incidence_degree`), and every
  classical, Packing and Hypergraph theorem type is unchanged (kernel evidence).
- **Rows.** X36, X84, X85, X37, X38, X6, XE2 #833, X73, X108 and X225 are frozen verbatim at `a54026d` with their
  14 chains. M1 edge-set aliases and every other helper stay live (no pre-M1 claim).
- **Degeneracy.** `FoundationLegacy` freezes the foundation's degeneracy test, opaque witness, least degeneracy,
  skeletal degeneracy and `d_max`. The witness's two support lemmas are copied verbatim, statement and proof, so
  the witness proof is the original one, closed over the frozen degree. The least naturals are compared by
  `eq_ex_minn`; no proof equality is claimed. The shared `hg_restrict` and `hg_skeleton` are unchanged.
  X225 keeps `ck` before the pattern, `K` after its three guards, and both exponents.
- **Reproduction.** Build the 15 packages, the Digraph targets `chi_bounded`/`classic_core` and the atlas. Run
  `python3 meta/migration_report.py incidence_degree --check --kernel` and the milestones of the ten rows and
  X15. Kernel probes, closures and the verbatim check are in `coordination/evidence/A10-incidence_degree/`.
