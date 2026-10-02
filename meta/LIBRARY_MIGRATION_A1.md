# Library Migration A1: Induced-Free Classes

> Batch A, first family (meta/LIBRARY_MIGRATION_PLAN.md section 15), implemented
> 2026-10-02 against `work/coordinator` at 9e03072.
>
> Registry status: `deprecated`, because the ten historical names remain as
> transparent compatibility aliases for one migration cycle (the M1 convention).
> `reviewed_by` stays unset until the coordinator records the step-10 review.

The generated report `meta/migration_reports/induced_free.md` (from
`meta/migration_reports/induced_free.spec.json`, via `meta/migration_report.py`)
holds the per-definition hashes, the per-row theorem names, the repository-wide
consumer list and the machine checks. This record explains the decisions.

## Scope

| Group | Definitions | Treatment |
|---|---|---|
| induced-subgraph exclusion | `x43_`, `x56_`, `x57_`, `x58_`, `x61_`, `x118_`, `x120_`, `x102_`, `x42_induced_free` (G H); `x41_induced_H_free` (H G) | migrated: each now unfolds to `GTBase.common.induced_free G H` |
| name match only | `Extremal.conjectures.X207.x207_H_free` | distinct: minor exclusion, documented in X207.v as the WRONG OBJECT for its source (row BLOCKED); untouched |
| name match only | `GTMisc.conjectures.X94.x94_H_free` | distinct: side-preserving induced copies between bigraphs; untouched |

## Protocol (section 9)

1. **Discover.** Ten source definitions. Ten affected statements, three of them
   through an intermediate helper (`x57_sparse_strong_eh_property`,
   `x61_induced_saturated`, `x102_free_class_tree_alpha_bounded`). Two cross-module
   consumers open the old wrapper in proofs: `implications_X42.v` and
   `implications_X223.v`. M1's frozen X102 statement also resolves through a helper
   of this family. Already canonical, and unaffected: X211, X223, X226 and their
   grounding files.
2. **Compare.** All ten bodies are `forall S : {set G}, ~ inhabited (induced S ≃ H)`.
   The canonical body is `forall S : {set G}, diso (induced S) H -> False` (`≃` is
   upstream notation for `diso`, a `Type`). The two are logically equivalent but not
   convertible. No body is defective.
3. **Specify.** The contract is the doc comment of `GTBase.common.induced_free`: host
   first, pattern second; `S` ranges over all vertex sets, the empty set and
   `[set: G]` included; isomorphism is `diso`. Degenerate cases: no graph is free of an
   empty pattern; the empty host is free of exactly the nonempty patterns; `K_1`-free
   means empty; a larger pattern is always excluded; no graph is free of itself.
4. **Audit upstream.** coq-graph-theory 0.9.7 has `induced`, `diso`, `isubgraph` and
   `diso_Kn`, but no class predicate. The existing `GTBase.common.induced_free` is
   kept unchanged as the canonical.
5. **Implement.** `GTBase.common` gains `induced_free_inhabited` (the local
   presentation) and `induced_free_diso` (invariance under isomorphism of the pattern).
6. **Ground.** `GTBase.common` gains `not_induced_free_self`, `not_induced_free_pattern0`,
   `induced_free_host0`, `induced_free_K1`, `not_induced_free_clique`, `induced_free_Kn`,
   `induced_free_K4_claw` (a positive example that cardinality does not decide) and
   `not_induced_free_K3_K2`, next to the existing `induced_free_card`.
   `meta/foundation_fidelity.json` enrols `GTBase.common.induced_free` as FAITHFUL
   with these eleven lemmas as machine evidence.
7. **Freeze.** Each area's `theories/migration/induced_free.v` holds a `Legacy`
   module with the ten helpers verbatim, under their original names, and an `XnnLegacy`
   module per statement that freezes the whole affected chain. The report checks every
   frozen copy against the source text at 9e03072, modulo the listed identifier
   substitutions. It records each original declaration hash (equal to the baseline
   inventory's `declaration_hash`) and git blob.
8. **Bridge.** `xnn_induced_free_compat` (and `x41_induced_H_free_compat`) prove each
   frozen helper equivalent to its alias. `x41_induced_H_free_order` checks that the
   alias keeps the `(H G)` order. The chain lemmas are
   `x57_sparse_strong_eh_property_compat`, `x61_induced_saturated_compat` and
   `x102_free_class_tree_alpha_bounded_compat`.
9. **Re-encode.** The ten alias bodies now read `induced_free G H`. Statement texts,
   doc blocks, manifest rows and leg states are unchanged; the report checks this.
   Each row has a per-row theorem `xnn_statement_compat : XnnLegacy.statement <-> <statement>`.
   The proof-only knock-on edits are in `implications_X42.v` (`induced_free_no_copy`,
   the `cl4` step of e050, `K4_free_clique_free`) and in `implications_X223.v` (e076).
10. **Independently review.** Pending: coordinator.
11. **Gate.** See the board announcement for the gate results of the commit.
12. **Deprecate.** The aliases stay. They have 10 direct consumers (registry
    `consumers_remaining`), plus the cross-module consumers above.

## Interaction with M1

- M1's `GTMisc.migration.simple_edges.X102Legacy.statement` froze only the
  edge-set chain and still resolves through the live
  `x102_free_class_tree_alpha_bounded`. After A1 its body therefore uses the
  canonical `induced_free`: it is no longer the pre-M1 statement, and M1's
  `x102_statement_compat` now certifies only the edge-set step. M1's file is not
  edited here. Instead, `GTMisc.migration.induced_free.X102Original.statement`
  freezes both chains: M1's frozen edge-set chain, which the report re-checks
  against the pre-M1 commit 061154c, and A1's frozen induced-free chain.
  `x102_statement_original_compat` relates it to the live statement.
- X61's chain also passes through the M1 alias `x60_edge_set`.
  `Extremal.migration.induced_free.X61Original` freezes it with M1's
  `simple_edges.Legacy.edge_set` (`x61_statement_original_compat`).
- X43's statement reaches the M1 alias `x43_edge_set` through `x43_line_graph`.
  M1 certified that alias only at alias level (`x43_edge_set_compat`), and A1 adds
  no end-to-end certificate for it: this would need χ and graph-power transport
  across line-graph carriers. It is outside A1's chain and is recorded as an
  existing M1 limitation.

## Tooling

`meta/migration_report.py FAMILY [--write|--check]` is generic. It runs without the
toolchain (it reads sources and git history) and is driven by a per-family spec. It
is not wired into `make audit` or `make gate`; that wiring, and its inclusion in
`make mutation` (`--validate` self-test), is left to the coordinator.
