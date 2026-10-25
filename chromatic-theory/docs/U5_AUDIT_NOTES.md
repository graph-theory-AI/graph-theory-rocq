# chromatic-theory / U5 — edge & total colouring audit notes

Per-statement decisions (keyed by `formal_name`). **base_ready** run. Verified: compiles axiom-free,
36/36 grounding lemmas `Qed`, `check_milestone U5` → ACCEPTED (9/9 axiom-free). 0 planar rows.

## Base reuse (the edge/total layer paid off)
Reused **verbatim** from base: the `mgraph` notation, `line_graph`, `total_graph`, `chromatic_index`
(χ'), `total_chromatic_number` (χ''), `edge_colourable`, `total_colourable`, `Delta`, `ceil_div`,
χ/`chi_mem`. Edge/total rows go through base's line/total graph (`edge_colourable G k =
chromatic_index G ≤ k`). Import order: `From GraphTheory Require Import minor mgraph.` **before** the
base import (so base's undirected `line_graph` shadows coq-graph-theory's directed one).

**`mDelta` promoted to base** (U4 ∩ U5 triggered the migration); both U4 and U5 retargeted.

## Leg state: 9 done, 0 blocked
All 9 rows faithful + axiom-free after the two corrections below.

## Two faithfulness corrections (one auto-fixed, one caught on read)
- **`behzads_statement` — auto-fixed, now faithful.** The faithfulness audit flagged an
  implement-phase version quantified over `loopless` multigraphs (false: a fat triangle with p≥3
  parallel edges has χ''>Δ+2). The correct+ground phase restricted it to **`msimple G` (= loopless ∧
  injective edge-ends = simple graph)** before landing, which excludes the counterexample, so the
  disk statement `msimple G -> (mDelta G).+1 <= χ''(G) <= (mDelta G).+2` is Behzad's TCC. **done.**
- **`seymours_r_graph_statement` — caught on read, corrected.** The agent stated it as
  `edge_colourable G r.+1` (χ' ≤ r+1). Seymour's r-graph conjecture is that every r-graph is
  **r-edge-colourable** (χ' = r), i.e. `edge_colourable G r`. The `r.+1` was a **weakening**, and it
  was *exactly* what made `goldberg ⟹ seymour` provable (Goldberg's bound `max(Δ+1,w)=max(r+1,r)=r+1`
  trivially gives ≤ r+1). Corrected to `edge_colourable G r`; the spurious "verified" edge is
  **demoted to candidate** (Goldberg's r+1 bound cannot reach the faithful r; the real Goldberg–
  Seymour link is the deep Chen–Jing–Zang theorem). Federation verified-edge count returns to 0 — the
  honest state. The r-graph density lemmas `mDelta_le`/`overfull_le` (both Goldberg terms ≤ r+1)
  remain as genuine facts in `implications_U5.v`.
- **2026-10-25 (coordination/PROGRAMME.md A1): reverted to the source.** The pinned OPG text is
  "Conjecture χ'(G) ≤ r+1 for every r-graph G", so the χ' = r reading above was stronger than the
  source. The body is `edge_colourable G r.+1` again, and `goldberg ⟹ seymour` is a verified edge
  (e001, `goldbergs_implies_seymours_r_graph`, from `mDelta_le` and `overfull_le`).

## Edges (machine-readable `(*@EDGE*)`)
- `edge_list_coloring ⟹ goldbergs` — candidate (cross-milestone to U4).
- `goldbergs ⟹ seymours_r_graph` — **verified** since 2026-10-25 (e001; a candidate before, see above).
- `list_total_colouring ⟹ behzads` — refuted-direction (now points at U5's real `behzads_statement`;
  the U4 annotation was retargeted from the old dangling `behzad_total_colouring_statement` name, and
  the extractor dedups the two assertions into one edge sourced `[U4+U5]`).

## Area-local primitives
`regular_m`/`cubic` (multigraph regularity), `strong_edge_colourable`, `is_r_graph`/`edge_boundary`,
`usimple`/`mconnected`/`remove_edge`, `subdivide_edge_s`/`subdivR_s`/`homeomorphic_s` (single-edge
subdivision + homeomorphism — overlaps conceptually with base's `subdivision`; promote together if a
2nd area needs homeomorphism), `overfull_parameter` (Goldberg density w), `hypergraph`/`uniform_hg`,
`sts` (Steiner triple system), `edge_colour_seq`/`acyclic_edge_colouring`, `star_edge_colouring`.

## Toolchain gotchas (recorded)
- coq-graph-theory's mgraph iso `≃` needs `comMonoid`/`elabel` label structures, so it does **not**
  apply to `graph unit unit`; after `Import mgraph` then base, `≃` resolves to digraph/sgraph `diso`,
  so the homeomorphism relation was built on the underlying **sgraphs** via `diso`.
- An `Inductive` indexed by `sgraph` must annotate parameters explicitly
  (`… (G H K : sgraph) (x y : H)`), else Coq infers `H : Type`.
