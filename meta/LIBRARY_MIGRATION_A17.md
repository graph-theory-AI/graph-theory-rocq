# Library Migration A17: Clique Counts

Batch A family A17, on the fixed A16 pin `16d5a05` (no private union). Registry
`meta/library_primitives/clique-count.json`; spec, hashes and per-row certificates:
`meta/migration_reports/clique_counts.{spec.json,md}`; API contracts are in the Rocq doc comments.

- **Contract.** The new `GTBase.clique_counts` owns three distinct numeric views over upstream `cliques [set: G]`:
  - `all_clique_count`: every clique, the empty one included;
  - `nonempty_clique_count`: the nonempty cliques;
  - `clique_count_size G r`: the cliques with exactly `r` vertices.

  No clique predicate is added. Each corpus count is related to its view by an unconditional cardinality equality
  that keeps the corpus comprehension's conjunction order; no equality between views is used as a bridge.
  - Minor X174's count is `all_clique_count`.
  - Extremal D2tur's and Minor X175's counts are `nonempty_clique_count`.
  - Extremal X88's count is `clique_count_size G r`.
  - Extremal X4's triangle count is `clique_count_size G 3`. Its `x4_triangle_set` support is frozen, and the live
    predicate stays unchanged.
- **API.** The three comprehension equalities; `nonempty_clique_countS` (the empty clique always exists); sizes 0,
  1 and 2 (`#|E(G)|`); and size above the order.
- **Client.** The public client proves the complete-graph formulas (all `2^n`, nonempty `2^n - 1`, size `r`
  binomial) and the edgeless ones. It then shows the corners:
  - `K_0`: all 1, nonempty 0, size 0 = 1;
  - `K_1`: all 2, nonempty 1;
  - `K_2`: all 4, nonempty 3, size 2 = 1;
  - `K_3`: size 3 = 1;
  - two isolated vertices: all 3, nonempty 2, size 2 = 0.
- **Rows.** Frozen verbatim at `16d5a05`: the five counts and the four current rows:
  - D2tur's `c^t * |G|` bound: strict `0 < t`, no older history, so also complete;
  - X4 supersaturation: every natural division and guard;
  - X174: all-clique count; the blocked natural subtraction `n - t + 3`, including the admitted `n = t-2, t-1`
    cases; both the bound and the attainment halves;
  - X175: nonempty count; eventual-in-`t` upper envelope.

  X88's count reaches no row; its misleadingly named row compares edge counts and is untouched.
- **Complete rows.** Seven whole-row iffs in all. Three complete rows reuse the earlier certificates:
  - X4 over A7's frozen edge count (`ae0e605`);
  - X174 over B8's frozen immersion chain (`048c768`);
  - X175 over B2's frozen subdivision chain (`9e03072`).
- **History.** A7's X4, B8's X174 and B2's X175 rows still name the live counts. They stay byte-for-byte and are
  documented in the spec. A17's per-row copies are documented reciprocally in those three specs. A16's spec and
  registry drop only their X174 count exclusion. Doc blocks are unchanged.
- **Proof consumers.** `Extremal.grounding_D2tur.clique_count_gt0` and `clique_count_K0` keep their types; each
  proof gains one rewrite back to the old comprehension. Atlas candidate e054 stays BLOCKED.
- **Distinct.** Maximum and inclusion-maximal clique predicates stay separate.
- **Reproduction.** Build the packages. Run `python3 meta/migration_report.py clique_counts --check --kernel` and
  the milestones Extremal D2tur, X4 and X88 and Minor X174 and X175. Kernel probes are in
  `coordination/evidence/A17-clique-counts/`.
