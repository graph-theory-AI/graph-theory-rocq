# Library Migration A20: Simple-Graph Stable Sets

Batch A family A20, on the fixed A19 pin `96be00e` (no private union). Registry `meta/library_primitives/stable-set.json`;
spec, hashes and per-row certificates: `meta/migration_reports/stable_sets.{spec.json,md}`; API contracts are in the Rocq
doc comments.

- **Contract.** Upstream `GraphTheory.core.dom.stable S` (Boolean `[disjoint NS(S) & S]`) is canonical; no stable-set
  predicate is added. `GTBase.stable_sets` relates it, for every graph and every supplied set, to the raw presentations:
  - `stable_noedgeP`: no supplied pair is an edge (`x -- y -> False`): X3, Chromatic/Extremal/Packing XE1, X56, X18;
  - `stable_distinctP`: distinct supplied vertices are nonadjacent: X97, X169, X208;
  - `stable_nonadjP`: every supplied pair, the diagonal included, is nonadjacent: X29;
  - `stable_eqbE`: X163's bounded Boolean with its equality disjunct, an actual Boolean equality.

  The variants agree by sgraph irreflexivity: no nonempty, cardinality or looplessness hypothesis. `stable_pair` is the
  two-vertex case. Upstream `stable0`, `stable1`, `sub_stable` and `stable_induced` are reused; upstream `diso_stable` is
  `Abort` and is not used.
- **Client.** The public client shows the empty set and `K_0`, singletons, the whole edgeless carrier, the two `K_2`
  vertices rejected together (each alone is stable; no superset is), hereditary restriction, induced-subgraph transport,
  the raw views and the Boolean form.
- **Rows.** Frozen verbatim at `96be00e`: the eleven sources, the fifteen row-reaching chains and the seventeen rows.
  - Chromatic: X3; X7 (`5 <= k`, omega < 5, chi = k + 3); XE2 #758 (12/4), #762 and #922 over the cochromatic colouring
    (finite ordinal palette, empty classes allowed), its attained minimum and the attained maximum on n vertices.
  - Extremal: X56's homogeneous set; X97's maximum-cardinality independent set, hitting set and hitting number; XE1 #802;
    XE2 #22, #73 and #801.
  - GTMisc: X163's Boolean normality; X169's token sliding and polytime decision, with its known blocked encoding kept;
    X208's numeric maximum output and polytime chain (`7 <= t`); X29's stable cover and normality.
  - Packing: X18's ordinal path partition and balance; XE1's triangle-free guarantee and #151.

  Extremal XE1's dormant `xe1_has_independent_set` is frozen too; no row reaches it. Every guard, attained extremum,
  quantifier order, natural subtraction, `trunc_log`, Boolean event, program/cost witness and leg state is unchanged.
- **Complete rows.** 26 whole-row iffs in all: the seventeen current rows, and nine complete rows at the pre-migration
  `9e03072`:
  - X3, over B3's frozen induced path and B1's frozen path support;
  - Chromatic #762 and Extremal #802, over A5's frozen subgraph relation;
  - Extremal #22 over A5's and A7's frozen helpers, and #801 over A7's frozen edge count;
  - Extremal X56 over A1's and A6's frozen helpers, and GTMisc X29 over A6's frozen complement;
  - GTMisc X169 over C13's frozen classes, with its polytime chain;
  - Packing #151 over A18's frozen transversal chain.

  The bridges reuse the earlier certificates.
- **History.** Fifteen earlier frozen bodies (B1, B3, A1, A5, A6, A7, C13 and A18) keep live stable-set names byte for
  byte; the spec documents them. A20's per-row copies keep those families' live names, with reciprocal notes in their
  specs.
- **Proof consumers.** Chromatic X7's cochromatic-gap application (`mycielski_gap`, `seed_colorings`, `cochromatic_gap`)
  routes its raw-forall scripts through `stable_noedgeP`. `cochromatic_gap_three_proved` and all 62 headers keep their
  types. `vocabulary_packing`'s X18/XE1 bridge and the earlier certificate modules are unchanged. The 75-file reverse
  closure (754 old headers) is type-identical to the baseline.
- **Distinct.** These stay separate:
  - Digraph X166's loop-ignoring `x166_stable_set` (registered, deferred);
  - the loop-forbidding `classic_core.stable` and `x2_arc_stable`;
  - GTMisc XE2's `xe2_independent3`;
  - Packing XE1's counting helper `xe1_independent_set_count`.
- **Before merge.** B21's X18 history and B22's X208/X3 histories lie outside A19 ancestry. The complete X18 and X208
  rows and the X3 rebinding on the combined parent are a mandatory, separately reviewed follow-up before merge. This
  pin's acceptance is not combined-parent acceptance.
- **Reproduction.** Build the packages. Run `python3 meta/migration_report.py stable_sets --check --kernel` and the
  milestones Chromatic X3/XE1/XE2/X7, Extremal X56/X97/XE1/XE2, GTMisc X163/X169/X208/X29 and Packing X18/XE1. Kernel
  probes are in `coordination/evidence/A20-stable-sets/`.
