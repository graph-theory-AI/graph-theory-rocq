# C22: exact-order tournament unavoidability

C22 starts from the fixed C21 commit `b6cd87b5af7943ebe744cd27dfe34ac42d9e543d`. The family
baseline stays the C20 commit `97605ddae838bc6e84b0602240148246e9d065f2`, where every directed
declaration below is byte-identical. C22 extends the C21 `poset-unavoidability` family with a
distinct `tournament-exact-order` class. C21's Minor canonical, owner, API, client, certificates,
fidelity entry and its two frozen objects are unchanged.

Three sources move to the focused public module `Digraph.foundations.tournament_unavoidability`,
which imports no conjecture file:

- `unvd.unavoidable D N` unfolds to `tournament_unavoidable D N`. Every bundled `Digraph.core`
  tournament with exactly N vertices contains D through an injective map that preserves arcs one
  way (upstream `is_dhom` through `to_GT`). Non-arcs may land on arcs, so this is not induced
  containment; upstream `isubgraph` is a different contract.
- `unvd.unvd D N` unfolds to `unavoidability_number D N`: D is N-unavoidable and not
  M-unavoidable for every smaller M.
- `X221.x221_linearly_unavoidable F` unfolds to `linearly_unavoidable F`: one natural C, chosen
  before all digraphs, with `F D -> unavoidability_number D N -> N <= C * #|D|`.

What is kept:

- D is an arbitrary finite digraph. Loops and digons are allowed, and such a D has no value.
- N is exact, and the empty digraph has value 0.
- No existence, positivity or acyclicity guard is added.

`tournament_unavoidable_unbundledE` is the same-carrier factory bridge: an irreflexive,
semicomplete and asymmetric `diGraphType` is a bundled tournament on the same carrier with the
same arcs. The API also proves:

- upward monotonicity;
- the order lower bound;
- uniqueness of the value;
- the loop and digon obstructions.

The supports `heroes.is_tournament` and `unvd.contains_subdigraph` are frozen as unchanged chain
objects. They stay live, unmigrated and in their own inventory groups. `X2.subdigraph_embed` and
`GTMisc.D7.is_tournament` are untouched. In the certificate
`digraph-theory/theories/migration/tournament_unavoidability.v`:

- the frozen `unavoidable` uses both frozen supports;
- the frozen `unvd` uses the frozen `unavoidable`;
- the frozen linear class uses the frozen `unvd`.

Five whole Props are frozen, each with a complete iff:

- X17 Sumner (std_sumner_s_conjecture);
- `unvd.conj_9` (arxiv:2410.23566#03);
- `unvd.prob_6` (arxiv:2410.23566#00);
- the X221 k-extension row (arxiv:2410.23566#05);
- the non-corpus alias `reals_growth.prob6_unvd_statement`, whose frozen copy is the frozen `prob_6`.

Every guard and quantifier order is kept, and all four corpus statement legs stay done. The
`conj_9` to X221 edge gc:e106 stays an unproved candidate. `prob6_nat_bound_real_envelope` keeps
its existing real and extensionality axioms; it is outside these closures and gets no exemption.

Scope: 3 sources, 2 supports and 5 whole Props make 10 new frozen objects, or 12 with C21's
two. There is no earlier directed frozen history. The 14 reverse files keep all 221 theorem
headers. Five proofs enter through the conjecture-local bridge `unvd.unavoidableP`, a wrapper of
the public bridge: `x221_unavoidable_void`, `unvd_K1`, `not_unvd_K1_0`, `unvd_K2` and
`unvd_relation_inhabited`. `x221_void_lin_unavoidable`, `conj9_weaken_const'` and
`conj9_weaken_const` compile unchanged.

The public-only client `digraph-theory/theories/examples/tournament_unavoidability.v` checks:

| Digraph | Value |
|---|---|
| empty `TT 0` | 0, and unavoidable at every order |
| one vertex `TT 1` | 1, and unavoidable at every positive order |
| one arc `TT 2` | 2, its only value |
| two isolated vertices | 2, because non-arcs may land on arcs |
| a loop or a digon | no value |

Regenerate the compact report through the pinned wrapper with
`python3 meta/migration_report.py poset_unavoidability --write`; request full details with
`--details /tmp/poset-unavoidability-details`. The directed class needs its own independent
step-10 review and root whole-statement check. Implementer evidence is in coordination
`evidence/C22-by-lancelot/`.
