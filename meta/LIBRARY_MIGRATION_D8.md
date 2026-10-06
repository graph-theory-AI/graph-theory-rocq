# D8: finite supplied-family incidence regularity

D8 is implemented on the fixed D7 pin `7e030f252c859c5334185673b10b69971cab9402`. It is the new `regularity` shard (normalized
name `regular`).

The canonical is the new public `Hypergraph.foundations.hypergraph_regularity.hg_regular E d`: every vertex of the finite
carrier lies in exactly `d` members of the supplied family `E`, counted by A10's `GTBase.incidence.incidence_degree`. The
carrier and family are arbitrary, `E` comes before `d`, and the equality is universal. There is no uniformity, positivity,
inhabited-carrier, nonempty-edge, covering or attained-degree premise: an empty carrier is regular of every degree and
empty members never count. The API gives:
- the Boolean view `hg_regularP` (`[forall v, incidence_degree E v == d]`);
- the empty carrier, and uniqueness of the degree given a supplied vertex;
- the empty family (0-regular, and only 0-regular when a vertex exists);
- invariance under adding an empty edge;
- the single empty edge (0-regular) and the single full edge (1-regular).

The public client covers each corner, including the failure of uniqueness on the empty carrier.

`X73.x73_regular` is now a qualified alias with an unchanged header. Frozen in `Hypergraph.migration.regularity` at the D7
pin (the family baseline):
- the source, which keeps A10's live degree alias;
- the complete current X73 row over it, which keeps the live D2 partite and D6 matching aliases.

The complete Original is the existing, unchanged D6 `X73MatchingOriginal` row, with its genuine D6 iff, reused as an
`original-statement`. It and the four raw providers it reaches (A10 raw degree and regularity, D2 raw partite source, D6
raw matching) are borrowed with explicit effective commits. That is 2 owned and 5 borrowed mappings, with 2 whole iffs.
Both rows keep every quantifier, `1 <= d`, the balanced partition, the partite predicate, the matching witness and the
exact `(d.-1 * n) %/ d` bound. Both owned bridges are conversions.

`Infinite.conjectures.D4inf3.regular` (an infinite graph with an ordinal neighbour enumeration) is a deferred class of this
owner; its source and row are untouched, so the status is `migrating`.

No older proof needed adaptation: the eight-file reverse closure compiles unchanged. A10's `incidence-degree`
`consumers_remaining` goes 17 -> 16, because `x73_regular` no longer names `x73_hyperdegree`. The old D2 `X73PartiteLegacy`
and D6 `X73MatchingLegacy` rows, which still call the live `x73_regular`, get notes; the other four old frozen X73
declarations are untouched. Reciprocal notes are added to A10 (+2), D2 (+1) and D6 (+1). All D7 additions are unchanged.
Statuses, legs, docs and guards are unchanged. Evidence: coordination `evidence/D8-by-lancelot/`.
