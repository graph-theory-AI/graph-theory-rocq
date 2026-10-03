# C23: ambient grad bounds

C23 starts from the fixed C22 commit `30459e9b9eeebbdb5451c70c529bd2e5dfb64c99`, which is also
the family baseline. Exactly two sources move:
`GTMisc.conjectures.X128.x128_grad_at_most` and `GTMisc.conjectures.X139.x139_grad_at_most`.
Both now unfold to `ambient_grad_at_most G r d`, a definition added to the existing
`GTMisc.foundations.ambient_shallow_minors` with the identical body:

    forall H : sgraph, ambient_shallow_minor G H r -> 2 * fg_edge_count H <= d * #|H|

What is kept:

- the host comes before the pattern, and all r and d are quantified;
- the arithmetic is natural cross-multiplication with the factor two;
- the radius is C16's host `graph_dist` with its finite truncation, and paths may leave a branch;
- the count is the A7 public edge count;
- the empty pattern is included (0 <= 0).

No nonempty, positive, connected, induced or covering guard is added. There is no division,
rational density or maximum. The internal-radius expansion of Minor X220 stays separate. The API
covers:

| Lemma | Content |
|---|---|
| `ambient_grad_at_mostE` | exact unfolding |
| `ambient_grad_at_most_bound` | the bound for any model |
| `ambient_grad_at_mostW` | monotone in d |
| `ambient_grad_at_most_radiusW` | restriction to a smaller radius |
| `ambient_grad_at_most_host` | the host's own density, via `ambient_shallow_minor_refl` |

Explicit `Arguments` keep the unfolded pattern argument from becoming implicit.

The certificate `graph-theory-misc/theories/migration/ambient_grad.v` freezes verbatim, each with
an iff certificate:

- both sources;
- both expansion chains (`x128_expansion_bounded`, `x139_polynomial_expansion_class`);
- both whole current rows.

These per-row copies keep the live C16 model aliases and the A7 count, as the sources did. The
complete histories are the existing A7+C16 `X128Original` and `X139Original` whole rows. They are
reused with their C16 iff certificates and not copied. The report therefore checks four
whole-statement iffs: two current and two Original.

- X128 keeps p before q, the individual-graph hypothesis, 1 <= t and natural costs. It stays
  statement-done.
- X139 keeps one p for the whole class and all radii and one conclusion f. It stays blocked: its
  backward r-ball omits the internal-order condition of strong reachability. That defect is not
  repaired here. Docs, manifest rows and legs are unchanged.

The 18 grad/expansion/row objects and 18 theorem headers of the A7 and C16 certificate modules
are byte-identical, as are C16's four radius/model headers. Both modules compile with no proof
change, so there is no proof-unfolding delta to record.

Reciprocal stale-snapshot notes were added to the `edge_count` and `ambient_shallow_minors` specs
for the two new current grad snapshots. A7 declares the new canonical/API and client as public-count
users. C16's `consumers_remaining` drops from 2 to 0, because its model aliases lost their only
direct consumers, the two grad sources.

The public-only client `graph-theory-misc/theories/examples/ambient_grad.v` checks:

- the empty pattern bound;
- the empty host at every radius;
- the edgeless one-vertex host with bound 0 (hence every d) at every radius;
- that K2 has no bound 0 at any radius.

Regenerate the compact report through the pinned wrapper with
`python3 meta/migration_report.py ambient_grad --write`; request full details with
`--details /tmp/ambient-grad-details`. Implementer evidence is in coordination
`evidence/C23-by-lancelot/`.
