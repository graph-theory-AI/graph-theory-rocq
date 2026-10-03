# Library Migration A9: Cut Sizes

> Batch A, family A9 (normalized `cut_size` / `cut_edge`), implemented 2026-10-03 on the private
> baseline `9de20ca`, which merges the A8 documentation follow-up `ed9735b` (on restacked A8 `a7901c4` and
> the A7 series) with main `54be55e` (C8's monochromatic API, B8, B9, report-role hardening); not for
> integration. Registry document `meta/library_primitives/cut-size.json`, status `deprecated` (the four
> names stay as transparent aliases for one cycle). Fidelity fragment `meta/foundation_fidelity/cut-size.json`
> enrolls `cut_size` and `non_monochromatic_count` (FAITHFUL). `reviewed_by` stays unset until the
> independent step-10 review and the coordinator's statement check are recorded.
>
> Compact report `meta/migration_reports/cut_size.md`, regenerated from
> `meta/migration_reports/cut_size.spec.json` (baseline `9de20ca`).

## Sources and the two representation classes

| Definition | Old body | Now |
|---|---|---|
| `Extremal.conjectures.X76.x76_cut_size` | `#|[set e in x76_edge_set G | ~~ [disjoint e & A] && ~~ (e \subset A)]|` | `cut_size A`, conversion (`x76_edge_set` is M1's alias of `E(G)`) |
| `Extremal.conjectures.X78.x78_cut_size` | same over `x78_edge_set` | `cut_size A`, conversion |
| `Hypergraph.conjectures.X209.x209_cut_edge` | `[exists x in e, [exists y in e, col x != col y]]` | `~~ monochromatic_on col e`, a proved Boolean equality (C8's `non_monochromatic_onP`) |
| `Hypergraph.conjectures.X209.x209_cut_size` | `#|[set e in E | x209_cut_edge col e]|` | `non_monochromatic_count E col`, proved through the cut-edge certificate |

The two classes stay explicit:
- **Graph cut.** The edges of the graph with one end in `A` and the other outside. It is the new
  `GTBase.common.cut_size`, over `E(G)`.
- **Coloured family cut.** The members of an arbitrary supplied finite family `E : {set {set T}}` that are
  not monochromatic under an arbitrary supplied colouring `col : T -> 'I_r`. It is the new graph-free
  `GTBase.monochromatic.non_monochromatic_count`, beside C8's `monochromatic_on`. The helper adds no
  uniformity, nonemptiness, positivity or palette premise. Empty and one-element members are never cut.

`cut_size_non_monochromatic` relates the two through the Boolean membership map `fun x => x \in A`.

Not touched: X209's `x209_uniform` (a premise of the row); set-valued edge cuts such as X212's; multigraph
cuts; Digraph's directed `dicut_size`.

## Canonical API

`GTBase.common`:
- `cut_sizeC`: a side and its complement have the same cut;
- `cut_size_set0`, `cut_size_setT`: the empty and the full side have no cut edge;
- `cut_size_non_monochromatic`: the cut is the non-monochromatic count of `E(G)` under membership;
- `cut_size_edges_between`: the cut is A8's ordered edge count between the two disjoint sides `A` and `~: A`.
`common.v` requires `GTBase.monochromatic` without Import (no cycle: `monochromatic.v` imports only MathComp).

`GTBase.monochromatic`:
- `non_monochromatic_count_le`: the count is at most `#|F|`;
- `_set0`: the empty family counts nothing;
- `_const`: a constant map counts nothing;
- `_small`: empty and one-element members count nothing, for any family;
- `_pair`: a two-colour pair counts once.

The public-only client `base/theories/examples/cut_size.v` imports `GTBase.base` only. It covers:
- empty and full sides, side-complement symmetry, and both bridges;
- a cut bounded by the edge count;
- `K_2` with one side (1), and `K_0`/`K_1` (0);
- the empty family, a constant map and small members;
- a varying two-colour pair;
- an empty carrier with an empty palette;
- a non-uniform family (a two-colour pair and a singleton count 1).

## Rows and certificates

The report tool's discovery at `9de20ca` gives three statements and X209's three chains, all frozen verbatim
at the baseline:

| Area | Frozen modules | Rows |
|---|---|---|
| extremal (`migration/cut_size.v`) | `Legacy` (the two cut sizes), `X76Legacy`, `X78Legacy`, `X76Original`, `X78Original` | X76 Ck-free max cut, X78 H-free max cut |
| hypergraph (`migration/cut_size.v`) | `Legacy` (cut edge and cut size), `X209Legacy` (`is_max_r_cut`, `scaled_excess`, `is_min_scaled_excess`, row) | X209 cut excess, Theta of sqrt |

Certificates:
- The X76/X78 cut-size and per-row certificates are conversions.
- `x209_cut_edge_compat` goes through C8's reflection, and `x209_cut_size_compat` through `eq_card`.
- The three X209 chains and the row are proved by setoid rewriting, with no `try`, under the binders,
  including the type binder of the minimum, using local `and3`/`and4` `Proper` instances.

Natural subtraction, the expected denominator, the maximum over all supplied colourings, quantifier order,
the whole excess sequence with `big_Theta_nat` on its square, statuses and doc blocks are unchanged.

**X209's documented carrier defect is preserved.** `x209_is_min_scaled_excess` binds a fresh `T'`, but `E'`
is a family over the OUTER carrier `T`, so `T'` is unused and the minimum does not range over all carriers.
The frozen chain keeps the binder `forall (T' : finType) (E' : {set {set T}})` verbatim. The kernel probe
proves the exact reading (`review_x209_carrier_defect`, evidence only): the live predicate is equivalent to
the same formula without `T'`. Nothing is repaired or relabelled.

## History and complete Originals

Five earlier frozen rows call the live cut sizes, and are documented in this spec:
- A7's `X76Legacy`/`X78Legacy` per-row copies and its `X76Original`/`X78Original`;
- A5's `X78Legacy`.

The complete rows are pre-M1:
- `X76Original.x76_cut_size` and `X78Original.x78_cut_size` are the `061154c` bodies over M1's frozen
  comprehension `Legacy.edge_set`. This is the frozen raw cut-edge representation, bridged by M1's
  `x76/x78_edge_set_compat` in `x76/x78_cut_size_original_compat`.
- The rows use A7's frozen pre-M1 counts `X76Original/X78Original.x76/x78_edge_count`, and, for X78, A5's
  frozen `Legacy.x78_subgraph_of` (aliased `M1`, `A5`, `A7`, not imported).

With A7's counts, this completes the X76/X78 pre-M1 labels that A7's metadata follow-up left open. A7's and
A5's specs record A9's per-row copies, which keep their live helpers. A7's spec also declares this family's
public client as a lexical consumer of the canonical `edge_count`. Their compact reports are regenerated.

Other families' metadata:
- A8's spec no longer lists the X76/X78 cut sizes as unchanged distinct variants, since this family migrates
  them.
- C8's spec declares `common.v`'s module token `monochromatic` as a consumer, like its existing `base.v`
  entry; it is not U13's predicate.
- No older frozen body is edited.
