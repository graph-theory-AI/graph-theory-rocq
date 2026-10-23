# X15 — `bipartite_matching_underrepresentation`: proved, with `c(m) = 12m + 14` (floor form)

Target (in `packing-theory/theories/conjectures/X15.v`), arXiv:1611.03196
Conj. 1.15, with the explicit constant claimed by the LLM attack
(`attacks/1611.03196__03/output.md`):

```coq
forall m : nat, exists c : nat,
  c <= 32 * (m + 1)^3 /\
  forall (G : sgraph) (E : 'I_m -> {set {set G}}),
    bipartite G -> 0 < Delta G -> x15_edge_family E ->
    exists S, x15_matching S /\
      (#|x15_edge_set G| %/ Delta G <= #|S| + c)%N /\
      forall i, #|S :&: E i| <= ceil_div #|E i| (Delta G).
```

## 1. Verdict

**Proved**, with the constant `c(m) = 12m + 14` — linear in `m`, against the
`32(m+1)^3` claimed by the attack and the `(m+1)^2(16m+29)` of the first version
of this development.

The constant is that of the formal size bound `#|E(G)| %/ Delta G <= #|S| + c`, a
FLOOR form. The source's form `|S| >= |E(G)|/Delta(G) - c(m)` needs the ceiling
of `|E(G)|/Delta(G)` instead, which exceeds the floor by less than one, so in the
source's form the certified constant is `12m + 15`. For the existence statement
(Conjecture 1.15) the two forms are equivalent.

The `O(m^3)` of the write-up became `O(m)` through two suggestions of Laurent
Viennot — remove one bead of every odd type and throw its edge away instead of
padding the type (which makes the halving exact and deletes the trimming phase
and the outer factor `m+1`), and halve a whole level of the mixing tree with a
single splitting of the concatenated necklaces (which pays the per-round loss
once per level instead of once per pair, deletes the `log m` and the second
factor `m+1`, and makes Carathéodory unnecessary); a third of his suggestions,
that hits and conflicts charge disjoint cuts and that a conflict costs one edge
rather than two, is what brings `16m + 24` down to `12m + 14`.

All four results live in `packing-theory/theories/foundations/fair_matching.v`:

| result | statement |
|---|---|
| `x15_llm3_proof` | `bipartite_matching_underrepresentation_llm3_statement` — `c <= 12m + 14` |
| `x15_llm2_proof` | `bipartite_matching_underrepresentation_llm2_statement` — `c <= (m+1)^2 (16m+29)` |
| `x15_llm_proof` | `bipartite_matching_underrepresentation_llm_statement` — the attack's `c <= 32(m+1)^3` |
| `bipartite_matching_underrepresentation` | Conj. 1.15, no explicit constant |

The last three are now corollaries of the first: all four exhibit the same
`c = 12m + 14`.

All are `Print Assumptions`-clean ("Closed under the global context"); no file
involved contains `Axiom`, `Parameter`, `Conjecture`, `admit` or `Admitted`
outside comments. `python3 meta/check_milestone.py X15 packing-theory` reports
`ACCEPTED: 11/11`, and the proof is registered in `meta/formal_resolutions.json`
under record key `1611.03196__03` (direction `prove`).

> The correspondence review recorded with that entry was performed independently
> on 2026-10-23 (the registry entry names the reviewer): correspondence
> confirmed, with the floor-form precision on the constant stated in section 1.
> The formal statement it proves is the pre-existing, already-reviewed encoding
> in `X15.v`, unchanged.

## 2. The proof

Fix `G` bipartite with `D := Delta G > 0`, edge sets `E_1..E_m`, and write
`z(M) := (|M|, |M ∩ E_1|, …, |M ∩ E_m|)` for a matching `M` — the `m+1`
*statistics* of `M`.

1. **König line colouring** — `E(G)` is the disjoint union of `D` matchings, so
   the target vector `(|E(G)|/D, |E_1|/D, …)` is the *average* of the `D`
   vectors `z(M_j)`.
   `ClassicalLemmas.konig.line_colouring.line_colouring_E`; `cls`,
   `cls_partition` in `fair_matching.v`.
2. **Halving two matchings with the Splitting Necklace Theorem** — for
   matchings `A`, `B` there is a matching `C` obtained by giving each edge of
   `A △ B` to one of two thieves, keeping thief 0's `A`-edges and thief 1's
   `B`-edges, and discarding three small families of edges (below). Every
   statistic of `C` is then *exactly* the rounded-down half of the sum of the
   statistics of `A` and `B`.
3. **Synchronized rounds** — Alon's cut budget `t(q-1)` is per *splitting*, not
   per pair, so all the pairs of one round of the mixing tree are halved by a
   **single** splitting, applied to the concatenation of their necklaces. The
   exact halves then hold for the sums over the round, which is all the
   induction needs. `round_exists`, `rounds_exists`.
4. **The leaves** — `2^L` copies of the list `M_1, …, M_D` of all colour
   classes, padded with the empty matching. No Carathéodory, no weights.
   `approx_fair_rounds`.

There is **no trimming phase**: because each round rounds the class counts
*down*, the ceilings `⌈|E_i|/D⌉` hold already.

### The heart of step 2

Let `S := A △ B`. Every vertex meets at most one edge of `A` and one of `B`, so
the "share a vertex" relation on `S` has degree at most two; using the
bipartition it can be **oriented**, becoming a partial injection `nxt`
(`konig/paths2.v`). Closing `nxt` into a permutation and taking its orbits
linearises `S` into blocks along which consecutive edges meet.

The necklace is that sequence: each edge contributes a *block* of `m+1`
consecutive beads, one per statistic, of type `(which matching, which
statistic)` — `2(m+1)` types, plus a null type for the beads of statistics the
edge does not serve. `splitting_necklace_seq` at `q = 2` gives each of two
thieves *exactly* half of every type, with at most `2(m+1)+1 = 2m+3` cuts.

Three families of edges are discarded, and discarding only decreases every
coordinate — the harmless direction for the `m` upper bounds:

| family | why | how many | name |
|---|---|---|---|
| non-unanimous | a cut falls strictly inside an edge's own group of beads, so its statistics went to different thieves; groups are disjoint and of constant size `m+1`, so distinct such edges use distinct **interior** cuts | `<= #interior cuts` | `runan`, `rQint`, `r_nonunan_int` |
| conflicting among the kept | two kept edges share a vertex; both are kept, hence *unanimous*, so their thief change sits exactly at the **boundary** between their groups — except for the wrap pair of a cyclic orbit block, at most one per block, charged to a thief change inside the block | `<= #boundary cuts + cuts` | `rPk`, `r_lin_bnd`, `r_wrap_cuts`, `r_Pk_cuts` |
| odd **class** type | a type of odd multiplicity cannot be halved: its **first** bead is retyped to the null type and its edge discarded. Only the `2m` class types are charged: a *size* type lives on the head bead of a group, whose edge is already absent from the exact half | `<= 2m` | `rmvp`, `retys`, `rhnr`, `count_rmvp_class` |

Interior cuts and boundary cuts are disjoint (`r_cuts_split`), so the first two
rows together cost `2 · cuts`, not `3 · cuts`.

The third row is the change that removes a whole factor `m+1` from the constant.
The first version padded the necklace with extra beads to make every type even,
which made the size error grow with the padding; retyping instead keeps the
block structure — and hence all the positional bookkeeping — intact, and loses
at most one edge per odd type.

### The heart of step 3

The first version mixed the `D` colour classes pairwise along a binary tree,
with one invocation of the splitting theorem per pair, then a chain of halvings
per dyadic weight; the depth of the tree and the final trimming are what made
`c(m)` cubic.

Here the pairs of one round share **one** thief sequence: their necklaces are
concatenated (`gtys`), split once, and each pair reads its own segment at an
offset (`rmatch`, and the induction `round_ind` over the pair list). One round
of `k` pairs replaces `2k` matchings by `k`, with

```
   Σ (|A_i| + |B_i|) <= 2 Σ |C_i| + (12m + 14)
   2 Σ |C_i ∩ E_l|   <= Σ (|A_i ∩ E_l| + |B_i ∩ E_l|)
```

`L` rounds on `2^L` matchings (`pairup`, `rounds_exists`) give one matching `C`
with `Σ |M| <= 2^L |C| + (2^L − 1)(12m+14)` and `2^L |C ∩ E_l| <= Σ |M ∩ E_l|`.
The per-round errors add, but so do the sizes, so after dividing by `2^L` the
error stays below `12m + 14` whatever `L` is — the geometric decay that replaces
the `log` of a balanced tree.

### The deviations from the write-up

1. Step 3 of `attacks/1611.03196__03/output.md` uses a **prescribed-ratio**
   continuous splitting theorem (its Lemma 1, Hobby–Rice style). That statement
   does *not* follow from the equal-share Splitting Necklace Theorem with a cut
   count independent of the ratio: reading `θ = a/q` off a `q`-splitting costs
   `t(q-1)` cuts, so the error would grow with the denominator of `θ`. Here
   every interpolation is a halving (`θ = 1/2`), which is exactly
   `splitting_necklace_seq` at `q = 2`.
2. Its step 2 (**Carathéodory**, to reduce to `m+2` classes with prescribed
   weights) and its step 4 (one interpolation per pair) are replaced by the
   synchronized rounds. No weights are needed: the leaves are copies of *all*
   the colour classes.
3. Its step 5 (**trimming** the classes that exceed their ceiling, at a cost of
   a further factor `m+1` in the size) disappears, because the halvings round
   the class counts down.

## 3. Constant ledger

| quantity | value | where |
|---|---|---|
| cuts of one round's splitting | `t · (q−1) = (2(m+1)+1) · 1 = 2m + 3` | `splitting_necklace_seq` at `q = 2`, `card_TT` |
| edges discarded per round | `cuts` (non-unanimous **and** boundary conflicts, on disjoint cuts) + `cuts` (wrap pairs) + `2m` odd class types | `r_nonunan_int`, `r_cuts_split`, `r_Pk_cuts`, `count_rmvp_class` |
| error of one round | `2(2m+3) + 2m = 6m + 6` | `herr` inside `round_exists` |
| error of one round, at scale 2, with the two roundings | `2(6m+6) + 2 = 12m + 14` | `round_exists` |
| `L` rounds on `2^L` matchings | `(2^L − 1)(12m + 14)` against `2^L` sizes | `rounds_exists` |
| `c(m)` | `12m + 14` (floor form; `12m + 15` in the source's form) | `approx_fair_rounds`, `x15_rounds_instance`, `x15_llm3_proof` |

### Next improvements: `c(m) = 8m + 8`, and `8m + 6`

Write `D` for the number of edges a round discards and `C` for the number of
cuts of its splitting. The proof charges

```
D <= 2C + 2m,
```

namely `C` cuts for the non-unanimous edges and the boundary conflicts together
(they charge *disjoint* cuts, `r_cuts_split`), `C` more for the wrap pairs of
the cyclic orbit blocks (`r_wrap_cuts`), and `2m` for the parity repair of the
class types (`count_rmvp_class`). With `C <= 2m+3` that is `6m+6` per round and
`K = 2 + 2D = 12m + 14`. Two sharpenings remain available without changing the
shape of the argument.

**(a) the wrap term: `2C` down to `C`.** The second `C` pays for the **wrap**
pair of a cyclic orbit block: its two ends are adjacent in `G` but have no bead
boundary between them, so no cut witnesses the conflict directly. The proof
charges such a pair to a thief change *inside* the block (`r_wrap_block`) and
bounds the number of wrapping blocks by `C`. That charge is crude: a cut inside
a block may already be paying for a non-unanimous edge of the same block. If
`A △ B` has no cycles at all — every orbit block a path — the wrap term
vanishes and `D <= C + 2m`, `K = 8m + 8`. In general one would have to choose
the interior cut charged to a wrap distinct from the cuts charged to hits, for
instance by charging the wrap of a block to a *boundary* cut inside it. This is
the cheapest remaining gain.

**(b) the null type costs one cut.** Every edge contributes a full group of
`m+1` beads and the beads of the statistics it does not serve get the null type,
raising the number of types from `2m+2` to `2m+3` and hence Alon's budget
`t(q−1)` from `2m+2` to `2m+3`. Variable-size bead groups remove it, at the
price of replacing the constant group size `m+1` by a prefix-sum index in every
positional lemma — and of redoing the interior/boundary split of the cuts, which
is currently a statement about `p mod (m+1)`. On its own that gives `C <= 2m+2`,
`D <= 6m+4` and `K = 12m + 10`; with (a), `D <= 4m+2` and `K = 8m + 6`.

### Is this optimal?

One round must lose `Θ(m)` in size: splitting `m+1` statistics exactly needs
`Ω(m)` cuts, and at a cut the selected edge of `A` and the selected edge of `B`
may share a vertex, forcing a deletion. So `c(m) = Ω(m)` for any argument of
this shape, and `12m + 14` — or `8m + 6` after (a) and (b) — is within a
constant factor of the floor. arXiv:1611.03196 suggests `c(m) = m/2`; closing
that last constant factor would need a different argument.

The natural discrepancy route does not work: every edge lies in at most `m` of
the classes, so Beck–Fiala would give discrepancy below `m`, but its proof
relaxes constraints once they hold few floating variables, and the vertex
constraints of a matching cannot be relaxed at all.

## 4. New code

All of it axiom-free. What is a classical lemma — reusable independently of
X15 — went to `classical-lemmas`, which depends only on mathcomp and
coq-graph-theory; the development that exists only for this proof lives in
`fair_matching.v`.

| file | lines | content |
|---|---|---|
| `classical-lemmas/theories/konig/paths2.v` | 783 | union of two matchings as chains of a partial injection; orbits, blocks, and the merge of two matchings |
| `classical-lemmas/theories/konig/line_colouring.v` | 427 | König's line-colouring theorem `χ' = Δ` for bipartite graphs, from Hall |
| `classical-lemmas/theories/caratheodory/caratheodory.v` | 320 | Carathéodory's theorem over ℚ, and its cleared-denominator form |
| `packing-theory/theories/foundations/fair_matching.v` | 2509 | the necklace, the halving of one pair, the synchronized rounds (`round_exists`, `rounds_exists`), and the assembly `approx_fair_rounds` → `x15_llm3_proof` → the three other statements |

`caratheodory.v` is **no longer used** by this proof — the synchronized rounds
made it unnecessary. It is kept in `classical-lemmas` as a classical lemma in
its own right.

`classical-lemmas/theories` is organised into `necklace/`, `konig/` and
`caratheodory/` (logical names `ClassicalLemmas.necklace.*` etc.);
`packing-theory` depends on `classical-lemmas`
(`-Q ../classical-lemmas/theories ClassicalLemmas`, and the root `Makefile`
orders the two packages).

The topological input is
`ClassicalLemmas.necklace.necklace.splitting_necklace_seq` (Alon 1987, via
Meunier's simplotopal Tucker lemma), formalised earlier in this repository.

## 5. What was removed

The synchronized-rounds proof supersedes, and this phase deleted from
`fair_matching.v`:

- the trimming phase: `Section Trim`, `trim_exists`, `x15_trim_instance`, and
  the `x15_approx_fair` / `x15_llm_instance` vocabulary that carried the
  additive error through it (`x15_approx_fair_instance`, `x15_approx_fair_llm`,
  `x15_approx_fair0`, `x15_small_instance`, `x15_llm_instance0`);
- the per-pair halving lemma `matching_halving` and the counting lemmas that
  only served it (`Chalf_stat`, `Chalf_size`, `Xc`, `Yc`, `Zc`, `Dc`,
  `share_bounds`, `cuts_thE`, …), replaced by the round-aware `rCr_card_le`,
  `rCr_card_ge`, `round_ind`;
- the whole mixing machinery `Section Mixing` (`realisesN`, `mix_half`,
  `mix_dyadic`, `mix_list`) and the arithmetic lemmas feeding it, replaced by
  `round_exists` / `rounds_exists`;
- the Carathéodory step of the assembly (`zstat`, `wone`, `sum_zstat`,
  `approx_fair_core`, `Bmix`, `Bmix_le`, `x15_approx_fair_proof`).

Kept and still used: `x15_edge_setE`, `matching_x15`, the necklace and counting
infrastructure of steps 2–3, `cls` / `cls_partition`. Kept but unused:
`edges_leq_cover`, `x15_big_matching` (König min-cover = max-matching) — the
`m = 0` case, and the sanity check that the size half of the conjecture alone is
König's theorem.

## 6. Tooling note

Rocq was driven interactively through the `rocq-mcp-evolve` MCP server
(LLM4Rocq); during the first phase its cached project configuration predated the
move of `classical-lemmas` into subdirectories, so goals were read from a small
`rocq repl` harness instead and files recompiled with `rocq c`. Every recurring
error and its fix is appended to `tactics-playbook.md`.
