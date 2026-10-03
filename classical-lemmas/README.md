# classical-lemmas

Rocq formalizations of **classical mathematical theorems**, proved from the
literature and stated so that they can be reused anywhere.

Everything here is proved from scratch on top of MathComp and coq-graph-theory.
The one prerequisite inside this repository is the MathComp-only module
`GTBase.incidence` of `base` (see Building): `konig/line_colouring.v`'s edge
count `edeg F v` is its `incidence_degree F v`, the number of members of `F`
containing `v`.  Nothing depends on the graph conjectures for which the lemmas
were first needed.
Every file is axiom-free — `Print Assumptions` answers *Closed under the global
context* for every result — and contains no `Axiom`, `Parameter`, `Conjecture`,
`admit` or `Admitted`.

Each `.v` file opens with a `Provenance, sources, and what corresponds to what`
comment giving, for that file: how it was produced, the models used and their
measured token cost, the papers it formalizes, and a statement-by-statement
correspondence between the paper and the Rocq names.

## The theorems

### Alon's Splitting Necklace Theorem — `theories/necklace/`

A necklace of `n` beads of `t` types, each type occurring a multiple of `q`
times, can be cut into at most `t(q-1)` places and the pieces distributed to `q`
thieves so that every thief receives exactly a `1/q` share of every type.

```coq
(* theories/necklace/necklace.v *)
Theorem splitting_necklace_theorem (n t q : nat) (c : 'I_n -> 'I_t) :
  0 < q -> (forall k : 'I_t, q %| #|[set i | c i == k]|) ->
  exists a : 'I_n -> 'I_q,
    #|[set pr : 'I_n * 'I_n | (pr.2 == pr.1.+1 :> nat) && (a pr.1 != a pr.2)]|
      <= t * q.-1
    /\ forall (k : 'I_t) (j : 'I_q),
         #|[set i | (c i == k) && (a i == j)]| = #|[set i | c i == k]| %/ q.
```

`splitting_necklace_seq` is the same statement on sequences.  The proof is the
topological one: it goes through the ℤ_p-simplotopal Tucker lemma
(`tucker.zp_tucker_prime`), which gives the theorem for a prime number of
thieves (`necklace_prime.necklace_prime`), the general case following by the
classical multiplicativity trick.  The twelve files, in dependency order:

| file | content |
|---|---|
| `necklace/chains.v` | finitely supported chains over a ring |
| `necklace/necklace_complex.v` | the complexes `K` and `L`, and the statement of the ℤ_p-simplotopal Tucker lemma |
| `necklace/salt.v` | strongly alternating patterns (HSSZ, Def. 3.5) |
| `necklace/cubical.v` | the cubical chain complex of the star power `R^N` |
| `necklace/hemispheres.v` | the hemisphere cochains of the ℤ_p-Tucker lemma |
| `necklace/simplotope.v` | the complex `L = (Δ_{p-1})^t` and its chain complex |
| `necklace/chainmap.v` | the chain map induced by a simplotopal map (Meunier, Thm 2.4) |
| `necklace/bar.v` | the homogeneous bar complex of ℤ_p |
| `necklace/eta.v` | the equivariant chain map `C(∂L) → C(EℤZ_p)` |
| `necklace/tucker.v` | the ℤ_p-simplotopal Tucker lemma (Meunier, Thm 3.3) |
| `necklace/necklace_prime.v` | the splitting theorem for a prime number of thieves |
| `necklace/necklace.v` | the splitting theorem, for every `q > 0` |

`NECKLACE_STATUS.md` documents the development stage by stage.

**References.**

- N. Alon, *Splitting necklaces*, Advances in Mathematics **63** (1987) 247–253.
  The theorem itself. Not available locally.
- F. Meunier, *Simplotopal maps and necklace splitting*, Discrete Mathematics
  **323** (2014) 14–26. The proof followed here, §2–§3.
  Local copy: `Meunier2014-Simplotopal_Necklace_web.pdf`.
- B. Hanke, R. Sanyal, C. Schultz, G. M. Ziegler, *Combinatorial Stokes formulas
  via minimal resolutions*, JCTA **116** (2009) 404–420. The cochain machinery
  behind the ℤ_p-Tucker lemma (reference [9] of Meunier 2014).
  Local copy: `HankeSSZ-Combinatorial_stokes_formulas-1-s2.0-S0097316508000988-main.pdf`.
- F. Meunier, *A Zq-Fan theorem*, technical report, "Topological combinatorics"
  workshop, Stockholm, December 2006 (reference [11] of Meunier 2014).
  Local copy: `Meunier2006-zqkyfan.pdf`.

### König's line-colouring theorem — `theories/konig/line_colouring.v`

The edges of a bipartite graph of maximum degree at most `D` can be coloured
with `D` colours so that every colour class is a matching (`χ' = Δ`), stated for
an arbitrary set `F` of edges and, as `line_colouring_E`, for `E(G)`.

```coq
Theorem line_colouring (G : sgraph) (f : G -> bool) :
  (forall x y : G, x -- y -> f x != f y) ->
  forall (D : nat) (F : {set {set G}}), F \subset E(G) ->
  (forall v : G, edeg F v <= D) ->
  exists col : {set G} -> nat,
    (forall e, e \in F -> col e < D) /\ (forall j, matching [set e in F | col e == j]).
```

Proved by the usual induction on `D`, peeling off one matching that covers every
vertex of maximum degree; Hall's theorem is imported from coq-graph-theory
(`GraphTheory.connectivity.Hall`), the one-sided form `Hall_sat` being derived
from it on an induced subgraph.

**Reference.** D. König, *Über Graphen und ihre Anwendung auf
Determinantentheorie und Mengenlehre*, Mathematische Annalen **77** (1916)
453–465.

### The union of two matchings — `theories/konig/paths2.v`

Two matchings `A`, `B` of a bipartite graph meet every vertex at most once each,
so their union has degree at most two; using the bipartition, the "share a
vertex" relation is *oriented* into a partial injection `nxt`, whose orbits
linearise `A ∪ B` into the blocks that are its paths and even cycles
(`blocks`, `block_nth`, `meetP`).  `merge` picks from them one matching covering
every vertex covered by `A` on one side and by `B` on the other.

**Reference.** None: the decomposition into paths and even cycles is folklore
(it underlies both König's theorem and Berge's augmenting-path theorem), and
nothing comparable was available in coq-graph-theory.  The orientation by the
bipartition is what makes it usable in Rocq without path combinatorics.

### Carathéodory's theorem over ℚ — `theories/caratheodory/caratheodory.v`

A convex combination of points of ℚ^d is a convex combination of at most `d+1`
of them.

```coq
Theorem caratheodory (d : nat) (T : finType) (z : T -> 'I_d -> rat) (lam : T -> rat) : ...
Theorem caratheodory_nat (d : nat) (T : finType) (z : T -> 'I_d -> nat) (w : T -> nat) : ...
```

`caratheodory_nat` is the same with the denominators cleared.  It was written
for the X15 proof of `packing-theory`, whose synchronized-rounds version (18 Sep
2026) no longer needs it; it is kept here as a classical lemma in its own right.
The proof is the standard one: more than `d+1` positive
weights give an affine dependency — obtained from a nonzero kernel vector of the
matrix of the points with a row of ones added — which is followed until one
weight vanishes.

**Reference.** C. Carathéodory, *Über den Variabilitätsbereich der Fourier'schen
Konstanten von positiven harmonischen Funktionen*, Rendiconti del Circolo
Matematico di Palermo **32** (1911) 193–217.

## Building

```sh
rocq makefile -f _CoqProject -o Makefile.coq && make -f Makefile.coq
```

after building `base` (`_CoqProject` maps `../base/theories` as `GTBase`), or,
from the repository root, `make classical-lemmas`, which builds `base` first.
Rocq 9.1.1 with MathComp 2.5.0 and coq-graph-theory 0.9.7.

## Who uses this

`packing-theory` uses `necklace/` and `konig/` to prove Conjecture 1.15 of
arXiv:1611.03196 (`packing-theory/theories/foundations/fair_matching.v`), with
the linear constant `c(m) = 12m + 14`; the two parts of that proof that are
*not* classical — the interpolation of two matchings by a necklace splitting,
and the synchronized rounds that iterate it — live there, with their only
client, and not here.  `caratheodory/` was written for an earlier version of
that proof and is no longer used by it.
