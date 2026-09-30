(** * Spectral.foundations.spectral — spectral graph-theory vocabulary (area-local)

    Matrix / eigenvalue vocabulary shared by the three SPECTRAL rows of milestone D5
    (signing eigenvalue bound, "determined by spectrum", Laplacian-degree majorisation).
    Kept area-local (NOT in [base]) since no other package consumes spectral vocabulary.

    Design decisions (D5 preflight):
    - [algC] / [mathcomp.field] are NOT installed.  We import only [all_algebra].
    - COSPECTRALITY / "determined by spectrum": [char_poly] EQUALITY over [int]
      (no field, no roots); iso via [diso] ([≃]), not equality.
    - EIGENVALUE MAGNITUDE / ORDERING / SPECTRAL RADIUS: quantify over an abstract
      real-closed field [R : rcfType] (order, [`|·|], [Num.sqrt]); statement-only.
    - The spectrum is a MULTISET (eigenvalues counted with multiplicity), encoded as
      "[char_poly A] factors as [\prod (X - x)] over a sorted sequence [s]".

    IMPORT ORDER (load-bearing for int/rat canonical structures):
      all_boot -> GraphTheory.sgraph -> GTBase.base -> all_algebra ; then perm. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph bij.
From GTBase Require Import base.
From mathcomp Require Import all_algebra perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

(** ** Adjacency, degree and Laplacian matrices over an arbitrary ring

    Vertices are indexed by ['I_#|G|] via [enum_val].  [adjmx] has a [1] for each
    edge and [0] elsewhere; [degmx] is the diagonal degree matrix; the (combinatorial)
    Laplacian is [L = D - A]. *)
Section Matrices.
Variable R : nzRingType.

Definition adjmx (G : sgraph) : 'M[R]_(#|G|) :=
  \matrix_(i, j) (if enum_val i -- enum_val j then 1 else 0).

Definition degmx (G : sgraph) : 'M[R]_(#|G|) :=
  \matrix_(i, j) (if i == j then (#|N(enum_val i)|)%:R else 0).

Definition Lapmx (G : sgraph) : 'M[R]_(#|G|) := degmx G - adjmx G.

End Matrices.

(** ** Cospectrality and spectral determination (over [int], no field needed)

    Two graphs are cospectral when their adjacency characteristic polynomials over
    [int] coincide (equality of multisets of eigenvalues, with multiplicity).  A graph
    is "determined by its spectrum" when every cospectral graph is isomorphic to it. *)
Definition cospectral (G H : sgraph) : Prop :=
  char_poly (adjmx int G) = char_poly (adjmx int H).

Definition determined_by_spectrum (G : sgraph) : Prop :=
  forall H : sgraph, cospectral G H -> inhabited (G ≃ H).

(** ** Real eigenvalue notions over a real-closed field [R]

    A real symmetric matrix has real eigenvalues, which live in any [rcfType]; this is
    enough to STATE spectral-radius and ordering facts (no concrete [algC]). *)
Section Spectral_rcf.
Variable R : rcfType.

(** All eigenvalues have magnitude at most [b]. *)
Definition spectral_radius_le (n : nat) (A : 'M[R]_n) (b : R) : Prop :=
  forall x : R, eigenvalue A x -> `|x| <= b.

(** [S] is a symmetric signing of [G]'s adjacency matrix: symmetric, entry [±1] on
    each edge and [0] off the edges (i.e. replace some [+1] entries of [adjmx] by [-1]). *)
Definition is_signing (G : sgraph) (S : 'M[R]_(#|G|)) : Prop :=
  (forall i j, S i j = S j i) /\
  (forall i j, if enum_val i -- enum_val j
               then (S i j = 1) \/ (S i j = -1)
               else S i j = 0).

(** [s] is the spectrum of [A] sorted in non-increasing order, counted with
    multiplicity: [s] has length [n], is decreasing, and [char_poly A] factors as
    [\prod_(x <- s) (X - x)]. *)
Definition is_spectrum (n : nat) (A : 'M[R]_n) (s : seq R) : Prop :=
  [/\ size s = n, sorted (fun x y : R => y <= x) s
    & char_poly A = \prod_(x <- s) ('X - x%:P)].

End Spectral_rcf.

(** ** Degree sequence sorted in non-increasing order *)
Definition degseq (G : sgraph) : seq nat := [seq #|N(v)| | v : G].

Definition is_deg_sorted (G : sgraph) (d : seq nat) : Prop :=
  perm_eq d (degseq G) /\ sorted geq d.

(** ** Labelled graphs on [n] vertices and spectral-determination density

    For the "almost all graphs are determined by their spectrum" row we need a finite,
    DECIDABLE encoding so the density [determined_count n / total_count n] is a genuine
    ratio of cardinalities.  A labelled graph on [n] vertices is a symmetric irreflexive
    boolean relation; cospectrality is [char_poly] equality over [int]; isomorphism is
    permutation-relabelling — all boolean, hence countable. *)
Section Labelled.
Variable n : nat.

Definition ladj := {ffun 'I_n * 'I_n -> bool}.

Definition is_lgraph (r : ladj) : bool :=
  [forall p : 'I_n * 'I_n, r p == r (p.2, p.1)] && [forall i, ~~ r (i, i)].

Definition lgraphs : {set ladj} := [set r | is_lgraph r].

Definition ladjmx (r : ladj) : 'M[int]_n :=
  \matrix_(i, j) (if r (i, j) then 1 else 0).

Definition lcospectral (r r' : ladj) : bool :=
  char_poly (ladjmx r) == char_poly (ladjmx r').

Definition liso (r r' : ladj) : bool :=
  [exists s : 'S_n, [forall i, [forall j, r (s i, s j) == r' (i, j)]]].

(** [r] is determined by its spectrum (within labelled [n]-graphs): every cospectral
    labelled graph is isomorphic to it. *)
Definition lspec_determined (r : ladj) : bool :=
  [forall r' : ladj, (r' \in lgraphs) ==> (lcospectral r r' ==> liso r r')].

End Labelled.

(** Total number of labelled [n]-graphs, and the number that are spectrally determined. *)
Definition total_count (n : nat) : nat := #|lgraphs n|.

Definition determined_count (n : nat) : nat :=
  #|[set r in lgraphs n | lspec_determined r]|.

(** ** Wave-V vocabulary equivalence: the labelled model vs [sgraph] ******

    meta/STATEMENT_IMPROVEMENTS.md (section "## spectral-graph-theory",
    "### Suspected unfaithful or proxy encodings", entry
    [opg:are_almost_all_graphs_determined_by_their_spectrum]) records that this
    file carries TWO notions of graph isomorphism: [liso] (permutation
    relabelling of a labelled adjacency [ladj n], used by [lspec_determined] and
    hence by the density row) and the [sgraph]-level [_ ≃ _] (used by
    [determined_by_spectrum], which no statement of the package uses).  The
    ledger asks for the equivalence [liso r r' <-> inhabited (sgraph_of r ≃
    sgraph_of r')] "before any proof work"; there was no [sgraph_of], so it is
    defined here and the equivalence is proved.

    The equivalence is UNCONDITIONAL on [is_lgraph r] / [is_lgraph r'] once
    [sgraph_of] is available: [sgraph_of] needs those two proofs to build the
    [sgraph] (adjacency must be symmetric and irreflexive), and no further
    hypothesis is required.  In particular nothing here depends on labels: on a
    labelled graph the [sgraph] carrier IS [['I_n]], so every bijection of
    carriers is a permutation and the two notions coincide exactly.  (Had the
    [sgraph] been taken on an abstract vertex type, the [sgraph] isomorphism
    would be the coarser notion.)

    No statement body is changed. *)

Section LabelledSgraph.
Variable n : nat.
Variables (r : ladj n) (rG : is_lgraph r).

Lemma lg_sym : symmetric (fun i j : 'I_n => r (i, j)).
Proof. by move: rG => /andP[/forallP Hs _] i j; apply/eqP; exact: (Hs (i, j)). Qed.

Lemma lg_irrefl : irreflexive (fun i j : 'I_n => r (i, j)).
Proof. by move: rG => /andP[_ /forallP Hi] i; apply/negbTE; exact: Hi. Qed.

(** The simple graph on [['I_n]] described by the labelled adjacency [r]. *)
Definition sgraph_of : sgraph := SGraph lg_sym lg_irrefl.

Lemma sgraph_ofE (i j : 'I_n) : (i : sgraph_of) -- j = r (i, j).
Proof. by []. Qed.

End LabelledSgraph.

Lemma liso_equiv_sgraph_of (n : nat) (r r' : ladj n)
    (rG : is_lgraph r) (rG' : is_lgraph r') :
  liso r r' <-> inhabited (sgraph_of rG ≃ sgraph_of rG').
Proof.
split=> [/existsP[s /forallP Hs]|[h]].
- have h1 : forall x y : sgraph_of rG', x -- y -> (s x : sgraph_of rG) -- s y.
    by move=> x y xy; rewrite sgraph_ofE (eqP (forallP (Hs x) y)) -sgraph_ofE.
  have h2 : forall x y : sgraph_of rG,
      x -- y -> ((s^-1)%g x : sgraph_of rG') -- (s^-1)%g y.
    move=> x y xy.
    rewrite sgraph_ofE -(eqP (forallP (Hs ((s^-1)%g x)) ((s^-1)%g y))).
    by rewrite !permKV -sgraph_ofE.
  split; apply: diso_sym.
  exact: (@Diso'' (sgraph_of rG') (sgraph_of rG) s (s^-1)%g
            (permK s) (permKV s) h1 h2).
- pose h' := diso_sym h.
  have hinj : injective (fun x : 'I_n => (h' x : 'I_n)) by apply: can_inj (bijK h').
  apply/existsP; exists (perm hinj); apply/forallP => i; apply/forallP => j.
  rewrite !permE -sgraph_ofE -[r' _]sgraph_ofE.
  by apply/eqP; exact: (edge_diso h' i j).
Qed.

Print Assumptions liso_equiv_sgraph_of.
