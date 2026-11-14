(** * Extremal.conjectures.grounding_X308 -- grounding certificates of wave X308

    [Qed]-closed, axiom-free certificates for the two rows of [Extremal.conjectures.X308]:
      - R1 (engbers_connected_h_colouring_maximisation_statement):
        - hyp_inhabited: H = K_3 without loops satisfies the uniqueness condition, and for every N the complete
          graph K_n with n = max(N, 6) is connected, has minimum degree at least 3 and is not isomorphic to
          K_(3,n-3) (it is not bipartite); the strict bound is then claimed for H = K_3;
        - not_trivially_true: the clause WITHOUT the non-trivial guard is false at H = K_1 (one unlooped vertex):
          every graph with an edge has no K_1-colouring, so K_n and K_(3,n-3) tie at 0, while that clause implies
          the row (the guard of the Notes is necessary);
      - R2 (engbers_connected_q_colouring_uniqueness_statement):
        - hyp_inhabited: the same K_n class; the strict bound is then claimed for q = 3;
        - not_trivially_true: the statement without q > 2 is false at q = 1 (a graph with an edge has no proper
          1-colouring, so K_n and K_(3,n-3) tie at 0), while it implies the row;
      - helper_sanity (R1's four helpers): hom(K_2, looped K_1) = 1 and hom(K_2, K_1) = 0; the looped K_1 is
        complete looped; K_2 is complete balanced bipartite; K_3 meets the uniqueness condition and K_2 does not. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries bij digraph sgraph.
From GTBase Require Import base common colourings.
From Extremal.conjectures Require Import X308.
From mathcomp Require Import zify.
From Stdlib Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Complete graphs *)

Lemma g308_edge_complete n (x y : 'K_n) : (x -- y) = (x != y).
Proof. by []. Qed.

Lemma g308_connected_complete n (A : {set 'K_n}) : connected A.
Proof.
move=> x y xA yA; have [->|xy] := eqVneq x y; first exact: connect0.
by apply: connect1; rewrite /= xA yA g308_edge_complete xy.
Qed.

Lemma g308_min_degree_complete n : min_degree_at_least 'K_n n.-1.
Proof.
move=> v; have -> : N(v) = [set~ v].
  by apply/setP => w; rewrite in_opn in_setC1 g308_edge_complete eq_sym.
by rewrite cardsC1 card_ord.
Qed.

(** Two vertices of K_n, n >= 2, are adjacent. *)
Lemma g308_complete_edge n : 1 < n -> exists x y : ('K_n), x -- y.
Proof.
move=> n2; exists (Ordinal (ltnW n2)), (Ordinal n2).
by rewrite g308_edge_complete -val_eqE.
Qed.

(** A complete graph on at least three vertices is not isomorphic to a complete bipartite graph: an isomorphism
    would 2-colour it properly through the sides, injectively. *)
Lemma g308_not_diso_complete_KB n a b : 2 < n -> ~ inhabited (diso 'K_n (KB a b)).
Proof.
move=> n3 [i].
pose f (x : 'K_n) := i x \in [set z : KB a b | is_inl z].
have inj : injective f.
  move=> x y fxy; apply/eqP/negPn/negP => xy.
  have := complete_bipartite_KB (i x) (i y).
  by rewrite edge_diso g308_edge_complete xy -/(f x) -/(f y) fxy addbb.
have := @leq_card _ _ f inj; rewrite card_bool card_ord; lia.
Qed.

(** The class of the rows, inhabited for every N by K_n, n = max(N, delta + 3). *)
Definition g308_family (delta : nat) : Prop :=
  forall N : nat, exists G : sgraph,
    [/\ N <= #|G|, connected [set: G], min_degree_at_least G delta
      & ~ inhabited (diso G (KB delta (#|G| - delta)))].

Lemma g308_complete_class (delta N : nat) :
  [/\ N <= #|'K_(maxn N delta.+3)|, connected [set: 'K_(maxn N delta.+3)],
      min_degree_at_least 'K_(maxn N delta.+3) delta
    & ~ inhabited (diso 'K_(maxn N delta.+3) (KB delta (#|'K_(maxn N delta.+3)| - delta)))].
Proof.
have hn : delta.+3 <= maxn N delta.+3 := leq_maxr N delta.+3.
split.
- by rewrite card_ord leq_maxl.
- exact: g308_connected_complete.
- move=> v; apply: (leq_trans _ (g308_min_degree_complete v)); lia.
- by apply: g308_not_diso_complete_KB; lia.
Qed.

Lemma g308_family_complete (delta : nat) : g308_family delta.
Proof. by move=> N; exists 'K_(maxn N delta.+3); exact: g308_complete_class. Qed.

(** ** Complete bipartite graphs and the one-vertex target *)

Lemma g308_KB_edge a b : 0 < a -> 0 < b -> exists x y : KB a b, x -- y.
Proof.
move=> a0 b0; exists (inl (Ordinal a0)), (inr (Ordinal b0)).
by have := complete_bipartite_KB (inl (Ordinal a0) : KB a b) (inr (Ordinal b0)); rewrite !inE /= => ->.
Qed.

Lemma g308_K1_noedge (a b : 'K_1) : ~~ (a -- b).
Proof. by rewrite g308_edge_complete negbK (ord1 a) (ord1 b). Qed.

(** A graph with an edge has no homomorphism into a graph without edges and loops. *)
Lemma g308_lhom_count_noedge (G H : sgraph) (x y : G) :
  x -- y -> (forall a b : H, ~~ (a -- b)) -> x308_lhom_count G (set0 : {set H}) = 0.
Proof.
move=> xy noedge; apply/eqP; rewrite cards_eq0; apply/eqP/setP => f.
rewrite !inE; apply/negbTE/negP => /forallP /(_ x) /forallP /(_ y).
by rewrite xy /= (negbTE (noedge _ _)) inE andbF.
Qed.

(** A graph with an edge has no proper 1-colouring. *)
Lemma g308_proper1_zero (G : sgraph) (x y : G) :
  x -- y -> #|[set f : {ffun G -> 'I_1} | proper_colouring f]| = 0.
Proof.
move=> xy; apply/eqP; rewrite cards_eq0; apply/eqP/setP => f.
rewrite !inE; apply/negbTE/negP => /proper_colouringP /(_ x y xy).
by rewrite (ord1 (f x)) (ord1 (f y)) eqxx.
Qed.

(** ** R1: the uniqueness condition on small targets *)

Lemma g308_K3_hyp : x308_uniqueness_hyp (set0 : {set 'K_3}).
Proof.
pose v0 := (@Ordinal 3 0 isT : 'K_3).
exists [set: 'K_3]; split.
- by apply/set0Pn; exists v0; rewrite inE.
- exact: g308_connected_complete.
- by move=> x y _ _; rewrite inE.
- by left; exists v0, (@Ordinal 3 1 isT : 'K_3); split; rewrite ?inE // g308_edge_complete.
- split.
  + by case=> sub _; move/subsetP: sub => /(_ v0); rewrite !inE => /(_ isT).
  + case=> _ [A [_ _ cb]]; apply: (@not_complete_bipartite_K3 A) => x y.
    by apply: cb; rewrite inE.
Qed.

Lemma g308_K2_balanced : x308_complete_balanced_bipartite (set0 : {set 'K_2}) [set: 'K_2].
Proof.
split; first by apply/disjointP => x _; rewrite inE.
exists [set (@Ordinal 2 0 isT : 'K_2)]; split.
- exact: subsetT.
- by rewrite cards1 setTD cardsC1 card_ord.
- move=> x y _ _; rewrite g308_edge_complete !inE.
  by case: x => [[|[|m]] p] //; case: y => [[|[|k]] q].
Qed.

Lemma g308_K2_not_hyp : ~ x308_uniqueness_hyp (set0 : {set 'K_2}).
Proof.
case=> C [C0 _ closed _ [_ nb]]; apply: nb.
have CT : C = [set: 'K_2].
  apply/setP => y; rewrite inE; case/set0Pn: C0 => x xC.
  have [<-|xy] := eqVneq x y; first exact: xC.
  by apply: (closed x y xC); rewrite g308_edge_complete.
by rewrite CT; exact: g308_K2_balanced.
Qed.

Lemma g308_lhom_K2_looped_K1 : x308_lhom_count 'K_2 [set: 'K_1] = 1.
Proof.
rewrite /x308_lhom_count.
have -> : [set f : {ffun 'K_2 -> 'K_1} |
            [forall x : ('K_2), [forall y : ('K_2),
               (x -- y) ==> ((f x -- f y) || ((f x == f y) && (f x \in [set: 'K_1])))]]] = setT.
  apply/setP => f; rewrite !inE; apply/forallP => x; apply/forallP => y; apply/implyP => _.
  by rewrite (ord1 (f x)) (ord1 (f y)) eqxx inE andbT orbT.
by rewrite cardsT card_ffun !card_ord.
Qed.

(** ** Grounding certificates *)

(** R1, hyp_inhabited. *)
Definition g308_hyp_claim : Prop :=
  [/\ x308_uniqueness_hyp (set0 : {set 'K_3}), g308_family 3 &
     (engbers_connected_h_colouring_maximisation_statement ->
        exists N : nat, forall G : sgraph,
          N <= #|G| -> connected [set: G] -> min_degree_at_least G 3 ->
          ~ inhabited (diso G (KB 3 (#|G| - 3))) ->
          x308_lhom_count G (set0 : {set 'K_3}) < x308_lhom_count (KB 3 (#|G| - 3)) (set0 : {set 'K_3}))].

Theorem g308_hyp_inhabited : g308_hyp_claim.
Proof.
split; [exact: g308_K3_hyp | exact: g308_family_complete | move=> S].
have [N hN] := S 3 'K_3 set0 isT; exists N => G h1 h2 h3 h4.
exact: (proj2 (hN G h1 h2 h3)) g308_K3_hyp h4.
Qed.

(** R1, not_trivially_true: the clause without the non-trivial guard. *)
Definition g308_unguarded_variant : Prop :=
  forall (delta : nat) (H : sgraph) (L : {set H}),
    3 <= delta ->
    exists N : nat, forall G : sgraph,
      N <= #|G| -> connected [set: G] -> min_degree_at_least G delta ->
      x308_lhom_count G L <= x308_lhom_count (KB delta (#|G| - delta)) L /\
      (~ inhabited (diso G (KB delta (#|G| - delta))) ->
         x308_lhom_count G L < x308_lhom_count (KB delta (#|G| - delta)) L).

Definition g308_ntt_claim : Prop :=
  ~ g308_unguarded_variant /\
  (g308_unguarded_variant -> engbers_connected_h_colouring_maximisation_statement).

Theorem g308_not_trivially_true : g308_ntt_claim.
Proof.
split=> [V | V delta H L d3].
  have [N hN] := V 3 'K_1 set0 isT.
  have [h1 h2 h3 h4] := g308_complete_class 3 N.
  have := proj2 (hN _ h1 h2 h3) h4.
  have [x [y xy]] := @g308_complete_edge (maxn N 6) (leq_trans (isT : 1 < 6) (leq_maxr N 6)).
  have b0 : 0 < #|'K_(maxn N 6)| - 3 by rewrite card_ord; have := leq_maxr N 6; lia.
  have [u [v uv]] := @g308_KB_edge 3 (#|'K_(maxn N 6)| - 3) isT b0.
  by rewrite (g308_lhom_count_noedge xy g308_K1_noedge) (g308_lhom_count_noedge uv g308_K1_noedge).
have [N hN] := V delta H L d3; exists N => G h1 h2 h3.
by have [le lt] := hN G h1 h2 h3; split=> // _.
Qed.

(** R2, hyp_inhabited. *)
Definition g308_q_hyp_claim : Prop :=
  g308_family 3 /\
  (engbers_connected_q_colouring_uniqueness_statement ->
     exists N : nat, forall G : sgraph,
       N <= #|G| -> connected [set: G] -> min_degree_at_least G 3 ->
       ~ inhabited (diso G (KB 3 (#|G| - 3))) ->
       #|[set f : {ffun G -> 'I_3} | proper_colouring f]| <
         #|[set f : {ffun KB 3 (#|G| - 3) -> 'I_3} | proper_colouring f]|).

Theorem g308_q_hyp_inhabited : g308_q_hyp_claim.
Proof. by split; [exact: g308_family_complete | move=> S; exact: S 3 3 isT isT]. Qed.

(** R2, not_trivially_true: the statement without q > 2. *)
Definition g308_q_variant : Prop :=
  forall delta q : nat,
    3 <= delta ->
    exists N : nat, forall G : sgraph,
      N <= #|G| -> connected [set: G] -> min_degree_at_least G delta ->
      ~ inhabited (diso G (KB delta (#|G| - delta))) ->
      #|[set f : {ffun G -> 'I_q} | proper_colouring f]| <
        #|[set f : {ffun KB delta (#|G| - delta) -> 'I_q} | proper_colouring f]|.

Definition g308_q_ntt_claim : Prop :=
  ~ g308_q_variant /\ (g308_q_variant -> engbers_connected_q_colouring_uniqueness_statement).

Theorem g308_q_not_trivially_true : g308_q_ntt_claim.
Proof.
split=> [V | V delta q d3 _].
  have [N hN] := V 3 1 isT.
  have [h1 h2 h3 h4] := g308_complete_class 3 N.
  have := hN _ h1 h2 h3 h4.
  have [x [y xy]] := @g308_complete_edge (maxn N 6) (leq_trans (isT : 1 < 6) (leq_maxr N 6)).
  have b0 : 0 < #|'K_(maxn N 6)| - 3 by rewrite card_ord; have := leq_maxr N 6; lia.
  have [u [v uv]] := @g308_KB_edge 3 (#|'K_(maxn N 6)| - 3) isT b0.
  by rewrite (g308_proper1_zero xy) (g308_proper1_zero uv).
exact: V delta q d3.
Qed.

(** R1, helper_sanity: the four helpers on small targets. *)
Definition g308_helper_claim : Prop :=
  [/\ x308_lhom_count 'K_2 [set: 'K_1] = 1,
      x308_lhom_count 'K_2 (set0 : {set 'K_1}) = 0,
      x308_complete_looped [set: 'K_1] [set: 'K_1],
      x308_complete_balanced_bipartite (set0 : {set 'K_2}) [set: 'K_2]
    & x308_uniqueness_hyp (set0 : {set 'K_3}) /\ ~ x308_uniqueness_hyp (set0 : {set 'K_2})].

Theorem g308_helper_sanity : g308_helper_claim.
Proof.
split.
- exact: g308_lhom_K2_looped_K1.
- have [x [y xy]] := @g308_complete_edge 2 isT.
  exact: g308_lhom_count_noedge xy g308_K1_noedge.
- by split=> [|x y _ _]; [exact: subxx | rewrite (ord1 x) (ord1 y) eqxx].
- exact: g308_K2_balanced.
- by split; [exact: g308_K3_hyp | exact: g308_K2_not_hyp].
Qed.
