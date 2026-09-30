(** * Packing.conjectures.grounding_X226 — grounding lemmas for wave X226.

    Qed-closed, axiom-free sanity results for the four X226 nodes.  They
    validate the STATEMENTS and the two primitives the wave introduces; they do
    not attack the conjectures.

    PRIMITIVE 1 — eta (rows 2302.04986 #00, #01, #04).

      NON-VACUITY   [x226_hitting_setT] / [x226_eta_le_card]: every graph with a
                    vertex HAS a hitting set, so eta is defined there;
                    [x226_eta_le_K1] is the concrete value eta(K_1) <= 1;
                    [x226_eta_bounded_card_le] shows [x226_eta_bounded] itself is
                    satisfiable (every class of graphs of bounded order is
                    eta-bounded).
      TEETH         [x226_not_eta_le0]: NO graph has eta(G) <= 0, so an
                    eta-bounding function is never the zero function;
                    [x226_no_eta_bound_empty]: a graph with no vertex has no
                    hitting set at all — this is exactly why the [0 < #|G|] guard
                    is in [x226_eta_bounded], and without it all three
                    eta-statements would be FALSE for trivial reasons.
      GUARDS        [x226_forest_witness] / [x226_not_forest_K3]: the forest
                    hypothesis of Conjecture 1.8 is satisfiable and does exclude
                    graphs; [x226_path_free_K1] / [x226_two_stars_free_K1]: the
                    P_t-free and (S_a u S_b)-free classes contain a graph with a
                    vertex, so the conclusion is not quantified over an empty
                    class.

    PRIMITIVE 2 — subcube partitions (row 2401.00299 #04).

      NON-VACUITY   [x226_f_dim_le2_gt0] / [x226_f_gt0]: both counting functions
                    are positive (the partition of Q_d into singletons uses only
                    0-dimensional subcubes).
      TEETH         [x226_f_dim_le2_leq] and [x226_f_dim_le2_lt]: the
                    dimension-at-most-2 restriction is a genuine restriction —
                    from d = 3 on it is STRICT, witnessed by the one-block
                    partition {Q_d}, whose block is a subcube of dimension d.
                    So the ratio the source asks about is a ratio of two
                    different, positive quantities.

    The source records proved cases for Conjecture 1.8 (stars, subdivided stars,
    P_t for t <= 5) but those are research theorems about eta-boundedness, not
    instances checkable from the definitions, so no settled case is grounded for
    the eta rows. *)

From GTBase Require Import base.
From Packing.conjectures Require Import U9 X226.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ============================================================================
    The parameter eta.
    ========================================================================== *)

(** Every graph with a vertex has a hitting set: all its vertices form one,
    because a maximum stable set of a nonempty graph is nonempty. *)
Lemma x226_hitting_setT (G : sgraph) : 0 < #|G| -> x226_hitting_set (setT : {set G}).
Proof.
move=> G0; apply/forallP => S; apply/implyP => SM.
by rewrite setIT -card_gt0 (card_maxstabset SM) lt0n alpha_eq0 -card_gt0 cardsT.
Qed.

(** Hence eta(G) <= |V(G)| whenever G has a vertex. *)
Lemma x226_eta_le_card (G : sgraph) : 0 < #|G| -> x226_eta_le G #|G|.
Proof. by move=> G0; exists setT; split; [exact: x226_hitting_setT|rewrite cardsT]. Qed.

(** [x226_eta_le] is monotone in the bound. *)
Lemma x226_eta_le_leq (G : sgraph) (b c : nat) :
  b <= c -> x226_eta_le G b -> x226_eta_le G c.
Proof. by move=> bc [X [hX cX]]; exists X; split => //; exact: leq_trans cX bc. Qed.

(** Concrete value: eta(K_1) <= 1. *)
Lemma x226_eta_le_K1 : x226_eta_le 'K_1 1.
Proof.
have c1 : #|'K_1| = 1 by rewrite card_ord.
by have := x226_eta_le_card (G := 'K_1); rewrite c1; apply.
Qed.

(** Teeth: NO graph satisfies eta(G) <= 0 — every graph has a maximum stable
    set, and the empty set meets none. *)
Lemma x226_not_eta_le0 (G : sgraph) : ~ x226_eta_le G 0.
Proof.
case=> X [/forallP hX]; rewrite leqn0 cards_eq0 => /eqP X0.
case: (alphaP [set: G]) => S SM.
by move: (hX S); rewrite SM implyTb X0 setI0 eqxx.
Qed.

(** Teeth for the [0 < #|G|] guard: a graph with no vertex has NO hitting set
    at all (its unique maximum stable set is empty), so without that guard the
    three eta-statements would be false for a reason unrelated to eta. *)
Lemma x226_no_eta_bound_empty (G : sgraph) (b : nat) :
  #|G| = 0 -> ~ x226_eta_le G b.
Proof.
move=> G0 [X [/forallP hX _]].
have T0 : [set: G] = set0 by apply/eqP; rewrite -cards_eq0 cardsT G0.
have S0 : (set0 : {set G}) \in maxstabsets [set: G].
  by rewrite inE in_stabsets sub0set stable0 /= cards0 T0 alpha0.
by move: (hX set0); rewrite S0 implyTb set0I eqxx.
Qed.

(** Non-vacuity of the CONCLUSION: [x226_eta_bounded] is satisfiable — any class
    of graphs of bounded order is eta-bounded. *)
Lemma x226_eta_bounded_card_le (n : nat) :
  x226_eta_bounded (fun G : sgraph => #|G| <= n).
Proof.
exists (fun _ => n) => G Cn G0; apply: x226_eta_le_leq Cn _.
exact: x226_eta_le_card.
Qed.

(** ============================================================================
    The guards of the three eta rows.
    ========================================================================== *)

(** The forest hypothesis of Conjecture 1.8 is satisfiable ... *)
Lemma x226_forest_witness : exists H : sgraph, is_forest [set: H].
Proof. by exists sunit; exact: unit_forest. Qed.

(** ... and it excludes graphs: K_3 is not a forest. *)
Lemma x226_not_forest_K3 : ~ is_forest [set: 'K_3].
Proof.
move=> F; have c3 : 3 <= #|'K_3| by rewrite card_ord.
have [x [y [xy nxy]]] := forest3 F c3.
by move: nxy; rewrite /edge_rel /= xy.
Qed.

(** The P_t-free class contains a graph with a vertex (t >= 2). *)
Lemma x226_path_free_K1 (t : nat) : 1 < t -> induced_free 'K_1 (x226_path_graph t).
Proof. by move=> t1; apply: induced_free_card; rewrite !card_ord. Qed.

(** The (S_a u S_b)-free class contains a graph with a vertex. *)
Lemma x226_two_stars_free_K1 (a b : nat) :
  induced_free 'K_1 (sjoin (x226_star a) (x226_star b)).
Proof.
apply: induced_free_card; rewrite card_ord card_sum !card_ord.
by rewrite addnS ltnS addSn.
Qed.

(** ============================================================================
    Subcube partitions of Q_d.
    ========================================================================== *)

Lemma x226_is_subcube_dim_leW (d k : nat) (S : {set hypercube d}) :
  @x226_is_subcube_dim_le d k S -> x226_is_subcube S.
Proof. by case/existsP => c /andP[h _]; apply/existsP; exists c. Qed.

Lemma x226_subcube_partitions_dim_leS (d k : nat) :
  x226_subcube_partitions_dim_le d k \subset x226_subcube_partitions d.
Proof. by apply/subsetP => P; rewrite inE => /andP[]. Qed.

(** Consistency: restricting the dimension can only lose partitions. *)
Lemma x226_f_dim_le2_leq (d : nat) : x226_f_dim_le2 d <= x226_f d.
Proof. exact: subset_leq_card (x226_subcube_partitions_dim_leS d 2). Qed.

Section Singletons.
Variable d : nat.

(** The partition of Q_d into single vertices: all blocks are 0-dimensional
    subcubes. *)
Definition x226_sing_part : {set {set hypercube d}} :=
  [set [set x] | x in [set: hypercube d]].

Lemma x226_sing_partition : partition x226_sing_part [set: hypercube d].
Proof.
apply/and3P; split.
- apply/eqP/setP => y; rewrite inE; apply/bigcupP; exists [set y]; last by rewrite inE.
  by apply/imsetP; exists y; rewrite ?inE.
- apply/trivIsetP => A B /imsetP[x _ ->] /imsetP[y _ ->] neq.
  by rewrite disjoints1 inE; apply: contra neq => /eqP ->.
- by apply/negP => /imsetP[x _ /setP/(_ x)]; rewrite !inE eqxx.
Qed.

Lemma x226_sing_blocks :
  [forall S in x226_sing_part, @x226_is_subcube_dim_le d 0 S].
Proof.
apply/forall_inP => S /imsetP[x _ ->]; apply/existsP.
exists [ffun i => Some (tnth x i)]; apply/andP; split.
- rewrite /x226_subcube; apply/eqP; apply/setP => y; rewrite !inE.
  apply/idP/idP => [/eqP ->|/forallP h].
    by apply/forallP => i; rewrite ffunE /= eqxx.
  by apply/eqP; apply: eq_from_tnth => i; apply/eqP; move: (h i); rewrite ffunE /=.
- rewrite /x226_subcube_dim.
  have -> : [set i : 'I_d | [ffun i0 => Some (tnth x i0)] i == None] = set0.
    by apply/setP => i; rewrite !inE ffunE.
  by rewrite cards0.
Qed.

End Singletons.

Lemma x226_f_dim_le2_gt0 (d : nat) : 0 < x226_f_dim_le2 d.
Proof.
apply/card_gt0P; exists (x226_sing_part d); rewrite !inE.
have blocks := x226_sing_blocks d.
rewrite x226_sing_partition /=.
have -> : [forall S in x226_sing_part d, @x226_is_subcube d S].
  apply/forall_inP => S SP; apply: x226_is_subcube_dim_leW.
  exact: (forall_inP blocks).
rewrite /=; apply/forall_inP => S SP.
case/existsP: (forall_inP blocks S SP) => c /andP[hc hd].
by apply/existsP; exists c; rewrite hc (leq_trans hd).
Qed.

Lemma x226_f_gt0 (d : nat) : 0 < x226_f d.
Proof. exact: leq_trans (x226_f_dim_le2_gt0 d) (x226_f_dim_le2_leq d). Qed.

Section TrivialPartition.
Variable d : nat.

Lemma x226_card_hypercube_gt0 : 0 < #|hypercube d|.
Proof. by rewrite card_tuple card_bool expn_gt0. Qed.

Lemma x226_triv_partition :
  partition [set [set: hypercube d]] [set: hypercube d].
Proof.
apply/and3P; split.
- by rewrite /cover big_set1.
- by apply/trivIsetP => A B /set1P -> /set1P ->; rewrite eqxx.
- apply/negP => /set1P /setP /(_ (enum_val (Ordinal x226_card_hypercube_gt0))).
  by rewrite !inE.
Qed.

Lemma x226_subcube_setT : @x226_is_subcube d [set: hypercube d].
Proof.
apply/existsP; exists [ffun _ => None]; apply/eqP; apply/setP => y.
by rewrite !inE; apply/esym/forallP => i; rewrite ffunE.
Qed.

(** From d = 3 on, Q_d itself is a subcube that the dimension-<=2 restriction
    rejects. *)
Lemma x226_not_subcube_dim_le2_setT :
  3 <= d -> ~~ @x226_is_subcube_dim_le d 2 [set: hypercube d].
Proof.
move=> d3; apply/negP => /existsP[c /andP[/eqP cT cdim]].
have [i ci] : exists i : 'I_d, c i != None.
  apply/existsP; apply: contraT; rewrite negb_exists => /forallP h.
  have hE : [set i : 'I_d | c i == None] = setT.
    by apply/setP => j; rewrite !inE; move: (h j); rewrite negbK.
  move: cdim; rewrite /x226_subcube_dim hE cardsT card_ord => dle2.
  by move: (leq_trans d3 dle2).
case cE : (c i) => [b|]; last by rewrite cE eqxx in ci.
have nb : forall z : bool, (~~ z == z) = false by case.
have : ([tuple (if j == i then ~~ b else true) | j < d] : hypercube d)
         \in x226_subcube c by rewrite -cT inE.
by rewrite inE => /forallP /(_ i); rewrite cE /= tnth_mktuple eqxx nb.
Qed.

End TrivialPartition.

(** Teeth: the dimension-<=2 restriction is STRICT from d = 3 on. *)
Lemma x226_f_dim_le2_lt (d : nat) : 3 <= d -> x226_f_dim_le2 d < x226_f d.
Proof.
move=> d3; apply: proper_card; rewrite properE.
apply/andP; split; first exact: x226_subcube_partitions_dim_leS.
apply/subsetPn; exists [set [set: hypercube d]].
- rewrite inE x226_triv_partition /=.
  by apply/forall_inP => S /set1P ->; exact: x226_subcube_setT.
- rewrite inE negb_and; apply/orP; right.
  rewrite negb_forall; apply/existsP; exists [set: hypercube d].
  by rewrite negb_imply inE eqxx /= x226_not_subcube_dim_le2_setT.
Qed.

(** ============================================================================
    Axiom audit.
    ========================================================================== *)

Print Assumptions x226_eta_le_K1.
Print Assumptions x226_not_eta_le0.
Print Assumptions x226_no_eta_bound_empty.
Print Assumptions x226_eta_bounded_card_le.
Print Assumptions x226_not_forest_K3.
Print Assumptions x226_path_free_K1.
Print Assumptions x226_two_stars_free_K1.
Print Assumptions x226_f_gt0.
Print Assumptions x226_f_dim_le2_lt.
