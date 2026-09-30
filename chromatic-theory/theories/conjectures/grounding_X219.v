(** * Chromatic.conjectures.grounding_X219 -- grounding lemmas for wave X219.

    Qed-closed, axiom-free sanity results for the primitives of [X219.v] and for
    the hypothesis blocks of its seven statements: a SATISFIABLE witness for
    every guard, a GUARD-HAS-TEETH lemma for every notion that could collapse,
    and the two settled instances the sources record ([K_2] is 1-edge-choosable,
    the 7/8 bound of X32.v implies the 5/6 bound of this wave). *)

From GraphTheory Require Import bij.
From GTBase Require Import base.
From Chromatic.conjectures Require Import X32 X219 grounding_X213.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Small-graph helpers ************************************************)

Lemma x219_induced0_empty (G : sgraph) (x : induced (@set0 G)) : False.
Proof. by move: (valP x); rewrite inE. Qed.

Lemma x219_card_induced0 (G : sgraph) : #|induced (@set0 G)| = 0.
Proof. by apply: eq_card0 => x; case: (x219_induced0_empty x). Qed.

Lemma x219_chi_K1 : χ([set: 'K_1]) = 1.
Proof.
have cl : clique [set: 'K_1] by move=> x y _ _ xy.
by rewrite (chi_clique cl) cardsT card_ord.
Qed.

Lemma x219_K1_del_vertex (v : 'K_1) : [set: 'K_1] :\ v = set0.
Proof. by apply/setP => u; rewrite !inE (ord1 u) (ord1 v) eqxx. Qed.

Lemma x219_no_three_distinct_I2 (u v w : 'I_2) :
  u != v -> u != w -> v != w -> False.
Proof. exact: x213_no_three_distinct_I2. Qed.

(** ** [x219_subgraph_critical_for] ***************************************)

(** Structural law: a critical graph fails the property. *)
Lemma x219_critical_failsP (P : sgraph -> Prop) (G : sgraph) :
  x219_subgraph_critical_for P G -> ~ P G.
Proof. by case. Qed.

(** Guard has teeth: a graph that HAS the property is never critical for it, so
    criticality is not a vacuous wrapper. *)
Lemma x219_not_critical_of (P : sgraph -> Prop) (G : sgraph) :
  P G -> ~ x219_subgraph_critical_for P G.
Proof. by move=> HP [H _ _]. Qed.

(** Non-vacuity: the one-vertex graph is critical for "chromatic number at most
    zero" (it is 1-chromatic, and deleting its only vertex leaves the empty
    graph, whose chromatic number is 0). *)
Lemma x219_critical_chi0_K1 :
  x219_subgraph_critical_for (fun H : sgraph => χ([set: H]) <= 0) 'K_1.
Proof.
split.
- by rewrite x219_chi_K1.
- move=> v; rewrite x219_K1_del_vertex.
  by apply: leq_trans (leq_chi _) _; rewrite cardsT x219_card_induced0.
- by move=> u v; rewrite /edge_rel /= (ord1 u) (ord1 v) eqxx.
Qed.

(** ** [x219_bipartition] ************************************************)

(** Non-vacuity: the left side of a complete bipartite graph is a bipartition. *)
Lemma x219_bipartition_KB n m :
  x219_bipartition [set x : KB n m | is_inl x].
Proof.
by move=> [a|a] [b|b]; rewrite /edge_rel /= !inE.
Qed.

(** Guard has teeth: the triangle admits NO bipartition. *)
Lemma x219_not_bipartition_K3 (A : {set 'K_3}) : ~ x219_bipartition A.
Proof.
move=> H.
pose a : 'K_3 := @Ordinal 3 0 isT.
pose b : 'K_3 := @Ordinal 3 1 isT.
pose c : 'K_3 := @Ordinal 3 2 isT.
move: (H a b isT) (H a c isT) (H b c isT).
by case: (a \in A); case: (b \in A); case: (c \in A).
Qed.

(** ** [x219_max_degree_on] **********************************************)

(** Non-vacuity: the number of vertices always bounds the degrees. *)
Lemma x219_max_degree_on_card (G : sgraph) (A : {set G}) :
  x219_max_degree_on A #|G|.
Proof. by move=> v _; apply: max_card. Qed.

(** Structural law: the bound is monotone. *)
Lemma x219_max_degree_onW (G : sgraph) (A : {set G}) (D D' : nat) :
  D <= D' -> x219_max_degree_on A D -> x219_max_degree_on A D'.
Proof. by move=> le H v vA; apply: leq_trans (H v vA) le. Qed.

(** Guard has teeth: [K_2] has a vertex of degree one, so the bound 0 fails. *)
Lemma x219_not_max_degree_on_K2_0 : ~ x219_max_degree_on [set: 'K_2] 0.
Proof.
move=> H; move: (H ord0 (in_setT _)); rewrite leqn0 cards_eq0 => /eqP/setP/(_ (@Ordinal 2 1 isT)).
by rewrite !inE.
Qed.

(** ** [x219_kAkB_choosable] *********************************************)

(** Non-vacuity: the one-vertex graph is (1,1)-choosable. *)
Lemma x219_kAkB_choosable_K1 : x219_kAkB_choosable [set: 'K_1] 1 1.
Proof.
move=> C L HA _.
have /set0Pn [c cL] : L ord0 != set0.
  by rewrite -card_gt0; exact: HA _ (in_setT _).
exists (fun _ => c); split.
- by move=> v; rewrite (ord1 v).
- by move=> x y; rewrite /edge_rel /= (ord1 x) (ord1 y) eqxx.
Qed.

(** Guard has teeth: with list sizes at least ZERO the empty palette defeats
    every graph with a vertex, so the list-size parameters really bite. *)
Lemma x219_not_kAkB_choosable_K1_zero :
  ~ x219_kAkB_choosable (G := 'K_1) [set: 'K_1] 0 0.
Proof.
move=> H.
have [f _] := H 'I_0 (fun _ => set0) (fun v _ => leq0n _) (fun v _ => leq0n _).
by case: (f ord0) => k; rewrite ltn0.
Qed.

(** ** [x219_edge_choosable] *********************************************)

(** Settled instance of the list-chromatic-index row at n = 2: [K_2] is
    1-edge-choosable (its single edge takes any colour of its own list). *)
Lemma x219_edge_choosable_K2 : x219_edge_choosable 'K_2 1.
Proof.
move=> C L Lsym Lcard.
pose u0 : 'K_2 := ord0.
pose u1 : 'K_2 := @Ordinal 2 1 isT.
have /set0Pn [c0 c0L] : L u0 u1 != set0.
  by rewrite -card_gt0; apply: Lcard.
exists (fun u v => odflt c0 [pick x in L u v]); split.
- by move=> u v; rewrite Lsym.
- move=> u v uv; case: pickP => [x xin|hno] //=.
  have /set0Pn [x xin] : L u v != set0 by rewrite -card_gt0; apply: Lcard.
  by rewrite hno in xin.
- by move=> u v w uv uw vw; case: (x219_no_three_distinct_I2 uv uw vw).
Qed.

(** Guard has teeth: a graph with an edge is not 1-edge-choosable over an
    EMPTY list, i.e. the list-size guard is load bearing. *)
Lemma x219_edge_choosable_needs_lists :
  ~ (forall (C : finType) (L : 'K_2 -> 'K_2 -> {set C}),
        (forall u v : ('K_2), L u v = L v u) ->
        exists col : ('K_2) -> ('K_2) -> C,
          forall u v : ('K_2), u -- v -> col u v \in L u v).
Proof.
move=> H; have [col Hcol] := H 'I_0 (fun _ _ => set0) (fun _ _ => erefl).
by case: (col ord0 ord0) => k; rewrite ltn0.
Qed.

(** ** [x219_frac_vertex_arboricity_le_two] ******************************)

(** Non-vacuity: the one-vertex graph has fractional vertex-arboricity at most
    two (it is itself an induced forest, used with full multiplicity), witnessed
    at the fold parameter b = 1. *)
Lemma x219_frac_va_sunit : x219_frac_vertex_arboricity_le_two sunit.
Proof.
exists 1; split => //; exists (fun _ => [set: sunit]); split.
- by move=> i; exact: unit_forest.
- move=> v; have -> : [set i : 'I_(2 * 1) | v \in [set: sunit]] = [set: 'I_(2 * 1)].
    by apply/setP => i; rewrite !inE.
  by rewrite cardsT card_ord.
Qed.

(** Structural law: the b-fold covering really covers -- every vertex lies in at
    least one of the 2b induced forests, because the fold parameter is positive. *)
Lemma x219_frac_va_covers (G : sgraph) :
  x219_frac_vertex_arboricity_le_two G ->
  exists (b : nat) (F : 'I_(2 * b) -> {set G}),
    [/\ 0 < b, forall i : 'I_(2 * b), is_forest (F i) &
        forall v : G, exists i, v \in F i].
Proof.
move=> [b [bpos [F [Hf Hc]]]]; exists b, F; split => // v.
have : 0 < #|[set i : 'I_(2 * b) | v \in F i]| by apply: leq_trans (Hc v).
by rewrite card_gt0 => /set0Pn [i]; rewrite inE => ?; exists i.
Qed.

(** GUARD HAS TEETH (added 2026-09-23 with the existential repair of the fold
    parameter): the [0 < b] guard is load bearing.  At b = 0 the covering
    conditions are empty -- there is no index and every vertex is covered zero
    times -- so WITHOUT the guard the existential form would be satisfied by
    every graph whatsoever, planar or not. *)
Lemma x219_frac_va_b0_vacuous (G : sgraph) :
  exists F : 'I_(2 * 0) -> {set G},
    (forall i : 'I_(2 * 0), is_forest (F i)) /\
    (forall v : G, 0 <= #|[set i : 'I_(2 * 0) | v \in F i]|).
Proof. by exists (fun _ => set0); split => // i; case: i => m; rewrite ltn0. Qed.

(** ** Hypothesis blocks of the statements ********************************)

(** The repaired torus guard -- [surface_embeddable 1] (ORIENTABLE genus at most
    one) together with [connected [set: G]] -- is satisfiable; witness
    re-exported from wave X213. *)
Lemma x219_toroidal_guard_K1 :
  surface_embeddable 1 'K_1 /\ connected [set: 'K_1].
Proof. exact: x213_toroidal_guard_K1. Qed.

(** GUARD HAS TEETH (the connectivity half, added 2026-09-23): a disconnected
    graph passes GTBase's whole-graph Euler count and is excluded by the guard.
    This is precisely the padding that refuted the unguarded body of
    arxiv:2407.18800#01 (a graph of genus g padded with g disjoint copies of K_2
    has computed genus zero). *)
Lemma x219_toroidal_connected_guard_has_teeth :
  exists G : sgraph, surface_embeddable 1 G /\ ~ connected [set: G].
Proof. exact: x213_connected_guard_has_teeth. Qed.

(** GUARD HAS TEETH (the maximum-degree threshold of conditions (ii) and (iii)
    of arxiv:2004.07457#01, added 2026-09-23).  WITHOUT the [D0 <= DA],
    [D0 <= DB] guards, condition (ii) is FALSE: at DA = DB = 1 the two
    hypotheses read [C * trunc_log 2 1 <= kA] and [C * trunc_log 2 1 <= kB],
    i.e. [0 <= kA] and [0 <= kB], for every C, so the condition would claim that
    every bipartite graph of maximum degree one is (1,1)-choosable -- and a
    single edge whose two ends carry the same one-element list is not.  This is
    the refutation the second reader committed as
    meta/probe_hints/asymmetric_bipartite_list_colouring_statement.v, kept here
    against the UNGUARDED condition so that it stays machine-checked after the
    repair. *)
Lemma x219_asym_needs_degree_guard :
  ~ (exists C : nat, 1 < C /\
       forall (G : sgraph) (A : {set G}) (DA DB kA kB : nat),
         x219_bipartition A ->
         x219_max_degree_on A DA ->
         x219_max_degree_on (~: A) DB ->
         0 < kA -> 0 < kB ->
         C * trunc_log 2 DB <= kA -> C * trunc_log 2 DA <= kB ->
         x219_kAkB_choosable A kA kB).
Proof.
case=> C [_ Hii].
(* [complete 2], not ['K_2]: in a binder followed by a comma the ['K_n]
   notation is swallowed by the complete-bipartite notation ['K_n , m]. *)
have deg : forall x : complete 2, #|N(x)| <= 1.
  move=> x; have -> : N(x) = [set~ x].
    by apply/setP => y; rewrite !inE /edge_rel /= eq_sym.
  by rewrite cardsC1 card_ord.
have bip : x219_bipartition [set (ord0 : complete 2)].
  move=> u v; rewrite /edge_rel /= !inE.
  by case: u => -[|[|u]] hu //=; case: v => -[|[|v]] hv //=.
have H := Hii (complete 2) [set (ord0 : complete 2)] 1 1 1 1 bip
            (fun v _ => deg v) (fun v _ => deg v) isT isT.
have tl : C * trunc_log 2 1 <= 1 by rewrite muln0.
have cu : 1 <= #|[set: unit]| by apply/card_gt0P; exists tt; rewrite inE.
have [f [fL fP]] := H tl tl unit (fun _ => [set: unit])
                      (fun v _ => cu) (fun v _ => cu).
have adj : (ord0 : complete 2) -- (Ordinal (isT : 1 < 2)) by rewrite /edge_rel /=.
by move: (fP _ _ adj); case: (f ord0); case: (f (Ordinal (isT : 1 < 2))).
Qed.

(** The planar and triangle-free guards are satisfiable. *)
Lemma x219_wagner_planar_K1 : wagner_planar 'K_1.
Proof.
split=> m; move: (minor_card m); first by rewrite !card_ord.
by rewrite card_sum !card_ord.
Qed.

Lemma x219_triangle_free_K1 : triangle_free 'K_1.
Proof. by move=> x y z; rewrite /edge_rel /= (ord1 x) (ord1 y) eqxx. Qed.

(** Settled comparison recorded by the source of arxiv:1709.04036#01: an
    induced 2-degenerate subgraph on at least seven eighths of the vertices is
    in particular one on at least five sixths. *)
Lemma x219_seven_eighths_implies_five_sixths (s n : nat) :
  8 * s >= 7 * n -> 6 * s >= 5 * n.
Proof.
move=> le.
have h1 : 6 * (7 * n) <= 6 * (8 * s) by rewrite leq_mul2l le orbT.
have h2 : 8 * (5 * n) <= 6 * (7 * n).
  by rewrite !mulnA leq_mul2r; apply/orP; right.
have h3 : 6 * (8 * s) = 8 * (6 * s) by rewrite !mulnA (mulnC 6 8).
have h4 : 8 * (5 * n) <= 8 * (6 * s).
  by rewrite -h3; apply: leq_trans h1.
by rewrite -(@leq_pmul2l 8).
Qed.

Print Assumptions toroidal_five_choosability_critical_iff_six_critical_statement.
Print Assumptions toroidal_five_choosable_iff_five_colourable_statement.
Print Assumptions toroidal_edge_width_four_five_choosable_statement.
Print Assumptions asymmetric_bipartite_list_colouring_statement.
Print Assumptions list_chromatic_index_even_clique_statement.
Print Assumptions planar_fractional_vertex_arboricity_two_statement.
Print Assumptions triangle_free_planar_five_sixths_two_degenerate_statement.
Print Assumptions x219_critical_chi0_K1.
Print Assumptions x219_edge_choosable_K2.
Print Assumptions x219_frac_va_sunit.
Print Assumptions x219_frac_va_b0_vacuous.
Print Assumptions x219_toroidal_guard_K1.
Print Assumptions x219_toroidal_connected_guard_has_teeth.
Print Assumptions x219_asym_needs_degree_guard.
Print Assumptions x219_seven_eighths_implies_five_sixths.
