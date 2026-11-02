(** * Frozen monochromatic subsets and complete reaching statements (C8)
    Original source: 47eed16, before C8. Every frozen body below preserves
    the original binders, guards and witnesses; only the recorded family
    references are redirected to other frozen bodies. Existing source
    discrepancies and partial/blocked statuses are not repaired. *)
From GTBase Require Import base monochromatic.
From GTBase.migration Require monochromatic.
From Chromatic.conjectures Require Import X181 X194 X218.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module BaseLegacy := GTBase.migration.monochromatic.Legacy.

Module X181Legacy.

Definition x181_monochromatic
    (G : sgraph) (k : nat) (col : G -> 'I_k) (S : {set G}) : bool :=
  [forall x in S, [forall y in S, col x == col y]].

Definition x181_clique_colourable (G : sgraph) (k : nat) : bool :=
  [exists col : {ffun G -> 'I_k},
    [forall S : {set G},
      x181_maximal_clique S ==> ~~ X181Legacy.x181_monochromatic (fun v => col v) S]].

Definition x181_clique_chromatic_window
    (a b n : nat) (E : {set {set 'I_n}}) : bool :=
  let G := fg_labelled_sgraph E in
  [exists k : 'I_n.+1,
    [&& X181Legacy.x181_clique_colourable G k,
        (b - a) * (trunc_log 2 n) <= b * (2 * k)
      & b * (2 * k) <= (b + a) * (trunc_log 2 n).+1]].

Definition x181_random_graph_clique_chromatic_constant : Prop :=
  forall a b : nat, 0 < a -> a <= b ->
    @fg_whp (fun n : nat => {set {set 'I_n}})
      (fun n => @fg_gnp_weight 1 2 n)
      (X181Legacy.x181_clique_chromatic_window a b).

Definition random_graph_clique_chromatic_tight_constant_statement : Prop :=
  X181Legacy.x181_random_graph_clique_chromatic_constant.

End X181Legacy.

Module X194Legacy.

Definition x194_clustered_chromatic_minor_class_le (H : sgraph) (k : nat) : Prop :=
  exists c : nat,
    forall G : sgraph, ~ minor G H -> BaseLegacy.clustered_colouring G k c.

Definition clustered_chromatic_minor_class_treedepth_bound_statement : Prop :=
  forall H : sgraph,
    forall k : nat,
      2 <= k ->
      x194_treedepth_at_most H k ->
      X194Legacy.x194_clustered_chromatic_minor_class_le H (2 * k - 2).

End X194Legacy.

Module X218Legacy.

Definition x218_clustered_chromatic_class_le (F : sgraph -> Prop) (k : nat) : Prop :=
  exists c : nat, forall G : sgraph, F G -> BaseLegacy.clustered_colouring G k c.

Definition odd_minor_free_defective_clustered_treedepth_statement : Prop :=
  forall (H : sgraph) (k : nat),
    1 <= k ->
    x218_connected_treedepth_at_most H k ->
    ~ x218_connected_treedepth_at_most H k.-1 ->
    x218_defective_chromatic_class_le (fun G : sgraph => ~ x218_odd_minor G H) (k - 1) /\
    X218Legacy.x218_clustered_chromatic_class_le (fun G : sgraph => ~ x218_odd_minor G H) (k - 1).

End X218Legacy.

Lemma x181_monochromatic_compat (G : sgraph) k (col : G -> 'I_k) (S : {set G}) :
  X181Legacy.x181_monochromatic col S = x181_monochromatic col S.
Proof. by rewrite /X181Legacy.x181_monochromatic /x181_monochromatic monochromatic_onE. Qed.

Lemma x181_clique_colourable_compat (G : sgraph) k :
  X181Legacy.x181_clique_colourable G k = x181_clique_colourable G k.
Proof.
rewrite /X181Legacy.x181_clique_colourable /x181_clique_colourable.
apply: eq_existsb => col; apply: eq_forallb => S.
by rewrite x181_monochromatic_compat.
Qed.

Lemma x181_clique_chromatic_window_compat a b n E :
  @X181Legacy.x181_clique_chromatic_window a b n E = @x181_clique_chromatic_window a b n E.
Proof.
rewrite /X181Legacy.x181_clique_chromatic_window /x181_clique_chromatic_window.
by apply: eq_existsb => k; rewrite x181_clique_colourable_compat.
Qed.

Lemma x181_event_weight_compat a b n :
  fg_event_weight (@fg_gnp_weight 1 2 n) (@X181Legacy.x181_clique_chromatic_window a b n) =
  fg_event_weight (@fg_gnp_weight 1 2 n) (@x181_clique_chromatic_window a b n).
Proof.
by apply: eq_bigl => E; exact: x181_clique_chromatic_window_compat.
Qed.

Lemma x181_random_graph_clique_chromatic_constant_compat :
  X181Legacy.x181_random_graph_clique_chromatic_constant <->
  x181_random_graph_clique_chromatic_constant.
Proof.
rewrite /X181Legacy.x181_random_graph_clique_chromatic_constant
  /x181_random_graph_clique_chromatic_constant /fg_whp /eventually.
split=> h a b a0 ab c d c0 cd; have [N hn] := h a b a0 ab c d c0 cd; exists N => n Nn.
- by move: (hn n Nn); rewrite x181_event_weight_compat.
- by move: (hn n Nn); rewrite x181_event_weight_compat.
Qed.

Lemma random_graph_clique_chromatic_tight_constant_statement_compat :
  X181Legacy.random_graph_clique_chromatic_tight_constant_statement <->
  random_graph_clique_chromatic_tight_constant_statement.
Proof. exact: x181_random_graph_clique_chromatic_constant_compat. Qed.

Lemma x194_clustered_chromatic_minor_class_le_compat (H : sgraph) k :
  X194Legacy.x194_clustered_chromatic_minor_class_le H k <->
  x194_clustered_chromatic_minor_class_le H k.
Proof.
split=> -[c hc]; exists c => G minor_free; have hg := hc G minor_free.
all: by apply/GTBase.migration.monochromatic.clustered_colouring_compat.
Qed.

(** ** X194 re-encoding: the weakening, kernel-checked *)

(* a walk of H inside S lifts to the induced subgraph on S *)
Lemma x194_lift (H : sgraph) (S : {set H}) (p : seq H) (x : H) (hx : x \in S) :
  all (fun v => v \in S) p -> path (--) x p ->
  exists p' : seq (induced S), map val p' = p /\ path (--) (Sub x hx : induced S) p'.
Proof.
elim: p x hx => [|y q IH] x hx /=; first by exists [::].
case/andP=> hy aq /andP [xy pq].
have [q' [mq pq']] := IH y hy aq pq.
by exists (Sub y hy :: q'); rewrite /= mq; split => //; apply/andP; split.
Qed.

(* td <= ctd: rank r at the top, the other vertices by the ranking of H - r *)
Lemma x194_td_of_ctd (H : sgraph) (k : nat) : x194_ctd_at_most H k -> x194_treedepth_at_most H k.
Proof.
case=> k0 [r [rank0 rk0]].
move: rank0 rk0; case: k k0 => [//|k] _ rank0 rk0 /=.
pose S := ~: [set r].
pose rank' (v : H) : 'I_k.+1 :=
  oapp (fun v' : induced S => widen_ord (leqnSn k) (rank0 v')) ord_max (insub v : option (induced S)).
have rr : rank' r = ord_max by rewrite /rank' insubF // !inE eqxx.
have rv (v : H) (hv : v \in S) : rank' v = widen_ord (leqnSn k) (rank0 (Sub v hv)).
  by rewrite /rank' (insubT (mem S) hv).
have lt (v : H) (hv : v \in S) : rank' v < k by rewrite (rv v hv) /=; exact: ltn_ord.
exists rank' => x y p xy pth lst e.
case: (eqVneq x r) => [xr|xr].
  have yS : y \in S.
    by rewrite !inE; apply: contra_neq xy => ->; rewrite xr.
  by move: (lt y yS); rewrite -e xr rr /= ltnn.
have xS : x \in S by rewrite !inE.
case: (eqVneq y r) => [yr|yr].
  by move: (lt x xS); rewrite e yr rr /= ltnn.
have yS : y \in S by rewrite !inE.
case rp: (r \in p).
  by exists r; split => //; rewrite rr /=; exact: lt x xS.
have ap : all (fun v => v \in S) p.
  by apply/allP => v vp; rewrite !inE; apply: contraFneq rp => <-.
have [p' [mp pp']] := x194_lift xS ap pth.
have lst' : last (Sub x xS : induced S) p' = Sub y yS.
  by apply: val_inj; rewrite /= -(last_map val) mp lst.
have xy' : (Sub x xS : induced S) != Sub y yS by apply: contra_neq xy => /(congr1 val).
have e' : rank0 (Sub x xS) = rank0 (Sub y yS).
  by apply: val_inj; move: (congr1 val e); rewrite (rv x xS) (rv y yS).
have [z' [zp ltz]] := rk0 _ _ _ xy' pp' lst' e'.
have zS : val z' \in S := valP z'.
exists (val z'); split; first by rewrite -mp; exact: map_f.
rewrite (rv x xS) (rv _ zS) /=.
by have -> : (Sub (val z') zS : induced S) = z' by apply: val_inj.
Qed.

(* ctd(H) <= 1: H has exactly one vertex, so every graph with a vertex has H as a minor *)
Lemma x194_ctd1_minor (H G : sgraph) (v : G) : x194_ctd_at_most H 1 -> minor G H.
Proof.
case=> _ [r [rank0 _]].
have one (y : H) : y = r.
  apply/eqP; apply: contraT => yr.
  have hy : y \in ~: [set r] by rewrite !inE.
  by case: (rank0 (Sub y hy)).
exists (fun x => if x == v then Some r else None); split.
- by move=> y; exists v; rewrite eqxx (one y).
- move=> y.
  have -> : (fun x => if x == v then Some r else None) @^-1: pred1 (Some y) = [set v].
    by apply/setP => x; rewrite !inE; case: (x == v) => /=; rewrite (one y) ?eqxx.
  exact: connected1.
- by move=> x y; rewrite (one x) (one y) sg_irrefl.
Qed.

Lemma x194_class_ctd1 (H : sgraph) : x194_ctd_at_most H 1 -> x194_clustered_chromatic_minor_class_le H 0.
Proof.
move=> hc; exists 0 => G noH.
have F (v : G) : False by exact: noH (x194_ctd1_minor v hc).
exists (fun v => False_rect _ (F v)) => S _ _.
by rewrite leqn0 cards_eq0; apply/eqP/setP => v; case: (F v).
Qed.

(** X194 RE-ENCODING (2026-11-02, PROGRAMME section 3, A2 with the direction weaken; record
    meta/STATEMENT_IMPROVEMENTS.md), not a migration equivalence: the live row uses the source's connected tree-depth
    (arXiv:1708.02370v2, l.147, l.184) for every H, the frozen row ordinary tree-depth with the guard 2 <= k.  The
    frozen row implies the live one: for k >= 2 through td <= ctd ([x194_td_of_ctd]), for k = 1 because the class is
    the graph with no vertex ([x194_class_ctd1]).  The type below is the repair's exact certificate
    (REPAIR_PROBES weaken: frozen -> live). *)
Lemma clustered_chromatic_minor_class_treedepth_bound_statement_compat :
  X194Legacy.clustered_chromatic_minor_class_treedepth_bound_statement ->
  clustered_chromatic_minor_class_treedepth_bound_statement.
Proof.
move=> L H k hc.
move: (hc) => [k0 _].
case: k k0 hc => [//|[|k]] _ hc.
- exact: x194_class_ctd1.
- apply/x194_clustered_chromatic_minor_class_le_compat.
  exact: L H k.+2 isT (x194_td_of_ctd hc).
Qed.

(** ** X194 re-encoding: the two parameters differ, kernel-checked (2K_2) *)

(* 2K_2 on 'I_4: two disjoint edges, {0, 1} and {2, 3} (the vertices sharing val / 2) *)
Definition x194_2K2_rel (x y : 'I_4) : bool := (x != y) && (val x %/ 2 == val y %/ 2).
Lemma x194_2K2_sym : symmetric x194_2K2_rel.
Proof. by move=> x y; rewrite /x194_2K2_rel eq_sym [val y %/ 2 == _]eq_sym. Qed.
Lemma x194_2K2_irrefl : irreflexive x194_2K2_rel.
Proof. by move=> x; rewrite /x194_2K2_rel eqxx. Qed.
Definition x194_2K2 : sgraph := SGraph x194_2K2_sym x194_2K2_irrefl.

(* a walk stays in its edge *)
Lemma x194_2K2_walk (x : x194_2K2) (p : seq x194_2K2) :
  path (--) x p -> val (last x p) %/ 2 = val x %/ 2.
Proof.
elim: p x => [|y q IH] x //= /andP [xy pq].
rewrite IH //.
by case/andP: xy => _ /eqP ->.
Qed.

(* td(2K_2) <= 2: rank by parity *)
Lemma x194_td_2K2 : x194_treedepth_at_most x194_2K2 2.
Proof.
exists (fun v : x194_2K2 => Ordinal (ltn_pmod (val v) (isT : 0 < 2))) => x y p xy pth lst e.
exfalso; move: xy; apply/negP; rewrite negbK; apply/eqP/val_inj.
have d : val x %/ 2 = val y %/ 2 by rewrite -lst (x194_2K2_walk pth).
have m : val x %% 2 = val y %% 2 by move/(congr1 val): e.
by rewrite (divn_eq (val x) 2) (divn_eq (val y) 2) d m.
Qed.

Lemma x194_2K2_avoid (r : x194_2K2) : exists a b : x194_2K2, [/\ a != r, b != r & a -- b].
Proof.
case: r => [[|[|[|[|m]]]] pr].
- by exists (@Ordinal 4 2 isT), (@Ordinal 4 3 isT).
- by exists (@Ordinal 4 2 isT), (@Ordinal 4 3 isT).
- by exists (@Ordinal 4 0 isT), (@Ordinal 4 1 isT).
- by exists (@Ordinal 4 0 isT), (@Ordinal 4 1 isT).
- by [].
Qed.

(* not ctd(2K_2) <= 2: whichever vertex is removed, an edge survives, and one rank cannot rank an edge *)
Lemma x194_not_ctd_2K2_2 : ~ x194_ctd_at_most x194_2K2 2.
Proof.
case=> _ [r [rank rk]].
have [a [b [ar br ab]]] := x194_2K2_avoid r.
have ha : a \in ~: [set r] by rewrite !inE.
have hb : b \in ~: [set r] by rewrite !inE.
have ab' : (Sub a ha : induced (~: [set r])) != Sub b hb.
  by apply: contraTneq ab => /(congr1 val) /= ->; rewrite sg_irrefl.
have pth : path (--) (Sub a ha : induced (~: [set r])) [:: Sub b hb] by rewrite /= andbT.
have e : rank (Sub a ha) = rank (Sub b hb).
  by rewrite (ord1 (rank (Sub a ha))) (ord1 (rank (Sub b hb))).
have [z [_ lt]] := rk _ _ _ ab' pth erefl e.
by move: lt; rewrite (ord1 (rank z)) (ord1 (rank (Sub a ha))).
Qed.

(* ctd(2K_2) <= 3: remove vertex 0; the rest is ranked by parity *)
Lemma x194_ctd_2K2_3 : x194_ctd_at_most x194_2K2 3.
Proof.
split => //; exists (@Ordinal 4 0 isT).
exists (fun v : induced (~: [set (@Ordinal 4 0 isT : x194_2K2)]) =>
          Ordinal (ltn_pmod (val (val v)) (isT : 0 < 2))) => x y p xy pth lst e.
exfalso; move: xy; apply/negP; rewrite negbK; apply/eqP/val_inj/val_inj.
have pth' : path (--) (val x) (map val p) by rewrite path_map.
have d : val (val x) %/ 2 = val (val y) %/ 2.
  by rewrite -lst -(last_map val) (x194_2K2_walk pth').
have m : val (val x) %% 2 = val (val y) %% 2 by move/(congr1 val): e.
by rewrite (divn_eq (val (val x)) 2) (divn_eq (val (val y)) 2) d m.
Qed.

Lemma x218_clustered_chromatic_class_le_compat (F : sgraph -> Prop) k :
  X218Legacy.x218_clustered_chromatic_class_le F k <-> x218_clustered_chromatic_class_le F k.
Proof.
split=> -[c hc]; exists c => G in_class; have hg := hc G in_class.
all: by apply/GTBase.migration.monochromatic.clustered_colouring_compat.
Qed.

(** X218 RE-ENCODING (2026-11-02, PROGRAMME section 3, A2 + A4 re-encode; record meta/STATEMENT_IMPROVEMENTS.md),
    not a migration equivalence.  The live row is Conjecture 2 of arXiv:2308.15721v2 (clustered <= 2 ctd(H) - 2 and
    defective = ctd(H) - 1, over the source's tree model and connected tree-depth); the frozen row gave both class
    parameters the bound k - 1 over [x218_odd_minor].  No implication between them is certified.  The type below is
    the placeholder relation of the spec's repair entry, not a claim. *)
Lemma odd_minor_free_defective_clustered_treedepth_statement_compat :
  (X218Legacy.odd_minor_free_defective_clustered_treedepth_statement -> True) /\
  (odd_minor_free_defective_clustered_treedepth_statement -> True).
Proof. by split. Qed.

(** ** X218 re-encoding: the normalisation defect, kernel-checked *)

(* on K_3, the colouring (false, true, false) of the vertices 0, 1, 2 *)
Definition x218_normalisation_sigma (v : 'K_3) : bool := val v == 1.

(* the bichromatic edges inside the branch set {0, 1, 2} *)
Definition x218_normalisation_rel (a b : 'K_3) : bool :=
  [&& a \in [set: 'K_3], b \in [set: 'K_3], a -- b & x218_normalisation_sigma a != x218_normalisation_sigma b].

Definition x218_normalisation_v1 : 'K_3 := @Ordinal 3 1 isT.

(* every vertex of K_3 reaches the middle vertex 1 and back through bichromatic edges *)
Lemma x218_normalisation_hub (a : 'K_3) :
  connect x218_normalisation_rel a x218_normalisation_v1 /\ connect x218_normalisation_rel x218_normalisation_v1 a.
Proof.
case: a => [[|[|[|m]]] p].
- by split; apply: connect1; rewrite /x218_normalisation_rel /x218_normalisation_sigma !inE /=.
- have -> : Ordinal p = x218_normalisation_v1 by apply: val_inj.
  by split; exact: connect0.
- by split; apply: connect1; rewrite /x218_normalisation_rel /x218_normalisation_sigma !inE /=.
- by [].
Qed.

(* DEFECT (the normalisation): with H = K_1, the branch set {0, 1, 2} of K_3 is connected through its bichromatic
   edges 0-1 and 1-2, so the source's tree model (arXiv.tex l.139-145) accepts it, while the edge 0-2 inside it is
   monochromatic, which [x218_odd_minor]'s per-edge condition rejects *)
Lemma x218_normalisation_defect :
  (forall (x : 'K_1) (u v : 'K_3), connect x218_normalisation_rel u v) /\
  ~ (forall (x : 'K_1) (u v : 'K_3), u \in [set: 'K_3] -> v \in [set: 'K_3] -> u -- v ->
       x218_normalisation_sigma u != x218_normalisation_sigma v).
Proof.
split.
- move=> _ u v; have [cu _] := x218_normalisation_hub u; have [_ cv] := x218_normalisation_hub v.
  exact: connect_trans cu cv.
- by move=> /(_ ord0 (@Ordinal 3 0 isT) (@Ordinal 3 2 isT) (in_setT _) (in_setT _) isT).
Qed.

(* the frozen model is a special case of the source's: every [x218_odd_minor] model is a tree model, so the live
   class (no odd H-minor in the tree model) is contained in the frozen one; the converse is not claimed *)
Lemma x218_legacy_model_is_tree_model (G H : sgraph) : x218_odd_minor G H -> x218_odd_minor_tree_model G H.
Proof.
case=> B [sigma [ne conn dis bi mono]].
exists B, sigma; split=> // x u v uB vB.
apply: connect_sub (conn x u v uB vB) => a b /=.
case/andP=> /andP [aB bB] ab; apply: connect1; rewrite aB bB ab /=.
exact: bi x a b aB bB ab.
Qed.
