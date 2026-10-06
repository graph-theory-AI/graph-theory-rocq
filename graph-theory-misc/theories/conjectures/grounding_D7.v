(** * GTMisc.conjectures.grounding_D7 — grounding lemmas for milestone D7.

    SIMPLE, Qed-closed sanity results validating the NEW area-specific primitives
    introduced in [D7.v] (the abstract cost/algorithm vocabulary kept for the
    hardness row, the coupled-prog-model glue of the POSITIVE rows — [dnat_val],
    the per-row encodings, the statement SHAPES — the MaxEDP routing vocabulary,
    the H-factor / abstract-complexity layer, the tournament feedback-arc-set
    vocabulary, and the edge-outerplanar layering proxy).  For (essentially)
    each new definition we record a SATISFIABLE witness and at least one
    textbook identity.  These are statement-validation lemmas, NOT the (open)
    conjectures themselves.

    Reusable carriers:
      - [K2] : the complete graph on 2 vertices (via [mk_sgraph] of the full
        relation) — the minimal carrier with an edge, used for the [walkb],
        [walk_uses] and [edge_outerplanar] witnesses;
      - [triv_problem] : the always-YES abstract decision problem, used for the
        [in_NP] witness.

    A reusable helper [minor_leq_card] (a minor has no more branch vertices than
    its host) lets us discharge [wagner_planar K2] = no [K5]/[K3,3] minor on a
    2-vertex graph purely by cardinality.

    Coverage notes (honest): every new primitive gets at least one Qed-closed
    identity, and almost all also get a satisfiable witness.  The POSITIVE-row
    statement SHAPES (coupled [prog] model of foundations/complexity.v) are
    grounded by concrete programs meeting a trivial spec within the stated cost
    budget ([hom_statement_shape_inhabited], [edp_realizes_shape_inhabited]) —
    non-vacuity of the FORM, leaving the mathematical content open.  Two
    primitives are grounded by a projection identity only:
      - [maxedp_approx] (its full positive witness would require a [prog]
        actually computing an approximation of the MaxEDP optimum together with
        a ratio proof for ALL planar inputs — out of scope for a SIMPLE check);
      - [NP_hard] (a positive witness is a complete problem, i.e. a genuine
        NP-hardness proof — out of scope; we record the elimination identity).
    These match the deliberate abstraction level of [D7.v]. *)

From GTBase Require Import base.
From GraphTheory Require Import minor.
From GTMisc.conjectures Require Import D7.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ============================================================================
    Helper: a minor has at most as many vertices as its host.
    ========================================================================== *)
Lemma minor_leq_card (G H : sgraph) : minor G H -> #|H| <= #|G|.
Proof.
case=> phi [Hsurj _ _].
have Hsurj' : forall y : H, exists x : G, phi x == Some y.
  by move=> y; case: (Hsurj y) => x Hx; exists x; rewrite Hx eqxx.
pose g (y : H) : G := xchoose (Hsurj' y).
have gP : forall y : H, phi (g y) == Some y.
  by move=> y; exact: (xchooseP (Hsurj' y)).
apply: (@leq_card _ _ g) => y1 y2 e.
by move: (gP y1) (gP y2) => /eqP H1 /eqP H2; rewrite e H2 in H1; case: H1.
Qed.

(** ============================================================================
    Reusable carrier [K2] (via a local [mk_sgraph]).
    ========================================================================== *)
Section Mk.
Variable V : finType.
Definition relAdj (r : rel V) : rel V := fun x y => (x != y) && (r x y || r y x).
Lemma relAdj_sym (r : rel V) : symmetric (relAdj r).
Proof. by move=> x y; rewrite /relAdj eq_sym orbC. Qed.
Lemma relAdj_irrefl (r : rel V) : irreflexive (relAdj r).
Proof. by move=> x; rewrite /relAdj eqxx. Qed.
Definition mk_sgraph (r : rel V) : sgraph := SGraph (@relAdj_sym r) (@relAdj_irrefl r).
End Mk.

Definition K2 : sgraph := @mk_sgraph 'I_2 (fun _ _ => true).

Lemma K2_edge (x y : K2) : (x -- y) = (x != y).
Proof. by rewrite /edge_rel/= /relAdj/= andbT. Qed.

Lemma cardK2 : #|K2| = 2.
Proof. by rewrite card_ord. Qed.

Lemma cardK33 : #|'K_3,3| = 6.
Proof. by rewrite card_sum !card_ord. Qed.

Lemma wagner_K2 : wagner_planar K2.
Proof.
split=> Hm.
- by move: (small_K_free (G := K2) (m := 4)); rewrite cardK2; apply.
- by move: (minor_leq_card Hm); rewrite cardK33 cardK2.
Qed.

(** ============================================================================
    Shared abstract cost / algorithm vocabulary.
    ========================================================================== *)

(** [decides]: the constant-true verdict decides the always-true predicate;
    a decider is sound. *)
Lemma decides_triv : decides (fun _ : nat => true) (fun _ => True).
Proof. by move=> x; split. Qed.

Lemma decides_sound (I : Type) (v : I -> bool) (P : I -> Prop) (x : I) :
  decides v P -> v x -> P x.
Proof. by move=> H; rewrite -H. Qed.

(** [runs_in_time]: the zero-cost function meets every bound; reflexivity. *)
Lemma runs_in_time_0 (I : Type) (bnd : I -> nat) : runs_in_time (fun _ => 0) bnd.
Proof. by move=> x. Qed.

Lemma runs_in_time_refl (I : Type) (c : I -> nat) : runs_in_time c c.
Proof. by move=> x. Qed.

(** [poly_bounded]: the zero-cost function is polynomially bounded by any size. *)
Lemma poly_bounded_0 (I : Type) (sz : I -> nat) : poly_bounded sz (fun _ => 0).
Proof. by exists 0, 0, 0 => x; rewrite mul0n. Qed.

(** ============================================================================
    Coupled prog model (positive rows) — decoder identity and statement-SHAPE
    non-vacuity.
    ========================================================================== *)

(** [dnat_val]: the output decoder reads back [Dnat] values (and 0 on junk). *)
Lemma dnat_val_K (n : nat) : dnat_val (Dnat n) = n.
Proof. by []. Qed.

Lemma dnat_val_junk : dnat_val Dnil = 0.
Proof. by []. Qed.

(** Row 1 SHAPE: a concrete [prog] (the constant-YES program) decides the
    trivial predicate on the homomorphism-instance encoding [enc_hom] within
    the exponential budget — the coupled form [exists c p a b, [/\ ...]] is
    inhabited for SOME predicate, so the open content of Row 1 is [homs_to],
    not the statement shape. *)
Lemma hom_statement_shape_inhabited :
  exists (c : nat) (p : prog) (a b : nat),
    [/\ 1 < c,
        decides_on enc_hom (fun _ : sgraph * sgraph => True) p &
        forall GH : sgraph * sgraph,
          pcost p (enc_hom GH) <= a * c ^ (#|GH.1| + #|GH.2|) + b ].
Proof.
by exists 2, (Pconst (Dnat 1)), 0, 1; split.
Qed.

(** Rows 2/4/5 SHAPE: a concrete [prog] realizes a (trivial) output-value spec
    on the MaxEDP instance encoding [enc_edp] within a polynomial step budget —
    the coupled [realizes_on ... /\ poly_cost_on ...] form is inhabited. *)
Lemma edp_realizes_shape_inhabited :
  exists p : prog,
    realizes_on enc_edp (fun _ out => dnat_val out = 0) p /\
    poly_cost_on enc_edp p.
Proof.
exists (Pconst (Dnat 0)); split=> [x|]; first by [].
by exists 1, 0 => x; rewrite /pcost /= expn0 muln1.
Qed.

(** ============================================================================
    Row 2 — MaxEDP routing vocabulary.
    ========================================================================== *)

(** [walkb]: a walk ends at its declared target; [K2] carries a 1-step walk. *)
Lemma walkb_last (G : sgraph) (s t : G) (p : seq G) : walkb s t p -> last s p = t.
Proof. by case/andP => _ /andP[_ /eqP ->]. Qed.

Lemma walkb_K2 : walkb (ord0 : K2) ord_max [:: ord_max].
Proof. by rewrite /walkb /pathp /= eqxx. Qed.

(** [walk_uses]: edge-usage is symmetric in its two endpoints (undirected
    edge); [K2]'s walk uses its only edge. *)
Lemma walk_uses_sym (G : sgraph) (s : G) (p : seq G) (u v : G) :
  walk_uses s p u v = walk_uses s p v u.
Proof. exact: walk_usage.seq_consecutiveb_sym. Qed.

Lemma walk_uses_K2 : walk_uses (ord0 : K2) [:: ord_max] ord0 ord_max.
Proof. by rewrite /walk_uses /=. Qed.

(** [edp_feasible]: the empty demand-set is vacuously feasible. *)
Lemma edp_feasible_set0 (G : sgraph) (D : seq (G * G))
  (route : 'I_(size D) -> seq G) : edp_feasible (set0 : {set 'I_(size D)}) route.
Proof. by split=> [i|i j u v]; rewrite inE. Qed.

(** [edp_opt]: with no demands the MaxEDP optimum is [0]. *)
Lemma edp_opt_nil (G : sgraph) : edp_opt (G := G) [::] 0.
Proof.
split.
- exists set0, (fun _ => [::]); split; first exact: edp_feasible_set0.
  by rewrite cards0.
- by move=> S route _; move: (max_card S); rewrite card_ord.
Qed.

(** [edp_vsize]: it sums vertices and demands. *)
Lemma edp_vsize_E (G : sgraph) (D : seq (G * G)) :
  edp_vsize (existT _ G D) = #|G| + size D.
Proof. by []. Qed.

(** [maxedp_approx] (coupled): projections — an approximating program has a
    polynomially bounded step count on the SAME encoding it answers on, and
    realizes the per-instance ratio spec. *)
Lemma maxedp_approx_cost (p : prog) (rho : nat -> nat) :
  maxedp_approx p rho -> poly_cost_on enc_edp p.
Proof. by case. Qed.

Lemma maxedp_approx_realizes (p : prog) (rho : nat -> nat) :
  maxedp_approx p rho -> realizes_on enc_edp (edp_ratio_spec rho) p.
Proof. by case. Qed.

(** [little_o_sqrt]: the constant-zero ratio is [o(sqrt n)]. *)
Lemma little_o_sqrt_0 : little_o_sqrt (fun _ => 0).
Proof. by move=> c; exists 0 => n _; rewrite expnS mul0n muln0. Qed.

(** ============================================================================
    Row 3 — H-factor and abstract-complexity vocabulary.
    ========================================================================== *)

(** [is_copy]: the identity is a copy of [G] in itself; a copy is injective. *)
Lemma is_copy_id (G : sgraph) : is_copy (@id G).
Proof. by split=> [|x y]; [exact: inj_id|]. Qed.

Lemma is_copy_inj (H G : sgraph) (f : H -> G) : is_copy f -> injective f.
Proof. by case. Qed.

(** [h_factor]: every graph has the trivial H-factor [G] = single copy of [G]. *)
Lemma h_factor_refl (G : sgraph) : h_factor G G.
Proof.
exists 1, (fun _ => [set: G]), (fun _ => id); split.
- by move=> v; exists ord0; rewrite in_setT.
- by move=> i j v _ _; rewrite (ord1 i) (ord1 j).
- by move=> i; exact: is_copy_id.
- move=> i; apply/setP => z; apply/idP/idP => _; last by rewrite in_setT.
  by apply/imsetP; exists z; rewrite ?in_setT.
Qed.

(** [mindeg_cn]: the [c = 0] (a = 0) min-degree constraint is vacuous. *)
Lemma mindeg_cn_0 (G : sgraph) (b : nat) : mindeg_cn G 0 b.
Proof. by move=> v; rewrite mul0n. Qed.

(** [problem]: the record projections compute on [triv_problem]. *)
Definition triv_problem : problem := Problem (fun _ : unit => 0) (fun _ => True).

Lemma triv_problem_size (u : unit) : @psize triv_problem u = 0.
Proof. by []. Qed.

(** [poly_reduces]: reflexivity (the identity reduction). *)
Lemma poly_reduces_refl (A : problem) : poly_reduces A A.
Proof.
exists id, (fun _ => 0), 1, 1, 0; split.
- by move=> x; exact: iff_refl.
- by move=> x; rewrite expn1 mul1n addn0.
- by move=> x; rewrite expn1 mul1n addn0.
Qed.

(** [in_NP]: the always-YES problem is in NP (empty certificate, constant
    verifier). *)
Lemma in_NP_triv : in_NP triv_problem.
Proof.
exists (fun _ _ => true), (fun _ _ => 0), 0, 0, 0; split.
- move=> x; split=> [_|_]; last by [].
  by exists [::]; split; rewrite ?mul0n.
- by move=> x cert; rewrite mul0n.
Qed.

(** [NP_hard]: elimination — NP-hardness yields a reduction from each NP
    problem.  (A positive witness is a genuine completeness proof, out of
    scope.) *)
Lemma NP_hard_elim (B A : problem) : NP_hard B -> in_NP A -> poly_reduces A B.
Proof. by move=> H; apply: H. Qed.

(** ============================================================================
    Row 4 — Tournament feedback-arc-set vocabulary.
    ========================================================================== *)

(** [is_tournament]: the 1-vertex relation is a tournament; tournaments are
    irreflexive. *)
Lemma is_tournament_triv : is_tournament (fun _ _ : 'I_1 => false).
Proof. by split=> [x|x y]; rewrite ?(ord1 x) ?(ord1 y) ?eqxx. Qed.

Lemma is_tournament_irrefl (T : finType) (r : rel T) :
  is_tournament r -> forall x : T, ~~ r x x.
Proof. by case. Qed.

(** [back_arcs]: the empty (arc-free) relation has no back arcs. *)
Lemma back_arcs_nil (T : finType) (pos : T -> nat) :
  back_arcs (fun _ _ : T => false) pos = 0.
Proof. by apply: eq_card0 => p; rewrite inE. Qed.

(** [fas_opt]: the arc-free tournament has optimum [0]. *)
Lemma fas_opt_nil : fas_opt (fun _ _ : 'I_2 => false) 0.
Proof.
split.
- by exists (@nat_of_ord 2); split; [exact: val_inj|exact: back_arcs_nil].
- by move=> pos _; rewrite back_arcs_nil.
Qed.

(** [t_vsize]: it counts vertices. *)
Lemma t_vsize_E (T : finType) (r : rel T) : t_vsize (existT _ T r) = #|T|.
Proof. by []. Qed.

(** ============================================================================
    Row 5 — Edge-outerplanar layering proxy.
    ========================================================================== *)

(** [edge_outerplanar] (repaired level-partition proxy): [K2] admits the
    depth-1 layering — its single level is [K2]-shaped, outerplanar in the
    Chartrand–Harary sense since it has 2 < 4 and 2 < 5 vertices ([minor_card]
    from base). *)
Lemma edge_outerplanar_K2 : edge_outerplanar K2 1.
Proof.
split; first exact: wagner_K2.
exists (fun _ _ => 0); split=> [x y _|j _] //.
split=> M; have := minor_card M.
- by rewrite !card_ord.
- by rewrite card_sum !card_ord.
Qed.

(** [min_edge_outerplanar]: [K2]'s minimal depth is [1] (a depth realising an
    edge is positive: the edge's level must be [< m]). *)
Lemma min_edge_outerplanar_K2 : min_edge_outerplanar K2 1.
Proof.
split; first exact: edge_outerplanar_K2.
move=> m [_ [lev [Hlt _]]].
have E : (ord0 : K2) -- ord_max by rewrite K2_edge.
exact: leq_ltn_trans (leq0n _) (Hlt _ _ E).
Qed.

(** ============================================================================
    Row 1 — [homs_to] non-vacuity and teeth.
    ========================================================================== *)

(** [homs_to] (the Row-1 decision predicate) is genuinely inhabited: the
    identity is an adjacency-preserving map, so the target predicate is not
    vacuously empty (the coupled-shape lemma above only decides [True]). *)
Lemma homs_to_refl (G : sgraph) : homs_to G G.
Proof. by exists id. Qed.

(** [homs_to] has teeth: an edge cannot map into the edgeless [ 'K_1 ] — the
    two distinct vertices of [K2] (adjacent) are forced onto the unique vertex
    of [ 'K_1 ], where [is_hom]'s edge-preservation clause contradicts
    [sg_irrefl].  So [homs_to] is not trivially always-true. *)
Lemma not_homs_to_K2_K1 : ~ homs_to K2 'K_1.
Proof.
case=> f Hf.
have E : (ord0 : K2) -- ord_max by rewrite K2_edge -val_eqE.
by move: (Hf _ _ E); rewrite [f ord0]ord1 [f ord_max]ord1 sg_irrefl.
Qed.

(** ============================================================================
    Row 4 (faithfulness) — [fas_ptas_spec] genuinely constrains the output.

    The PTAS statement is [forall p q, 0<p -> 0<q -> exists alg, realizes_on
    enc_tournament (fas_ptas_spec p q) alg /\ poly_cost_on ...].  Proving it in
    full is the Kenyon-Mathieu-Schudy PTAS — out of scope here.  What we DO pin
    down is that the [exists alg] is not a vacuous proxy: [fas_ptas_spec] forces
    the output VALUE to track the per-instance feedback-arc-set optimum [k], so
    no program emitting a fixed answer can realize it.  We exhibit two genuine
    tournaments with DIFFERENT optima:
      - the cyclic 3-tournament [c3] (0->1->2->0), whose minimum feedback arc
        set is exactly 1 ([fas_opt_c3] — its unique directed triangle forces a
        backward arc under every linear order); and
      - the one-vertex tournament, acyclic, optimum 0 ([fas_opt_r1]);
    and show no single output [data] satisfies [fas_ptas_spec p q] on both. *)
Section FASteeth.

Definition c3 : rel 'I_3 := fun i j =>
  [|| (val i == 0) && (val j == 1),
      (val i == 1) && (val j == 2)
    | (val i == 2) && (val j == 0)].

Lemma c3_tournament : is_tournament c3.
Proof.
split.
- by move=> x; rewrite /c3; case: x => -[|[|[|?]]] //.
- by move=> x y; rewrite /c3; case: x => -[|[|[|?]]] ? //; case: y => -[|[|[|?]]] ? //.
Qed.

Local Notation o0 := (@ord0 2 : 'I_3).
Local Notation o1 := (@Ordinal 3 1 isT : 'I_3).
Local Notation o2 := (@Ordinal 3 2 isT : 'I_3).

Definition c3set (pos : 'I_3 -> nat) : {set 'I_3 * 'I_3} :=
  [set p : 'I_3 * 'I_3 | c3 p.1 p.2 && (pos p.2 < pos p.1)].

(** Under the natural order 0<1<2 only the wrap-around arc 2->0 points backward,
    so [back_arcs] there is exactly 1 (the achievable optimum witness). *)
Lemma back_arcs_c3_val : back_arcs c3 (@nat_of_ord 3) = 1.
Proof.
rewrite /back_arcs -/(c3set (@nat_of_ord 3)).
have -> : c3set (@nat_of_ord 3) = [set (o2, o0)].
  apply/setP => p; rewrite !inE; case: p => a b /=.
  by case: a => -[|[|[|?]]] ? //; case: b => -[|[|[|?]]] ? //.
by rewrite cards1.
Qed.

(** Every injective order leaves at least one backward arc: an arc-free order
    would linearise the directed triangle, forcing pos o0 <= pos o1 <= pos o2 <=
    pos o0, hence o0 = o2, contradicting injectivity. *)
Lemma back_arcs_c3_lb (pos : 'I_3 -> nat) : injective pos -> 1 <= back_arcs c3 pos.
Proof.
move=> Hpos; rewrite lt0n; apply/eqP => H0.
have Hset : c3set pos = set0 by exact: cards0_eq H0.
have arc : forall a b : 'I_3, c3 a b -> pos a <= pos b.
  move=> a b Hab; move: (in_set0 (a, b)); rewrite -Hset inE /= Hab /=.
  by move/negbT; rewrite -leqNgt.
have H01 : pos o0 <= pos o1 by apply: arc; rewrite /c3 /=.
have H12 : pos o1 <= pos o2 by apply: arc; rewrite /c3 /=.
have H20 : pos o2 <= pos o0 by apply: arc; rewrite /c3 /=.
have E : pos o0 = pos o2 by apply/eqP; rewrite eqn_leq (leq_trans H01 H12) H20.
move/Hpos: E => E2.
have Hne : (o0 == o2 :> 'I_3) = false by rewrite -val_eqE.
by move: Hne; rewrite E2 eqxx.
Qed.

(** The feedback-arc-set optimum of the cyclic 3-tournament is exactly 1. *)
Lemma fas_opt_c3 : fas_opt c3 1.
Proof.
split.
- by exists (@nat_of_ord 3); split; [exact: val_inj|exact: back_arcs_c3_val].
- exact: back_arcs_c3_lb.
Qed.

(** The one-vertex tournament (no arcs) is acyclic: its optimum is 0. *)
Lemma fas_opt_r1 : fas_opt (fun _ _ : 'I_1 => false) 0.
Proof.
split.
- by exists (@nat_of_ord 1); split; [exact: val_inj|exact: back_arcs_nil].
- by move=> pos _; exact: leq0n.
Qed.

Definition c3_input : t_input := existT (fun T : finType => rel T) 'I_3 c3.
Definition triv_input : t_input :=
  existT (fun T : finType => rel T) 'I_1 (fun _ _ => false).

(** TEETH (the requested probe): the constant output [Dnat 0] does NOT satisfy
    [fas_ptas_spec p q] on the cyclic 3-tournament — the achievability clause
    [k <= dnat_val out] at the true optimum [k = 1] would demand [1 <= 0].  So
    the spec is not vacuously met by the zero program; it constrains the output. *)
Lemma fas_ptas_spec_teeth (p q : nat) :
  ~ fas_ptas_spec p q c3_input (Dnat 0).
Proof.
move=> H; have [H1 _] := H 1 c3_tournament fas_opt_c3.
by [].
Qed.

(** STRONGER — the output must track the optimum: NO single output [data]
    realizes [fas_ptas_spec p q] on BOTH the cyclic (optimum 1) and the
    one-vertex (optimum 0) tournaments.  On the one-vertex instance the ratio
    clause forces [q * dnat_val out <= 0], i.e. value 0 (as [0 < q]); on the
    cyclic instance the achievability clause forces [1 <= dnat_val out].  Hence
    the [exists alg] of the PTAS statement cannot be met by any constant-output
    program: the answer genuinely depends on the instance optimum [k]. *)
Lemma fas_ptas_spec_no_output (p q : nat) : 0 < q ->
  forall out : data,
    ~ (fas_ptas_spec p q c3_input out /\ fas_ptas_spec p q triv_input out).
Proof.
move=> Hq out [Hc Ht].
have [Hc1 _] := Hc 1 c3_tournament fas_opt_c3.
have [_ Ht2] := Ht 0 is_tournament_triv fas_opt_r1.
move: Ht2; rewrite muln0 leqn0 muln_eq0 (gtn_eqF Hq) /= => /eqP Hv0.
by move: Hc1; rewrite Hv0.
Qed.

(** Corollary: every positive constant value [n] fails the spec on the
    one-vertex tournament (the ratio clause forces value 0). *)
Lemma fas_ptas_spec_teeth_pos (p q n : nat) : 0 < q -> 0 < n ->
  ~ fas_ptas_spec p q triv_input (Dnat n).
Proof.
move=> Hq Hn H.
have [_ H2] := H 0 is_tournament_triv fas_opt_r1.
by move: H2; rewrite muln0 leqn0 muln_eq0 (gtn_eqF Hq) (gtn_eqF Hn).
Qed.

End FASteeth.
