(** * Digraph.conjectures.grounding_X251 -- grounding certificates of wave X251.

    For each of the four rows: hyp_inhabited (the hypotheses hold on a concrete instance, and the statement then yields
    its conclusion there) and not_trivially_true in the contract form of meta/EXPANSION_PLAN.md 4.4 (a variant of the
    row, with one hypothesis dropped or the conclusion strengthened, is false, and that variant implies the row).
    arxiv:2410.23566#01: the arcless digraphs (unavoidability number = order, maximum average degree 0); the variant
    with a CONSTANT bound for F[k] fails on the 1-blow-ups of the arcless digraphs. #04: TT 3 is a 1-extension of the
    oriented tree TT 2; without the guard 1 < n the bound at n = 1 is 0, and TT 2 (a 1-extension of TT 1) is not
    0-unavoidable. arxiv:2202.13977#00: TT 1 (strong EH-property vacuously, a forest backedge graph); the variant
    "every tournament has a forest backedge graph" fails at the Paley tournament QR7 (grounding_X248.v). #01: TT 1;
    the variant with the constant c = 1 fails at H = TT 3 (no backedge under the identity), since C3 is TT 3-free and
    two disjoint sets cannot both have 3 of its 3 vertices. helper_sanity covers the six x251_ definitions in every
    row. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup.
From GraphTheory Require Import preliminaries digraph sgraph.
From Digraph Require Import prelude interop_graph_theory digraph oriented dipath tournament order.
From Digraph Require Import heroes dichromatic unvd chi_bounded path_fas X2 X221 X251.
From Digraph Require Import grounding_dichromatic grounding_degreewidth_c3 grounding_X248.
From Digraph.foundations Require Import tournament_unavoidability.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Grounding.

(** The arcless digraph on n vertices. *)
Definition g251_arcless (n : nat) : Type := 'I_n.
HB.instance Definition _ (n : nat) := Finite.on (g251_arcless n).
HB.instance Definition _ (n : nat) := HasArc.Build (g251_arcless n) [rel u v : 'I_n | false].

Definition g251_arcless_family (D : diGraphType) : Prop := forall u v : D, ~~ (u --> v).

Lemma g251_unvd_arcless (D : diGraphType) : g251_arcless_family D -> unavoidability_number D #|D|.
Proof.
move=> noA; split.
  move=> T cT; pose e : #|D| = #|T| := esym cT.
  exists (fun x => enum_val (cast_ord e (enum_rank x))); split.
    by move=> x y /enum_val_inj /cast_ord_inj /enum_rank_inj.
  by move=> u v uv; move: (noA u v) => /negP; case; exact: uv.
by move=> M lt un; have := tournament_unavoidable_card un; rewrite leqNgt lt.
Qed.

Lemma g251_arcless_lin : linearly_unavoidable g251_arcless_family.
Proof.
exists 1 => D N hD hN; rewrite mul1n.
by rewrite (unavoidability_number_unique hN (g251_unvd_arcless hD)).
Qed.

Lemma g251_arcless_mad (D : diGraphType) : g251_arcless_family D -> x251_mad_le D 0.
Proof.
move=> noA S _; rewrite mul0n leqn0.
have -> : [set p | (p.1 \in S) && (p.2 \in S) & p.1 --> p.2] = set0.
  by apply/setP => p; rewrite !inE (negbTE (noA p.1 p.2)) andbF.
by rewrite cards0.
Qed.

Lemma g251_blowup_arcless (D : diGraphType) (k : nat) :
  g251_arcless_family D -> g251_arcless_family (x251_blowup D k : diGraphType).
Proof. by move=> noA a b; exact: noA. Qed.

Lemma g251_dgiso_refl (D : diGraphType) : dgiso D D.
Proof. by exists id; split; [exists id | ]. Qed.

Definition g251_blowup_hyp_claim : Prop :=
  [/\ linearly_unavoidable g251_arcless_family,
      (forall D : diGraphType, g251_arcless_family D -> x251_mad_le D 0) &
      (blowup_linear_unavoidability_statement ->
         linearly_unavoidable (x251_blowup_family 1 g251_arcless_family))].

Theorem g251_blowup_hyp_inhabited : g251_blowup_hyp_claim.
Proof.
split; [exact: g251_arcless_lin | exact: g251_arcless_mad |].
by move=> h; apply: h => //; [exact: g251_arcless_lin | exists 0; exact: g251_arcless_mad].
Qed.

Definition g251_blowup_constant_bound : Prop :=
  forall (F : diGraphType -> Prop) (k : nat), 1 <= k ->
    linearly_unavoidable F ->
    (exists a : nat, forall D : diGraphType, F D -> x251_mad_le D a) ->
    exists B : nat, forall (E : diGraphType) (N : nat),
      x251_blowup_family k F E -> unavoidability_number E N -> N <= B.

Definition g251_blowup_ntt_claim : Prop :=
  ~ g251_blowup_constant_bound /\ (g251_blowup_constant_bound -> blowup_linear_unavoidability_statement).

Theorem g251_blowup_not_trivially_true : g251_blowup_ntt_claim.
Proof.
split.
  move=> h; have [B hB] := h g251_arcless_family 1 isT g251_arcless_lin (ex_intro _ 0 g251_arcless_mad).
  pose E := (x251_blowup (g251_arcless B.+1 : diGraphType) 1 : diGraphType).
  have mE : x251_blowup_family 1 g251_arcless_family E.
    by exists (g251_arcless B.+1 : diGraphType); split => //; exact: g251_dgiso_refl.
  have aE : g251_arcless_family E by apply: g251_blowup_arcless.
  have := hB E #|E| mE (g251_unvd_arcless aE).
  have cE : #|E| = B.+1 by rewrite card_prod !card_ord muln1.
  by rewrite cE ltnn.
move=> h F k k1 lF mF; have [B hB] := h F k k1 lF mF; exists B => E N mE uN.
have [E0|Epos] := posnP #|E|.
  by rewrite (unavoidability_number_unique uN (unavoidability_number_empty E0)).
by apply: (leq_trans (hB E N mE uN)); rewrite leq_pmulr.
Qed.

(** TT n is an oriented tree for n = 1, 2 (every vertex has at most one neighbour). *)
Lemma g251_TT_oriented_tree (n : nat) : 0 < n -> n <= 2 -> oriented_tree (TT n : orientedDigraph).
Proof.
move=> n0 n2; split.
- by rewrite card_TT.
- by move=> u v /arc_asymm ->.
- apply: sdeg_le1_is_forest => x.
  have hsub : [set y | x -- y] \subset [set~ x].
    by apply/subsetP=> y; rewrite !inE /chi_bounded.urel => /andP[hxy _]; rewrite eq_sym.
  rewrite /sdeg; apply: (leq_trans (subset_leq_card hsub)); rewrite cardsC1.
  by rewrite card_ord; case: n n0 n2 {x hsub} => [|[|[|]]].
- apply: connectedTI => x y; have [->|hxy] := eqVneq x y; first exact: connect0.
  apply: connect1.
  by rewrite /edge_rel/= /chi_bounded.urel hxy /= !arcTTE -neq_ltn val_eqE.
Qed.

(** Deleting the last vertex of TT (n+1) leaves TT n. *)
Lemma g251_TT_del_max (n : nat) :
  dgiso (induced_digraph (~: [set ord_max] : {set (TT n.+1 : diGraphType)})) (TT n : diGraphType).
Proof.
have bnd (x : {x : TT n.+1 | x \in [set~ ord_max]}) : val (val x) < n.
  case: x => [x hx] /=; move: hx; rewrite !inE -val_eqE /= => hx.
  by rewrite ltn_neqAle hx -ltnS ltn_ord.
exists (fun x => Ordinal (bnd x)); split.
  have gin (i : 'I_n) : widen_ord (leqnSn n) i \in [set~ (ord_max : TT n.+1)].
    by rewrite !inE -val_eqE /= neq_ltn ltn_ord.
  exists (fun i => exist _ (widen_ord (leqnSn n) i) (gin i)).
    by move=> [x hx]; apply: val_inj; apply: val_inj.
  by move=> i; apply: val_inj.
by move=> u v.
Qed.

Lemma g251_kext_TT (n : nat) : 0 < n -> n <= 2 ->
  x221_kextension 1 (x251_oriented_tree_of_order n) (TT n.+1 : diGraphType).
Proof.
move=> n0 n2; split; first exact: acyclicb_TT.
exists [set ord_max]; split; first by rewrite cards1.
exists (TT n : diGraphType); split; last exact: g251_TT_del_max.
exists (TT n : orientedDigraph); split; first exact: g251_TT_oriented_tree.
split; [exact: card_TT | exact: g251_dgiso_refl].
Qed.

Definition g251_kext_hyp_claim : Prop :=
  [/\ x221_kextension 1 (x251_oriented_tree_of_order 2) (TT 3 : diGraphType) &
      (kextension_oriented_tree_unavoidability_statement ->
         exists C : nat, unavoidable (TT 3 : diGraphType) (C ^ 1 * (2 * 2 - 2)))].

Theorem g251_kext_hyp_inhabited : g251_kext_hyp_claim.
Proof.
split; first exact: g251_kext_TT.
by move=> [C hC]; exists C; apply: hC => //; exact: g251_kext_TT.
Qed.

Definition g251_kext_any_order : Prop :=
  exists C : nat, forall k n : nat, 1 <= k ->
    forall D : diGraphType, x221_kextension k (x251_oriented_tree_of_order n) D ->
      unavoidable D (C ^ k * (2 * n - 2)).

Definition g251_kext_ntt_claim : Prop :=
  ~ g251_kext_any_order /\ (g251_kext_any_order -> kextension_oriented_tree_unavoidability_statement).

Theorem g251_kext_not_trivially_true : g251_kext_ntt_claim.
Proof.
split; last by move=> [C hC]; exists C => k n k1 _; exact: hC.
move=> [C hC].
have h1 : x221_kextension 1 (x251_oriented_tree_of_order 1) (TT 2 : diGraphType) by apply: g251_kext_TT.
have := hC 1 1 (ltn0Sn 0) _ h1.
rewrite muln0 => /tournament_unavoidable_card.
by rewrite card_TT.
Qed.

(** Every tournament with a vertex contains TT 1; so TT 1 has the strong EH-property vacuously. *)
Lemma g251_TT1_in (G : tournament) : 0 < #|G| -> ind_subdigraph (TT 1 : diGraphType) G.
Proof.
move=> /card_gt0P [x _]; exists (fun _ => x); split.
  by move=> u v _; apply: val_inj; case: u v => [[|//] ?] [[|//] ?].
by move=> u v; rewrite arcxx; case: u v => [[|//] ?] [[|//] ?].
Qed.

Lemma g251_seh_TT1 : x251_seh (TT 1).
Proof.
exists 1; split => // G Gfree G1; exfalso; apply: Gfree; apply: g251_TT1_in; exact: ltnW G1.
Qed.

(** A backedge graph on n vertices has at most C(n, 2) edges. *)
Lemma g251_backedges_le (T : tournament) (p : {perm T}) : #|E(backedge p)| <= 'C(#|T|, 2).
Proof.
have sub : E(backedge p) \subset [set A : {set backedge p} | #|A| == 2].
  by apply/subsetP => e /edgesP [x [y [-> xy]]]; rewrite inE cards2 (sg_edgeNeq xy).
by rewrite (leq_trans (subset_leq_card sub)) // card_draws.
Qed.

Definition g251_seh_hyp_claim : Prop :=
  [/\ x251_seh (TT 1), (exists p : {perm (TT 1 : tournament)}, is_forest [set: backedge p]) &
      (strong_eh_iff_forest_backedge_statement ->
         (x251_seh (TT 1) <-> exists p : {perm (TT 1 : tournament)}, is_forest [set: backedge p]))].

Theorem g251_seh_hyp_inhabited : g251_seh_hyp_claim.
Proof. by split; [exact: g251_seh_TT1 | exact: g248_TT1_forest | move=> h; exact: h]. Qed.

(** The "only if" direction with its hypothesis dropped: every tournament has a forest backedge graph
    (the "if" direction kept); false at the Paley tournament QR7 (grounding_X248). *)
Definition g251_seh_no_hyp : Prop :=
  forall H : tournament,
    ((exists p : {perm H}, is_forest [set: backedge p]) -> x251_seh H) /\
    (exists p : {perm H}, is_forest [set: backedge p]).

Definition g251_seh_ntt_claim : Prop :=
  ~ g251_seh_no_hyp /\ (g251_seh_no_hyp -> strong_eh_iff_forest_backedge_statement).

Theorem g251_seh_not_trivially_true : g251_seh_ntt_claim.
Proof.
split; last by move=> h H; have [hif hf] := h H; split=> _; [exact: hf | exact: hif].
by move=> h; have [_ [p hp]] := h (g248_qr7 : tournament); exact: g248_qr7_no_forest hp.
Qed.

Definition g251_three_hyp_claim : Prop :=
  [/\ (exists p : {perm (TT 1 : tournament)}, #|E(backedge p)| <= 3) &
      (three_backedges_strong_eh_statement -> x251_seh (TT 1))].

Theorem g251_three_hyp_inhabited : g251_three_hyp_claim.
Proof.
split; first by exists 1%g; apply: (leq_trans (g251_backedges_le _)); rewrite card_TT.
by move=> h; apply: h; exists 1%g; apply: (leq_trans (g251_backedges_le _)); rewrite card_TT.
Qed.

(** C3 contains no TT 3: 0 -> 1 and 0 -> 2 would force f 1 = f 0 + 1 = f 2. *)
Lemma g251_C3_TT3_free : ind_free (TT 3 : diGraphType) (C3 : diGraphType).
Proof.
move=> [f [inj hf]].
have a01 := hf (Ordinal (isT : 0 < 3)) (Ordinal (isT : 1 < 3)).
have a02 := hf (Ordinal (isT : 0 < 3)) (Ordinal (isT : 2 < 3)).
rewrite arcC3E in a01; rewrite arcC3E in a02.
move: a01 a02 => /eqP e01 /eqP e02.
by have := inj _ _ (etrans e01 (esym e02)).
Qed.

(** The conclusion strengthened to the constant c = 1 (q = 1). *)
Definition g251_three_q1 : Prop :=
  forall H : tournament, (exists p : {perm H}, #|E(backedge p)| <= 3) ->
    forall G : tournament, ind_free H G -> 1 < #|G| ->
      exists A B : {set G}, [/\ [disjoint A & B], (forall a b, a \in A -> b \in B -> a --> b),
        #|G| <= #|A| & #|G| <= #|B|].

Definition g251_three_ntt_claim : Prop :=
  ~ g251_three_q1 /\ (g251_three_q1 -> three_backedges_strong_eh_statement).

Theorem g251_three_not_trivially_true : g251_three_ntt_claim.
Proof.
split; last first.
  move=> h H hH; exists 1; split => // G Gf G1.
  have [A [B [d ar hA hB]]] := h H hH G Gf G1; exists A, B; by rewrite !mul1n; split.
move=> h.
have hTT3 : exists p : {perm (TT 3 : tournament)}, #|E(backedge p)| <= 3.
  by exists 1%g; apply: (leq_trans (g251_backedges_le _)); rewrite card_TT.
have c1 : 1 < #|(C3 : tournament)| by rewrite card_C3.
have [A [B [dAB _ hA hB]]] := h (TT 3) hTT3 (C3 : tournament) g251_C3_TT3_free c1.
have := leq_add hA hB.
have hU : #|A| + #|B| = #|A :|: B| by rewrite -cardsUI (disjoint_setI0 dAB) cards0 addn0.
rewrite hU => h2; have := leq_trans h2 (max_card _); by rewrite card_C3.
Qed.

(** ** helper_sanity *)

(** x251_blowup / x251_blowup_rel: TT 2 blown up by 2 has 4 vertices; (0,0) -> (1,0) and (0,0) -> (1,1) are arcs (every
    i, j: the printed "i <> j" is not followed), and the two copies of 0 are independent. *)
Definition g251_blowup_helper_claim : Prop :=
  [/\ #|(x251_blowup (TT 2 : diGraphType) 2 : diGraphType)| = 4,
      x251_blowup_rel ((ord0, ord0) : x251_blowup (TT 2 : diGraphType) 2) (ord_max, ord0),
      x251_blowup_rel ((ord0, ord0) : x251_blowup (TT 2 : diGraphType) 2) (ord_max, ord_max) &
      ~~ x251_blowup_rel ((ord0, ord0) : x251_blowup (TT 2 : diGraphType) 2) (ord0, ord_max)].

Theorem g251_blowup_helper_sanity : g251_blowup_helper_claim.
Proof. by split; rewrite // card_prod !card_ord. Qed.

(** x251_blowup_family: the 2-blow-up of the arcless digraph on 3 vertices is in the family of 2-blow-ups of arcless
    digraphs; the empty family has no blow-up. *)
Definition g251_blowup_family_helper_claim : Prop :=
  x251_blowup_family 2 g251_arcless_family (x251_blowup (g251_arcless 3 : diGraphType) 2 : diGraphType) /\
  forall (k : nat) (D : diGraphType), ~ x251_blowup_family k (fun _ => False) D.

Theorem g251_blowup_family_helper_sanity : g251_blowup_family_helper_claim.
Proof.
split; last by move=> k D [E [[]]].
by exists (g251_arcless 3 : diGraphType); split => //; exact: g251_dgiso_refl.
Qed.

(** x251_mad_le: the arcless digraph has maximum average degree 0; TT 2 (one arc) does not. *)
Definition g251_mad_helper_claim : Prop :=
  x251_mad_le (g251_arcless 2 : diGraphType) 0 /\ ~ x251_mad_le (TT 2 : diGraphType) 0.

Theorem g251_mad_helper_sanity : g251_mad_helper_claim.
Proof.
split; first exact: g251_arcless_mad.
move=> /(_ setT) h.
have ne : (setT : {set (TT 2 : diGraphType)}) != set0 by apply/set0Pn; exists ord0; rewrite inE.
have := h ne; rewrite mul0n leqn0 muln_eq0 /= cards_eq0 => /eqP/setP/(_ (ord0, ord_max)).
by rewrite !inE.
Qed.

(** x251_oriented_tree_of_order: TT 2 is an oriented tree of order 2; TT 3 is not of order 2. *)
Definition g251_tree_helper_claim : Prop :=
  x251_oriented_tree_of_order 2 (TT 2 : diGraphType) /\ ~ x251_oriented_tree_of_order 2 (TT 3 : diGraphType).

Theorem g251_tree_helper_sanity : g251_tree_helper_claim.
Proof.
split.
  exists (TT 2 : orientedDigraph); split; first exact: g251_TT_oriented_tree.
  by split; [exact: card_TT | exact: g251_dgiso_refl].
move=> [T [_ [cT [f [bf _]]]]].
by have := bij_eq_card bf; rewrite cT card_TT.
Qed.

(** x251_seh: TT 1 has the strong EH-property (vacuously); the property is not vacuous for TT 3, since C3 is a TT 3-free
    tournament on more than one vertex. *)
Definition g251_seh_helper_claim : Prop :=
  [/\ x251_seh (TT 1), ind_free (TT 3 : diGraphType) (C3 : diGraphType) & 1 < #|(C3 : tournament)|].

Theorem g251_seh_helper_sanity : g251_seh_helper_claim.
Proof. by split; [exact: g251_seh_TT1 | exact: g251_C3_TT3_free | rewrite card_C3]. Qed.

End Grounding.
