(** * Digraph.conjectures.grounding_X248 -- grounding certificates of wave X248.

    For each of the five rows: hyp_inhabited (the hypotheses hold on a concrete instance, and the
    statement then yields its conclusion there) and not_trivially_true in the contract form of
    meta/EXPANSION_PLAN.md 4.4 (a strengthened variant of the row is false, and that variant
    implies the row); and helper_sanity for the x248_ helpers (one instance where each holds, one
    where it fails). The variants: "every ordering" for arxiv:2310.04265#00 (TT 2 reversed);
    a constant bound on the closure for #01 and #11 (the tournaments S_k of the paper, l.836,
    built by substitution from the tournaments on at most three vertices, are not
    k-dicolourable); the only-if direction of #05 without its hypothesis, "every tournament has
    a forest backedge graph" (the Paley tournament QR_7 has domination number 3, hence clique
    number at least 3, l.494); g fixed to the identity for #08 (C3). [g248_omegab_dg_tournament]
    shows that the digraph clique number [x248_omegab_dg] is [omegabar] on tournaments. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup.
From GraphTheory Require Import preliminaries digraph sgraph coloring.
From Digraph Require Import prelude interop_graph_theory digraph oriented dipath tournament order.
From Digraph Require Import heroes heroes_dichotomy dichromatic omegabar domination X221 X248.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The digraph clique number is omegabar on tournaments, by conversion. *)
Lemma g248_omegab_dg_tournament (T : tournament) : x248_omegab_dg T = omegabar T.
Proof. reflexivity. Qed.

(** The Paley tournament on 7 vertices: i -> j iff j - i is a nonzero square mod 7. *)
Definition g248_qr7 : Type := 'I_7.
HB.instance Definition _ := Finite.on g248_qr7.
HB.instance Definition _ := HasArc.Build g248_qr7 [rel u v : 'I_7 | ((v + 7 - u) %% 7 \in [:: 1; 2; 4])%N].

Lemma g248_qr7_irrefl : irreflexive (arc : rel g248_qr7).
Proof. by case=> -[|[|[|[|[|[|[|//]]]]]]] ?. Qed.

Lemma g248_qr7_total (u v : g248_qr7) : (u != v) = (arc u v) (+) (arc v u).
Proof. by case: u v => -[|[|[|[|[|[|[|//]]]]]]] ? [[|[|[|[|[|[|[|//]]]]]]] ?]. Qed.

HB.instance Definition _ := DiGraph_IsTournament.Build g248_qr7 g248_qr7_irrefl g248_qr7_total.

Lemma g248_qr7_common (x y : g248_qr7) : exists v : g248_qr7, (v --> x) && (v --> y).
Proof.
case: x y => -[|[|[|[|[|[|[|//]]]]]]] ? [[|[|[|[|[|[|[|//]]]]]]] ?];
  first [ by exists (@Ordinal 7 0 isT) | by exists (@Ordinal 7 1 isT) | by exists (@Ordinal 7 2 isT)
        | by exists (@Ordinal 7 3 isT) | by exists (@Ordinal 7 4 isT) | by exists (@Ordinal 7 5 isT)
        | by exists (@Ordinal 7 6 isT) ].
Qed.

Lemma g248_qr7_domnum : (2 < domnum (g248_qr7 : tournament))%N.
Proof.
have [X dX ->] := domnum_witness (g248_qr7 : tournament).
rewrite ltnNge; apply/negP => X2.
have [v /andP [vx vy]] := g248_qr7_common (nth ord0 (enum X) 0) (nth ord0 (enum X) 1).
have hv : forall z, z \in X -> v --> z.
  move=> z; rewrite -mem_enum; move: X2 vx vy; rewrite cardE.
  case: (enum X) => [|a [|b [|c s]]] //= _ vx vy; rewrite !inE; first by move/eqP->.
  by case/orP => /eqP ->.
have vX : v \notin X by apply/negP => /hv; rewrite arcxx.
have [x xX xv] := dominatesbP X dX v vX.
by have := arc_asym (hv x xX); rewrite xv.
Qed.

Lemma g248_omega3_not_forest (G : sgraph) : (2 < ω([set: G]))%N -> ~ is_forest [set: G].
Proof.
case: omegaP => K Kmax K3 hf.
have Kcl : clique K := maxclique_clique Kmax.
have /forest3 := induced_forest (sub_forest (subsetT K) hf).
rewrite card_sig => /(_ K3) [x [y [xy]]]; rewrite -val_eqE in xy.
by case/negP; exact: (Kcl _ _ (valP x) (valP y) xy).
Qed.

Lemma g248_qr7_no_forest (p : {perm (g248_qr7 : tournament)}) : ~ is_forest [set: backedge p].
Proof.
apply: g248_omega3_not_forest.
exact: leq_trans (leq_trans g248_qr7_domnum (domnum_le_omegabar _)) (omegabar_min p).
Qed.

(** ** S_k by substitution (the paper's S_n = Delta(1, S_(n-1), S_(n-1)), l.836) *)
Lemma g248_dicycle_map (D D' : diGraphType) (g : D -> D') :
  injective g -> (forall u v, (g u --> g v) = (u --> v)) -> forall s : seq D, dicycle (map g s) = dicycle s.
Proof.
move=> gi ga s; rewrite /dicycle (map_inj_uniq gi) cycle_map.
have -> : path.cycle (relpre g arc) s = path.cycle arc s by apply: eq_cycle => u v; rewrite /relpre /= ga.
by case: s.
Qed.

Lemma g248_not_acyclic_induced (D : diGraphType) (S : {set D}) (c : seq D) :
  dicycle c -> all (mem S) c -> ~~ acyclicb (induced_digraph S).
Proof.
move=> dc cS.
pose c' : seq (induced_digraph S) := pmap insub c.
have ec : map val c' = c.
  rewrite /c'; elim: c cS {dc c'} => [|x t IH] //= /andP [xS tS]; rewrite insubT /= IH //.
have gi : injective (fun v : induced_digraph S => (val v : D)) by move=> x y; exact: val_inj.
have ga : forall u v : induced_digraph S, ((val u : D) --> val v) = (u --> v) by move=> u v; rewrite sub_arcE.
rewrite -ec (g248_dicycle_map gi ga) in dc; exact: dicycle_not_acyclicb dc.
Qed.

Definition g248_c : C3 := @Ordinal 3 2 isT.
Definition g248_inner (D : diGraphType) : diGraphType := x248_subst (g248_c : (C3 : diGraphType)) D.
Definition g248_b (D : diGraphType) : g248_inner D := inl (exist _ (@Ordinal 3 1 isT : C3) isT).

Fixpoint g248_S (k : nat) : diGraphType :=
  if k is k'.+1 then (x248_subst (g248_b (g248_S k')) (g248_S k') : diGraphType) else K1.

Lemma g248_S_mono (k : nat) (col : g248_S k -> nat) (L : seq nat) :
  (size L <= k)%N -> (forall v, col v \in L) ->
  exists c : seq (g248_S k), dicycle c /\ forall v w, v \in c -> w \in c -> col v = col w.
Proof.
elim: k col L => [|k IH] col L sL hL.
  by have := hL ord0; move: sL; rewrite leqn0 => /nilP ->.
pose x : g248_S k.+1 := inl (exist _ (inl (exist _ (@Ordinal 3 0 isT : C3) isT)) isT).
pose c0 := col x.
have c0L : c0 \in L := hL x.
have sF : (size (filter (predC1 c0) L) <= k)%N.
  rewrite size_filter -ltnS; apply: leq_trans sL; rewrite -(count_predC (pred1 c0) L) -add1n leq_add2r.
  by rewrite -has_count has_pred1.
have lift : forall g : g248_S k -> g248_S k.+1, injective g -> (forall u v, (g u --> g v) = (u --> v)) ->
    (forall b, col (g b) != c0) ->
    exists c : seq (g248_S k.+1), dicycle c /\ forall v w, v \in c -> w \in c -> col v = col w.
  move=> g gi ga hb.
  have hF : forall b, col (g b) \in filter (predC1 c0) L by move=> b; rewrite mem_filter /= hb hL.
  have [c [dc mono]] := IH (fun b => col (g b)) _ sF hF.
  exists (map g c); split; first by rewrite (g248_dicycle_map gi ga).
  by move=> v w /mapP [v' v'c ->] /mapP [w' w'c ->]; exact: mono.
pose g1 (b : g248_S k) : g248_S k.+1 := inl (exist _ (inr b) isT).
pose g2 (b : g248_S k) : g248_S k.+1 := inr b.
have g1i : injective g1 by move=> u v [].
have g2i : injective g2 by move=> u v [].
have g1a : forall u v, (g1 u --> g1 v) = (u --> v) by [].
have g2a : forall u v, (g2 u --> g2 v) = (u --> v) by [].
case: (boolP [exists b, col (g1 b) == c0]) => [/existsP [b1 /eqP e1] | /existsPn n1]; last by apply: lift g1i g1a _.
case: (boolP [exists b, col (g2 b) == c0]) => [/existsP [b2 /eqP e2] | /existsPn n2]; last by apply: lift g2i g2a _.
(* the apex, a vertex of the copy for b and one of the copy for c share a colour: a -> B -> C -> a *)
exists [:: x; g2 b2; g1 b1]; split; first by [].
by move=> v w; rewrite !inE => /or3P [] /eqP -> /or3P [] /eqP ->; rewrite ?e1 ?e2.
Qed.

Lemma g248_S_not_dicolorable (k : nat) : ~~ dicolorableb (g248_S k) k.
Proof.
apply/negP => /existsP [col /forallP ac].
have sz : (size (iota 0 k) <= k)%N by rewrite size_iota.
have inL : forall v, val (col v) \in iota 0 k by move=> v; rewrite mem_iota add0n ltn_ord.
have [c [dc mono]] := @g248_S_mono k (fun v => val (col v)) (iota 0 k) sz inL.
case: c dc mono => [|x t] dc mono; first by case/and3P: dc.
have hall : all (mem [set v | col v == col x]) (x :: t).
  apply/allP => v vc.
  by rewrite !inE; apply/eqP/ord_inj; apply: mono => //; rewrite inE eqxx.
by have := g248_not_acyclic_induced dc hall; rewrite ac.
Qed.

(** ** The class of tournaments on at most three vertices *)
Definition g248_C3le (D : diGraphType) : Prop := is_tournament D /\ (#|D| <= 3)%N.

Lemma g248_is_tournament (T : tournament) : is_tournament T.
Proof. by split; [exact: arcxx | exact: arc_or | exact: arc_asym]. Qed.

Lemma g248_C3le_hereditary : x248_hereditary g248_C3le.
Proof.
move=> D S [[irr tot asy] c3]; split; last by rewrite card_sig; exact: leq_trans (max_card _) c3.
split=> [u|u v|u v]; rewrite ?sub_arcE.
- exact: irr.
- by move=> uv; apply: tot; rewrite val_eqE.
- exact: asy.
Qed.

Lemma g248_C3le_tournament (D : diGraphType) : g248_C3le D -> is_tournament D.
Proof. by case. Qed.

Lemma g248_S_closure (k : nat) : x248_subst_closure g248_C3le (g248_S k).
Proof.
elim: k => [|k IH] /=.
  by apply: x248_sc_base; split; [exact: (g248_is_tournament (TT 1)) | rewrite card_ord].
apply: x248_sc_step => //; apply: x248_sc_step => //.
by apply: x248_sc_base; split; [exact: (g248_is_tournament C3) | rewrite card_ord].
Qed.

(** ** The dichromatic number x221_dichro against its range and a colouring *)
Lemma g248_bigmin_le (n m : nat) (P : pred 'I_n) (F : 'I_n -> nat) (i : 'I_n) :
  P i -> (\big[minn/m]_(j | P j) F j <= F i)%N.
Proof.
move=> Pi; rewrite -big_filter.
have : i \in [seq j <- index_enum 'I_n | P j] by rewrite mem_filter Pi mem_index_enum.
elim: [seq j <- index_enum 'I_n | P j] => //= j s IH; rewrite big_cons inE => /orP [/eqP <- | /IH h].
  exact: geq_minl.
exact: leq_trans (geq_minr _ _) h.
Qed.

Lemma g248_dichro_le_card (D : diGraphType) : (x221_dichro D <= #|D|)%N.
Proof.
rewrite /x221_dichro; elim/big_ind: _ => // [x y hx _ | i _]; first exact: leq_trans (geq_minl x y) hx.
by rewrite -ltnS ltn_ord.
Qed.

Lemma g248_dichro_le_dicol (D : diGraphType) (B : nat) : dicolorableb D B -> (x221_dichro D <= B)%N.
Proof.
move=> hB; case: (leqP B #|D|) => [BD | DB]; last exact: leq_trans (g248_dichro_le_card D) (ltnW DB).
have := @g248_bigmin_le #|D|.+1 #|D| (fun k : 'I_#|D|.+1 => dicolorableb D k) (fun k => k) (Ordinal (BD : B < #|D|.+1)) hB.
by [].
Qed.

Lemma g248_C3le_poly : x248_poly_dic_bounded g248_C3le.
Proof. by exists 3, 0 => D [_ c3]; rewrite expn0 muln1; exact: leq_trans (g248_dichro_le_card D) c3. Qed.

Lemma g248_C3le_dic : x248_dic_bounded g248_C3le.
Proof. by exists (fun _ => 3) => D [_ c3]; exact: leq_trans (g248_dichro_le_card D) c3. Qed.

Lemma g248_C3le_oriented (D : diGraphType) : g248_C3le D -> oriented_dg D.
Proof. by case=> [[_ _ asy] _]. Qed.

(** ** Row arxiv:2310.04265#01 *)
Definition g248_poly_hyp_claim : Prop :=
  [/\ x248_hereditary g248_C3le, (forall D, g248_C3le D -> is_tournament D), x248_poly_dic_bounded g248_C3le &
      (poly_chi_bounded_tournaments_subst_statement -> x248_poly_dic_bounded (x248_subst_closure g248_C3le))].

Theorem g248_poly_hyp_inhabited : g248_poly_hyp_claim.
Proof.
split; [exact: g248_C3le_hereditary | exact: g248_C3le_tournament | exact: g248_C3le_poly |].
by move=> h; exact: h _ g248_C3le_hereditary g248_C3le_tournament g248_C3le_poly.
Qed.

(** The strengthened conclusion, one constant bound on the closure, is false: the closure of the tournaments on at most
    three vertices contains S_k (not k-dicolourable).  It implies the row (c = B, d = 0). *)
Definition g248_poly_constant_bound : Prop :=
  forall C : diGraphType -> Prop, x248_hereditary C -> (forall D, C D -> is_tournament D) ->
    x248_poly_dic_bounded C -> dichromatic_bounded (x248_subst_closure C).

Definition g248_poly_ntt_claim : Prop :=
  ~ g248_poly_constant_bound /\ (g248_poly_constant_bound -> poly_chi_bounded_tournaments_subst_statement).

Theorem g248_poly_not_trivially_true : g248_poly_ntt_claim.
Proof.
split.
- move=> h; have [B hB] := h _ g248_C3le_hereditary g248_C3le_tournament g248_C3le_poly.
  by have := g248_S_not_dicolorable B; rewrite hB //; exact: g248_S_closure.
- move=> h C hC tC pC; have [B hB] := h C hC tC pC; exists B, 0 => D cD.
  by rewrite expn0 muln1; exact: g248_dichro_le_dicol (hB D cD).
Qed.

(** ** Row arxiv:2310.04265#11 *)
Definition g248_dsubst_hyp_claim : Prop :=
  [/\ x248_hereditary g248_C3le, (forall D, g248_C3le D -> oriented_dg D), x248_dic_bounded g248_C3le &
      (chi_bounded_digraphs_subst_statement -> x248_dic_bounded (x248_subst_closure g248_C3le))].

Theorem g248_dsubst_hyp_inhabited : g248_dsubst_hyp_claim.
Proof.
split; [exact: g248_C3le_hereditary | exact: g248_C3le_oriented | exact: g248_C3le_dic |].
by move=> h; exact: h _ g248_C3le_hereditary g248_C3le_oriented g248_C3le_dic.
Qed.

Definition g248_dsubst_constant_bound : Prop :=
  forall C : diGraphType -> Prop, x248_hereditary C -> (forall D, C D -> oriented_dg D) ->
    x248_dic_bounded C -> dichromatic_bounded (x248_subst_closure C).

Definition g248_dsubst_ntt_claim : Prop :=
  ~ g248_dsubst_constant_bound /\ (g248_dsubst_constant_bound -> chi_bounded_digraphs_subst_statement).

Theorem g248_dsubst_not_trivially_true : g248_dsubst_ntt_claim.
Proof.
split.
- move=> h; have [B hB] := h _ g248_C3le_hereditary g248_C3le_oriented g248_C3le_dic.
  by have := g248_S_not_dicolorable B; rewrite hB //; exact: g248_S_closure.
- move=> h C hC oC dC; have [B hB] := h C hC oC dC; exists (fun _ => B) => D cD.
  exact: g248_dichro_le_dicol (hB D cD).
Qed.

(** ** Row arxiv:2310.04265#05 *)
Lemma g248_edgeless_forest (G : sgraph) : (forall x y : G, ~~ (x -- y)) -> is_forest [set: G].
Proof.
move=> noE x y p q [ip _] [iq _].
have xy : x = y.
  case/connectP: (Path_connect p) => -[_ -> //|z s] /= /andP[xz _].
  by case/negP: (noE x z).
move: p q ip iq; rewrite -xy => p q ip iq.
by rewrite (irredxx ip) (irredxx iq).
Qed.

Lemma g248_TT1_forest : exists p : {perm (TT 1 : tournament)}, is_forest [set: backedge p].
Proof.
exists 1%g; apply: g248_edgeless_forest => x y.
by rewrite (fintype.ord1 (x : 'I_1)) (fintype.ord1 (y : 'I_1)) backedgeE ltp_irrefl.
Qed.

Definition g248_binding_hyp_claim : Prop :=
  (exists p : {perm (TT 1 : tournament)}, is_forest [set: backedge p]) /\
  (chi_binding_iff_forest_backedge_statement ->
     exists f : nat -> nat, forall T : tournament, ind_free (TT 1 : tournament) T -> (x221_dichro T <= f (omegabar T))%N).

Theorem g248_binding_hyp_inhabited : g248_binding_hyp_claim.
Proof. by split; [exact: g248_TT1_forest | move=> h; apply/(h (TT 1 : tournament)); exact: g248_TT1_forest]. Qed.

(** Contract form: the only-if direction with its hypothesis (H is dic-binding) dropped, "every tournament has a forest
    backedge graph", with the if direction kept; it implies the row and fails at QR7 (domination number 3, l.494). *)
Definition g248_binding_no_hyp : Prop :=
  forall H : tournament,
    ((exists p : {perm H}, is_forest [set: backedge p]) ->
       exists f : nat -> nat, forall T : tournament, ind_free H T -> (x221_dichro T <= f (omegabar T))%N) /\
    (exists p : {perm H}, is_forest [set: backedge p]).

Definition g248_binding_ntt_claim : Prop :=
  ~ g248_binding_no_hyp /\ (g248_binding_no_hyp -> chi_binding_iff_forest_backedge_statement).

Theorem g248_binding_not_trivially_true : g248_binding_ntt_claim.
Proof.
split; first by move=> h; have [_ [p hp]] := h (g248_qr7 : tournament); exact: g248_qr7_no_forest hp.
by move=> h H; have [hRL hR] := h H; split=> // _.
Qed.

(** ** Row arxiv:2310.04265#00 *)
Definition g248_orderings_hyp_claim : Prop :=
  omegabar C3 = 2 /\
  (omega_dic_orderings_statement ->
     exists p : {perm C3}, omegab_at p = 2 /\ χ([set: backedge p]) = x221_dichro C3).

Theorem g248_orderings_hyp_inhabited : g248_orderings_hyp_claim.
Proof. by split; [exact: omegabar_C3 | move=> h; rewrite -omegabar_C3; exact: h]. Qed.

(** Contract form: "exists an ordering" strengthened to "every ordering"; it implies the row (the identity) and fails at TT 2
    under the reversed order (one back edge, omega 2, against omegabar 1). *)
Definition g248_orderings_every : Prop :=
  forall (T : tournament) (p : {perm T}), omegab_at p = omegabar T /\ χ([set: backedge p]) = x221_dichro T.

Definition g248_orderings_ntt_claim : Prop :=
  ~ g248_orderings_every /\ (g248_orderings_every -> omega_dic_orderings_statement).

Theorem g248_orderings_not_trivially_true : g248_orderings_ntt_claim.
Proof.
split; last by move=> h T; exists 1%g; exact: h.
move=> h; pose p : {perm (TT 2 : tournament)} := tperm ord0 ord1.
have [e _] := h _ p; move: e; rewrite omegabar_TT // => e.
have : (2 <= omegab_at p)%N; last by rewrite e.
rewrite /omegab_at; apply: (@omega_ge2 (backedge p) [set: backedge p] ord0 ord1); rewrite ?inE //.
by rewrite backedgeE /ltp !enum_rank_ord /= tpermL tpermR.
Qed.

(** ** Row arxiv:2310.04265#08 *)
Lemma g248_C3_out (v : C3) : (omegabar (sub_tournament [set w | v --> w]) <= 1)%N.
Proof.
have cS : (#|[set w | v --> w]| <= 2)%N.
  have : [set w | v --> w] \subset [set~ v] by apply/subsetP => w; rewrite !inE => /arc_neq; rewrite eq_sym.
  by move/subset_leq_card; rewrite cardsC1 card_C3.
case: (posnP #|sub_tournament [set w | v --> w]|) => [/omegabar_nil -> // | pos].
by rewrite omegabar_card_le2 // pos /= card_sig.
Qed.

Definition g248_local_hyp_claim : Prop :=
  (forall v : C3, (omegabar (sub_tournament [set w | v --> w]) <= 1)%N) /\
  (local_to_global_omegabar_statement ->
     exists g : nat -> nat, forall T : tournament,
       (forall v : T, (omegabar (sub_tournament [set w | v --> w]) <= 1)%N) -> (omegabar T <= g 1)%N).

Theorem g248_local_hyp_inhabited : g248_local_hyp_claim.
Proof. by split; [exact: g248_C3_out | case=> g hg; exists g => T; exact: hg]. Qed.

(** Contract form: g fixed to the identity; it implies the row and fails at C3 (out-neighbourhoods of omegabar 1,
    omegabar C3 = 2). *)
Definition g248_local_identity : Prop :=
  forall (t : nat) (T : tournament),
    (forall v : T, (omegabar (sub_tournament [set w | v --> w]) <= t)%N) -> (omegabar T <= t)%N.

Definition g248_local_ntt_claim : Prop :=
  ~ g248_local_identity /\ (g248_local_identity -> local_to_global_omegabar_statement).

Theorem g248_local_not_trivially_true : g248_local_ntt_claim.
Proof.
split; last by move=> h; exists id.
by move=> h; have := h 1 C3 g248_C3_out; rewrite omegabar_C3.
Qed.

(** ** Helper sanity *)

(** x248_backedge_rel / x248_backedge: TT 2 has one back edge under the reversed order and none under the identity;
    on tournaments the edge relation is order.v's backedge. *)
Definition g248_backedge_helper_claim : Prop :=
  [/\ x248_backedge_rel (tperm ord0 ord1 : {perm (TT 2 : diGraphType)}) ord0 ord1,
      ~~ x248_backedge_rel (1%g : {perm (TT 2 : diGraphType)}) ord0 ord1 &
      forall (T : tournament) (p : {perm T}) (u v : T), @edge_rel (x248_backedge p) u v = @edge_rel (backedge p) u v].

Theorem g248_backedge_helper_sanity : g248_backedge_helper_claim.
Proof.
split=> //.
- by rewrite /x248_backedge_rel /= /ltp !enum_rank_ord /= tpermL tpermR.
- by rewrite /x248_backedge_rel /= /ltp !perm1 !enum_rank_ord.
Qed.

(** x248_omegab_dg: omegabar on tournaments; 2 on C3 and 1 on TT 1. *)
Definition g248_omegab_dg_helper_claim : Prop :=
  [/\ forall T : tournament, x248_omegab_dg T = omegabar T, x248_omegab_dg C3 = 2 & x248_omegab_dg (TT 1) = 1].

Theorem g248_omegab_dg_helper_sanity : g248_omegab_dg_helper_claim.
Proof. by split; [exact: g248_omegab_dg_tournament | exact: omegabar_C3 | exact: omegabar_TT]. Qed.

(** A loop at every vertex and no other arc: no dicolouring at all (dichromatic value #|D|), no back edge (omega 1). *)
Definition g248_loops (n : nat) : Type := 'I_n.
HB.instance Definition _ (n : nat) := Finite.on (g248_loops n).
HB.instance Definition _ (n : nat) := HasArc.Build (g248_loops n) [rel u v : 'I_n | u == v].

Definition g248_loopy (D : diGraphType) : Prop := forall u v : D, (u --> v) = (u == v).

Lemma g248_loops_loopy (n : nat) : g248_loopy (g248_loops n).
Proof. by []. Qed.

Lemma g248_loops_dichro (n : nat) : x221_dichro (g248_loops n.+1) = n.+1.
Proof.
rewrite /x221_dichro big_pred0 ?card_ord // => k.
apply/negbTE/negP => /existsP [col /forallP ac].
have v0 : (ord0 : g248_loops n.+1) \in [set v | col v == col ord0] by rewrite inE.
have := @loop_not_acyclicb _ (Sub (ord0 : g248_loops n.+1) v0 : induced_digraph _).
by rewrite ac => /(_ isT).
Qed.

Lemma g248_loops_omega (n : nat) : x248_omegab_dg (g248_loops n.+1) = 1.
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split.
  apply: omega_le1 => u v _ _; rewrite /edge_rel /= /x248_backedge_rel /=.
  have a : forall x y : g248_loops n.+1, (x --> y) = (x == y) by [].
  by case: (eqVneq u v) => [->|uv]; rewrite ?ltp_irrefl // !a eq_sym (negbTE uv) !andbF.
by apply: omega_ge1; apply/set0Pn; exists ord0; rewrite inE.
Qed.

Definition g248_dic_bounded_helper_claim : Prop :=
  x248_dic_bounded g248_C3le /\ ~ x248_dic_bounded g248_loopy.

Theorem g248_dic_bounded_helper_sanity : g248_dic_bounded_helper_claim.
Proof.
split; first exact: g248_C3le_dic.
move=> [f hf]; have := hf _ (@g248_loops_loopy (f 1).+1).
by rewrite g248_loops_dichro g248_loops_omega ltnn.
Qed.

Definition g248_poly_helper_claim : Prop :=
  x248_poly_dic_bounded g248_C3le /\ ~ x248_poly_dic_bounded g248_loopy.

Theorem g248_poly_helper_sanity : g248_poly_helper_claim.
Proof.
split; first exact: g248_C3le_poly.
move=> [c [d hf]]; have := hf _ (@g248_loops_loopy c.+1).
by rewrite g248_loops_dichro g248_loops_omega exp1n muln1 ltnn.
Qed.

(** x248_hereditary: the tournaments on at most three vertices, not the one-vertex digraphs (the empty set induces
    an empty digraph). *)
Definition g248_hereditary_helper_claim : Prop :=
  x248_hereditary g248_C3le /\ ~ x248_hereditary (fun D : diGraphType => #|D| = 1).

Theorem g248_hereditary_helper_sanity : g248_hereditary_helper_claim.
Proof.
split; first exact: g248_C3le_hereditary.
by move=> h; have := h (TT 1 : diGraphType) set0 (card_ord 1); rewrite card_sig cards0.
Qed.

(** x248_subst / x248_subst_rel: substituting TT 2 for the vertex 2 of C3 (0 -> 1 -> 2 -> 0) gives four vertices;
    2 -> 0 becomes an arc from each new vertex to 0, 0 -> 2 is not an arc, and TT 2's arc is kept. *)
Definition g248_subst_helper_claim : Prop :=
  [/\ #|(x248_subst (g248_c : (C3 : diGraphType)) (TT 2 : diGraphType) : diGraphType)| = 4,
      x248_subst_rel (inr ord0 : x248_subst (g248_c : (C3 : diGraphType)) (TT 2 : diGraphType)) (inl (exist _ (@Ordinal 3 0 isT : C3) isT)),
      ~~ x248_subst_rel (inl (exist _ (@Ordinal 3 0 isT : C3) isT) : x248_subst (g248_c : (C3 : diGraphType)) (TT 2 : diGraphType)) (inr ord0) &
      x248_subst_rel (inr ord0 : x248_subst (g248_c : (C3 : diGraphType)) (TT 2 : diGraphType)) (inr ord1)].

Theorem g248_subst_helper_sanity : g248_subst_helper_claim.
Proof.
split=> //.
by rewrite card_sum card_sig cardC1 card_C3 card_ord.
Qed.

(** x248_subst_closure: S_2 is in the closure of the tournaments on at most three vertices; the empty class has an empty
    closure. *)
Definition g248_closure_helper_claim : Prop :=
  x248_subst_closure g248_C3le (g248_S 2) /\ forall D : diGraphType, ~ x248_subst_closure (fun _ => False) D.

Theorem g248_closure_helper_sanity : g248_closure_helper_claim.
Proof. by split; [exact: g248_S_closure | move=> D; elim]. Qed.

