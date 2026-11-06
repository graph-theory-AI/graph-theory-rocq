(** * Minor.conjectures.grounding_X293 -- grounding lemmas for wave X293.

    Qed-closed, axiom-free certificates for the row of [X293.v] (hyp_inhabited, not_trivially_true; X293 declares
    no helper, so no helper_sanity), its equivalence with X214's encoding of Hadwiger's conjecture
    ([g293_equiv_X214]) and with its form over proper minor-closed classes, the source's convention
    ([g293_proper_equiv]).  The hyp witness is the class of edgeless graphs at t = 1: it is minor-closed (an
    edge of a minor needs an edge between two branch sets) and satisfies both sides.  The ntt variant drops
    minor-closure; it fails at t = 1 for the class of graphs of chromatic number 3, which holds K_3 but not
    K_2.  They validate the statement and relate it to X214; they do not prove it (it is Hadwiger's conjecture). *)

From GraphTheory Require Import minor.
From GTBase Require Import base minor_classes.
From Minor.foundations Require Import minor_dec.
From Minor.conjectures Require Import X214 X293.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* The chromatic number of K_n is n (it is a clique). *)
Lemma g293_chi_K (n : nat) : χ([set: 'K_n]) = n.
Proof. by rewrite chi_clique ?Kn_clique // cardsT card_ord. Qed.

(* K_m is a minor of K_n when m <= n. *)
Lemma g293_minor_K_le (m n : nat) : m <= n -> minor 'K_n 'K_m.
Proof. by move=> le_mn; apply: (minor_of_clique _ (@Kn_clique n)); rewrite cardsT card_ord. Qed.

(* The row is equivalent to X214's Hadwiger statement (chi(G) = k -> K_k is a minor of G). *)
Lemma g293_equiv_X214 :
  hadwiger_minor_closed_class_statement <-> hadwiger_chromatic_clique_minor_statement.
Proof.
split.
- move=> S k G chiG; have [//|nmin] := minorP G 'K_k.
  exfalso; move: k chiG nmin => [|[|t]] chiG nmin.
  + apply: nmin; apply: (@minor_of_clique G set0 0) => //; by move=> x y; rewrite inE.
  + have := leq_chi [set: G]; rewrite chiG cardsT => /card_gt0P [x _]; apply: nmin.
    by apply: (@minor_of_clique G [set x] 1); [rewrite cards1 | exact: clique1].
  + have [_ h] := S t.+1 isT (fun H => ~ base.minor H 'K_t.+2)
      (fun G0 H0 nG0 mGH mHK => nG0 (minor_trans mGH mHK)).
    have nn : ~ ~ base.minor ('K_(t.+1 + 1)) ('K_t.+2).
      by rewrite addn1 => /(_ (g293_minor_K_le (leqnn _))).
    by have := h nn G nmin; rewrite chiG ltnn.
- move=> H214 t t1 C Cmin; split.
  + move=> chiC CK; have := chiC _ CK; by rewrite g293_chi_K addn1 ltnn.
  + move=> nCK G CG; rewrite leqNgt; apply/negP => lt_t.
    apply: nCK; apply: (Cmin G) => //.
    apply: minor_trans (H214 _ G erefl) _.
    by apply: g293_minor_K_le; rewrite addn1.
Qed.

(* The source's minor-closed classes are proper (arXiv:1710.02727v1, IslandsI4.tex l.57: not all graphs).  The row
   quantifies over every minor-closed class; it is equivalent to its proper-class form, since a class without
   K_(t+1) is proper and a class with K_(t+1) fails both sides. *)
Definition g293_proper_form : Prop :=
  forall t : nat, 1 <= t ->
  forall C : sgraph -> Prop,
    minor_closed C -> ~ (forall G : sgraph, C G) ->
    ((forall G : sgraph, C G -> χ([set: G]) <= t) <-> ~ C 'K_(t + 1)).

Lemma g293_proper_equiv : hadwiger_minor_closed_class_statement <-> g293_proper_form.
Proof.
split.
- by move=> S t t1 C Cmin _; exact: S t t1 C Cmin.
- move=> P t t1 C Cmin; split.
  + move=> chiC CK; have := chiC _ CK; by rewrite g293_chi_K addn1 ltnn.
  + move=> nCK; have [_ h] := P t t1 C Cmin (fun allC => nCK (allC _)); exact: h nCK.
Qed.

(* hyp: the edgeless graphs, a minor-closed class satisfying both sides at t = 1. *)
Definition g293_edgeless (G : sgraph) : Prop := forall x y : G, ~~ (x -- y).

Lemma g293_edgeless_minor_closed (G H : sgraph) : g293_edgeless G -> minor G H -> g293_edgeless H.
Proof.
move=> eG /minorRE [phi [_ _ _ hE]] x y; apply/negP => /hE /existsP [u /andP [_ /existsP [v /andP [_ uv]]]].
by move: (eG u v); rewrite uv.
Qed.

Lemma g293_edgeless_chi (G : sgraph) : g293_edgeless G -> χ([set: G]) <= 1.
Proof.
move=> eG; apply: leq_trans (@chiD1 G [set: G] [set: G] (introT (@stableP G [set: G]) (fun u v _ _ => eG u v))) _.
by rewrite setDv ltnS; apply: leq_trans (leq_chi _) _; rewrite cards0.
Qed.

Lemma g293_K2_not_edgeless : ~ g293_edgeless ('K_2).
Proof. move=> /(_ ord0 (Ordinal (isT : 1 < 2))); by rewrite /edge_rel /=. Qed.

(* The claim names the row (gate_contracts: a claim mentions every reference): at t = 1 and the edgeless class the
   statement gives its equivalence, whose two sides both hold there. *)
Definition g293_hmc_hyp_claim : Prop :=
  [/\ minor_closed g293_edgeless,
      (forall G : sgraph, g293_edgeless G -> χ([set: G]) <= 1),
      ~ g293_edgeless ('K_(1 + 1))
    & (hadwiger_minor_closed_class_statement ->
       ((forall G : sgraph, g293_edgeless G -> χ([set: G]) <= 1) <-> ~ g293_edgeless ('K_(1 + 1))))].

Theorem g293_hmc_hyp_inhabited : g293_hmc_hyp_claim.
Proof.
split; [exact: g293_edgeless_minor_closed | exact: g293_edgeless_chi | exact: g293_K2_not_edgeless |].
by move=> S; exact: S 1 isT g293_edgeless g293_edgeless_minor_closed.
Qed.

(* ntt: without minor-closure the row fails at t = 1 for the class of graphs of chromatic number 3. *)
Definition g293_hmc_no_closure : Prop :=
  forall t : nat, 1 <= t -> forall C : sgraph -> Prop,
    ((forall G : sgraph, C G -> χ([set: G]) <= t) <-> ~ C 'K_(t + 1)).

Definition g293_hmc_ntt_claim : Prop :=
  ~ g293_hmc_no_closure /\ (g293_hmc_no_closure -> hadwiger_minor_closed_class_statement).

Theorem g293_hmc_not_trivially_true : g293_hmc_ntt_claim.
Proof.
split.
- move=> /(_ 1 isT (fun G : sgraph => χ([set: G]) = 3)) [_ h].
  have nC : ~ (χ([set: 'K_(1 + 1)]) = 3) by rewrite g293_chi_K.
  by have := h nC ('K_3) (g293_chi_K 3); rewrite g293_chi_K.
- by move=> V t t1 C _; exact: V t t1 C.
Qed.
