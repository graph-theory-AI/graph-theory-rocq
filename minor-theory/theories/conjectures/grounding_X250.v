(** * Minor.conjectures.grounding_X250 -- grounding certificates of wave X250.

    For the one row (arxiv:2004.14789#00, a synonym of X220's
    polynomial_expansion_bounded_twin_width_statement): hyp_inhabited (the edgeless graphs have
    polynomial expansion, with the zero polynomial, and the statement then yields its conclusion
    for them) and not_trivially_true in the contract form of meta/EXPANSION_PLAN.md 4.4: the
    variant dropping the polynomial-expansion hypothesis is false and implies the row.  The
    variant fails for the class of all graphs: in the parity graph on the subsets of 'I_(m+1)
    (x -- y when x <> y and |x :&: y| is odd) any two vertices differ on exactly 2^m vertices,
    so the first merge of any contraction sequence already creates a part with at least
    2^m - 2 red neighbours.  The wave has no local helper, so no helper_sanity certificate. *)

From GTBase Require Import base.
From GraphTheory Require Import preliminaries minor.
From Minor.conjectures Require Import X220 X250.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The edgeless graphs have polynomial expansion *)

Lemma g250_edgeless_poly_expansion :
  x220_polynomial_expansion (fun G : sgraph => stable [set: G]).
Proof.
exists [::] => G sG r H [B [ctr [[_ _ _ hE] _ _]]].
suff -> : E(H) = set0 by rewrite cards0.
apply/setP => e; rewrite inE; apply/negbTE/negP => /edgesP[u [v [_ uv]]].
case/neighborP: (hE u v uv) => p [q [_ _ pq]].
by move/stableP: sG => /(_ p q (in_setT p) (in_setT q)); rewrite pq.
Qed.

(** ** The parity graph *)

(** x -- y in the parity graph when x <> y and |x :&: y| is odd. *)
Definition g250_par_rel (k : nat) : rel {set 'I_k} :=
  fun x y => (x != y) && odd #|x :&: y|.

Lemma g250_par_sym (k : nat) : symmetric (@g250_par_rel k).
Proof. by move=> x y; rewrite /g250_par_rel eq_sym setIC. Qed.

Lemma g250_par_irrefl (k : nat) : irreflexive (@g250_par_rel k).
Proof. by move=> x; rewrite /g250_par_rel eqxx. Qed.

Definition g250_par_graph (k : nat) : sgraph := SGraph (@g250_par_sym k) (@g250_par_irrefl k).

(** The involution z |-> z Δ {a}. *)
Definition g250_flip (k : nat) (a : 'I_k) (z : {set 'I_k}) : {set 'I_k} :=
  if a \in z then z :\ a else a |: z.

Lemma g250_flipK (k : nat) (a : 'I_k) : involutive (g250_flip a).
Proof.
move=> z; rewrite /g250_flip; case: (boolP (a \in z)) => az.
- by rewrite setD11 setD1K.
- by rewrite setU11 setU1K.
Qed.

Lemma g250_odd_flip_in (k : nat) (a : 'I_k) (w z : {set 'I_k}) :
  a \in w -> odd #|w :&: g250_flip a z| = ~~ odd #|w :&: z|.
Proof.
move=> aw; rewrite /g250_flip; case: (boolP (a \in z)) => az.
- by rewrite setIDA [in RHS](cardsD1 a) !inE aw az /= add0n negbK.
- have -> : w :&: (a |: z) = a |: (w :&: z) by rewrite setIUr (setIidPr _) // sub1set.
  by rewrite cardsU1 !inE (negbTE az) andbF.
Qed.

Lemma g250_flip_out (k : nat) (a : 'I_k) (w z : {set 'I_k}) :
  a \notin w -> w :&: g250_flip a z = w :&: z.
Proof.
move=> aw; apply/setP => b; rewrite /g250_flip; case: ifP => az; rewrite !inE;
  by case: (b =P a) => [->|]; rewrite ?(negbTE aw).
Qed.

(** The vertices z on which x and y disagree. *)
Definition g250_diff (k : nat) (x y : {set 'I_k}) : {set {set 'I_k}} :=
  [set z | odd #|x :&: z| != odd #|y :&: z|].

(** When a lies in exactly one of x and y, the flip at a exchanges the disagreement set with
    its complement, so it has half of the 2^(m+1) subsets. *)
Lemma g250_card_diff (m : nat) (x y : {set 'I_m.+1}) (a : 'I_m.+1) :
  a \in x -> a \notin y -> #|g250_diff x y| = 2 ^ m.
Proof.
move=> ax ay; set D := g250_diff x y.
have fD z : (g250_flip a z \in D) = (z \notin D).
  by rewrite !inE g250_odd_flip_in // g250_flip_out //; case: (odd _); case: (odd _).
have CD : ~: D = g250_flip a @^-1: D by apply/setP => z; rewrite in_setC [RHS]inE fD.
have := cardsC D; rewrite CD (card_preimset _ (inv_inj (g250_flipK a))).
rewrite -cardsT -powersetT card_powerset cardsT card_ord expnS addnn -mul2n.
by move/eqP; rewrite eqn_mul2l => /eqP.
Qed.

(** The parity graph on the subsets of 'I_(m+1) has twin-width above d when d + 2 < 2^m. *)
Lemma g250_par_graph_tww (m d : nat) :
  d.+2 < 2 ^ m -> ~ x220_twin_width_le (g250_par_graph m.+1) d.
Proof.
move=> hd [s [hp hl hdeg]].
case: s hp hl hdeg => [|Q s] /= hp hl hdeg.
  move: hl; rewrite /x220_singletons (card_imset _ (@set1_inj _)).
  by rewrite -cardsT -powersetT card_powerset cardsT card_ord leqNgt (@ltn_exp2l 2 0 m.+1).
case/andP: hp => /existsP[X /andP[XP /existsP[Y /andP[YP /andP[XY /eqP QE]]]]] _.
case/imsetP: XP => x _ Xx; case/imsetP: YP => y _ Yy; subst X Y.
have xy : x != y by apply: contraNneq XY => ->.
have hX : x220_red_deg Q [set x; y] <= d.
  by apply: hdeg; rewrite ?QE ?setU11 // !inE eqxx orbT.
(* the vertices on which x and y differ: 2 ^ m of them *)
have cD : #|g250_diff x y| = 2 ^ m.
  case: (pickP (fun a => (a \in x) != (a \in y))) => [a ha | h]; last first.
    by case/eqP: xy; apply/setP => a; apply/eqP; rewrite -[_ == _]negbK h.
  case: (boolP (a \in x)) ha => ax /= ha.
  - by apply: (@g250_card_diff m x y a ax); move: ha; case: (a \in y).
  - have -> : g250_diff x y = g250_diff y x by apply/setP => z; rewrite !inE eq_sym.
    by apply: (@g250_card_diff m y x a) => //; move: ha; case: (a \in y).
have c2 : #|g250_diff x y| <= (#|g250_diff x y :\ x :\ y|).+2.
  rewrite (cardsD1 x (g250_diff x y)) (cardsD1 y (g250_diff x y :\ x)).
  by rewrite addnA addnC -addn2 leq_add2l (leq_add (leq_b1 _) (leq_b1 _)).
(* each other such vertex z gives a singleton part red to the merged part [set x; y] *)
have c3 : #|g250_diff x y :\ x :\ y| <= x220_red_deg Q [set x; y].
  rewrite /x220_red_deg -(card_imset _ (@set1_inj _)).
  apply: subset_leq_card; apply/subsetP => _ /imsetP[z zD ->].
  move: zD; rewrite !inE => /and3P[zy zx zo].
  have e (u : g250_par_graph m.+1) : u -- (z : g250_par_graph m.+1) = (u != z) && odd #|u :&: z|.
    by [].
  apply/and3P; split.
  - rewrite QE !inE (inj_eq (@set1_inj _)) zy (inj_eq (@set1_inj _)) zx /=.
    by apply/orP; right; exact: imset_f.
  - apply: contraNneq zx => /setP/(_ x); rewrite !inE eqxx /= => h.
    by rewrite eq_sym h.
  - have ex : x -- z = odd #|x :&: z| by rewrite e eq_sym zx.
    have ey : y -- z = odd #|y :&: z| by rewrite e eq_sym zy.
    rewrite /x220_red_pair; case: (boolP (odd #|x :&: z|)) zo => ox zo.
    + apply/andP; split; apply/existsP; [exists x | exists y]; rewrite !inE eqxx ?orbT /=;
        apply/existsP; exists z; rewrite !inE eqxx /=.
      * by rewrite ex.
      * by rewrite ey; move: zo; case: (odd _).
    + apply/andP; split; apply/existsP; [exists y | exists x]; rewrite !inE eqxx ?orbT /=;
        apply/existsP; exists z; rewrite !inE eqxx /=.
      * by rewrite ey; move: zo; case: (odd _).
      * by rewrite ex.
have c4 : #|g250_diff x y| <= d.+2.
  by apply: (leq_trans c2); rewrite !ltnS; exact: leq_trans c3 hX.
by move: hd; rewrite -cD ltnNge c4.
Qed.

(** ** hyp_inhabited *)

Definition g250_hyp_claim : Prop :=
  x220_polynomial_expansion (fun G : sgraph => stable [set: G]) /\
  (polynomial_expansion_bounded_twin_width_duplicate_statement ->
     exists d : nat, forall G : sgraph, stable [set: G] -> x220_twin_width_le G d).

Theorem g250_hyp_inhabited : g250_hyp_claim.
Proof.
split; first exact: g250_edgeless_poly_expansion.
by move=> h; exact: h _ g250_edgeless_poly_expansion.
Qed.

(** ** not_trivially_true: the polynomial-expansion hypothesis dropped *)

Definition g250_any_class_bounded : Prop :=
  forall C : sgraph -> Prop, exists d : nat, forall G : sgraph, C G -> x220_twin_width_le G d.

Definition g250_ntt_claim : Prop :=
  ~ g250_any_class_bounded /\
  (g250_any_class_bounded -> polynomial_expansion_bounded_twin_width_duplicate_statement).

Theorem g250_not_trivially_true : g250_ntt_claim.
Proof.
split; last by move=> h C _; exact: h C.
move=> h; have [d hb] := h (fun _ : sgraph => True).
apply: (@g250_par_graph_tww d.+2 d); first by rewrite ltn_expl.
exact: hb.
Qed.
