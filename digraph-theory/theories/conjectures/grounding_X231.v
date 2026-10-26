(** * Digraph.conjectures.grounding_X231 -- grounding certificates of wave X231.

    The row of X231.v gets a [g231_fc_hyp_inhabited] certificate (the complete digraphs K*_n
    are strong digraphs of every size, and the row then promises logarithmic forward covers
    of them) and a [g231_fc_not_trivially_true] certificate (without the strong-connectivity
    guard the statement fails: the arcless digraph on two or more vertices has no forward
    cover at all). Two helper-sanity certificates pin the x231 helpers: a forward walk raises
    the ranking, forward connection is symmetric in the pair, and in K*_n every pair is
    forward connected in the index ordering; one ordering covers K*_n, the empty family covers
    no digraph on two or more vertices, and a non-injective ranking is not an ordering. The
    row itself is refuted in applications/forward_cover_disproof.v. Everything is closed by
    [Qed]; see the [Print Assumptions] audit at the end. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph strong X231.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Witnesses: the complete digraph K*_n and the arcless digraph E_n on ['I_n] *)
Section G231Witnesses.
Variable n : nat.

Definition g231_K : Type := 'I_n.
HB.instance Definition _ := Finite.on g231_K.
HB.instance Definition _ := HasArc.Build g231_K (fun u v : 'I_n => u != v).

Definition g231_E : Type := 'I_n.
HB.instance Definition _ := Finite.on g231_E.
HB.instance Definition _ := HasArc.Build g231_E (fun _ _ : 'I_n => false).

Lemma g231_K_card : #|{: g231_K}| = n.
Proof. exact: card_ord. Qed.

Lemma g231_E_card : #|{: g231_E}| = n.
Proof. exact: card_ord. Qed.

Lemma g231_K_strong : strongb g231_K.
Proof.
apply/strongP => x y; case: (eqVneq x y) => [->|xy]; first exact: connect0.
exact: connect1.
Qed.

(** In K*_n every pair of distinct vertices is forward connected in the index ordering. *)
Lemma g231_K_pair (x y : g231_K) :
  x != y -> x231_forward_pair (fun v : g231_K => nat_of_ord v) x y.
Proof.
move=> xy; rewrite /x231_forward_pair.
case: (ltngtP (nat_of_ord x) (nat_of_ord y)) => [lt|lt|/val_inj eq].
- apply/orP; left; apply: connect1; rewrite /x231_forward_arc lt andbT.
  exact: xy.
- apply/orP; right; apply: connect1; rewrite /x231_forward_arc lt andbT.
  by change (y != x); rewrite eq_sym.
- by move: xy; rewrite eq eqxx.
Qed.

(** E_n has no forward walk between distinct vertices. *)
Lemma g231_E_connect (r : g231_E -> nat) (x y : g231_E) :
  connect (x231_forward_arc r) x y -> x = y.
Proof. by case/connectP => -[|z p] //= /andP []. Qed.

End G231Witnesses.

(** ** Certificates: row arxiv:2304.03567#04 *)
Definition g231_fc_hyp_claim : Prop :=
  (forall n : nat, strongb (g231_K n) /\ #|{: g231_K n}| = n) /\
  (logarithmic_forward_cover_statement ->
     exists c n0 : nat, forall n : nat, n0 <= n ->
       exists rs : seq {ffun g231_K n -> nat},
         x231_forward_cover rs /\ size rs <= c * trunc_log 2 n).

Theorem g231_fc_hyp_inhabited : g231_fc_hyp_claim.
Proof.
split; first by move=> n; split; [exact: g231_K_strong | exact: g231_K_card].
move=> [c [n0 h]]; exists c, n0 => n hn.
have hn' : n0 <= #|{: g231_K n}| by rewrite g231_K_card.
by have := h (g231_K n) (g231_K_strong n) hn'; rewrite g231_K_card.
Qed.

Definition g231_fc_unguarded : Prop :=
  exists c n0 : nat, forall D : diGraphType, n0 <= #|D| ->
    exists rs : seq {ffun D -> nat}, x231_forward_cover rs /\ size rs <= c * trunc_log 2 #|D|.

Definition g231_fc_ntt_claim : Prop :=
  ~ g231_fc_unguarded /\ (g231_fc_unguarded -> logarithmic_forward_cover_statement).

Theorem g231_fc_not_trivially_true : g231_fc_ntt_claim.
Proof.
split; last by move=> [c [n0 h]]; exists c, n0 => D _; exact: h.
move=> [c [n0 h]].
have hn : n0 <= #|{: g231_E n0.+2}| by rewrite g231_E_card ltnW.
have [rs [[_ hcov] _]] := h (g231_E n0.+2) hn.
have := hcov (@Ordinal n0.+2 0 isT) (@Ordinal n0.+2 1 isT) isT.
case/hasP => r _ /orP [] /g231_E_connect /(congr1 val) //.
Qed.

(** ** Certificates: helper sanity *)
Definition g231_forward_sanity_claim : Prop :=
  [/\ forall (D : diGraphType) (r : D -> nat) (x y : D),
        connect (x231_forward_arc r) x y -> x = y \/ r x < r y,
      forall (D : diGraphType) (r : D -> nat) (x y : D),
        x231_forward_pair r x y = x231_forward_pair r y x
    & forall (n : nat) (x y : g231_K n),
        x != y -> x231_forward_pair (fun v : g231_K n => nat_of_ord v) x y].

Theorem g231_forward_sanity : g231_forward_sanity_claim.
Proof.
split.
- move=> D r x y /connectP [p pth ->] {y}.
  elim: p x pth => [|z p IH] x /=; first by left.
  case/andP => /andP [_ xz] pth; right.
  by case: (IH z pth) => [<- //|]; exact: ltn_trans.
- by move=> D r x y; rewrite /x231_forward_pair orbC.
- by move=> n x y; exact: g231_K_pair.
Qed.

Definition g231_cover_sanity_claim : Prop :=
  [/\ forall n : nat, x231_forward_cover [:: [ffun v : g231_K n => nat_of_ord v]],
      forall D : diGraphType, 2 <= #|D| -> ~ x231_forward_cover ([::] : seq {ffun D -> nat})
    & ~ x231_forward_cover [:: [ffun v : g231_K 2 => 0]]].

Theorem g231_cover_sanity : g231_cover_sanity_claim.
Proof.
split.
- move=> n; split.
    rewrite /= andbT; apply/injectiveP => x y; rewrite !ffunE; exact: val_inj.
  move=> x y xy /=; rewrite orbF.
  have e : x231_forward_arc [ffun v : g231_K n => nat_of_ord v] =2
           x231_forward_arc (fun v : g231_K n => nat_of_ord v).
    by move=> u v; rewrite /x231_forward_arc !ffunE.
  rewrite /x231_forward_pair !(eq_connect e); exact: g231_K_pair.
- move=> D /card_gt1P [x [y [_ _ xy]]] [_ hcov].
  by have := hcov x y xy.
- move=> [/= /andP [/injectiveP inj _] _].
  by have := inj (@Ordinal 2 0 isT) (@Ordinal 2 1 isT); rewrite !ffunE => /(_ erefl) /(congr1 val).
Qed.

Print Assumptions g231_fc_hyp_inhabited.
Print Assumptions g231_fc_not_trivially_true.
Print Assumptions g231_forward_sanity.
Print Assumptions g231_cover_sanity.
