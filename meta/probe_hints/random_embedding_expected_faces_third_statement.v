(** Counterexample probe: [random_embedding_expected_faces_third_statement]
    (X228, arxiv:2202.07746#00) is refutable, because it drops the source's
    CONNECTEDNESS hypothesis.  Witness: four disjoint edges (n = 8, one
    rotation system, four faces): 3 * 4 = 12 > 11 = (8 + 3) * 1. *)
From GTBase Require Import base.
From mathcomp Require Import fingroup perm.
From Topological.conjectures Require Import X228 grounding_X228.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition m8_rel : rel 'I_8 := fun x y => (x != y) && (x %/ 2 == y %/ 2).

Lemma m8_sym : symmetric m8_rel.
Proof. by move=> x y; rewrite /m8_rel eq_sym [x %/ 2 == _]eq_sym. Qed.

Lemma m8_irr : irreflexive m8_rel.
Proof. by move=> x; rewrite /m8_rel eqxx. Qed.

Definition M8 : sgraph := SGraph m8_sym m8_irr.

(** Two vertices of ['I_8] with the same quotient by 2 and the same parity are
    equal, so every vertex of [M8] has at most one neighbour. *)
Lemma div2_odd_inj (a b : nat) : a %/ 2 = b %/ 2 -> odd a = odd b -> a = b.
Proof. by move=> Hd Ho; rewrite (divn_eq a 2) (divn_eq b 2) Hd !modn2 Ho. Qed.

Lemma M8_deg1 (x y z : M8) : x -- y -> x -- z -> y = z.
Proof.
rewrite /edge_rel/= /m8_rel => /andP[xy /eqP dxy] /andP[xz /eqP dxz].
apply/val_inj/div2_odd_inj; first by rewrite -dxy dxz.
have odd_ne (a b : 'I_8) : a %/ 2 = b %/ 2 -> a != b -> odd a = ~~ odd b.
  move=> d ne; case: (boolP (odd a == odd b)) => [/eqP e|]; last first.
    by case: (odd a) (odd b) => [] [] //=.
  by move: ne; rewrite (val_inj (div2_odd_inj d e) : a = b) eqxx.
by rewrite (odd_ne y x _ _) ?(odd_ne z x _ _) // 1?eq_sym // 1?dxy 1?dxz.
Qed.

Lemma M8_card : #|M8| = 8.
Proof. by rewrite card_ord. Qed.

Lemma M8_nrot : x228_nrot M8 = 1.
Proof. by apply: x228_nrot_deg1; exact: M8_deg1. Qed.

(** ** Four distinct faces *)

Notation P8 := (@surface_edge_perm M8).

Lemma P8_invol : involutive P8.
Proof. by move=> d; rewrite !permE; exact: surface_rev_dartK. Qed.

Lemma expg_invol (i : nat) (d : surface_dart M8) :
  ((P8 ^+ i)%g d = d) \/ ((P8 ^+ i)%g d = P8 d).
Proof.
elim: i => [|i IH]; first by left; rewrite expg0 perm1.
by rewrite expgSr permM; case: IH => ->; [right|left; rewrite P8_invol].
Qed.

Lemma lt2i (i : 'I_4) : 2 * i < 8.
Proof. by case: i => -[|[|[|[|m]]]] Hm. Qed.

Lemma lt2i1 (i : 'I_4) : (2 * i).+1 < 8.
Proof. by case: i => -[|[|[|[|m]]]] Hm. Qed.

Definition va (i : 'I_4) : 'I_8 := Ordinal (lt2i i).
Definition vb (i : 'I_4) : 'I_8 := Ordinal (lt2i1 i).

Lemma va_div (i : 'I_4) : (va i) %/ 2 = i.
Proof. by rewrite /= mulKn. Qed.

Lemma vb_div (i : 'I_4) : (vb i) %/ 2 = i.
Proof. by rewrite /= -addn1 mulnC divnMDl // divn_small // addn0. Qed.

Lemma va_adj (i : 'I_4) : m8_rel (va i) (vb i).
Proof.
rewrite /m8_rel va_div vb_div eqxx andbT.
by apply/eqP => /(f_equal val) /= /eqP; rewrite eqn_leq ltnn andbF.
Qed.

Definition dt (i : 'I_4) : surface_dart M8 := exist _ (va i, vb i) (va_adj i).

Definition qd (d : surface_dart M8) : nat := (sval d).1 %/ 2.

Lemma qd_dt (i : 'I_4) : qd (dt i) = i.
Proof. by rewrite /qd /= va_div. Qed.

Lemma qd_rev (i : 'I_4) : qd (P8 (dt i)) = i.
Proof. by rewrite /qd permE /= vb_div. Qed.

Lemma porbit_dt_inj : injective (fun i : 'I_4 => porbit P8 (dt i)).
Proof.
move=> i j /eqP; rewrite eq_porbit_mem => /porbitP[k Hk].
have E : qd (dt i) = qd (dt j).
  by rewrite Hk; case: (expg_invol k (dt j)) => ->; rewrite ?qd_rev ?qd_dt.
by apply: ord_inj; move: E; rewrite !qd_dt.
Qed.

Lemma M8_faces_ge4 : 4 <= x228_faces (1%g : {perm surface_dart M8}).
Proof.
rewrite /x228_faces mul1g.
have <- : #|[set porbit P8 (dt i) | i : 'I_4]| = 4.
  by rewrite card_imset ?card_ord //; exact: porbit_dt_inj.
apply: subset_leq_card; apply/subsetP => A /imsetP[i _ ->].
by apply/imsetP; exists (dt i).
Qed.

Lemma M8_total_ge4 : 4 <= x228_total_faces M8.
Proof.
rewrite /x228_total_faces (x228_rotation_system_deg1 (@M8_deg1)) big_set1.
exact: M8_faces_ge4.
Qed.

(** The statement is REFUTED: it lacks the source's connectedness hypothesis. *)
Lemma refuted : ~ random_embedding_expected_faces_third_statement.
Proof.
move=> /(_ M8); rewrite M8_nrot M8_card muln1 => H.
by have := leq_trans (leq_mul (leqnn 3) M8_total_ge4) H.
Qed.

Print Assumptions refuted.
