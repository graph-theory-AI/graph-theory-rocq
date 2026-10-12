(** * GTBase.poly_nat -- Horner evaluation of natural coefficient lists

    The canonical evaluation of a polynomial with natural coefficients, given by its coefficient list
    [p = [:: a0; a1; ...; an]] (lowest degree first), at [x : nat] is upstream MathComp's [horner_rec] at
    the natural semiring: [horner_nat p x = a0 + x * (a1 + x * (... + x * an))].  No evaluator is
    re-implemented here; this module is the thin adapter, with the nil/cons API that clients need
    because they do not get the natural semiring instance of [ssralg] by importing it:
    - [horner_nat_nil] / [horner_nat_cons]: the empty list evaluates to 0, every [x] included; the
      Horner step on a cons;
    - [horner_nat_foldr]: the [foldr] shape [foldr (fun a r => a + x * r) 0 p];
    - [horner_nat_x0]: at [x = 0] the head coefficient; [horner_nat_rcons0]: trailing zero coefficients
      do not change the value; [horner_nat_monomial]: [d] zeros then [c] evaluate to [c * t ^ d];
    - [horner_nat_mono]: monotone in [x];
    - [horner_nat_dom]: for [1 <= t], domination by (sum of the coefficients) * t ^ (size p - 1).  The
      guard is necessary: at [t = 0], [[:: 1; 1]] evaluates to 1 while the bound is 0.
    Coefficient order matters ([[:: 1; 2; 3]] at 10 is 321, the reversed list gives 123).  Imports are
    deliberately narrow: [ssralg]/[poly] are Required and only the canonical structures of [ssralg] are
    imported, nothing algebraic is re-exported, and [GTBase.base] does not re-export this module.
    Registry: meta/library_primitives/poly-eval.json (A31). *)
From mathcomp Require Import all_boot.
From mathcomp Require ssralg poly.
Import (canonicals) ssralg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition horner_nat (p : seq nat) (x : nat) : nat := poly.horner_rec p x.

Lemma horner_nat_nil (x : nat) : horner_nat [::] x = 0.
Proof. by []. Qed.

Lemma horner_nat_cons (a : nat) (p : seq nat) (x : nat) : horner_nat (a :: p) x = a + x * horner_nat p x.
Proof. by rewrite /horner_nat /= [in RHS]addnC [in RHS]mulnC. Qed.

(** Everything below goes through [horner_nat_nil] / [horner_nat_cons] only. *)
Lemma horner_nat_foldr (p : seq nat) (x : nat) : horner_nat p x = foldr (fun a r => a + x * r) 0 p.
Proof. by elim: p => [//|a p IH]; rewrite horner_nat_cons IH. Qed.

Lemma horner_nat_x0 (a : nat) (p : seq nat) : horner_nat (a :: p) 0 = a.
Proof. by rewrite horner_nat_cons mul0n addn0. Qed.

Lemma horner_nat_monomial (c d t : nat) : horner_nat (nseq d 0 ++ [:: c]) t = c * t ^ d.
Proof.
elim: d => [|d IH].
  have -> : nseq 0 0 ++ [:: c] = [:: c] by [].
  by rewrite horner_nat_cons horner_nat_nil muln0 addn0 expn0 muln1.
have -> : nseq d.+1 0 ++ [:: c] = 0 :: (nseq d 0 ++ [:: c]) by [].
by rewrite horner_nat_cons IH add0n expnS mulnCA.
Qed.

Lemma horner_nat_rcons0 (p : seq nat) (x : nat) : horner_nat (rcons p 0) x = horner_nat p x.
Proof.
elim: p => [|a p IH]; first by rewrite [rcons _ _]/= horner_nat_cons !horner_nat_nil muln0.
by rewrite rcons_cons !horner_nat_cons IH.
Qed.

Lemma horner_nat_mono (p : seq nat) (a b : nat) : a <= b -> horner_nat p a <= horner_nat p b.
Proof.
move=> ab; elim: p => [|c q IH]; first by rewrite !horner_nat_nil.
by rewrite !horner_nat_cons leq_add2l leq_mul.
Qed.

Lemma horner_nat_dom (p : seq nat) (t : nat) :
  1 <= t -> horner_nat p t <= (\sum_(i <- p) i) * t ^ (size p).-1.
Proof.
move=> t1; rewrite horner_nat_foldr; elim: p => [|a p IH] //=.
have ht k : 1 <= t ^ k by rewrite expn_gt0 t1.
case: p IH => [|b q] IH /=.
  by rewrite muln0 addn0 big_cons big_nil addn0 expn0 muln1.
rewrite big_cons mulnDl; apply: leq_add.
  by rewrite -{1}(muln1 a) leq_mul2l ht orbT.
apply: leq_trans (leq_mul (leqnn t) IH) _.
by rewrite mulnCA -expnS.
Qed.
