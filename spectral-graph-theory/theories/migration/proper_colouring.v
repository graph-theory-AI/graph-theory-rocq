(** * Spectral.migration.proper_colouring -- C5 frozen supplied colourings

    Frozen at a6db537. Supplied function carriers and palettes are unchanged.
    Boolean source bridges are equalities; Prop source bridges are iff. Counts
    still enumerate labelled finite functions. No surjectivity or positivity
    guard is added. The ten full statements retain their existing readings and
    statuses, including the unrelated blocked X162 Kempe-step defect.
    X64Original combines the pre-M1/A3 graph chain with frozen colouring;
    X83Original combines the B3 induced-path chain with frozen colouring.
    Historical migration bodies are imported unchanged. *)

From GTBase Require Import base colourings.
From Spectral.conjectures Require Import D5.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition proper_colb (G : sgraph) (k : nat) (c : {ffun G -> 'I_k}) : bool :=
  [forall x, [forall y, (x -- y) ==> (c x != c y)]].

End Legacy.

Module D5Legacy.

Definition csf_coeff (G : sgraph) (k : nat) (a : 'I_k -> nat) : nat :=
  #|[set c : {ffun G -> 'I_k} |
       Legacy.proper_colb c && [forall b : 'I_k, #|[set x | c x == b]| == a b]]|.

Definition same_csf (G H : sgraph) : Prop :=
  forall (k : nat) (a : 'I_k -> nat), D5Legacy.csf_coeff G a = D5Legacy.csf_coeff H a.

Definition does_the_symmetric_chromatic_function_distinguish_tr_statement : Prop :=
  exists T1 T2 : sgraph,
    [/\ is_tree [set: T1], is_tree [set: T2],
        ~ inhabited (T1 ≃ T2) & D5Legacy.same_csf T1 T2].

End D5Legacy.

(** ** Unconditional source, chain and full-statement certificates. *)

Lemma proper_colb_compat (G : sgraph) (k : nat) (c : {ffun G -> 'I_k}) :
  Legacy.proper_colb c = proper_colb c.
Proof. by rewrite /Legacy.proper_colb /proper_colb proper_colouringE. Qed.

Lemma csf_coeff_compat (G : sgraph) (k : nat) (a : 'I_k -> nat) :
  D5Legacy.csf_coeff G a = csf_coeff G a.
Proof.
rewrite /D5Legacy.csf_coeff /csf_coeff.
apply: eq_card=> c.
by rewrite !inE proper_colb_compat.
Qed.

Lemma same_csf_compat (G H : sgraph) :
  D5Legacy.same_csf G H <-> same_csf G H.
Proof.
rewrite /D5Legacy.same_csf /same_csf.
setoid_rewrite csf_coeff_compat.
reflexivity.
Qed.

Lemma does_the_symmetric_chromatic_function_distinguish_tr_statement_compat :
  D5Legacy.does_the_symmetric_chromatic_function_distinguish_tr_statement <->
  does_the_symmetric_chromatic_function_distinguish_tr_statement.
Proof.
split=> -[T1 [T2 [h1 h2 hn hc]]]; exists T1, T2; split=> //.
- exact: (proj1 (same_csf_compat T1 T2) hc).
- exact: (proj2 (same_csf_compat T1 T2) hc).
Qed.
