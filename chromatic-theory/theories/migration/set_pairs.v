(** A21 set pairs (chromatic): X3's frozen disjoint anticomplete pair and the two rows using it, X3's #1111 and X213's
    El-Zahar-Erdos.  Baseline, hashes and exact substitutions are recorded in
    meta/migration_reports/set_pairs.spec.json.
    - [Legacy]: X3's [[disjoint A & B] /\ (a -- b -> False for cross pairs)] is equivalent to
      [GTBase.set_pairs.anticomplete A B] by [anticompleteP] (an iff, not a conversion); no nonempty guard is added.
    - [X3Legacy], [X213Legacy]: #1111 keeps [1 <= t], [1 <= c], [exists d >= 1] before every graph and the ordered
      chromatic bounds; El-Zahar-Erdos keeps one [f] before r, k and G, the exactly-r clique alternative and both parts
      of chromatic number exactly k, with no positivity guard.  Neither row has older frozen history, so these are also
      their complete rows. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base set_pairs.
From Chromatic.conjectures Require Import X3 X213.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** [[/\ _, _ & _]] is a morphism for iff, so the frozen pieces can be rewritten inside it. *)
#[local] Instance and3_iff_morphism : Proper (iff ==> iff ==> iff ==> iff) and3.
Proof. by move=> a a' ha b b' hb c c' hc; split=> -[x y z]; split; by [apply/ha|apply/hb|apply/hc]. Qed.

Module Legacy.

Definition x3_anticomplete (G : sgraph) (A B : {set G}) : Prop :=
  [disjoint A & B] /\
  forall a b : G, a \in A -> b \in B -> a -- b -> False.

End Legacy.

Module X3Legacy.

Definition erdos_anticomplete_pairs_statement : Prop :=
  forall t c : nat, 1 <= t -> 1 <= c ->
    exists d : nat,
      1 <= d /\
      forall G : sgraph,
        d <= χ([set: G]) -> ω([set: G]) < t ->
        exists A B : {set G},
          Legacy.x3_anticomplete A B /\
          c <= χ(B) /\ χ(B) <= χ(A).

End X3Legacy.

Module X213Legacy.

Definition el_zahar_erdos_statement : Prop :=
  exists f : nat -> nat -> nat,
    forall (r k : nat) (G : sgraph),
      f r k <= χ([set: G]) ->
      (exists S : {set G}, clique S /\ #|S| = r) \/
      (exists A B : {set G}, [/\ Legacy.x3_anticomplete A B, χ(A) = k & χ(B) = k]).

End X213Legacy.

(** Not a conversion: the raw conjunction against the Boolean pair, by reflection. *)
Lemma x3_anticomplete_compat (G : sgraph) (A B : {set G}) :
  Legacy.x3_anticomplete A B <-> x3_anticomplete A B.
Proof.
exact: (rwP (anticompleteP A B)).
Qed.

Lemma erdos_anticomplete_pairs_statement_compat :
  X3Legacy.erdos_anticomplete_pairs_statement <-> erdos_anticomplete_pairs_statement.
Proof.
rewrite /X3Legacy.erdos_anticomplete_pairs_statement /erdos_anticomplete_pairs_statement.
setoid_rewrite x3_anticomplete_compat.
reflexivity.
Qed.

Lemma el_zahar_erdos_statement_compat :
  X213Legacy.el_zahar_erdos_statement <-> el_zahar_erdos_statement.
Proof.
rewrite /X213Legacy.el_zahar_erdos_statement /el_zahar_erdos_statement.
setoid_rewrite x3_anticomplete_compat.
reflexivity.
Qed.
