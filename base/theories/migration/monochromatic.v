(** * Frozen monochromatic subsets and complete reaching statements (C8)
    Original source: 47eed16, before C8. Every frozen body below preserves
    the original binders, guards and witnesses; only the recorded family
    references are redirected to other frozen bodies. Existing source
    discrepancies and partial/blocked statuses are not repaired. *)
From GTBase Require Import base monochromatic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition same_colour_on (G : sgraph) (k : nat)
    (col : G -> 'I_k) (S : {set G}) : Prop :=
  forall x y : G, x \in S -> y \in S -> col x = col y.

Definition clustered_colouring (G : sgraph) (k c : nat) : Prop :=
  exists col : G -> 'I_k,
    forall S : {set G},
      connected S -> Legacy.same_colour_on col S -> #|S| <= c.

Definition clustered_chromatic_at_most (G : sgraph) (k : nat) : Prop :=
  exists c : nat, Legacy.clustered_colouring G k c.

End Legacy.

Lemma same_colour_on_compat (G : sgraph) k (col : G -> 'I_k) (S : {set G}) :
  Legacy.same_colour_on col S <-> same_colour_on col S.
Proof.
rewrite /Legacy.same_colour_on /same_colour_on.
by split=> [h|/monochromatic_onP h]; [apply/monochromatic_onP | ].
Qed.

Lemma clustered_colouring_compat (G : sgraph) k c :
  Legacy.clustered_colouring G k c <-> clustered_colouring G k c.
Proof.
split=> -[col h]; exists col => S conn mono; apply: h=> //.
- by apply/same_colour_on_compat.
- by apply/same_colour_on_compat.
Qed.

Lemma clustered_chromatic_at_most_compat (G : sgraph) k :
  Legacy.clustered_chromatic_at_most G k <-> clustered_chromatic_at_most G k.
Proof.
by split=> -[c hc]; exists c; apply/clustered_colouring_compat.
Qed.
