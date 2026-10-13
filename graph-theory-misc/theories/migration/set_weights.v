(** A30: finite-set weights, frozen at the accepted parent 3bdfdae32824d4762ba8105367f7858a706a02e2.
    - [X128Legacy]: the X128 weight [x128_weight], its separator chain [x128_cheap_bal_sep] and the WHOLE current
      row, verbatim. The row keeps C23's live expansion chain [x128_expansion_bounded] (with the live C16 model
      alias and A7 count below it), as the source did.
    - [X128Original]: the complete deepest X128 row, the same statement text over the existing complete A7+C16
      Original expansion chain [GTMisc.migration.ambient_shallow_minors.X128Original.x128_expansion_bounded]
      (aliased [ASM]: frozen count, radius, model and grad) and this family's frozen separator and weight.
      The earlier X128 rows of edge_count, ambient_shallow_minors and ambient_grad stay byte-exact.
    - [U13Legacy]: U13's [gold_total], its game-value chain [leaf_game_solution] and the WHOLE gold-grabbing row.
    The live weights are transparent aliases of upstream [weight_set] with the same body, so each certificate is a
    conversion. X128 keeps p before q, the individual-graph hypothesis and 1 <= t, its bounded outliers, t-times
    cheapness and two-times connected-part balance; the gold row keeps its nonempty-tree guards and truncated
    subtraction. Zero weights and empty sets stay allowed; no positivity is added. *)
From GTBase Require Import base.
From GTMisc.conjectures Require Import X128 U13.
From GTMisc Require migration.ambient_shallow_minors.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module ASM := GTMisc.migration.ambient_shallow_minors.

Module X128Legacy.

Definition x128_weight (G : sgraph) (rho : G -> nat) (S : {set G}) : nat :=
  \sum_(v in S) rho v.

Definition x128_cheap_bal_sep (G : sgraph) (rho : G -> nat) (t k : nat) : Prop :=
  exists S Z : {set G},
    [/\ #|Z| <= k,
        t * X128Legacy.x128_weight rho S <= X128Legacy.x128_weight rho [set: G] &
        forall A : {set G},
          A \subset ~: (S :|: Z) ->
          connected A ->
          2 * X128Legacy.x128_weight rho A <= X128Legacy.x128_weight rho [set: G]].

Definition dvorak_cheap_balanced_separator_bounded_expansion_statement : Prop :=
  forall p : seq nat,
    exists q : nat -> nat,
      forall (G : sgraph) (rho : G -> nat) (t : nat),
        1 <= t ->
        x128_expansion_bounded G p ->
        X128Legacy.x128_cheap_bal_sep rho t (q t).

End X128Legacy.

Module X128Original.

Definition dvorak_cheap_balanced_separator_bounded_expansion_statement : Prop :=
  forall p : seq nat,
    exists q : nat -> nat,
      forall (G : sgraph) (rho : G -> nat) (t : nat),
        1 <= t ->
        ASM.X128Original.x128_expansion_bounded G p ->
        X128Legacy.x128_cheap_bal_sep rho t (q t).

End X128Original.

Module U13Legacy.

Definition gold_total (G : sgraph) (g : G -> nat) (S : {set G}) : nat :=
  \sum_(v in S) g v.

Definition leaf_game_solution (G : sgraph) (g : G -> nat)
  (val : {set G} -> nat) (sigma : {set G} -> G) : Prop :=
  forall S : {set G},
    (~ (exists v : G, is_leaf S v) -> val S = 0) /\
    ((exists v : G, is_leaf S v) ->
       [/\ is_leaf S (sigma S),
           val S = g (sigma S) + U13Legacy.gold_total g (S :\ sigma S) - val (S :\ sigma S) &
           (forall w : G, is_leaf S w ->
              g w + U13Legacy.gold_total g (S :\ w) - val (S :\ w) <= val S)]).

Definition a_gold_grabbing_game_statement : Prop :=
  forall (G : sgraph) (g : G -> nat),
    0 < #|G| ->
    is_tree_card G ->
    exists (val : {set G} -> nat) (sigma : {set G} -> G),
      U13Legacy.leaf_game_solution g val sigma.

End U13Legacy.

(** The live weights are upstream [weight_set], the same body. *)
Lemma x128_weight_compat (G : sgraph) (rho : G -> nat) (S : {set G}) :
  X128Legacy.x128_weight rho S = x128_weight rho S.
Proof. by []. Qed.

Lemma x128_cheap_bal_sep_compat (G : sgraph) (rho : G -> nat) (t k : nat) :
  X128Legacy.x128_cheap_bal_sep rho t k <-> x128_cheap_bal_sep rho t k.
Proof. exact: iff_refl. Qed.

Lemma dvorak_cheap_balanced_separator_bounded_expansion_statement_compat :
  X128Legacy.dvorak_cheap_balanced_separator_bounded_expansion_statement <->
  dvorak_cheap_balanced_separator_bounded_expansion_statement.
Proof. exact: iff_refl. Qed.

(** The deepest row: C16's whole-chain certificate for the expansion bound, and this family's frozen separator. *)
Lemma dvorak_cheap_balanced_separator_bounded_expansion_statement_original_compat :
  X128Original.dvorak_cheap_balanced_separator_bounded_expansion_statement <->
  dvorak_cheap_balanced_separator_bounded_expansion_statement.
Proof.
split=> st p; have [q hq] := st p; exists q => G rho t t1 bounded.
- exact: hq G rho t t1 (proj2 (ASM.x128_expansion_bounded_original_compat G p) bounded).
- exact: hq G rho t t1 (proj1 (ASM.x128_expansion_bounded_original_compat G p) bounded).
Qed.

Lemma gold_total_compat (G : sgraph) (g : G -> nat) (S : {set G}) :
  U13Legacy.gold_total g S = gold_total g S.
Proof. by []. Qed.

Lemma leaf_game_solution_compat (G : sgraph) (g : G -> nat)
    (val : {set G} -> nat) (sigma : {set G} -> G) :
  U13Legacy.leaf_game_solution g val sigma <-> leaf_game_solution g val sigma.
Proof. exact: iff_refl. Qed.

Lemma a_gold_grabbing_game_statement_compat :
  U13Legacy.a_gold_grabbing_game_statement <-> a_gold_grabbing_game_statement.
Proof. exact: iff_refl. Qed.
