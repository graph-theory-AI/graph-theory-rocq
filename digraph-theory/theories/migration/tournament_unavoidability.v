(** C22: exact-order tournament unavoidability, frozen at the fixed C21 pin
    b6cd87b5af7943ebe744cd27dfe34ac42d9e543d.  Every declaration frozen here is
    byte-identical at the family baseline, the C20 pin 97605dd.
    - [Legacy]: the two unchanged supports [heroes.is_tournament] and
      [unvd.contains_subdigraph], verbatim, and the three migrated sources
      [unvd.unavoidable], [unvd.unvd] and [X221.x221_linearly_unavoidable] over them.
      The live sources now unfold to
      [Digraph.foundations.tournament_unavoidability]: bundled tournaments of exactly
      [N] vertices, injective upstream [is_dhom] maps, all-smaller minimality and one
      natural [C] chosen before all digraphs.
    - [X17Legacy], [UnvdLegacy], [X221Legacy], [RealsLegacy]: the five whole Props over
      the frozen chain.  Sumner's oriented-tree and [1 < n] guards, the deletion
      acyclicity / [1 < #|D|] guards with a uniform [C], Problem 6's nonempty guard,
      rational [mad] bound and uniform [a, d, b], and X221's exact k-extension and
      class quantifiers are kept; the non-corpus alias points to the frozen
      [prob_6].  [mad], [oriented_tree], [del_vertex], [acyclicb] and [x221_kextension]
      are unchanged live helpers.
    There is no earlier frozen history for these declarations. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude digraph oriented tournament dipath dichromatic heroes.
From Digraph.foundations Require Import tournament_unavoidability.
From Digraph.conjectures Require Import X2 unvd X17 X221 reals_growth.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition is_tournament (D : diGraphType) : Prop :=
  [/\ irreflexive (@arc D),
      (forall u v : D, u != v -> (u --> v) || (v --> u))
    & (forall u v : D, u --> v -> ~~ (v --> u))].

Definition contains_subdigraph (H D : diGraphType) : Prop :=
  exists f : H -> D, injective f /\ forall u v : H, u --> v -> f u --> f v.

Definition unavoidable (D : diGraphType) (N : nat) : Prop :=
  forall T : diGraphType, Legacy.is_tournament T -> #|T| = N -> Legacy.contains_subdigraph D T.

Definition unvd (D : diGraphType) (N : nat) : Prop :=
  Legacy.unavoidable D N /\ (forall M : nat, M < N -> ~ Legacy.unavoidable D M).

Definition x221_linearly_unavoidable (F : diGraphType -> Prop) : Prop :=
  exists C : nat,
    forall (D : diGraphType) (N : nat), F D -> Legacy.unvd D N -> (N <= C * #|D|)%N.

End Legacy.

Module X17Legacy.

Definition sumner_oriented_tree_unavoidable_statement : Prop :=
  forall (n : nat) (T : orientedDigraph),
    1 < n ->
    oriented_tree T ->
    #|T| = n ->
    Legacy.unavoidable T (2 * n - 2).

End X17Legacy.

Module UnvdLegacy.
Local Open Scope ring_scope.

Definition conj_9 : Prop :=
  exists C : nat,
    forall (D : diGraphType) (v : D),
      acyclicb D -> (1 < #|D|)%N ->
      forall nD nDv : nat,
        Legacy.unvd D nD -> Legacy.unvd (del_vertex v) nDv ->
        (nD <= C * nDv)%N.

Definition prob_6 : Prop :=
  forall alpha : rat,
    exists a d b : nat,
      forall (D : diGraphType),
        (0 < #|D|)%N -> (mad D <= alpha) ->
        forall nD : nat, Legacy.unvd D nD ->
          (nD <= a * #|D| ^ d + b)%N.

End UnvdLegacy.

Module X221Legacy.

Definition kextension_linear_unavoidability_statement : Prop :=
  forall (F : diGraphType -> Prop) (k : nat),
    Legacy.x221_linearly_unavoidable F ->
    Legacy.x221_linearly_unavoidable (x221_kextension k F).

End X221Legacy.

Module RealsLegacy.

Definition prob6_unvd_statement : Prop := UnvdLegacy.prob_6.

End RealsLegacy.

(** The supports are unchanged live helpers: reflexive equivalences. *)
Lemma is_tournament_compat (D : diGraphType) :
  Legacy.is_tournament D <-> is_tournament D.
Proof. exact: iff_refl. Qed.

Lemma contains_subdigraph_compat (H D : diGraphType) :
  Legacy.contains_subdigraph H D <-> contains_subdigraph H D.
Proof. exact: iff_refl. Qed.

(** The same-carrier factory bridge [unavoidableP] relates the frozen unbundled
    quantification to the bundled one. *)
Lemma unavoidable_compat (D : diGraphType) (N : nat) :
  Legacy.unavoidable D N <-> unavoidable D N.
Proof.
split=> [un|/unavoidableP un T isT cardT].
- apply/unavoidableP => T isT cardT.
  exact/contains_subdigraph_compat/un/cardT/is_tournament_compat.
- exact/contains_subdigraph_compat/un/cardT/is_tournament_compat.
Qed.

Lemma unvd_compat (D : diGraphType) (N : nat) :
  Legacy.unvd D N <-> unvd D N.
Proof.
have E := unavoidable_compat D.
split=> -[uN mN]; split=> [|M lt uM].
- exact: (proj1 (E N) uN).
- exact: mN M lt (proj2 (E M) uM).
- exact: (proj2 (E N) uN).
- exact: mN M lt (proj1 (E M) uM).
Qed.

Lemma x221_linearly_unavoidable_compat (F : diGraphType -> Prop) :
  Legacy.x221_linearly_unavoidable F <-> x221_linearly_unavoidable F.
Proof.
split=> -[C hC]; exists C => D N FD uN.
- exact: hC D N FD (proj2 (unvd_compat D N) uN).
- exact: hC D N FD (proj1 (unvd_compat D N) uN).
Qed.

Lemma sumner_oriented_tree_unavoidable_statement_compat :
  X17Legacy.sumner_oriented_tree_unavoidable_statement <->
  sumner_oriented_tree_unavoidable_statement.
Proof.
split=> st n T n1 tree cardT.
- exact: (proj1 (unavoidable_compat T _) (st n T n1 tree cardT)).
- exact: (proj2 (unavoidable_compat T _) (st n T n1 tree cardT)).
Qed.

Lemma conj_9_compat : UnvdLegacy.conj_9 <-> conj_9.
Proof.
split=> -[C hC]; exists C => D v acyc nonsingle nD nDv uD uDv.
- exact: hC D v acyc nonsingle nD nDv
    (proj2 (unvd_compat D nD) uD) (proj2 (unvd_compat _ nDv) uDv).
- exact: hC D v acyc nonsingle nD nDv
    (proj1 (unvd_compat D nD) uD) (proj1 (unvd_compat _ nDv) uDv).
Qed.

Lemma prob_6_compat : UnvdLegacy.prob_6 <-> prob_6.
Proof.
split=> st alpha; have [a [d [b h]]] := st alpha; exists a, d, b => D pos madD nD uD.
- exact: h D pos madD nD (proj2 (unvd_compat D nD) uD).
- exact: h D pos madD nD (proj1 (unvd_compat D nD) uD).
Qed.

Lemma kextension_linear_unavoidability_statement_compat :
  X221Legacy.kextension_linear_unavoidability_statement <->
  kextension_linear_unavoidability_statement.
Proof.
split=> st F k lin.
- exact: (proj1 (x221_linearly_unavoidable_compat _)
    (st F k (proj2 (x221_linearly_unavoidable_compat F) lin))).
- exact: (proj2 (x221_linearly_unavoidable_compat _)
    (st F k (proj1 (x221_linearly_unavoidable_compat F) lin))).
Qed.

(** The non-corpus alias is the frozen [prob_6] on both sides. *)
Lemma prob6_unvd_statement_compat :
  RealsLegacy.prob6_unvd_statement <-> prob6_unvd_statement.
Proof. exact: prob_6_compat. Qed.
