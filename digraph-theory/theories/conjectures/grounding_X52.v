(** * Digraph.conjectures.grounding_X52 — guard-repair grounding for the X52 row

    GROUNDING for the wave-E4 GUARD REPAIR of row arxiv:1610.00876#03
    ([oriented_tree_mader_chi_linear_bound_statement]), whose host is quantified
    through [x52_mader_chi_bound], now guarded by [0 < #|D|].

    1. THE GUARD HAS TEETH: [x52_unguarded_false] — the UNGUARDED body (spelled
       out here in full, so that this file carries no refutation of a committed
       row) is FALSE at k = 1.  The one-vertex oriented tree makes the threshold
       [2 * 1 - 2 = 0], and chi of the EMPTY vertex set is 0, so the unguarded
       body demands a subdivision of a one-vertex digraph inside the empty
       digraph — but [contains_subdivision] needs an injective branch map.  This
       is the wave-E3 scratch refutation X52_mader_chi_false, ported.

    2. THE GUARD RESCUES k = 1 rather than hiding it: [x52_k1_holds] — for a
       one-vertex oriented tree, EVERY non-empty host contains a subdivision
       (there is no arc to replace), so no [2 <= k] guard is needed and the row
       keeps its k = 1 instance with its intended content.

    3. THE GUARD IS NOT VACUOUS: [x52_hyps_nonvacuous] — the one-arc oriented
       tree [TT 2] (k = 2) together with the host [TT 2] satisfies all four
       hypotheses, the chromatic bound [2 * 2 - 2 = 2 <= chi] included (its
       underlying graph has an edge, so omega and hence chi is at least 2).

    Every lemma is closed by [Qed] and axiom-free (audit at the end). *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory digraph oriented dipath tournament.
From Digraph Require Import subdivision.
From Digraph Require Import classic_core chi_bounded heroes path_fas X2 X52.
From Digraph Require Import grounding_X2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** 1. The guard has teeth *)

(** The X52 body with [x52_mader_chi_bound] spelled out WITHOUT the [0 < #|D|]
    guard. FALSE: take the one-vertex oriented tree and the empty host. *)
Lemma x52_unguarded_false :
  ~ (forall (T : orientedDigraph) (k : nat),
        oriented_tree T -> #|T| = k ->
        forall D : diGraphType,
          (2 * k - 2 <= χ([set: chi_bounded.underlying D]))%N ->
          contains_subdivision T D).
Proof.
move=> H.
have := H (TT 1 : orientedDigraph) 1 x2_oriented_tree_TT1 (card_TT 1)
          (x2_emptyD : diGraphType) (leq0n _).
by apply: (no_subdiv_emptyD (F := (TT 1 : diGraphType))); rewrite card_TT.
Qed.

(** ** 2. The guard rescues k = 1 *)

(** A one-vertex oriented tree has no arc, so mapping its vertex anywhere into a
    NON-EMPTY host is a subdivision model: the k = 1 instance of the repaired row
    is a theorem, which is why the repair needs no [2 <= k] guard. *)
Lemma x52_k1_holds (T : orientedDigraph) :
  oriented_tree T -> #|T| = 1%N ->
  forall D : diGraphType, (0 < #|D|)%N -> contains_subdivision T D.
Proof.
move=> [_ hor _ _] hcard D hD.
have h1 : forall x y : T, x = y.
  by move=> x y; apply: (@card_le1_eqP T predT) => //; rewrite hcard.
have habs (u v : T) : u --> v -> False.
  move=> huv; rewrite (h1 v u) in huv.
  by move: (hor _ _ huv); rewrite huv.
move/card_gt0P: hD => [v0 _].
exists (fun _ : T => v0); split; first by move=> x y _; exact: h1.
exists (fun _ _ : T => [::]); split.
- by move=> u v /habs.
- by move=> u v x y /habs.
Qed.

(** ** 3. The guarded hypotheses are inhabited *)

Definition x52_v0 : chi_bounded.underlying (TT 2 : diGraphType) :=
  Ordinal (isT : (0 < 2)%N).
Definition x52_v1 : chi_bounded.underlying (TT 2 : diGraphType) :=
  Ordinal (isT : (1 < 2)%N).

Lemma x52_TT2_edge : x52_v0 -- x52_v1.
Proof. by rewrite /edge_rel/= /chi_bounded.urel !arcTTE. Qed.

Lemma x52_chi_TT2_ge2 : (2 <= χ([set: chi_bounded.underlying (TT 2 : diGraphType)]))%N.
Proof.
apply: leq_trans (omega_leq_chi _).
by apply: (omega_ge2 (x := x52_v0) (y := x52_v1)); rewrite ?inE //; exact: x52_TT2_edge.
Qed.

Lemma x52_hyps_nonvacuous :
  exists (T : orientedDigraph) (k : nat) (D : diGraphType),
    [/\ oriented_tree T, #|T| = k, (0 < #|D|)%N
      & (2 * k - 2 <= χ([set: chi_bounded.underlying D]))%N ].
Proof.
exists (TT 2 : orientedDigraph), 2, (TT 2 : diGraphType); split.
- exact: x2_oriented_tree_TT2.
- exact: card_TT 2.
- by rewrite card_TT.
- by rewrite (_ : 2 * 2 - 2 = 2)%N //; exact: x52_chi_TT2_ge2.
Qed.

(** ** Print Assumptions audit *)

Print Assumptions x52_unguarded_false.
Print Assumptions x52_k1_holds.
Print Assumptions x52_chi_TT2_ge2.
Print Assumptions x52_hyps_nonvacuous.
