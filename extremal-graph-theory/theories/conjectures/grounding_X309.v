(** * Extremal.conjectures.grounding_X309 -- grounding certificates of wave X309.

    hyp_inhabited and not_trivially_true (the contract form: a variant obtained from the body by deleting one hypothesis
    is false and implies the row) for the one row; the wave adds no helper, so there is no helper_sanity.
    - Hypotheses: the 5-cycle C_5 (GTBase cycle_graph 5) is triangle-free and subcubic, checked by vm_compute on an
      explicit vertex list (as the C_5 example of GTBase examples/perfect_graphs.v), and it contains none of the six
      graphs, which have 11 to 22 vertices (X287's g287_helper_sanity) while a subgraph never has more vertices than
      its host (has_subgraph_card); the statement then gives the bound for C_5.
    - Without the forbidden-subgraph hypothesis the statement fails at F_11 (x287_bb_graph 0), which is triangle-free
      and subcubic with 8 * alpha(F_11) < 3 * 11 (X287's g287_f11_triangle_free, g287_f11_subcubic and
      g287_f11_sparse). *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base common.
From Extremal.conjectures Require Import X287 grounding_X287 X309.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** C_5 meets the hypotheses *)

Local Notation C5 := (cycle_graph 5).

Definition g309_c5 : seq C5 :=
  [:: @Ordinal 5 0 isT; @Ordinal 5 1 isT; @Ordinal 5 2 isT; @Ordinal 5 3 isT; @Ordinal 5 4 isT].

Lemma g309_c5_enum : enum 'I_5 = g309_c5.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

Lemma g309_c5_all (x : C5) : x \in g309_c5.
Proof. by rewrite -g309_c5_enum mem_enum. Qed.

Lemma g309_c5_card (S : {set C5}) : #|S| = count (mem S) g309_c5.
Proof. by rewrite cardE /enum_mem -enumT g309_c5_enum size_filter. Qed.

Lemma g309_C5_triangle_free : triangle_free C5.
Proof.
have h : all (fun x : C5 => all (fun y : C5 => all (fun z : C5 =>
           ~~ [&& x -- y, y -- z & z -- x]) g309_c5) g309_c5) g309_c5 by vm_compute.
move=> x y z xy yz zx.
move/allP/(_ x (g309_c5_all x))/allP/(_ y (g309_c5_all y))/allP/(_ z (g309_c5_all z)): h.
by rewrite xy yz zx.
Qed.

Lemma g309_C5_subcubic : subcubic C5.
Proof.
have h : all (fun v : C5 => count (fun u : C5 => v -- u) g309_c5 <= 3) g309_c5 by vm_compute.
move=> v; rewrite g309_c5_card.
have -> : count (mem N(v)) g309_c5 = count (fun u : C5 => v -- u) g309_c5.
  by apply: eq_count => u; exact: in_opn.
exact: (allP h v (g309_c5_all v)).
Qed.

Lemma g309_C5_no_forbidden (i : 'I_6) : ~ has_subgraph C5 (x287_bb_graph i).
Proof.
move/has_subgraph_card; have [_ _ ->] := g287_helper_sanity; rewrite card_ord.
by case: i => -[|[|[|[|[|[|n]]]]]].
Qed.

(** hyp_inhabited: C_5 meets the three hypotheses, and the statement gives the bound for it. *)
Definition g309_hyp_claim : Prop :=
  [/\ triangle_free C5, subcubic C5, (forall i : 'I_6, ~ has_subgraph C5 (x287_bb_graph i)) &
      (fraughnaugh_locke_forbidden_subgraph_independence_statement -> 3 * #|C5| <= 8 * α([set: C5]))].

Theorem g309_hyp_inhabited : g309_hyp_claim.
Proof.
split; [exact: g309_C5_triangle_free | exact: g309_C5_subcubic | exact: g309_C5_no_forbidden |].
by move=> h; apply: h; [exact: g309_C5_triangle_free | exact: g309_C5_subcubic | exact: g309_C5_no_forbidden].
Qed.

(** ** not_trivially_true: the forbidden-subgraph hypothesis is needed *)

Definition g309_without_forbidden : Prop :=
  forall G : sgraph, triangle_free G -> subcubic G -> 3 * #|G| <= 8 * α([set: G]).

Definition g309_ntt_claim : Prop :=
  ~ g309_without_forbidden /\
  (g309_without_forbidden -> fraughnaugh_locke_forbidden_subgraph_independence_statement).

Theorem g309_not_trivially_true : g309_ntt_claim.
Proof.
split; last by move=> h G t s _; exact: h.
move=> h; move: (h _ g287_f11_triangle_free g287_f11_subcubic).
by rewrite leqNgt g287_f11_sparse.
Qed.
