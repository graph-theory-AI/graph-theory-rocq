(** * Infinite.conjectures.grounding_X216 — grounding lemmas for wave X216.

    Qed-closed, axiom-free sanity results for
    [halin_hypomorphic_infinite_subgraph_statement] and for the three notions it
    introduces ([x216_embeds], [x216_del_iso], [x216_hypomorphic]).

    Contents:
      - NON-VACUITY: the hypotheses are jointly satisfiable — the countable
        complete graph [Komega] (igraph.v) is infinite and hypomorphic to
        itself, so the statement is not an empty implication.
      - GUARD HAS TEETH: [infinite_graph] rejects a one-vertex graph;
        [x216_hypomorphic] rejects a genuine pair (the countable complete graph
        and the countable edgeless graph are NOT hypomorphic); and the
        CONCLUSION has content — [x216_embeds] is not universally true
        ([Komega] does not embed in the edgeless graph).
      - STRUCTURAL LAWS: both new relations are reflexive, and embedding is
        transitive. *)

From GTBase Require Import base.
From Infinite Require Import foundations.igraph conjectures.X216.
From mathcomp Require Import all_boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Structural laws *)

Lemma x216_embeds_refl (G : iGraph) : x216_embeds G G.
Proof. by exists id; split=> //; exact: inj_id. Qed.

Lemma x216_embeds_trans (G H K : iGraph) :
  x216_embeds G H -> x216_embeds H K -> x216_embeds G K.
Proof.
move=> [f [finj fadj]] [g [ginj gadj]]; exists (g \o f); split.
  by move=> x y /= /ginj/finj.
by move=> x y /fadj/gadj.
Qed.

Lemma x216_del_iso_refl (G : iGraph) (v : iV G) : @x216_del_iso G G v v.
Proof.
exists id; split.
- by [].
- by move=> x y _ _ ->.
- by move=> y yv; exists y.
- by [].
Qed.

Lemma x216_hypomorphic_refl (G : iGraph) : x216_hypomorphic G G.
Proof.
have cid : cancel (@id (iV G)) id by [].
exists id; split; first exact: (Bijective cid cid).
by move=> v; exact: x216_del_iso_refl.
Qed.

(** ** The countable edgeless graph *)

Lemma x216_empty_sym : irel_sym (fun _ _ : nat => False).
Proof. by []. Qed.

Lemma x216_empty_irr : irel_irr (fun _ _ : nat => False).
Proof. by move=> x []. Qed.

(** [Eomega]: countably many vertices, no edge. *)
Definition x216_Eomega : iGraph := Build_iGraph x216_empty_sym x216_empty_irr.

(** ** The one-vertex graph *)

Lemma x216_unit_sym : irel_sym (fun _ _ : unit => False).
Proof. by []. Qed.

Lemma x216_unit_irr : irel_irr (fun _ _ : unit => False).
Proof. by move=> x []. Qed.

Definition x216_K1i : iGraph := Build_iGraph x216_unit_sym x216_unit_irr.

(** ** Non-vacuity *)

(** [Komega] (igraph.v) is infinite. *)
Lemma x216_Komega_infinite : infinite_graph Komega.
Proof. by exists id. Qed.

(** ... and the edgeless graph on [nat] is infinite too. *)
Lemma x216_Eomega_infinite : infinite_graph x216_Eomega.
Proof. by exists id. Qed.

(** NON-VACUITY of the statement: [Komega] satisfies all three hypotheses (it is
    infinite and hypomorphic to itself), so the implication is not vacuous — and
    in this instance the conclusion indeed holds. *)
Lemma x216_nonvacuous :
  infinite_graph Komega /\ infinite_graph Komega /\
  x216_hypomorphic Komega Komega /\
  (x216_embeds Komega Komega /\ x216_embeds Komega Komega).
Proof.
split; [exact: x216_Komega_infinite|split; [exact: x216_Komega_infinite|]].
by split; [exact: x216_hypomorphic_refl | split; exact: x216_embeds_refl].
Qed.

(** ** Guards have teeth *)

(** TEETH #1 — [infinite_graph] is load-bearing: a one-vertex graph is not
    infinite, so the statement really only speaks about infinite graphs. *)
Lemma x216_K1i_not_infinite : ~ infinite_graph x216_K1i.
Proof.
case=> f finj; have : f 0 = f 1 by case: (f 0); case: (f 1).
by move/finj.
Qed.

(** TEETH #2 — the CONCLUSION has content: the countable complete graph is not
    isomorphic to a subgraph of the countable edgeless graph, so [x216_embeds]
    is not a universally true relation. *)
Lemma x216_Komega_not_embeds_Eomega : ~ x216_embeds Komega x216_Eomega.
Proof. by case=> f [_ fadj]; apply: (fadj 0 1). Qed.

(** TEETH #3 — the HYPOMORPHY guard is load-bearing: the countable complete
    graph and the countable edgeless graph are infinite but NOT hypomorphic, so
    the hypothesis of the statement excludes genuine pairs (and in particular the
    statement is not refuted by this pair). *)
Lemma x216_Komega_not_hypomorphic_Eomega :
  ~ x216_hypomorphic Komega x216_Eomega.
Proof.
case=> phi [_ H]; have [f [_ _ _ Hadj]] := H 0.
have n1 : (1 : iV Komega) <> 0 by [].
have n2 : (2 : iV Komega) <> 0 by [].
have H12 : iadj (1 : iV Komega) 2 by [].
by case: (Hadj 1 2 n1 n2) => /(_ H12).
Qed.

Print Assumptions halin_hypomorphic_infinite_subgraph_statement.
Print Assumptions x216_nonvacuous.
Print Assumptions x216_Komega_not_hypomorphic_Eomega.
Print Assumptions x216_Komega_not_embeds_Eomega.
