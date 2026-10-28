(** * Digraph.conjectures.X248 -- wave X248: the clique number of tournaments and of digraphs
    (Aboulker, Aubian, Charbit, Lopes, arXiv:2310.04265) (2026-10-27)

    A five-row wave under the prospective contract of meta/faithfulness_policy.json (hard lint,
    classified local helpers, grounding certificates, an independent verifier). Rows:
    arxiv:2310.04265#00 (omega- and dic-orderings), #01 (polynomial dic-boundedness under
    substitution), #05 (the Gyarfas-Sumner analogue for tournaments), #08 (local to global
    clique number) and #11 (dic-boundedness of digraph classes under substitution). Shared
    vocabulary is reused: [omegabar] and [omegab_at] (invariants/omegabar.v), [backedge] and
    [ltp] (core/order.v), [sub_tournament] (core/tournament.v), [induced_digraph]
    (core/digraph.v), [is_tournament] and [ind_free] (conjectures/heroes.v), [oriented_dg]
    (conjectures/heroes_dichotomy.v), [dicolorableb] (conjectures/dichromatic.v), the
    dichromatic number [x221_dichro] (conjectures/X221.v), and coq-graph-theory's chromatic
    number, clique number and [is_forest]. The source is the Mac's deposit
    coordination/sources/x236-mac-20261026/2310.04265v1 (TeX x/main.tex, line numbers below);
    the grounding certificates are in grounding_X248.v. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup.
From GraphTheory Require Import preliminaries digraph sgraph coloring.
From Digraph Require Import prelude interop_graph_theory digraph oriented dipath tournament order.
From Digraph Require Import heroes heroes_dichotomy dichromatic omegabar X221.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x248 vocabulary ************************************************* *)

(** The BACKEDGE GRAPH D^< of a digraph D under a vertex order (TeX l.385-386): u and v are
    adjacent when the later of the two has an arc to the earlier one. This is order.v's
    [backedge_rel] over every digraph instead of tournaments; the symmetry and irreflexivity
    proofs are given inline. Loops never give edges (u < v is strict). *)
Definition x248_backedge_rel (D : diGraphType) (p : {perm D}) : rel D :=
  [rel u v | ltp p u v && (v --> u) || ltp p v u && (u --> v)].

Definition x248_backedge (D : diGraphType) (p : {perm D}) : sgraph :=
  @SGraph D (x248_backedge_rel p)
    (fun u v => orbC (ltp p u v && (v --> u)) (ltp p v u && (u --> v)))
    (fun u => @eq_ind_r bool false (fun b : bool => b && (u --> u) || b && (u --> u) = false)
                (erefl false) (ltp p u u) (ltp_irrefl p u)).

(** The CLIQUE NUMBER OF A DIGRAPH (TeX l.403-406): the least clique number of a backedge graph
    over all vertex orders, written with [omegabar]'s own arg-min body; on a tournament it is
    [omegabar] by conversion (grounding_X248.v, [g248_omegab_dg_tournament]). *)
Definition x248_omegab_dg (D : diGraphType) : nat :=
  ω([set: x248_backedge [arg min_(p < (1%g : {perm D})) ω([set: x248_backedge p])]]).

(** A class C is DIC-BOUNDED (TeX l.412) when one f bounds the dichromatic number by f of the
    clique number on every member, and POLYNOMIALLY dic-bounded when f can be c * t^d (X218's
    normal form: a polynomial with natural coefficients of degree d is at most the sum of its
    coefficients times t^d for t >= 1, and t = 0 only for the empty digraph, whose dichromatic
    number is 0). *)
Definition x248_dic_bounded (C : diGraphType -> Prop) : Prop :=
  exists f : nat -> nat, forall D : diGraphType, C D -> (x221_dichro D <= f (x248_omegab_dg D))%N.

Definition x248_poly_dic_bounded (C : diGraphType -> Prop) : Prop :=
  exists c d : nat, forall D : diGraphType, C D -> (x221_dichro D <= c * x248_omegab_dg D ^ d)%N.

(** A CLASS of digraphs is closed under induced subdigraphs (TeX l.454). *)
Definition x248_hereditary (C : diGraphType -> Prop) : Prop :=
  forall (D : diGraphType) (S : {set D}), C D -> C (induced_digraph S).

(** SUBSTITUTING D2 for the vertex u of D1 (TeX l.663-668): the vertices of D1 other than u and
    those of D2; the arcs inside each part are kept; a vertex v of D1 - u has an arc to every
    vertex of D2 when v -> u, and every vertex of D2 has an arc to v when u -> v. *)
Definition x248_subst (D1 : diGraphType) (u : D1) (D2 : diGraphType) : Type :=
  ({x : D1 | x != u} + D2)%type.

Section Subst.
Variables (D1 : diGraphType) (u : D1) (D2 : diGraphType).
HB.instance Definition _ := Finite.on (x248_subst u D2).
Definition x248_subst_rel (a b : x248_subst u D2) : bool :=
  match a, b with
  | inl x, inl y => val x --> val y
  | inr x, inr y => x --> y
  | inl x, inr _ => val x --> u
  | inr _, inl y => u --> val y
  end.
HB.instance Definition _ := HasArc.Build (x248_subst u D2) x248_subst_rel.
End Subst.

(** The CLOSURE of a class under substitution (TeX l.672). *)
Inductive x248_subst_closure (C : diGraphType -> Prop) : diGraphType -> Prop :=
| x248_sc_base (D : diGraphType) : C D -> x248_subst_closure C D
| x248_sc_step (D1 : diGraphType) (u : D1) (D2 : diGraphType) :
    x248_subst_closure C D1 -> x248_subst_closure C D2 ->
    x248_subst_closure C (x248_subst u D2 : diGraphType).

(** ** Statements ************************************************************ *)

(** Corpus row: arxiv:2310.04265#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2310.04265__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2310.04265__00.json
    English statement: (Aboulker, Aubian, Charbit, Lopes, Clique number of tournaments,
      arXiv:2310.04265v1, Question 3.5)
      Every tournament has a vertex ordering that is both an omega-ordering and a dic-ordering.
    Definitions: [omegab_at p] - the clique number of the backedge graph [backedge p]
      (invariants/omegabar.v, core/order.v); [omegabar T] - its least value over all orderings;
      [χ(_)] - the chromatic number (coq-graph-theory); [x221_dichro T] - the least k with a
      k-dicolouring (conjectures/X221.v).
    Notes: An ordering is an omega-ordering when the clique number of its backedge graph is
      omegabar(T), and a dic-ordering when "dic(T^<) = dic(T)" (TeX l.462); T^< is an undirected
      graph, whose dic is its chromatic number (l.391: dic(D) is the least chromatic number of a
      backedge graph). The question (l.549-551) is encoded in its affirmative form. Literature
      status: open at the pin (pinned status open; the review status "unclear" asked whether
      arXiv:2401.07776 refutes it; that paper's counterexample, Theorem 4.2, is the one to
      Conjecture 4.3, arxiv:2310.04265#05, per the corrected review of that row). *)
Definition omega_dic_orderings_statement : Prop :=
  forall T : tournament, exists p : {perm T},
    omegab_at p = omegabar T /\ χ([set: backedge p]) = x221_dichro T.

(** Corpus row: arxiv:2310.04265#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2310.04265__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2310.04265__01.json
    English statement: (Aboulker, Aubian, Charbit, Lopes, Clique number of tournaments,
      arXiv:2310.04265v1, Question 3.10)
      If a class of tournaments is polynomially dic-bounded, then so is its closure under
      substitution.
    Definitions: [x248_poly_dic_bounded C], [x248_hereditary C], [x248_subst_closure C] (this
      file); [is_tournament D] (conjectures/heroes.v).
    Notes: A class is closed under induced subdigraphs (TeX l.454); only induced-closure is
      required: for an induced-closed C, its closure under isomorphism C' is a class in the
      paper's sense with the same bound (dic and omegabar are isomorphism invariants), and the
      closure of C under substitution lies inside that of C', so the two readings agree. The
      closure is taken without isomorphic copies for the same reason. Substitution follows the
      standard definition: TeX l.668 prints the two arc cases swapped ("V(H_1) => v" when
      vu is an arc), which the proof (l.818) and [CPST13] read as here. Polynomial means c * t^d
      (see [x248_poly_dic_bounded]). The paper proves the non-polynomial version (Theorem 3.9,
      with g(w) = (3w f(w))^w). Literature status: open at the pin (pinned status open). *)
Definition poly_chi_bounded_tournaments_subst_statement : Prop :=
  forall C : diGraphType -> Prop, x248_hereditary C -> (forall D, C D -> is_tournament D) ->
    x248_poly_dic_bounded C -> x248_poly_dic_bounded (x248_subst_closure C).

(** Corpus row: arxiv:2310.04265#05
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2310.04265__05/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2310.04265__05.json
    English statement: (Aboulker, Aubian, Charbit, Lopes, Clique number of tournaments,
      arXiv:2310.04265v1, Conjecture 4.3)
      A tournament H is dic-binding if and only if H has a backedge graph which is a forest.
    Definitions: [ind_free H T] - T has no induced copy of H (conjectures/heroes.v);
      [x221_dichro], [omegabar], [backedge] as above; [is_forest] (coq-graph-theory).
    Notes: H is dic-binding when the H-free tournaments form a dic-bounded class (TeX l.988,
      l.412). The biconditional is encoded as stated (l.1045-1047). Literature status:
      DISPROVED at the pin (pinned status disproved): Aubian, arXiv:2401.07776, Theorem 4.2
      refutes the "if" direction; the "only if" direction is the paper's theorem only_if_part_GS
      (l.1065-1067), so the row is false. *)
Definition chi_binding_iff_forest_backedge_statement : Prop :=
  forall H : tournament,
    (exists f : nat -> nat, forall T : tournament, ind_free H T -> (x221_dichro T <= f (omegabar T))%N) <->
    (exists p : {perm H}, is_forest [set: backedge p]).

(** Corpus row: arxiv:2310.04265#08
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2310.04265__08/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2310.04265__08.json
    English statement: (Aboulker, Aubian, Charbit, Lopes, Clique number of tournaments,
      arXiv:2310.04265v1, Conjecture 5.6)
      There is a function g such that every tournament in which every out-neighbourhood has
      clique number at most t has clique number at most g(t).
    Definitions: [omegabar] as above; [sub_tournament T S] - the sub-tournament on S
      (core/tournament.v).
    Notes: N^+(v) is the out-neighbourhood [set w | v --> w] and its clique number is that of
      the sub-tournament it induces (TeX l.1430-1432); g is chosen before t. Literature
      status: SOLVED at the pin (pinned status solved): Crew, Fan, Koerts, Moore, Spirkl,
      arXiv:2602.09863, Corollary 13. *)
Definition local_to_global_omegabar_statement : Prop :=
  exists g : nat -> nat, forall (t : nat) (T : tournament),
    (forall v : T, (omegabar (sub_tournament [set w | v --> w]) <= t)%N) -> (omegabar T <= g t)%N.

(** Corpus row: arxiv:2310.04265#11
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2310.04265__11/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2310.04265__11.json
    English statement: (Aboulker, Aubian, Charbit, Lopes, Clique number of tournaments,
      arXiv:2310.04265v1, Conjecture 6.1)
      If a class of digraphs is dic-bounded, then so is its closure under substitution.
    Definitions: [x248_dic_bounded C], [x248_omegab_dg D], [x248_hereditary C],
      [x248_subst_closure C] (this file); [oriented_dg D] (conjectures/heroes_dichotomy.v).
    Notes: The paper's digraphs have no loops, no parallel and no anti-parallel arcs (TeX
      l.377), hence the guard that every member is oriented. The clique number of a digraph is
      [x248_omegab_dg] (l.403-406), which equals [omegabar] on tournaments. Classes,
      substitution and its closure are read as at arxiv:2310.04265#01. The tournament case is
      the paper's Theorem 3.9 (l.679-683). Literature status: open at the pin (pinned status
      open). *)
Definition chi_bounded_digraphs_subst_statement : Prop :=
  forall C : diGraphType -> Prop, x248_hereditary C -> (forall D, C D -> oriented_dg D) ->
    x248_dic_bounded C -> x248_dic_bounded (x248_subst_closure C).
