(** * Extremal.conjectures.grounding_X223 -- grounding lemmas for wave X223.

    For every authored statement of [X223.v] this file records
    (i)  a NON-VACUITY witness (the hypotheses are satisfiable by a concrete
         finite object), and
    (ii) a GUARD-HAS-TEETH lemma (a degenerate candidate is rejected, so the
         guard does restricting work),
    together with sanity lemmas for the vocabulary of the BLOCKED row
    arxiv:2210.16971#01.

    Everything is closed by [Qed]; see the [Print Assumptions] audit at the end. *)

From GTBase Require Import base.
From Extremal.conjectures Require Import X223.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Witness digraphs *)

(** The single directed edge (the oriented graph [K_2] with one arc). *)
Definition x223_arc : diGraph := DiGraph (fun x y : bool => ~~ x && y).

(** Both arcs between two vertices: NOT oriented, and no homomorphism to an arc. *)
Definition x223_bidir : diGraph := DiGraph (fun x y : bool => x != y).

(** The arcless digraph on two vertices. *)
Definition x223_empty : diGraph := DiGraph (fun _ _ : bool => false).

(** ** Row arxiv:2210.16971#00 (directed Sidorenko) *)

(** NON-VACUITY: the single directed edge satisfies all three hypotheses, so the
    class of oriented bipartite graphs with a homomorphism to the arc is
    inhabited. *)
Lemma x223_arc_oriented : oriented x223_arc.
Proof. by move=> [] []. Qed.

Lemma x223_arc_bipartite : x223_bipartite_dg x223_arc.
Proof. by exists id => -[] []. Qed.

Lemma x223_arc_hom_to_arc : x223_hom_to_arc x223_arc.
Proof. by exists id => -[] []. Qed.

(** GUARD HAS TEETH: the homomorphism-to-the-arc guard genuinely bites -- the
    two-way arc pair admits no such homomorphism. *)
Lemma not_hom_to_arc_bidir : ~ x223_hom_to_arc x223_bidir.
Proof.
case=> f Hf.
have [_ H1] := Hf false true isT.
have [H2 _] := Hf true false isT.
by rewrite H1 in H2.
Qed.

Lemma not_oriented_bidir : ~ oriented x223_bidir.
Proof. by move=> /(_ false true isT). Qed.

(** ** Row arxiv:2210.16971#01 (BLOCKED placeholder): the cycle vocabulary *)

(** GUARD HAS TEETH: an arcless digraph has no cycle in its underlying graph,
    so [x223_und_cyclic] is not satisfied by every digraph. *)
Lemma not_und_cyclic_empty : ~ x223_und_cyclic x223_empty.
Proof.
case=> S [S0].
have E : [set uv : x223_empty * x223_empty |
            [&& uv.1 \in S, uv.2 \in S & uv.1 -- uv.2]] = set0.
  by apply/setP => uv; rewrite !inE [uv.1 -- uv.2](_ : _ = false) ?andbF.
by rewrite E cards0 leqn0 => /eqP E0; rewrite E0 in S0.
Qed.

(** NON-VACUITY: the two-way arc pair DOES have a cycle in its underlying
    graph (the two vertices span two arcs). *)
Lemma und_cyclic_bidir : x223_und_cyclic x223_bidir.
Proof.
exists [set: x223_bidir]; split; first by rewrite cardsT card_bool.
have -> : [set uv : x223_bidir * x223_bidir |
             [&& uv.1 \in [set: x223_bidir], uv.2 \in [set: x223_bidir]
               & uv.1 -- uv.2]]
        = [set ((false : x223_bidir), (true : x223_bidir));
              ((true : x223_bidir), (false : x223_bidir))].
  by apply/setP => -[[|] [|]]; rewrite !inE.
by rewrite cardsT card_bool cards2.
Qed.

(** ** Witness graphs for the sparse-pair and Turan rows *)

(** The edgeless graph on two vertices. *)
Lemma compl_K2_edgeless (x y : compl 'K_2) : (x -- y) = false.
Proof. by rewrite /edge_rel /= andbN. Qed.

Lemma compl_K2_opn (v : compl 'K_2) : N(v) = set0.
Proof. by apply/setP => u; rewrite !inE compl_K2_edgeless. Qed.

Lemma compl_K2_cln (v : compl 'K_2) : #|N[v]| = 1.
Proof. by rewrite /closed_neigh compl_K2_opn setU0 cards1. Qed.

Lemma card_compl_K2 : #|compl 'K_2| = 2.
Proof. exact: card_ord. Qed.

(** ** Row arxiv:1810.00058#01 (triangle-free eps-bounded anticomplete pair) *)

(** NON-VACUITY: the edgeless graph on two vertices is triangle-free, has more
    than one vertex, and is eps-bounded for eps = 1. *)
Lemma triangle_free_eps_bounded_satisfiable :
  1 < #|compl 'K_2| /\ induced_free (compl 'K_2) 'K_3 /\
  x223_eps_bounded (compl 'K_2) 1 1.
Proof.
split; first by rewrite card_compl_K2.
split; first by apply: induced_free_card; rewrite card_compl_K2 card_ord.
by move=> v; rewrite compl_K2_cln card_compl_K2.
Qed.

(** GUARD HAS TEETH: eps-boundedness rejects a graph with a dominating vertex --
    ['K_1] is not eps-bounded for any eps <= 1. *)
Lemma not_eps_bounded_K1 : ~ x223_eps_bounded 'K_1 1 1.
Proof.
move=> /(_ ord0); rewrite card_ord !mul1n ltnS leqn0 => /eqP/cards0_eq E.
by have := v_in_clneigh (ord0 : 'K_1); rewrite E inE.
Qed.

(** NON-VACUITY of the anticomplete conclusion: the empty pair is anticomplete,
    so the shape of the conclusion is satisfiable (the content is the SIZE
    bounds). *)
Lemma anticomplete_set0 (G : sgraph) (B : {set G}) : x223_anticomplete set0 B.
Proof. by split; [rewrite disjoints_subset sub0set | move=> a b; rewrite inE]. Qed.

(** ** Row arxiv:1810.00058#02 (c-sparse pairs) *)

Lemma x223_edges_between0 (G : sgraph) (B : {set G}) :
  x223_edges_between set0 B = 0.
Proof.
apply/eqP; rewrite cards_eq0; apply/eqP; apply/setP => uv.
by rewrite !inE.
Qed.

(** NON-VACUITY: the empty pair is c-sparse for every c. *)
Lemma sparse_pair_set0 (G : sgraph) (B : {set G}) (a b : nat) :
  x223_sparse_pair set0 B a b.
Proof.
split; first by rewrite disjoints_subset sub0set.
by rewrite x223_edges_between0 muln0.
Qed.

(** GUARD HAS TEETH: an adjacent pair is NOT 0-sparse, so the c-sparse
    requirement is not automatic. *)
Lemma edges_between_K2_gt0 :
  0 < x223_edges_between (G := 'K_2) [set ord0] [set (Ordinal (isT : 1 < 2))].
Proof.
rewrite /x223_edges_between; apply/card_gt0P.
by exists (ord0, Ordinal (isT : 1 < 2)); rewrite !inE.
Qed.

Lemma not_sparse_pair_K2 :
  ~ x223_sparse_pair (G := 'K_2) [set ord0] [set (Ordinal (isT : 1 < 2))] 0 1.
Proof.
case=> _; rewrite mul1n mul0n leqn0 => /eqP E.
by have := edges_between_K2_gt0; rewrite E.
Qed.

(** ** Row arxiv:1912.02342#00 (VC-dimension Erdos-Hajnal) *)

(** NON-VACUITY: ['K_1] has VC-dimension at most 2 (indeed at most 1), so the
    hypothesis class of the statement is inhabited for d = 2. *)
Lemma vc_dim_leq_K1 : x223_vc_dim_leq 'K_1 2.
Proof. by move=> S _; apply: leq_trans (max_card _) _; rewrite card_ord. Qed.

(** GUARD HAS TEETH: shattering is not automatic -- the single vertex of ['K_1]
    is NOT shattered (no vertex is its own neighbour). *)
Lemma not_shattered_K1 : ~ x223_shattered (G := 'K_1) [set: 'K_1].
Proof.
move=> /(_ [set: 'K_1] (subxx _)) [v]; rewrite setIT => E.
have : (v : 'K_1) \in N(v) by rewrite E inE.
by rewrite inE sg_irrefl.
Qed.

(** ** Row arxiv:2405.05902#01 (induced Turan number in sparse hosts) *)

(** NON-VACUITY: the edgeless graph on two vertices is (1,1)-sparse. *)
Lemma ct_sparse_compl_K2 : x223_ct_sparse (compl 'K_2) 1 1 1.
Proof.
move=> A B _ _; rewrite /x223_edges_between.
have -> : [set uv : compl 'K_2 * compl 'K_2 |
             (uv.1 \in A) && (uv.2 \in B) && (uv.1 -- uv.2)] = set0.
  by apply/setP => uv; rewrite !inE compl_K2_edgeless andbF.
by rewrite cards0.
Qed.

(** GUARD HAS TEETH: the complete graph on two vertices is NOT (1,1)-sparse. *)
Lemma not_ct_sparse_K2 : ~ x223_ct_sparse 'K_2 1 1 1.
Proof.
move=> /(_ [set: 'K_2] [set: 'K_2]).
rewrite cardsT card_ord => /(_ isT isT); rewrite mul1n subnn mul0n leqn0 => /eqP E.
have : 0 < x223_edges_between (G := 'K_2) [set: 'K_2] [set: 'K_2].
  rewrite /x223_edges_between; apply/card_gt0P.
  by exists (ord0, Ordinal (isT : 1 < 2)); rewrite !inE.
by rewrite E.
Qed.

(** ** Print Assumptions audit *)

Print Assumptions x223_arc_oriented.
Print Assumptions x223_arc_bipartite.
Print Assumptions x223_arc_hom_to_arc.
Print Assumptions not_hom_to_arc_bidir.
Print Assumptions not_oriented_bidir.
Print Assumptions not_und_cyclic_empty.
Print Assumptions und_cyclic_bidir.
Print Assumptions triangle_free_eps_bounded_satisfiable.
Print Assumptions not_eps_bounded_K1.
Print Assumptions anticomplete_set0.
Print Assumptions sparse_pair_set0.
Print Assumptions not_sparse_pair_K2.
Print Assumptions vc_dim_leq_K1.
Print Assumptions not_shattered_K1.
Print Assumptions ct_sparse_compl_K2.
Print Assumptions not_ct_sparse_K2.
