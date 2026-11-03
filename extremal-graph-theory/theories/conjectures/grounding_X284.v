(** * Extremal.conjectures.grounding_X284 -- grounding certificates of wave X284.

    For each of the two rows: hyp_inhabited (the hypotheses hold on a concrete instance, and the statement gives its
    consequence there) and not_trivially_true in the contract form (a variant obtained from the body by deleting one
    hypothesis or guard is false and implies the row).  The wave has no helper.
    - Rainbow cycles: K_2 with a constant colouring is properly coloured, meets the degree bound for C = 1 and has no
      cycle at all; the statement for C = N = 4 gives a properly coloured graph with more edges than vertices (so
      with cycles) and no rainbow cycle.  Without the range 2^L <= n of the degree bound the row is false at
      C = N = 1: no graph with a vertex has C * (n * L) <= 2 |E(G)| for every L.
    - Erdos #584: on K_2, H_1 = H_2 = E(K_2) meet the body with d = 1 (one edge, no pair to check); the statement
      gives a nonempty H_2 in every graph with an edge.  If the pairs of H_1 may be equal, the row is false at K_2:
      the edge of H_1 would lie on a cycle of K_2, which has two vertices. *)

From Extremal.conjectures Require Import X284.
From GTBase Require Import base edge_colourings.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** K_2 *)

Lemma g284_K2_edge : #|E('K_2)| = 1.
Proof. by rewrite card_edge_Kn. Qed.

(** K_2 has no cycle, for any relation: a cycle has more than two distinct vertices. *)
Lemma g284_K2_no_cycle (r : rel 'K_2) (c : seq 'K_2) : ~ seq_cycle r c.
Proof.
move=> [/andP[_ uc] sz]; move: sz; rewrite ltnNge => /negP; apply.
by rewrite -(card_uniqP uc); apply: leq_trans (max_card _) _; rewrite card_ord.
Qed.

Lemma g284_K2_one_edge (e f : {set 'K_2}) : e \in E('K_2) -> f \in E('K_2) -> e = f.
Proof.
move=> eE fE; have /card_le1_eqP : #|E('K_2)| <= 1 by rewrite g284_K2_edge.
by apply.
Qed.

(** ** Row 1: arxiv:2309.04460#00 *)

(** K_2 meets the degree bound for C = 1: 2^L <= 2 forces L <= 1. *)
Lemma g284_K2_degree (L : nat) : 2 ^ L <= #|'K_2| -> 1 * (#|'K_2| * L) <= 2 * #|E('K_2)|.
Proof.
rewrite g284_K2_edge card_ord; case: L => [|[|L]] //.
by rewrite !expnS mulnA leqNgt (leq_trans _ (leq_pmulr _ (expn_gt0 2 L))).
Qed.

Definition g284_rc_hyp_claim : Prop :=
  (exists (G : sgraph) (col : {set G} -> nat),
     [/\ 2 <= #|G|, proper_edge_colouring col,
         forall L : nat, 2 ^ L <= #|G| -> 1 * (#|G| * L) <= 2 * #|E(G)| &
         forall c : seq G, seq_cycle (--) c -> ~~ uniq (map col (seq_cycle_edge_list c))]) /\
  (rainbow_cycle_log_degree_insufficient_statement ->
     exists (G : sgraph) (col : {set G} -> nat),
       [/\ #|G| < #|E(G)|, proper_edge_colouring col &
           forall c : seq G, seq_cycle (--) c -> ~~ uniq (map col (seq_cycle_edge_list c))]).

Theorem g284_rc_hyp_inhabited : g284_rc_hyp_claim.
Proof.
split.
  exists ('K_2), (fun _ => 0); split.
  - by rewrite card_ord.
  - exact: proper_edge_colouring_K2.
  - exact: g284_K2_degree.
  - by move=> c /g284_K2_no_cycle.
move=> S; have [G [col [N4 pr bd nr]]] := S 4 4; exists G, col; split=> //.
move: (bd 2 N4); rewrite (mulnC #|G| 2) mulnCA leq_pmul2l // => h4.
by apply: leq_trans h4; rewrite ltn_Pmull // (leq_trans _ N4).
Qed.

(** The variant asking the degree bound for every L, without the range 2^L <= n. *)
Definition g284_rc_every_L : Prop :=
  forall C N : nat, exists (G : sgraph) (col : {set G} -> nat),
    [/\ N <= #|G|, proper_edge_colouring col,
        forall L : nat, C * (#|G| * L) <= 2 * #|E(G)| &
        forall c : seq G, seq_cycle (--) c -> ~~ uniq (map col (seq_cycle_edge_list c))].

Definition g284_rc_ntt_claim : Prop :=
  ~ g284_rc_every_L /\ (g284_rc_every_L -> rainbow_cycle_log_degree_insufficient_statement).

Theorem g284_rc_not_trivially_true : g284_rc_ntt_claim.
Proof.
split; last first.
  by move=> h C N; have [G [col [NG pr bd nr]]] := h C N; exists G, col; split=> // L _; exact: bd.
move=> h; have [G [col [NG _ bd _]]] := h 1 1.
move: (bd (2 * #|E(G)|).+1); rewrite mul1n => h'.
by have := leq_trans (leq_pmull _ NG) h'; rewrite ltnn.
Qed.

(** ** Row 2: erdos:584 *)

Definition g284_e584_hyp_claim : Prop :=
  ((exists2 H1 : {set {set 'K_2}}, H1 \subset E('K_2) &
      [/\ #|E('K_2)| ^ 3 <= 1 * (#|H1| * #|'K_2| ^ 4),
          forall e f, e \in H1 -> f \in H1 -> e != f ->
            exists2 c : seq ('K_2), seq_cycle (fun x y => [set x; y] \in H1) c &
              [/\ size c <= 6, e \in seq_cycle_edge_list c & f \in seq_cycle_edge_list c] &
          forall e f, e \in H1 -> f \in H1 -> e != f -> e :&: f != set0 ->
            exists2 c : seq ('K_2), seq_cycle (fun x y => [set x; y] \in H1) c &
              [/\ size c = 4, e \in seq_cycle_edge_list c & f \in seq_cycle_edge_list c]]) /\
   (exists2 H2 : {set {set 'K_2}}, H2 \subset E('K_2) &
      #|E('K_2)| ^ 2 <= 1 * (#|H2| * #|'K_2| ^ 2) /\
      forall e f, e \in H2 -> f \in H2 -> e != f ->
        exists2 c : seq ('K_2), seq_cycle (fun x y => [set x; y] \in H2) c &
          [/\ size c <= 8, e \in seq_cycle_edge_list c & f \in seq_cycle_edge_list c])) /\
  (erdos_584_short_cycle_subgraphs_statement ->
     forall G : sgraph, 0 < #|E(G)| -> exists2 H2 : {set {set G}}, H2 \subset E(G) & 0 < #|H2|).

Theorem g284_e584_hyp_inhabited : g284_e584_hyp_claim.
Proof.
split.
  have ne : forall e f, e \in E('K_2) -> f \in E('K_2) -> e != f -> False.
    by move=> e f eE fE; rewrite (g284_K2_one_edge eE fE) eqxx.
  split; exists E('K_2) => //; rewrite g284_K2_edge card_ord.
    by split=> // e f eE fE ef; [case: (ne e f eE fE ef) | move=> _; case: (ne e f eE fE ef)].
  by split=> // e f eE fE ef; case: (ne e f eE fE ef).
move=> [d [d0 h]] G EG; have [_ [H2 H2E [b2 _]]] := h G; exists H2 => //.
rewrite lt0n; apply/negP => /eqP H0; move: b2; rewrite H0 mul0n muln0 leqn0 expn_eq0 andbT.
by move/eqP => E0; rewrite E0 in EG.
Qed.

(** The variant whose first H_1 clause also takes equal edges (no e != f). *)
Definition g284_e584_any_pair : Prop :=
  exists d : nat, 0 < d /\ forall G : sgraph,
    (exists2 H1 : {set {set G}}, H1 \subset E(G) &
       [/\ #|E(G)| ^ 3 <= d * (#|H1| * #|G| ^ 4),
           forall e f, e \in H1 -> f \in H1 ->
             exists2 c : seq G, seq_cycle (fun x y => [set x; y] \in H1) c &
               [/\ size c <= 6, e \in seq_cycle_edge_list c & f \in seq_cycle_edge_list c] &
           forall e f, e \in H1 -> f \in H1 -> e != f -> e :&: f != set0 ->
             exists2 c : seq G, seq_cycle (fun x y => [set x; y] \in H1) c &
               [/\ size c = 4, e \in seq_cycle_edge_list c & f \in seq_cycle_edge_list c]]) /\
    (exists2 H2 : {set {set G}}, H2 \subset E(G) &
       #|E(G)| ^ 2 <= d * (#|H2| * #|G| ^ 2) /\
       forall e f, e \in H2 -> f \in H2 -> e != f ->
         exists2 c : seq G, seq_cycle (fun x y => [set x; y] \in H2) c &
           [/\ size c <= 8, e \in seq_cycle_edge_list c & f \in seq_cycle_edge_list c]).

Definition g284_e584_ntt_claim : Prop :=
  ~ g284_e584_any_pair /\ (g284_e584_any_pair -> erdos_584_short_cycle_subgraphs_statement).

Theorem g284_e584_not_trivially_true : g284_e584_ntt_claim.
Proof.
split; last first.
  move=> [d [d0 h]]; exists d; split=> // G; have [[H1 H1E [b1 c1 c2]] h2] := h G.
  by split=> //; exists H1 => //; split=> // e f eH fH _; exact: c1.
move=> [d [d0 h]]; have [[H1 H1E [b1 c1 _]] _] := h ('K_2).
have : 0 < #|H1|.
  rewrite lt0n; apply/negP => /eqP H0; move: b1; rewrite H0 g284_K2_edge.
  by rewrite mul0n muln0.
case/card_gt0P => f fH; have [c cyc _] := c1 f f fH fH.
exact: g284_K2_no_cycle cyc.
Qed.
