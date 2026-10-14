(** Downstream use of the public neighbourhoods ([Digraph.foundations.neighbourhoods]: [Nout], [Nin],
    [Nout2]) and of the degree_balance additions ([diregular], the degree bridges and the tournament
    equalities), without conjecture imports.  Each example uses public API lemmas and the public
    grounding digraphs of [Digraph.foundations.degree_balance] and [Digraph.core.tournament]. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra.
From Digraph Require Import prelude digraph oriented tournament.
From Digraph.foundations Require Import neighbourhoods degree_balance.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section AnyDigraph.
Variable D : diGraphType.
Implicit Types (u v w : D).

(** Membership is the arc relation, read from either end. *)
Example membership v w : (w \in Nout v) = (v --> w) /\ (v \in Nin w) = (v --> w).
Proof. by rewrite NoutE NinE. Qed.

(** An out-neighbour of an out-neighbour, other than [v] and not itself an out-neighbour, is at
    distance exactly two. *)
Example second_neighbourhood v u w :
  v --> u -> u --> w -> w != v -> ~~ (v --> w) -> w \in Nout2 v.
Proof. exact: (@Nout2I D v u w). Qed.

(** The distance-two exclusion: neither [v] nor an out-neighbour of [v] is at distance two. *)
Example exclusion v : v \notin Nout2 v /\ [disjoint Nout2 v & Nout v].
Proof. by split; [exact: (self_notin_Nout2 v) | exact: (disjoint_Nout2_Nout v)]. Qed.

(** The canonical degrees are the neighbourhood sizes, and the converse swaps the neighbourhoods. *)
Example degrees_converse v :
  [/\ outdeg v = #|Nout v|, indeg v = #|Nin v| & @Nout (converse D) v = Nin v].
Proof. by split; [exact: (outdeg_NoutE v) | exact: (indeg_NinE v) | exact: (Nout_converse v)]. Qed.

(** Diregularity is pointwise and implies balance; the converse has the same diregularity. *)
Example diregular_pointwise d :
  diregular D d -> [/\ forall v, outdeg v = d /\ indeg v = d, balanced D & diregular (converse D) d].
Proof. by move=> r; split; [exact/diregularP | exact: (@diregular_balanced D d r) | rewrite diregular_converse]. Qed.

(** An arcless digraph has empty neighbourhoods and is 0-diregular. *)
Example arcless v :
  (forall x y : D, ~~ (x --> y)) -> [/\ Nout v = set0, Nout2 v = set0 & diregular D 0].
Proof.
by move=> none; split; [exact: (arcless_Nout none v) | exact: (arcless_Nout2 none v) | exact: (diregular_arcless none)].
Qed.

End AnyDigraph.

(** ** Concrete corners *)

(** The empty digraph is [d]-diregular for every [d] (vacuously), the arcless vertex is 0-diregular, and
    the one-vertex loop is 1-diregular: the loop counts once on each side. *)
Example diregular_corners :
  [/\ forall d, diregular empty_dg d, diregular arcless1 0 & diregular loop1 1].
Proof.
split.
- by move=> d; apply: diregular_card0; exact: card_ord.
- by apply: diregular_arcless.
- have [b i] := balanced_ground_loop.
  by apply/diregularP=> v; rewrite -(b v) i.
Qed.

(** A loop does not create a vertex at distance two: the one-vertex loop has an empty [Nout2]. *)
Example loop_no_second_neighbourhood (v : loop1) : (v \in Nout v) /\ Nout2 v = set0.
Proof.
split; first by rewrite NoutE.
by apply/setP=> w; rewrite in_set0; apply/negP=> /Nout2_neq; rewrite (ord1 w) (ord1 v) eqxx.
Qed.

(** The digon is 1-diregular, and its return walk [v --> w --> v] does not put [v] at distance two:
    [Nout2] is empty. *)
Example digon_corner (v : digon) : diregular digon 1 /\ Nout2 v = set0.
Proof.
have arcE : forall x y : digon, (x --> y) = (x != y) by [].
have c2 : #|{: digon}| = 2 := card_ord 2.
split.
  apply/diregularP=> u; have o : outdeg u = 1.
    rewrite outdeg_NoutE (_ : Nout u = [set~ u]) ?cardsC1 ?c2 //.
    by apply/setP=> w; rewrite NoutE arcE !inE eq_sym.
  by split=> //; rewrite (balanced_ground_digon u).
apply/setP=> w; rewrite in_set0; apply/negP=> /Nout2P[wv nvw _].
by move: nvw; rewrite arcE eq_sym wv.
Qed.

(** Two disjoint loops: 1-diregular and disconnected (no connectivity premise). *)
Example twoloops_diregular : diregular twoloops 1.
Proof.
have arcE : forall x y : twoloops, (x --> y) = (x == y) by [].
apply/diregularP=> v; have o : outdeg v = 1.
  rewrite outdeg_NoutE (eq_card1 (x := v)) // => w.
  by rewrite NoutE arcE inE eq_sym.
have [b _] := balanced_ground_disconnected.
by split=> //; rewrite (b v).
Qed.

(** The directed triangle is 1-diregular; the single arc [TT 2] is diregular of no degree. *)
Example triangle_and_single_arc : diregular C3 1 /\ forall d, ~~ diregular (TT 2) d.
Proof.
split.
  apply/diregularP=> v; have o : outdeg v = 1.
    rewrite outdeg_NoutE (_ : Nout v = [set (v + 1)%R]) ?cards1 //.
    by apply/setP=> w; rewrite NoutE inE arcC3E.
  by split=> //; rewrite (balanced_ground_C3 v).
by move=> d; apply/negP=> /diregular_balanced; exact: not_balanced_ground_TT2.
Qed.

(** In a transitive tournament every vertex at distance two is already an out-neighbour, so the
    second out-neighbourhood is empty. *)
Example TT_no_second_neighbourhood n (v : TT n) : Nout2 v = set0.
Proof.
apply/setP=> w; rewrite in_set0; apply/negP=> /Nout2P[_ nvw [u vu uw]].
move: nvw vu uw; rewrite !arcTTE => nvw vu uw.
by rewrite (ltn_trans vu uw) in nvw.
Qed.

(** In a tournament, [N_out]/[N_in] are the general neighbourhoods, and in- plus out-degree is
    [#|T| - 1]: 2 in the directed triangle. *)
Example tournament_neighbourhoods (T : tournament) (u : T) :
  [/\ N_out u = Nout u, N_in u = Nin u & indeg u + outdeg u = #|T|.-1].
Proof. by split; [exact: (tournament_N_outE u) | exact: (tournament_N_inE u) | exact: (tournament_indeg_outdeg u)]. Qed.

Example triangle_degree_sum (v : C3) : indeg v + outdeg v = 2.
Proof. by rewrite (tournament_indeg_outdeg (v : (C3 : tournament))) card_C3. Qed.

Print Assumptions exclusion.
Print Assumptions digon_corner.
Print Assumptions triangle_and_single_arc.
Print Assumptions tournament_neighbourhoods.
