(** * Digraph.foundations.cycles — two reusable counting/extraction lemmas

    Both are graph-theory-free combinatorics used by the conjecture implication
    edges of wave E3:

    1. [min_deg2_has_cycle] (for corpus edge e020, X2): a simple graph with a
       NONEMPTY vertex set [S] in which every vertex has at least two neighbours
       inside [S] contains a cycle — a [ucycle] on more than two vertices.  This
       is the "degeneracy >= 2 implies not a forest" half of the standard
       characterisation, proved by taking a LONGEST duplicate-free walk inside
       [S] ([ex_maxnP] over the sizes, which are bounded by [#|G|]): the last
       vertex of such a walk has all its [S]-neighbours on the walk, and one of
       them is not its predecessor, which closes a cycle on at least three
       vertices.

    2. [laminar_sum_bound] (for corpus edge e172, P9): if a list [P] of
       duplicate-free vertex sequences is LAMINAR in the Hoàng–Reed sense (the
       j-th member meets the union of the earlier ones in at most one vertex)
       then [\sum_(i < m) size P_i <= #|union of the first m| + m - 1].  With
       [m = size P] this is the counting step "r cycles pairwise sharing at most
       one vertex have total length at most n + r - 1". *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** 1. Minimum degree two inside a set forces a cycle *)

Lemma sorted_rcons_edge (T : Type) (e : rel T) (a : T) (s : seq T) (w : T) :
  sorted e (a :: s) -> e (last a s) w -> sorted e (rcons (a :: s) w).
Proof. by move=> h1 h2; rewrite rcons_cons /= rcons_path h2 andbT; exact: h1. Qed.

Lemma lt_leq_pred (i k : nat) : i < k -> i <= k.-1.
Proof. by case: k => [//|k]; rewrite ltnS. Qed.

Lemma last_drop (T : Type) (x : T) (s : seq T) (i : nat) :
  i < size s -> last x (drop i s) = last x s.
Proof.
elim: s i => [i|b l IH i]; first by rewrite ltn0.
case: i => [_|i hi]; first by rewrite drop0.
by rewrite /= (IH i hi); move: hi {IH}; case: l => [|c l'] /=.
Qed.

Section MinDegreeCycle.
Variable G : sgraph.

(** A duplicate-free walk all of whose vertices lie in [S]. *)
Definition walk_in (S : {set G}) (s : seq G) : bool :=
  [&& uniq s, all (mem S) s & sorted (--) s].

Lemma walk_in_size (S : {set G}) (s : seq G) : walk_in S s -> size s <= #|G|.
Proof.
by case/and3P=> us _ _; move/card_uniqP: us => <-; exact: max_card.
Qed.

Lemma min_deg2_has_cycle (S : {set G}) :
  S != set0 -> (forall x : G, x \in S -> 2 <= #|N(x) :&: S|) ->
  exists c : seq G, ucycle (--) c /\ 2 < size c.
Proof.
move=> /set0Pn[x0 x0S] degS.
pose Q := fun n => [exists t : n.-tuple G, walk_in S (val t)].
have Q1 : Q 1.
  by apply/existsP; exists [tuple x0]; rewrite /walk_in /= x0S.
have exQ : exists n, Q n by exists 1.
have ubQ : forall n, Q n -> n <= #|G|.
  by move=> n /existsP[t ht]; rewrite -(size_tuple t); exact: walk_in_size ht.
have [m /existsP[t ht] maxm] := ex_maxnP exQ ubQ.
have m1 : 1 <= m := maxm 1 Q1.
have szt : size (val t) = m := size_tuple t.
move: ht szt; case: (val t) => [|a s']; first by move=> _ e; move: m1; rewrite -e.
move=> /and3P[us aS ss] szs.
(* the last vertex of the maximal walk has all its S-neighbours ON the walk *)
have zS : last a s' \in S by move/allP: aS; apply; exact: mem_last.
have hsub : forall w : G, w \in N(last a s') :&: S -> w \in a :: s'.
  move=> w; rewrite !inE => /andP[hzw wS]; apply: contraT => wns.
  have : Q m.+1.
    apply/existsP.
    have szr : size (rcons (a :: s') w) == m.+1 by rewrite size_rcons szs.
    exists (Tuple szr); apply/and3P; split.
    - by rewrite rcons_uniq us andbT.
    - apply/allP => v; rewrite mem_rcons inE => /orP[/eqP->|hv] //.
      exact: (allP aS).
    - exact: sorted_rcons_edge ss hzw.
  by move/maxm; rewrite ltnn.
have zsq : last a s' = nth a (a :: s') m.-1 by rewrite -szs nth_last.
(* every S-neighbour of the last vertex sits strictly before it *)
have hidx : forall w : G, w \in N(last a s') :&: S -> index w (a :: s') < m.-1.
  move=> w wN; have wsq := hsub _ wN.
  have hw : index w (a :: s') < m by rewrite -szs index_mem.
  have wz : w != last a s'.
    by apply: contraTneq (wN) => ->; rewrite !inE sg_irrefl.
  rewrite ltn_neqAle; apply/andP; split; last exact: lt_leq_pred hw.
  apply/eqP => hidxw; apply: (negP wz); apply/eqP.
  by rewrite zsq -hidxw (nth_index a wsq).
have [y yN yi] : exists2 y : G, y \in N(last a s') :&: S
                              & index y (a :: s') < m.-2.
  apply/exists_inP; apply: contraT; rewrite negb_exists_in => /forall_inP h.
  have hcard : #|N(last a s') :&: S| <= 1.
    apply: leq_trans (_ : #|[set nth a (a :: s') m.-2]| <= 1);
      last by rewrite cards1.
    apply: subset_leq_card; apply/subsetP => w wN; rewrite inE.
    have hle : m.-2 <= index w (a :: s') by rewrite leqNgt; exact: (h _ wN).
    have hlt : index w (a :: s') <= m.-2.
      by apply: lt_leq_pred; exact: (hidx _ wN).
    by rewrite -(nth_index a (hsub _ wN)) (anti_leq (introT andP (conj hlt hle))).
  by move: (leq_trans (degS _ zS) hcard).
(* the walk piece from y to the last vertex, closed by the edge, is a cycle *)
have hi : index y (a :: s') < size (a :: s').
  by rewrite szs; apply: leq_trans yi (leq_trans (leq_pred _) (leq_pred _)).
have hdrop : drop (index y (a :: s')) (a :: s')
             = y :: drop (index y (a :: s')).+1 (a :: s').
  by rewrite (drop_nth a hi) nth_index //; exact: hsub.
have hsorted : sorted (--) (drop (index y (a :: s')) (a :: s')).
  move: ss; rewrite -{1}(cat_take_drop (index y (a :: s')) (a :: s')).
  case: (take (index y (a :: s')) (a :: s')) => [//|b l] /=.
  by rewrite cat_path => /andP[_]; exact: path_sorted.
have hlast : last y (drop (index y (a :: s')).+1 (a :: s')) = last a s'.
  transitivity (last a (drop (index y (a :: s')) (a :: s')));
    first by rewrite hdrop /=.
  exact: (last_drop a hi).
exists (drop (index y (a :: s')) (a :: s')); split.
  rewrite /ucycle drop_uniq // andbT hdrop /= rcons_path.
  apply/andP; split; first by move: hsorted; rewrite hdrop.
  rewrite hlast; move: yN; rewrite inE => /andP[hy _].
  by move: hy; rewrite inE.
by rewrite size_drop szs ltn_subRL addnC -ltn_subRL subn2.
Qed.

End MinDegreeCycle.

(** ** 2. The laminar (intersection-forest) counting bound *)

Section LaminarBound.
Variable T : finType.
Implicit Type P : seq (seq T).

(** The union of the vertex sets of the first [m] members of [P]. *)
Definition lam_union P (m : nat) : {set T} :=
  \bigcup_(i < m) [set v : T | v \in nth [::] P i].

Lemma lam_unionS P (m : nat) :
  lam_union P m.+1 = lam_union P m :|: [set v : T | v \in nth [::] P m].
Proof. by rewrite /lam_union big_ord_recr. Qed.

Lemma laminar_sum_bound P :
  all uniq P ->
  (forall j : 'I_(size P), 0 < j ->
     #|[set v : T | (v \in nth [::] P j) &&
          [exists i : 'I_(size P), (i < j) && (v \in nth [::] P i)]]| <= 1) ->
  forall m, m <= size P ->
    \sum_(i < m) size (nth [::] P i) <= #|lam_union P m| + m.-1.
Proof.
move=> uP lam; elim=> [_|m IH hm]; first by rewrite big_ord0.
have hmP : m < size P := hm.
have hsize : #|[set v : T | v \in nth [::] P m]| = size (nth [::] P m).
  rewrite cardsE; apply/card_uniqP; exact: (allP uP _ (mem_nth [::] hmP)).
have hcap : #|lam_union P m :&: [set v : T | v \in nth [::] P m]| <= (m != 0).
  case: (posnP m) => [->|hm0].
    by rewrite /lam_union big_ord0 set0I cards0.
  apply: leq_trans (lam (Ordinal hmP) hm0).
  apply: subset_leq_card; apply/subsetP => v.
  rewrite !inE => /andP[/bigcupP[i _]]; rewrite inE => hiv hvm.
  rewrite hvm /=; apply/existsP; exists (widen_ord (ltnW hmP) i).
  by rewrite /= ltn_ord.
have hstep : #|lam_union P m| + size (nth [::] P m)
             <= #|lam_union P m.+1| + (m != 0).
  rewrite lam_unionS -hsize -cardsUI.
  by rewrite leq_add2l.
rewrite big_ord_recr /=; apply: (leq_trans (leq_add (IH (ltnW hm)) (leqnn _))).
rewrite -addnA [(m.-1 + _)%N]addnC addnA.
apply: (leq_trans (leq_add hstep (leqnn _))).
by rewrite -addnA leq_add2l; case: m {IH hm hmP hsize hcap hstep} => [|k] //=;
   rewrite addnC.
Qed.

End LaminarBound.
