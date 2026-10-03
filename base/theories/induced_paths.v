(** * GTBase.induced_paths — induced (chordless) vertex-sequence paths

    Library migration B22, family [induced-path] (meta/library_primitives/induced-path.json).  An
    induced path is a duplicate-free vertex sequence that follows host edges and has no chord: every
    host edge between two of its vertices joins consecutive entries ([seq_consecutive],
    GTBase.walks_paths).  Five views share this core and differ only in what they say about the ends
    and the length:
    - [induced_path p]: the empty sequence is allowed (Chromatic X3);
    - [nonempty_induced_path p]: a nonempty sequence (GTMisc X91);
    - [induced_path_between a b p]: a nonempty sequence from [a] to [b], endpoint inclusive
      (Extremal X98, GTMisc X114, Packing U9, and the pattern-edge field of the public strong
      induced-subdivision Record [GTBase.induced_subdivisions.induced_subdivision_model]);
    - [long_induced_path_between a b p]: the previous view with at least three vertices (Minor X67);
    - [has_induced_path_of_order t]: some nonempty induced path has exactly [t] vertices (GTMisc X208).
    The bodies keep the exact match/conjunction shapes of the migrated helpers, so the X3, X91, X98,
    X114 and X67 aliases and the Record field are conversions.  U9's Boolean [spath]/[consec]
    encoding and X208's index encoding are bridged by explicit theorems with their membership and
    uniqueness premises ([seq_consecutive_index], [chordless_nthP]): the index test
    [(index u p).+1 == index v p] agrees with consecutiveness only for members of a duplicate-free
    list, so no unconditional index bridge is claimed.  A singleton is an induced path; the empty
    sequence is accepted by [induced_path] only; repeated entries are rejected; reversal exchanges
    the endpoints; no nonempty induced path has order 0, and one of order 1 exists exactly when the
    graph has a vertex.

    Distinct, untouched: Chromatic X177's tail-list path with its documented tautological chord
    clause, Chromatic X218's induced-run condition, induced cycles and holes, and upstream
    [upath]/[IPath] (irredundant walks, chords allowed).  This module imports [GTBase.base] (which
    re-exports walks_paths) and is not re-exported by [base]. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section InducedPaths.
Variable G : sgraph.
Implicit Types (p q : seq G) (a b u v x y : G).

(** No chord: a host edge between two distinct entries joins consecutive entries. *)
Definition chordless p : Prop :=
  forall u v : G, u \in p -> v \in p -> u -- v -> u != v -> seq_consecutive p u v.

(** The empty-allowed view (the X3 shape). *)
Definition induced_path p : Prop :=
  [/\ uniq p,
      (if p is u :: q then path (--) u q else true)
    & forall u v : G,
        u \in p -> v \in p -> u != v -> u -- v ->
        seq_consecutive p u v].

(** The nonempty view (the X91 shape). *)
Definition nonempty_induced_path p : Prop :=
  match p with
  | [::] => False
  | x :: q =>
      uniq p /\
      path (--) x q /\
      forall u v : G,
        u \in p -> v \in p -> u -- v -> u != v ->
        seq_consecutive p u v
  end.

(** The full-endpoint view (the X98 / X114 shape, also the public Record field). *)
Definition induced_path_between a b p : Prop :=
  match p with
  | [::] => False
  | x :: q =>
      x = a /\
      last x q = b /\
      uniq p /\
      path (--) x q /\
      forall u v : G,
        u \in p -> v \in p -> u -- v -> u != v ->
        seq_consecutive p u v
  end.

(** The full-endpoint view with at least three vertices (the X67 shape). *)
Definition long_induced_path_between a b p : Prop :=
  match p with
  | [::] => False
  | x :: q =>
      x = a /\
      last x q = b /\
      3 <= size p /\
      uniq p /\
      path (--) x q /\
      forall u v : G,
        u \in p -> v \in p -> u -- v -> u != v ->
        seq_consecutive p u v
  end.

(** Some nonempty induced path has exactly [t] vertices (the X208 contract). *)
Definition has_induced_path_of_order (t : nat) : Prop :=
  exists p : seq G, size p = t /\ nonempty_induced_path p.

(** ** The views in terms of the core *)

Lemma chordlessE p :
  chordless p <->
  forall u v : G, u \in p -> v \in p -> u != v -> u -- v -> seq_consecutive p u v.
Proof. by split=> h u v up vp h1 h2; apply: h. Qed.

Lemma induced_pathP p : induced_path p <-> [/\ uniq p, sorted (--) p & chordless p].
Proof. by case: p => [|x q]; split=> -[u s c]; split=> //= v w vp wp h1 h2; apply: c. Qed.

Lemma nonempty_induced_pathP p : nonempty_induced_path p <-> p != [::] /\ induced_path p.
Proof.
case: p => [|x q] /=; first by split=> [|[]].
split=> [[u [pth c]] | [_ [u pth c]]]; split=> //.
  by split=> // z w zp wp ne zw; exact: c.
by split=> // z w zp wp zw ne; exact: c.
Qed.

Lemma induced_path_betweenP a b p :
  induced_path_between a b p <-> [/\ nonempty_induced_path p, head a p = a & last a p = b].
Proof.
case: p => [|x q] /=; first by split=> [|[]].
split=> [[xa [lst [u [pth c]]]] | [[u [pth c]] xa lst]]; last by do ?split.
by split=> //; split=> //; split.
Qed.

Lemma long_induced_path_betweenP a b p :
  long_induced_path_between a b p <-> induced_path_between a b p /\ 3 <= size p.
Proof.
case: p => [|x q] /=; first by split=> [|[]].
split=> [[xa [lst [sz [u [pth c]]]]] | [[xa [lst [u [pth c]]]] sz]]; by do ?split.
Qed.

(** ** Projections *)

Lemma induced_path_uniq p : induced_path p -> uniq p.
Proof. by case. Qed.

Lemma induced_path_sorted p : induced_path p -> sorted (--) p.
Proof. by case: p => [|x q] [_ s _]. Qed.

Lemma induced_path_chordless p : induced_path p -> chordless p.
Proof. by move/induced_pathP => []. Qed.

Lemma nonempty_induced_path_induced p : nonempty_induced_path p -> induced_path p.
Proof. by move/nonempty_induced_pathP => []. Qed.

Lemma induced_path_between_nonempty a b p : induced_path_between a b p -> nonempty_induced_path p.
Proof. by move/induced_path_betweenP => []. Qed.

Lemma induced_path_between_head a b p : induced_path_between a b p -> head a p = a.
Proof. by move/induced_path_betweenP => []. Qed.

Lemma induced_path_between_last a b p : induced_path_between a b p -> last a p = b.
Proof. by move/induced_path_betweenP => []. Qed.

Lemma induced_path_between_mem a b p : induced_path_between a b p -> a \in p /\ b \in p.
Proof.
case: p => [|x q] // [<- [<- _]]; split; first by rewrite inE eqxx.
exact: mem_last.
Qed.

Lemma long_induced_path_between_size a b p : long_induced_path_between a b p -> 3 <= size p.
Proof. by move/long_induced_path_betweenP => []. Qed.

(** ** Small sequences *)

Lemma induced_path_nil : induced_path [::].
Proof. by split=> // u v; rewrite in_nil. Qed.

Lemma not_nonempty_induced_path_nil : ~ nonempty_induced_path [::].
Proof. by []. Qed.

Lemma not_induced_path_between_nil a b : ~ induced_path_between a b [::].
Proof. by []. Qed.

Lemma nonempty_induced_path_seq1 x : nonempty_induced_path [:: x].
Proof.
split=> //; split=> // u v; rewrite !inE => /eqP-> /eqP-> _.
by rewrite eqxx.
Qed.

Lemma induced_path_seq1 x : induced_path [:: x].
Proof. exact: nonempty_induced_path_induced (nonempty_induced_path_seq1 x). Qed.

Lemma induced_path_between_seq1 a b x : induced_path_between a b [:: x] <-> x = a /\ x = b.
Proof.
split=> [[xa [xb _]] // | [xa xb]].
have [_ [_ c]] := nonempty_induced_path_seq1 x.
by split=> //=; split=> //; split=> //; split.
Qed.

Lemma not_induced_path_repeat x p : ~ induced_path (x :: x :: p).
Proof. by case=> /= /andP[]; rewrite inE eqxx /=. Qed.

Lemma not_induced_path_dup p : ~~ uniq p -> ~ induced_path p.
Proof. by move=> nu /induced_path_uniq; rewrite (negbTE nu). Qed.

(** ** Exact orders *)

Lemma has_induced_path_of_order0 : ~ has_induced_path_of_order 0.
Proof. by case=> [[|x q]] []. Qed.

Lemma has_induced_path_of_order1 : has_induced_path_of_order 1 <-> 0 < #|G|.
Proof.
split=> [[[|x [|y q]] [//= _ _]] | /card_gt0P[x _]].
  by apply/card_gt0P; exists x.
by exists [:: x]; split=> //; exact: nonempty_induced_path_seq1.
Qed.

(** ** Reversal exchanges the endpoints *)

Lemma induced_path_rev p : induced_path (rev p) <-> induced_path p.
Proof.
have sym : (fun z : G => edge_rel^~ z) =2 (--) by move=> z y /=; exact: sg_sym.
have revs : sorted (--) (rev p) = sorted (--) p by rewrite rev_sorted (eq_sorted sym).
split=> /induced_pathP[u s c]; apply/induced_pathP; split.
- by rewrite rev_uniq in u.
- by rewrite revs in s.
- by move=> x y xp yp xy ne; apply: (seq_consecutive_rev p x y).1; apply: c; rewrite ?mem_rev.
- by rewrite rev_uniq.
- by rewrite revs.
- by move=> x y xp yp xy ne; rewrite mem_rev in xp; rewrite mem_rev in yp; apply: (seq_consecutive_rev p x y).2; apply: c.
Qed.

Lemma head_rev_last a p : head a (rev p) = last a p.
Proof. by case: p => [|x q] //; rewrite -nth0 nth_rev // subn1 nth_last. Qed.

Lemma last_rev_head a p : last a (rev p) = head a p.
Proof. by rewrite -{2}(revK p) head_rev_last. Qed.

Lemma induced_path_between_rev a b p :
  induced_path_between a b p -> induced_path_between b a (rev p).
Proof.
case: p => [|z q] // [hz [lst [up [srt c]]]].
apply/induced_path_betweenP; split.
- apply/nonempty_induced_pathP; split; first by rewrite -size_eq0 size_rev.
  apply/induced_path_rev; apply: nonempty_induced_path_induced.
  by do ?split.
- by rewrite head_rev_last /= lst.
- by rewrite last_rev_head /= hz.
Qed.

(** ** Index bridges, with the membership and uniqueness premises they need *)

Lemma infix_pair_index p u v : uniq p -> infix [:: u; v] p -> (index u p).+1 = index v p.
Proof.
move=> up /infixP[s1 [s2 e]]; rewrite e in up *.
move: up; rewrite cat_uniq /= => /and3P[_ /norP[us1 /norP[vs1 _]] /andP[uv _]].
rewrite inE negb_or in uv; have [uv' _] := andP uv.
rewrite !index_cat (negbTE us1) (negbTE vs1) /= (negbTE uv') !eqxx /=.
by rewrite addn0 addn1.
Qed.

Lemma index_pair_infix p u v :
  u \in p -> v \in p -> (index u p).+1 = index v p -> infix [:: u; v] p.
Proof.
move=> up vp e; apply/infixP; exists (take (index u p) p), (drop (index v p).+1 p).
rewrite -{1}(cat_take_drop (index u p) p); congr cat.
by rewrite (drop_nth u) ?index_mem // nth_index // e (drop_nth v) ?index_mem // nth_index.
Qed.

(** For members of a duplicate-free list, consecutiveness is the index relation; without the
    membership premise the index relation can hold for a non-member ([(index a [:: a]).+1 = index b
    [:: a]] for every [b] different from [a]). *)
Lemma seq_consecutive_index p u v :
  uniq p -> u \in p -> v \in p ->
  seq_consecutive p u v <-> (index u p).+1 = index v p \/ (index v p).+1 = index u p.
Proof.
move=> up uq vq; split.
  by move/seq_consecutiveE => [/(infix_pair_index up) | /(infix_pair_index up)]; [left | right].
by move=> [/(index_pair_infix uq vq) | /(index_pair_infix vq uq)] inf; apply/seq_consecutiveE; [left | right].
Qed.

Lemma index_relation_non_member a b : a != b -> (index a [:: a]).+1 = index b [:: a].
Proof. by move=> ab; rewrite /= eqxx (negbTE ab). Qed.

(** The X208 index form: on a duplicate-free nonempty list, chordlessness says that non-consecutive
    positions are not adjacent. *)
Lemma chordless_nthP x q :
  uniq (x :: q) ->
  chordless (x :: q) <->
  (forall i j : nat,
     i.+1 < j -> j < size (x :: q) -> ~~ (nth x (x :: q) i -- nth x (x :: q) j)).
Proof.
set p := x :: q => up; split.
- move=> c i j ij jp; apply/negP => adj.
  have ip : i < size p by apply: ltn_trans jp; exact: ltn_trans (ltnSn i) ij.
  have ne : nth x p i != nth x p j by rewrite nth_uniq // neq_ltn (ltn_trans (ltnSn i) ij).
  have := c _ _ (mem_nth x ip) (mem_nth x jp) adj ne.
  move/(seq_consecutive_index up (mem_nth x ip) (mem_nth x jp)).
  rewrite !index_uniq // => -[e | e]; first by rewrite -e ltnn in ij.
  by have := ltn_trans (ltnSn i) ij; rewrite -e ltnNge leqnSn.
- move=> h u v uq vq uv ne.
  have iu : index u p < size p by rewrite index_mem.
  have iv : index v p < size p by rewrite index_mem.
  have nei : index u p != index v p.
    by apply: contraNneq ne => e; rewrite -(nth_index x uq) -(nth_index x vq) e.
  apply/(seq_consecutive_index up uq vq).
  have [lt | lt] := ltnP (index u p) (index v p).
  + left; apply/eqP; rewrite eqn_leq lt andTb leqNgt; apply/negP => gt.
    by have := h _ _ gt iv; rewrite !nth_index // uv.
  + right; have lt' : index v p < index u p by rewrite ltn_neqAle eq_sym nei lt.
    apply/eqP; rewrite eqn_leq lt' andTb leqNgt; apply/negP => gt.
    by have := h _ _ gt iu; rewrite !nth_index // sg_sym uv.
Qed.

End InducedPaths.
