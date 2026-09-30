(** * Atlas.foundations.queue_layouts -- from a vertex key to a vertex sequence

    [queue_number_le] (minor-theory width_params) orders the vertices by an
    injective key [G -> nat]; [x158_queue_layout] (topological X158) by the
    positions in a duplicate-free enumeration.  Sorting the enumeration by the
    key makes the two orders agree ([sort_index_lt]). *)

From GTBase Require Import base.
From Topological.conjectures Require Import X158.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Sorting the vertices by an injective key: positions follow the key. *)
Lemma sort_index_lt (G : finType) (key : G -> nat) (a b : G) :
  injective key ->
  let s := sort (fun x y => key x <= key y) (enum G) in
  (index a s < index b s) = (key a < key b).
Proof.
move=> ki s.
have tr : transitive (fun x y : G => key x <= key y) by move=> ??? ; exact: leq_trans.
have to : total (fun x y : G => key x <= key y) by move=> ??; exact: leq_total.
have ss : sorted (fun x y => key x <= key y) s by exact: sort_sorted.
have ms (x : G) : x \in s by rewrite mem_sort mem_enum.
have us : uniq s by rewrite sort_uniq enum_uniq.
have ne x y : x != y -> key x != key y by move=> xy; apply: contra xy => /eqP /ki ->.
apply/idP/idP => h.
- have le := sorted_ltn_index tr ss a b (ms a) (ms b) h.
  have ab : a != b by apply: contraTneq h => ->; rewrite ltnn.
  by rewrite ltn_neqAle le (ne _ _ ab).
- rewrite ltnNge; apply/negP; rewrite leq_eqVlt => /orP [/eqP e|ba].
  + have ab : a = b by apply/eqP; rewrite -(nth_index a (ms a)) -(nth_index a (ms b)) e.
    by rewrite ab ltnn in h.
  + have le := sorted_ltn_index tr ss b a (ms b) (ms a) ba.
    by move: h; rewrite ltnNge le.
Qed.

(** The two named ends of an X158 edge are its ends, and they are adjacent. *)
Lemma x158_edge_ends (G : sgraph) (e : {set G}) (a d : G) :
  e \in x158_edge_set G -> a \in e -> d \in e -> a != d -> e = [set a; d] /\ a -- d.
Proof.
rewrite inE => /existsP [x /existsP [y /andP [xy /eqP ->]]].
rewrite !inE => /orP [] /eqP -> /orP [] /eqP ->; rewrite ?eqxx //= => _.
by split; [rewrite setUC | rewrite sg_sym].
Qed.
