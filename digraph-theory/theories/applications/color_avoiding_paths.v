(** A finite resolution of arXiv:2512.10438, Problem 5.1.
    Source: Graph-Theory-LLM-Proofs/attacks/2512.10438__00/output.md.
    Paths are simple and their length here is the number of VERTICES. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude digraph oriented tournament dipath.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Search.
Variable V : eqType.
Variable e : rel V.

(** [search k x available] recognizes continuations with k edges. *)
Fixpoint search k (x : V) (available : seq V) : bool :=
  if k is k'.+1 then
    has (fun y => if e x y then search k' y [seq z <- available | z != y] else false) available
  else true.

Lemma search_complete k x s available :
  path e x s -> uniq s -> {subset s <= available} ->
  size s = k -> search k x available.
Proof.
elim: k x s available => [|k IH] x [|y s] available //=.
move=> /andP[xy ps] /andP[yNs us] sub [sk].
apply/hasP; exists y; first by apply: sub; rewrite mem_head.
rewrite xy /=; apply: IH ps us _ sk => z zs.
rewrite mem_filter (sub z) ?inE ?zs ?orbT // andbT.
apply: contraNneq yNs => <-; exact: zs.
Qed.
End Search.

Section Avoidance.
Variable D : diGraphType.
Variable chi : D -> D -> 'I_6.
Definition avoiding c x s := path (fun u v => (u --> v) && (chi u v != c)) x s.
Definition color_avoiding x s := [exists c : 'I_6, avoiding c x s].
Definition avoids_bound n := forall x s, dipath x s -> color_avoiding x s -> size s < n.

Lemma avoiding_take c x s n : avoiding c x s -> avoiding c x (take n s).
Proof.
rewrite /avoiding -{1}(cat_take_drop n s) cat_path.
by case/andP.
Qed.

Lemma search_bound n (vertices : seq D) :
  (forall z, z \in vertices) ->
  (forall c x, ~~ search (fun u v => (u --> v) && (chi u v != c)) n x
     [seq z <- vertices | z != x]) -> avoids_bound n.
Proof.
move=> covers cert x s ps /existsP[c ac].
apply: contraT; rewrite -leqNgt => sn.
have ts : size (take n s) = n by exact: size_takel sn.
have /andP[_ us] := dipath_take n ps.
have [xNt ut] := andP us.
have ht : {subset take n s <= [seq z <- vertices | z != x]}.
  move=> z zt; rewrite mem_filter covers andbT.
  apply: contraNneq xNt => <-; exact: zt.
have yes := search_complete (avoiding_take n ac) ut ht ts.
by have := cert c x; rewrite yes.
Qed.
End Avoidance.

Definition Nine : Type := 'I_9.
HB.instance Definition _ := Finite.on Nine.
Definition nine_arc (u v : Nine) :=
  if (val u == 3) && (val v == 5) then false else
  if (val u == 5) && (val v == 3) then true else (u < v)%N.
HB.instance Definition _ := HasArc.Build Nine nine_arc.

Lemma nine_irrefl : irreflexive (arc : rel Nine).
Proof. by move=> u; rewrite /arc /= /nine_arc; case: u=> -[|[|[|[|[|[|[|[|[|//]]]]]]]]] ?. Qed.
Lemma nine_total (u v : Nine) : (u != v) = (arc u v) (+) (arc v u).
Proof.
by case: u v => -[|[|[|[|[|[|[|[|[|//]]]]]]]]] ? [[|[|[|[|[|[|[|[|[|//]]]]]]]]] ?].
Qed.
HB.instance Definition _ := DiGraph_IsTournament.Build Nine nine_irrefl nine_total.

Notation v0 := (@Ordinal 9 0 (erefl true)).
Notation v1 := (@Ordinal 9 1 (erefl true)).
Notation v2 := (@Ordinal 9 2 (erefl true)).
Notation v3 := (@Ordinal 9 3 (erefl true)).
Notation v4 := (@Ordinal 9 4 (erefl true)).
Notation v5 := (@Ordinal 9 5 (erefl true)).
Notation v6 := (@Ordinal 9 6 (erefl true)).
Notation v7 := (@Ordinal 9 7 (erefl true)).
Notation v8 := (@Ordinal 9 8 (erefl true)).

Notation c0 := (@Ordinal 6 0 (erefl true)).
Notation c1 := (@Ordinal 6 1 (erefl true)).
Notation c2 := (@Ordinal 6 2 (erefl true)).
Notation c3 := (@Ordinal 6 3 (erefl true)).
Notation c4 := (@Ordinal 6 4 (erefl true)).
Notation c5 := (@Ordinal 6 5 (erefl true)).

Definition vertices9 : seq Nine := [:: v0; v1; v2; v3; v4; v5; v6; v7; v8].
Definition colors6 : seq 'I_6 := [:: c0; c1; c2; c3; c4; c5].
Lemma vertices9_full z : z \in vertices9.
Proof. by case: z=> -[|[|[|[|[|[|[|[|[|//]]]]]]]]] ?. Qed.
Lemma colors6_full c : c \in colors6.
Proof. by case: c=> -[|[|[|[|[|[|//]]]]]] ?. Qed.

(** Vertex order: l1,l2,l3,x0,x1,x2,r1,r2,r3.
    Colors 0,...,5 encode the source's 1,...,6. *)
Definition nine_color (u v : Nine) : 'I_6 :=
  match val u, val v with
  | 0, 1 => c0 | 1, 2 => c2 | 0, 2 => c2
  | 6, 7 => c3 | 6, 8 => c3 | 7, 8 => c0
  | 3, 4 => c1 | 4, 5 => c4 | 5, 3 => c5
  | 2, 3 => c5 | 2, 4 => c1 | 2, 5 => c4
  | 3, 6 => c1 | 4, 6 => c4 | 5, 6 => c5
  | 1, 3 => c2 | 1, 4 => c2 | 1, 5 => c2
  | 3, 7 => c3 | 4, 7 => c3 | 5, 7 => c3
  | _, _ => c0
  end.

Lemma nine_nontransitive : ~~ transb (Nine : tournament).
Proof. apply/ntransbP; exists v3, v4, v5; by split. Qed.

Lemma nine_search_certificate :
  all (fun c => all (fun x =>
    ~~ search (fun u v : Nine => (u --> v) && (nine_color u v != c))
       7 x [seq z <- vertices9 | z != x]) vertices9) colors6.
Proof. by vm_compute. Qed.

Theorem nine_color_avoiding_bound : avoids_bound nine_color 7.
Proof.
apply: (@search_bound _ nine_color 7 vertices9 vertices9_full) => c x.
exact: (allP (allP nine_search_certificate c (colors6_full c)) x (vertices9_full x)).
Qed.

Theorem nine_seven_vertex_witness :
  dipath (v0 : Nine) [:: v1; v2; v3; v4; v5; v6] /\
  color_avoiding nine_color (v0 : Nine) [:: v1; v2; v3; v4; v5; v6].
Proof. split; first by vm_compute. apply/existsP; exists c3; by vm_compute. Qed.

(** The universal transitive lower bound needs only the eight consecutive
    edge colors. Deleting an internal vertex removes two consecutive colors
    and introduces one arbitrary chord color. Two missing colors suffice. *)
Definition missing (w : seq 'I_6) := has (fun c => c \notin w) colors6.
Definition omit_pair i (w : seq 'I_6) := take i w ++ drop i.+2 w.
Definition good_word (w : seq 'I_6) :=
  if missing (behead w) then true else
  if missing (take 7 w) then true else
      has (fun i => 1 < count (fun c => c \notin omit_pair i w) colors6) (iota 0 7).

Fixpoint every_word k (prefix : seq 'I_6) : bool :=
  if k is k'.+1 then all (fun c => every_word k' (c :: prefix)) colors6
  else good_word prefix.

