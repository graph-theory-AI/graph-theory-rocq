From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude digraph oriented tournament dipath.
From Digraph.applications Require Import color_avoiding_paths.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section EdgeColors.
Variable D : diGraphType.
Variable chi : D -> D -> 'I_6.
Fixpoint edge_colors x (s : seq D) :=
  if s is y :: t then chi x y :: edge_colors y t else [::].
Lemma avoidingE c x s :
  avoiding chi c x s = path arc x s && (c \notin edge_colors x s).
Proof.
elim: s x=> [|y s IH] x //=.
rewrite /avoiding /= -/(avoiding _ _ _ _) IH /= inE negb_or.
rewrite (eq_sym c (chi x y)).
by case: (x --> y); case: (chi x y == c); case: (path arc y s);
   case: (c \notin edge_colors y s).
Qed.
Lemma missing_path x s : dipath x s -> missing (edge_colors x s) ->
  color_avoiding chi x s.
Proof.
move=> /andP[ps _] /hasP[c _ cm].
apply/existsP; exists c; by rewrite avoidingE ps.
Qed.
End EdgeColors.

Lemma missing_after_one (w : seq 'I_6) d :
  1 < count (fun c => c \notin w) colors6 -> missing (d :: w).
Proof.
move=> many; apply: contraT => /hasPn no.
have sub : {subset (fun c : 'I_6 => c \notin w) <= (pred1 d)}.
  move=> c cw; change (is_true (c \notin w)) in cw; have := no c (colors6_full c).
  by rewrite inE negb_or cw andbT negbK.
have le := sub_count sub colors6.
have uc : uniq colors6 by [].
rewrite (count_uniq_mem d uc) colors6_full in le.
by have := leq_ltn_trans le many; rewrite ltnn.
Qed.

Lemma missing_insert (a b : seq 'I_6) d :
  missing (d :: (a ++ b)) = missing (a ++ d :: b).
Proof.
apply: eq_has=> c.
by rewrite !inE !mem_cat !inE orbCA.
Qed.

Section Benchmark.
Variable chi : TT 9 -> TT 9 -> 'I_6.
Hypothesis words_good : forall w : seq 'I_6, size w = 8 -> good_word w.
Let w := [:: chi v0 v1; chi v1 v2; chi v2 v3; chi v3 v4;
             chi v4 v5; chi v5 v6; chi v6 v7; chi v7 v8].

Theorem transitive_eight_vertex_path :
  exists (x : TT 9) s, [ /\ dipath x s, color_avoiding chi x s & size s = 7].
Proof.
have good : good_word w by apply: words_good.
move/or3P: good => [h | h | /hasP[i hi many]].
- exists v1, [:: v2; v3; v4; v5; v6; v7; v8]; split.
  + by vm_compute.
  + apply: missing_path; first by vm_compute.
    exact: h.
  + reflexivity.
- exists v0, [:: v1; v2; v3; v4; v5; v6; v7]; split.
  + by vm_compute.
  + apply: missing_path; first by vm_compute.
    exact: h.
  + reflexivity.
- move: hi; rewrite mem_iota add0n leq0n /= => hi.
  case: i hi many => [|[|[|[|[|[|[|i]]]]]]] //= hi many.
  + exists v0, [:: v2; v3; v4; v5; v6; v7; v8]; split.
    * by vm_compute.
    * apply: missing_path; first by vm_compute.
      have h := missing_after_one (chi v0 v2) many.
      rewrite /omit_pair missing_insert in h.
      exact: h.
    * reflexivity.
  + exists v0, [:: v1; v3; v4; v5; v6; v7; v8]; split.
    * by vm_compute.
    * apply: missing_path; first by vm_compute.
      have h := missing_after_one (chi v1 v3) many.
      rewrite /omit_pair missing_insert in h.
      exact: h.
    * reflexivity.
  + exists v0, [:: v1; v2; v4; v5; v6; v7; v8]; split.
    * by vm_compute.
    * apply: missing_path; first by vm_compute.
      have h := missing_after_one (chi v2 v4) many.
      rewrite /omit_pair missing_insert in h.
      exact: h.
    * reflexivity.
  + exists v0, [:: v1; v2; v3; v5; v6; v7; v8]; split.
    * by vm_compute.
    * apply: missing_path; first by vm_compute.
      have h := missing_after_one (chi v3 v5) many.
      rewrite /omit_pair missing_insert in h.
      exact: h.
    * reflexivity.
  + exists v0, [:: v1; v2; v3; v4; v6; v7; v8]; split.
    * by vm_compute.
    * apply: missing_path; first by vm_compute.
      have h := missing_after_one (chi v4 v6) many.
      rewrite /omit_pair missing_insert in h.
      exact: h.
    * reflexivity.
  + exists v0, [:: v1; v2; v3; v4; v5; v7; v8]; split.
    * by vm_compute.
    * apply: missing_path; first by vm_compute.
      have h := missing_after_one (chi v5 v7) many.
      rewrite /omit_pair missing_insert in h.
      exact: h.
    * reflexivity.
  + exists v0, [:: v1; v2; v3; v4; v5; v6; v8]; split.
    * by vm_compute.
    * apply: missing_path; first by vm_compute.
      have h := missing_after_one (chi v6 v8) many.
      rewrite /omit_pair missing_insert in h.
      exact: h.
    * reflexivity.
Qed.
End Benchmark.

Definition transitive_color (u v : TT 9) : 'I_6 :=
  match val u, val v with
  | 0, 1 => c0 | 1, 2 => c1 | 2, 3 => c2
  | 3, 4 => c3 | 4, 5 => c4 | 5, 6 => c5
  | 6, 7 => c0 | 7, 8 => c1
  | _, _ => c0
  end.

Lemma transitive_search_certificate :
  all (fun c => all (fun x : TT 9 =>
    ~~ search (fun u v : TT 9 => (u --> v) && (transitive_color u v != c))
       8 x [seq z <- vertices9 | z != x]) vertices9) colors6.
Proof. by vm_compute. Qed.

Theorem transitive_color_avoiding_bound : avoids_bound transitive_color 8.
Proof.
apply: (@search_bound _ transitive_color 8 vertices9 vertices9_full) => c x.
exact: (allP (allP transitive_search_certificate c (colors6_full c)) x (vertices9_full x)).
Qed.

(** Exact extremal values specified by their matching upper/lower bounds.
    This avoids enumerating the much larger set of all tournament colorings. *)
Definition longest_avoiding_vertices (D : diGraphType) (chi : D -> D -> 'I_6) n :=
  avoids_bound chi n /\
  exists x s, [/\ dipath x s, color_avoiding chi x s & size (x :: s) = n].

Theorem nine_longest_avoiding_vertices : longest_avoiding_vertices nine_color 7.
Proof.
split; first exact: nine_color_avoiding_bound.
have [ps ac] := nine_seven_vertex_witness.
by exists v0, [:: v1; v2; v3; v4; v5; v6]; split.
Qed.

Definition transitive_minimum_is n :=
  (forall chi : TT 9 -> TT 9 -> 'I_6,
    exists x s, [/\ dipath x s, color_avoiding chi x s & n <= size (x :: s)]) /\
  exists chi : TT 9 -> TT 9 -> 'I_6, longest_avoiding_vertices chi n.

Lemma benchmark_from_word_certificate :
  (forall w : seq 'I_6, size w = 8 -> good_word w) -> transitive_minimum_is 8.
Proof.
move=> good; split.
- move=> chi; have [x [s [ps ac ss]]] := transitive_eight_vertex_path chi good.
  by exists x, s; split=> //; rewrite /= ss.
- exists transitive_color; split; first exact: transitive_color_avoiding_bound.
  have [x [s [ps ac ss]]] := transitive_eight_vertex_path transitive_color good.
  by exists x, s; split=> //; rewrite /= ss.
Qed.
