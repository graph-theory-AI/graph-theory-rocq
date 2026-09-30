# Extraits mathcomp utiles pour les graphes (mathcomp 2.5)

Sélection pour le travail sur cycles/chemins/cardinaux avec coq-graph-theory.
Pour le reste de mathcomp, utiliser `Search`/`About` (les modules standards sont
bien connus ; seuls les lemmes ci-dessous sont fréquemment mal devinés).

## Lemmes vérifiés fréquemment utiles (fintype/finset)

```coq
card_uniqP : forall {T : finType} {s : seq T}, reflect (#|s| = size s) (uniq s).
card_gt0P  : reflect (exists i, i \in A) (0 < #|A|).
card_gt1P  : reflect (exists x y, [/\ x \in A, y \in A & x != y]) (1 < #|A|).
card_gt2P  : reflect (exists x y z, [/\ x \in A, y \in A & z \in A] /\
                       [/\ x != y, y != z & z != x]) (2 < #|A|).
cards1 : #|[set x]| = 1.        cards2 : #|[set x; y]| = (x != y).+1.
cards2P : forall (A : {set T}), reflect (exists x y, x != y /\ A = [set x; y]) (#|A| == 2).
disjoints1 : [disjoint [set x] & A] = (x \notin A).
disjointFr : [disjoint A & B] -> x \in A -> (x \in B) = false.
disjointFl : [disjoint A & B] -> x \in B -> (x \in A) = false.
disjointWl : A \subset B -> [disjoint B & C] -> [disjoint A & C].
disjointWr : A \subset B -> [disjoint C & B] -> [disjoint C & A].
disjoint_sym / disjoint_subset / subset_disjoint.
subset_cardP : #|A| = #|B| -> reflect (A =i B) (A \subset B).
eq_card : A =i B -> #|A| = #|B|.       card_imset : injective f -> #|f @: A| = #|A|.
card_sig : forall (P : pred T), #|{: {x : T | P x}}| = #|[pred x | P x]|.
card_sub : forall (sfT : subFinType P), #|sfT| = #|[pred x | P x]|.
```

## path.v intégral sans preuves (path, cycle, ucycle, next/prev, arc, rot, sorted)
```coq
(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

(******************************************************************************)
(*    The basic theory of paths over an eqType; this file is essentially a    *)
(* complement to seq.v. Paths are non-empty sequences that obey a progression *)
(* relation. They are passed around in three parts: the head and tail of the  *)
(* sequence, and a proof of a (boolean) predicate asserting the progression.  *)
(* This "exploded" view is rarely embarrassing, as the first two parameters   *)
(* are usually inferred from the type of the third; on the contrary, it saves *)
(* the hassle of constantly constructing and destructing a dependent record.  *)
(*    We define similarly cycles, for which we allow the empty sequence,      *)
(* which represents a non-rooted empty cycle; by contrast, the "empty" path   *)
(* from a point x is the one-item sequence containing only x.                 *)
(*   We allow duplicates; uniqueness, if desired (as is the case for several  *)
(* geometric constructions), must be asserted separately. We do provide       *)
(* shorthand, but only for cycles, because the equational properties of       *)
(* "path" and "uniq" are unfortunately incompatible (esp. wrt "cat").         *)
(*    We define notations for the common cases of function paths, where the   *)
(* progress relation is actually a function. In detail:                       *)
(*   path e x p == x :: p is an e-path [:: x_0; x_1; ... ; x_n], i.e., we     *)
(*                 have e x_i x_{i+1} for all i < n. The path x :: p starts   *)
(*                 at x and ends at last x p.                                 *)
(*  fpath f x p == x :: p is an f-path, where f is a function, i.e., p is of  *)
(*                 the form [:: f x; f (f x); ...]. This is just a notation   *)
(*                 for path (frel f) x p.                                     *)
(*   sorted e s == s is an e-sorted sequence: either s = [::], or s = x :: p  *)
(*                 is an e-path (this is often used with e = leq or ltn).     *)
(*    cycle e c == c is an e-cycle: either c = [::], or c = x :: p with       *)
(*                 x :: (rcons p x) an e-path.                                *)
(*   fcycle f c == c is an f-cycle, for a function f.                         *)
(* traject f x n == the f-path of size n starting at x                        *)
(*              := [:: x; f x; ...; iter n.-1 f x]                            *)
(* looping f x n == the f-paths of size greater than n starting at x loop     *)
(*                 back, or, equivalently, traject f x n contains all         *)
(*                 iterates of f at x.                                        *)
(* merge e s1 s2 == the e-sorted merge of sequences s1 and s2: this is always *)
(*                 a permutation of s1 ++ s2, and is e-sorted when s1 and s2  *)
(*                 are and e is total.                                        *)
(*     sort e s == a permutation of the sequence s, that is e-sorted when e   *)
(*                 is total (computed by a merge sort with the merge function *)
(*                 above).  This sort function is also designed to be stable. *)
(*   mem2 s x y == x, then y occur in the sequence (path) s; this is          *)
(*                 non-strict: mem2 s x x = (x \in s).                        *)
(*     next c x == the successor of the first occurrence of x in the sequence *)
(*                 c (viewed as a cycle), or x if x \notin c.                 *)
(*     prev c x == the predecessor of the first occurrence of x in the        *)
(*                 sequence c (viewed as a cycle), or x if x \notin c.        *)
(*    arc c x y == the sub-arc of the sequence c (viewed as a cycle) starting *)
(*                 at the first occurrence of x in c, and ending just before  *)
(*                 the next occurrence of y (in cycle order); arc c x y       *)
(*                 returns an unspecified sub-arc of c if x and y do not both *)
(*                 occur in c.                                                *)
(*  ucycle e c <-> ucycleb e c (ucycle e c is a Coercion target of type Prop) *)
(* ufcycle f c <-> c is a simple f-cycle, for a function f.                   *)
(*  shorten x p == the tail a duplicate-free subpath of x :: p with the same  *)
(*                 endpoints (x and last x p), obtained by removing all loops *)
(*                 from x :: p.                                               *)
(* rel_base e e' h b <-> the function h is a functor from relation e to       *)
(*                 relation e', EXCEPT at points whose image under h satisfy  *)
(*                 the "base" predicate b:                                    *)
(*                    e' (h x) (h y) = e x y UNLESS b (h x) holds             *)
(*                 This is the statement of the side condition of the path    *)
(*                 functorial mapping lemma map_path.                         *)
(* fun_base f f' h b <-> the function h is a functor from function f to f',   *)
(*                 except at the preimage of predicate b under h.             *)
(* We also provide three segmenting dependently-typed lemmas (splitP, splitPl *)
(* and splitPr) whose elimination split a path x0 :: p at an internal point x *)
(* as follows:                                                                *)
(*  - splitP applies when x \in p; it replaces p with (rcons p1 x ++ p2), so  *)
(*    that x appears explicitly at the end of the left part. The elimination  *)
(*    of splitP will also simultaneously replace take (index x p) with p1 and *)
(*    drop (index x p).+1 p with p2.                                          *)
(*  - splitPl applies when x \in x0 :: p; it replaces p with p1 ++ p2 and     *)
(*    simultaneously generates an equation x = last x0 p1.                    *)
(*  - splitPr applies when x \in p; it replaces p with (p1 ++ x :: p2), so x  *)
(*    appears explicitly at the start of the right part.                      *)
(* The parts p1 and p2 are computed using index/take/drop in all cases, but   *)
(* only splitP attempts to substitute the explicit values. The substitution   *)
(* of p can be deferred using the dependent equation generation feature of    *)
(* ssreflect, e.g.: case/splitPr def_p: {1}p / x_in_p => [p1 p2] generates    *)
(* the equation p = p1 ++ p2 instead of performing the substitution outright. *)
(*   Similarly, eliminating the loop removal lemma shortenP simultaneously    *)
(* replaces shorten e x p with a fresh constant p', and last x p with         *)
(* last x p'.                                                                 *)
(*   Note that although all "path" functions actually operate on the          *)
(* underlying sequence, we provide a series of lemmas that define their       *)
(* interaction with the path and cycle predicates, e.g., the cat_path equation*)
(* can be used to split the path predicate after splitting the underlying     *)
(* sequence.                                                                  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Paths.

Variables (n0 : nat) (T : Type).

Section Path.

Variables (x0_cycle : T) (e : rel T).

Fixpoint path x (p : seq T) :=
  if p is y :: p' then e x y && path y p' else true.

Lemma cat_path x p1 p2 : path x (p1 ++ p2) = path x p1 && path (last x p1) p2.

Lemma rcons_path x p y : path x (rcons p y) = path x p && e (last x p) y.

Lemma take_path x p i : path x p -> path x (take i p).

Lemma pathP x p x0 :
  reflect (forall i, i < size p -> e (nth x0 (x :: p) i) (nth x0 p i))
          (path x p).

Definition cycle p := if p is x :: p' then path x (rcons p' x) else true.

Lemma cycle_path p : cycle p = path (last x0_cycle p) p.

Lemma cycle_catC p q : cycle (p ++ q) = cycle (q ++ p).

Lemma rot_cycle p : cycle (rot n0 p) = cycle p.

Lemma rotr_cycle p : cycle (rotr n0 p) = cycle p.

Definition sorted s := if s is x :: s' then path x s' else true.

Lemma sortedP s x :
  reflect (forall i, i.+1 < size s -> e (nth x s i) (nth x s i.+1)) (sorted s).

Lemma path_sorted x s : path x s -> sorted s.

Lemma path_min_sorted x s : all (e x) s -> path x s = sorted s.

Lemma pairwise_sorted s : pairwise e s -> sorted s.

Lemma sorted_cat_cons s1 x s2 :
  sorted (s1 ++ x :: s2) = sorted (rcons s1 x) && path x s2.

End Path.

Section PathEq.

Variables (e e' : rel T).

Lemma rev_path x p :
  path e (last x p) (rev (belast x p)) = path (fun z => e^~ z) x p.

Lemma rev_cycle p : cycle e (rev p) = cycle (fun z => e^~ z) p.

Lemma rev_sorted p : sorted e (rev p) = sorted (fun z => e^~ z) p.

Lemma path_relI x s :
  path [rel x y | e x y && e' x y] x s = path e x s && path e' x s.

Lemma cycle_relI s :
  cycle [rel x y | e x y && e' x y] s = cycle e s && cycle e' s.

Lemma sorted_relI s :
  sorted [rel x y | e x y && e' x y] s = sorted e s && sorted e' s.

End PathEq.

Section SubPath_in.

Variable (P : {pred T}) (e e' : rel T).
Hypothesis (ee' : {in P &, subrel e e'}).

Lemma sub_in_path x s : all P (x :: s) -> path e x s -> path e' x s.

Lemma sub_in_cycle s : all P s -> cycle e s -> cycle e' s.

Lemma sub_in_sorted s : all P s -> sorted e s -> sorted e' s.

End SubPath_in.

Section EqPath_in.

Variable (P : {pred T}) (e e' : rel T).
Hypothesis (ee' : {in P &, e =2 e'}).

Let e_e' : {in P &, subrel e e'}. Proof. by move=> ? ? ? ?; rewrite ee'. Qed.
Let e'_e : {in P &, subrel e' e}. Proof. by move=> ? ? ? ?; rewrite ee'. Qed.

Lemma eq_in_path x s : all P (x :: s) -> path e x s = path e' x s.

Lemma eq_in_cycle s : all P s -> cycle e s = cycle e' s.

Lemma eq_in_sorted s : all P s -> sorted e s = sorted e' s.

End EqPath_in.

Section SubPath.

Variables e e' : rel T.

Lemma sub_path : subrel e e' -> forall x p, path e x p -> path e' x p.

Lemma sub_cycle : subrel e e' -> subpred (cycle e) (cycle e').

Lemma sub_sorted : subrel e e' -> subpred (sorted e) (sorted e').

Lemma eq_path : e =2 e' -> path e =2 path e'.

Lemma eq_cycle : e =2 e' -> cycle e =1 cycle e'.

Lemma eq_sorted : e =2 e' -> sorted e =1 sorted e'.

End SubPath.

Section Transitive_in.

Variables (P : {pred T}) (leT : rel T).

Lemma order_path_min_in x s :
  {in P & &, transitive leT} -> all P (x :: s) -> path leT x s -> all (leT x) s.

Hypothesis leT_tr : {in P & &, transitive leT}.

Lemma path_sorted_inE x s :
  all P (x :: s) -> path leT x s = all (leT x) s && sorted leT s.

Lemma sorted_pairwise_in s : all P s -> sorted leT s = pairwise leT s.

Lemma path_pairwise_in x s :
  all P (x :: s) -> path leT x s = pairwise leT (x :: s).

Lemma cat_sorted2 s s' : sorted leT (s ++ s') -> sorted leT s * sorted leT s'.

Lemma sorted_mask_in m s : all P s -> sorted leT s -> sorted leT (mask m s).

Lemma sorted_filter_in a s : all P s -> sorted leT s -> sorted leT (filter a s).

Lemma path_mask_in x m s :
  all P (x :: s) -> path leT x s -> path leT x (mask m s).

Lemma path_filter_in x a s :
  all P (x :: s) -> path leT x s -> path leT x (filter a s).

Lemma sorted_ltn_nth_in x0 s : all P s -> sorted leT s ->
  {in [pred n | n < size s] &, {homo nth x0 s : i j / i < j >-> leT i j}}.

Hypothesis leT_refl : {in P, reflexive leT}.

Lemma sorted_leq_nth_in x0 s : all P s -> sorted leT s ->
  {in [pred n | n < size s] &, {homo nth x0 s : i j / i <= j >-> leT i j}}.

End Transitive_in.

Section Transitive.

Variable (leT : rel T).

Lemma order_path_min x s : transitive leT -> path leT x s -> all (leT x) s.

Hypothesis leT_tr : transitive leT.

Lemma path_le x x' s : leT x x' -> path leT x' s -> path leT x s.

Let leT_tr' : {in predT & &, transitive leT}. Proof. exact: in3W. Qed.

Lemma path_sortedE x s : path leT x s = all (leT x) s && sorted leT s.

Lemma sorted_pairwise s : sorted leT s = pairwise leT s.

Lemma path_pairwise x s : path leT x s = pairwise leT (x :: s).

Lemma sorted_mask m s : sorted leT s -> sorted leT (mask m s).

Lemma sorted_filter a s : sorted leT s -> sorted leT (filter a s).

Lemma path_mask x m s : path leT x s -> path leT x (mask m s).

Lemma path_filter x a s : path leT x s -> path leT x (filter a s).

Lemma sorted_ltn_nth x0 s : sorted leT s ->
  {in [pred n | n < size s] &, {homo nth x0 s : i j / i < j >-> leT i j}}.

Hypothesis leT_refl : reflexive leT.

Lemma sorted_leq_nth x0 s : sorted leT s ->
  {in [pred n | n < size s] &, {homo nth x0 s : i j / i <= j >-> leT i j}}.

Lemma take_sorted n s : sorted leT s -> sorted leT (take n s).

Lemma drop_sorted n s : sorted leT s -> sorted leT (drop n s).

End Transitive.

End Paths.

Arguments pathP {T e x p}.
Arguments sortedP {T e s}.
Arguments path_sorted {T e x s}.
Arguments path_min_sorted {T e x s}.
Arguments order_path_min_in {T P leT x s}.
Arguments path_sorted_inE {T P leT} leT_tr {x s}.
Arguments sorted_pairwise_in {T P leT} leT_tr {s}.
Arguments path_pairwise_in {T P leT} leT_tr {x s}.
Arguments sorted_mask_in {T P leT} leT_tr {m s}.
Arguments sorted_filter_in {T P leT} leT_tr {a s}.
Arguments path_mask_in {T P leT} leT_tr {x m s}.
Arguments path_filter_in {T P leT} leT_tr {x a s}.
Arguments sorted_ltn_nth_in {T P leT} leT_tr x0 {s}.
Arguments sorted_leq_nth_in {T P leT} leT_tr leT_refl x0 {s}.
Arguments order_path_min {T leT x s}.
Arguments path_sortedE {T leT} leT_tr x s.
Arguments sorted_pairwise {T leT} leT_tr s.
Arguments path_pairwise {T leT} leT_tr x s.
Arguments sorted_mask {T leT} leT_tr m {s}.
Arguments sorted_filter {T leT} leT_tr a {s}.
Arguments path_mask {T leT} leT_tr {x} m {s}.
Arguments path_filter {T leT} leT_tr {x} a {s}.
Arguments sorted_ltn_nth {T leT} leT_tr x0 {s}.
Arguments sorted_leq_nth {T leT} leT_tr leT_refl x0 {s}.

Section HomoPath.

Variables (T T' : Type) (P : {pred T}) (f : T -> T') (e : rel T) (e' : rel T').

Lemma path_map x s : path e' (f x) (map f s) = path (relpre f e') x s.

Lemma cycle_map s : cycle e' (map f s) = cycle (relpre f e') s.

Lemma sorted_map s : sorted e' (map f s) = sorted (relpre f e') s.

Lemma homo_path_in x s : {in P &, {homo f : x y / e x y >-> e' x y}} ->
  all P (x :: s) -> path e x s -> path e' (f x) (map f s).

Lemma homo_cycle_in s : {in P &, {homo f : x y / e x y >-> e' x y}} ->
  all P s -> cycle e s -> cycle e' (map f s).

Lemma homo_sorted_in s : {in P &, {homo f : x y / e x y >-> e' x y}} ->
  all P s -> sorted e s -> sorted e' (map f s).

Lemma mono_path_in x s : {in P &, {mono f : x y / e x y >-> e' x y}} ->
  all P (x :: s) -> path e' (f x) (map f s) = path e x s.

Lemma mono_cycle_in s : {in P &, {mono f : x y / e x y >-> e' x y}} ->
  all P s -> cycle e' (map f s) = cycle e s.

Lemma mono_sorted_in s : {in P &, {mono f : x y / e x y >-> e' x y}} ->
  all P s -> sorted e' (map f s) = sorted e s.

Lemma homo_path x s : {homo f : x y / e x y >-> e' x y} ->
  path e x s -> path e' (f x) (map f s).

Lemma homo_cycle : {homo f : x y / e x y >-> e' x y} ->
  {homo map f : s / cycle e s >-> cycle e' s}.

Lemma homo_sorted : {homo f : x y / e x y >-> e' x y} ->
  {homo map f : s / sorted e s >-> sorted e' s}.

Lemma mono_path x s : {mono f : x y / e x y >-> e' x y} ->
  path e' (f x) (map f s) = path e x s.

Lemma mono_cycle : {mono f : x y / e x y >-> e' x y} ->
  {mono map f : s / cycle e s >-> cycle e' s}.

Lemma mono_sorted : {mono f : x y / e x y >-> e' x y} ->
  {mono map f : s / sorted e s >-> sorted e' s}.

End HomoPath.

Arguments path_map {T T' f e'}.
Arguments cycle_map {T T' f e'}.
Arguments sorted_map {T T' f e'}.
Arguments homo_path_in {T T' P f e e' x s}.
Arguments homo_cycle_in {T T' P f e e' s}.
Arguments homo_sorted_in {T T' P f e e' s}.
Arguments mono_path_in {T T' P f e e' x s}.
Arguments mono_cycle_in {T T' P f e e' s}.
Arguments mono_sorted_in {T T' P f e e' s}.
Arguments homo_path {T T' f e e' x s}.
Arguments homo_cycle {T T' f e e'}.
Arguments homo_sorted {T T' f e e'}.
Arguments mono_path {T T' f e e' x s}.
Arguments mono_cycle {T T' f e e'}.
Arguments mono_sorted {T T' f e e'}.

Section CycleAll2Rel.

Lemma cycle_all2rel (T : Type) (leT : rel T) :
  transitive leT -> forall s, cycle leT s = all2rel leT s.

Lemma cycle_all2rel_in (T : Type) (P : {pred T}) (leT : rel T) :
  {in P & &, transitive leT} ->
  forall s, all P s -> cycle leT s = all2rel leT s.

End CycleAll2Rel.

Section PreInSuffix.

Variables (T : eqType) (e : rel T).
Implicit Type s : seq T.

Local Notation path := (path e).
Local Notation sorted := (sorted e).

Lemma prefix_path x s1 s2 : prefix s1 s2 -> path x s2 -> path x s1.

Lemma prefix_sorted s1 s2 : prefix s1 s2 -> sorted s2 -> sorted s1.

Lemma infix_sorted s1 s2 : infix s1 s2 -> sorted s2 -> sorted s1.

Lemma suffix_sorted s1 s2 : suffix s1 s2 -> sorted s2 -> sorted s1.

End PreInSuffix.

Section EqSorted.

Variables (T : eqType) (leT : rel T).
Implicit Type s : seq T.

Local Notation path := (path leT).
Local Notation sorted := (sorted leT).

Lemma subseq_path_in x s1 s2 :
  {in x :: s2 & &, transitive leT} -> subseq s1 s2 -> path x s2 -> path x s1.

Lemma subseq_sorted_in s1 s2 :
  {in s2 & &, transitive leT} -> subseq s1 s2 -> sorted s2 -> sorted s1.

Lemma sorted_ltn_index_in s : {in s & &, transitive leT} -> sorted s ->
  {in s &, forall x y, index x s < index y s -> leT x y}.

Lemma sorted_leq_index_in s :
  {in s & &, transitive leT} -> {in s, reflexive leT} -> sorted s ->
  {in s &, forall x y, index x s <= index y s -> leT x y}.

Hypothesis leT_tr : transitive leT.

Lemma subseq_path x s1 s2 : subseq s1 s2 -> path x s2 -> path x s1.

Lemma subseq_sorted s1 s2 : subseq s1 s2 -> sorted s2 -> sorted s1.

Lemma sorted_uniq : irreflexive leT -> forall s, sorted s -> uniq s.

Lemma sorted_eq : antisymmetric leT ->
  forall s1 s2, sorted s1 -> sorted s2 -> perm_eq s1 s2 -> s1 = s2.

Lemma irr_sorted_eq : irreflexive leT ->
  forall s1 s2, sorted s1 -> sorted s2 -> s1 =i s2 -> s1 = s2.

Lemma sorted_ltn_index s :
  sorted s -> {in s &, forall x y, index x s < index y s -> leT x y}.

Lemma undup_path x s : path x s -> path x (undup s).

Lemma undup_sorted s : sorted s -> sorted (undup s).

Hypothesis leT_refl : reflexive leT.

Lemma sorted_leq_index s :
  sorted s -> {in s &, forall x y, index x s <= index y s -> leT x y}.

End EqSorted.

Arguments sorted_ltn_index_in {T leT s} leT_tr s_sorted.
Arguments sorted_leq_index_in {T leT s} leT_tr leT_refl s_sorted.
Arguments sorted_ltn_index {T leT} leT_tr {s}.
Arguments sorted_leq_index {T leT} leT_tr leT_refl {s}.

Section EqSorted_in.

Variables (T : eqType) (leT : rel T).
Implicit Type s : seq T.

Lemma sorted_uniq_in s :
  {in s & &, transitive leT} -> {in s, irreflexive leT} ->
  sorted leT s -> uniq s.

Lemma sorted_eq_in s1 s2 :
  {in s1 & &, transitive leT} -> {in s1 &, antisymmetric leT} ->
  sorted leT s1 -> sorted leT s2 -> perm_eq s1 s2 -> s1 = s2.

Lemma irr_sorted_eq_in s1 s2 :
  {in s1 & &, transitive leT} -> {in s1, irreflexive leT} ->
  sorted leT s1 -> sorted leT s2 -> s1 =i s2 -> s1 = s2.

End EqSorted_in.

Section EqPath.

Variables (n0 : nat) (T : eqType) (e : rel T).
Implicit Type p : seq T.

Variant split x : seq T -> seq T -> seq T -> Type :=
  Split p1 p2 : split x (rcons p1 x ++ p2) p1 p2.

Lemma splitP p x (i := index x p) :
  x \in p -> split x p (take i p) (drop i.+1 p).

Variant splitl x1 x : seq T -> Type :=
  Splitl p1 p2 of last x1 p1 = x : splitl x1 x (p1 ++ p2).

Lemma splitPl x1 p x : x \in x1 :: p -> splitl x1 x p.

Variant splitr x : seq T -> Type :=
  Splitr p1 p2 : splitr x (p1 ++ x :: p2).

Lemma splitPr p x : x \in p -> splitr x p.

Fixpoint next_at x y0 y p :=
  match p with
  | [::] => if x == y then y0 else x
  | y' :: p' => if x == y then y' else next_at x y0 y' p'
  end.

Definition next p x := if p is y :: p' then next_at x y y p' else x.

Fixpoint prev_at x y0 y p :=
  match p with
  | [::]     => if x == y0 then y else x
  | y' :: p' => if x == y' then y else prev_at x y0 y' p'
  end.

Definition prev p x := if p is y :: p' then prev_at x y y p' else x.

Lemma next_nth p x :
  next p x = if x \in p then
               if p is y :: p' then nth y p' (index x p) else x
             else x.

Lemma prev_nth p x :
  prev p x = if x \in p then
               if p is y :: p' then nth y p (index x p') else x
             else x.

Lemma mem_next p x : (next p x \in p) = (x \in p).

Lemma mem_prev p x : (prev p x \in p) = (x \in p).

(* ucycleb is the boolean predicate, but ucycle is defined as a Prop *)
(* so that it can be used as a coercion target. *)
Definition ucycleb p := cycle e p && uniq p.
Definition ucycle p : Prop := cycle e p && uniq p.

(* Projections, used for creating local lemmas. *)
Lemma ucycle_cycle p : ucycle p -> cycle e p.

Lemma ucycle_uniq p : ucycle p -> uniq p.

Lemma next_cycle p x : cycle e p -> x \in p -> e x (next p x).

Lemma prev_cycle p x : cycle e p -> x \in p -> e (prev p x) x.

Lemma rot_ucycle p : ucycle (rot n0 p) = ucycle p.

Lemma rotr_ucycle p : ucycle (rotr n0 p) = ucycle p.

(* The "appears no later" partial preorder defined by a path. *)

Definition mem2 p x y := y \in drop (index x p) p.

Lemma mem2l p x y : mem2 p x y -> x \in p.

Lemma mem2lf {p x y} : x \notin p -> mem2 p x y = false.

Lemma mem2r p x y : mem2 p x y -> y \in p.

Lemma mem2rf {p x y} : y \notin p -> mem2 p x y = false.

Lemma mem2_cat p1 p2 x y :
  mem2 (p1 ++ p2) x y = mem2 p1 x y || mem2 p2 x y || (x \in p1) && (y \in p2).

Lemma mem2_splice p1 p3 x y p2 :
  mem2 (p1 ++ p3) x y -> mem2 (p1 ++ p2 ++ p3) x y.

Lemma mem2_splice1 p1 p3 x y z :
  mem2 (p1 ++ p3) x y -> mem2 (p1 ++ z :: p3) x y.

Lemma mem2_cons x p y z :
  mem2 (x :: p) y z = (if x == y then z \in x :: p else mem2 p y z).

Lemma mem2_seq1 x y z : mem2 [:: x] y z = (y == x) && (z == x).

Lemma mem2_last y0 p x : mem2 p x (last y0 p) = (x \in p).

Lemma mem2l_cat {p1 p2 x} : x \notin p1 -> mem2 (p1 ++ p2) x =1 mem2 p2 x.

Lemma mem2r_cat {p1 p2 x y} : y \notin p2 -> mem2 (p1 ++ p2) x y = mem2 p1 x y.

Lemma mem2lr_splice {p1 p2 p3 x y} :
  x \notin p2 -> y \notin p2 -> mem2 (p1 ++ p2 ++ p3) x y = mem2 (p1 ++ p3) x y.

Lemma mem2E s x y :
  mem2 s x y = subseq (if x == y then [:: x] else [:: x; y]) s.

Variant split2r x y : seq T -> Type :=
  Split2r p1 p2 of y \in x :: p2 : split2r x y (p1 ++ x :: p2).

Lemma splitP2r p x y : mem2 p x y -> split2r x y p.

Fixpoint shorten x p :=
  if p is y :: p' then
    if x \in p then shorten x p' else y :: shorten y p'
  else [::].

Variant shorten_spec x p : T -> seq T -> Type :=
   ShortenSpec p' of path e x p' & uniq (x :: p') & {subset p' <= p} :
     shorten_spec x p (last x p') p'.

Lemma shortenP x p : path e x p -> shorten_spec x p (last x p) (shorten x p).

End EqPath.

(* Ordered paths and sorting. *)

Section SortSeq.

Variables (T : Type) (leT : rel T).

Fixpoint merge s1 :=
  if s1 is x1 :: s1' then
    let fix merge_s1 s2 :=
      if s2 is x2 :: s2' then
        if leT x1 x2 then x1 :: merge s1' s2 else x2 :: merge_s1 s2'
      else s1 in
    merge_s1
  else id.

Arguments merge !s1 !s2 : rename.

Fixpoint merge_sort_push s1 ss :=
  match ss with
  | [::] :: ss' | [::] as ss' => s1 :: ss'
  | s2 :: ss' => [::] :: merge_sort_push (merge s2 s1) ss'
  end.

Fixpoint merge_sort_pop s1 ss :=
  if ss is s2 :: ss' then merge_sort_pop (merge s2 s1) ss' else s1.

Fixpoint merge_sort_rec ss s :=
  if s is [:: x1, x2 & s'] then
    let s1 := if leT x1 x2 then [:: x1; x2] else [:: x2; x1] in
    merge_sort_rec (merge_sort_push s1 ss) s'
  else merge_sort_pop s ss.

Definition sort := merge_sort_rec [::].

(* The following definition `sort_rec1` is an auxiliary function for          *)
(* inductive reasoning on `sort`. One can rewrite `sort le s` to              *)
(* `sort_rec1 le [::] s` by `sortE` and apply the simple structural induction *)
(* on `s` to reason about it.                                                 *)
Fixpoint sort_rec1 ss s :=
  if s is x :: s then sort_rec1 (merge_sort_push [:: x] ss) s else
  merge_sort_pop [::] ss.

Lemma sortE s : sort s = sort_rec1 [::] s.

Lemma count_merge (p : pred T) s1 s2 :
  count p (merge s1 s2) = count p (s1 ++ s2).

Lemma size_merge s1 s2 : size (merge s1 s2) = size (s1 ++ s2).

Lemma allrel_merge s1 s2 : allrel leT s1 s2 -> merge s1 s2 = s1 ++ s2.

Lemma count_sort (p : pred T) s : count p (sort s) = count p s.

Lemma pairwise_sort s : pairwise leT s -> sort s = s.

Remark size_merge_sort_push s1 :
  let graded ss := forall i, size (nth [::] ss i) \in pred2 0 (2 ^ (i + 1)) in
  size s1 = 2 -> {homo merge_sort_push s1 : ss / graded ss}.

Section Stability.

Variable leT' : rel T.
Hypothesis (leT_total : total leT) (leT'_tr : transitive leT').

Let leT_lex := [rel x y | leT x y && (leT y x ==> leT' x y)].

Lemma merge_stable_path x s1 s2 :
  allrel leT' s1 s2 -> path leT_lex x s1 -> path leT_lex x s2 ->
  path leT_lex x (merge s1 s2).

Lemma merge_stable_sorted s1 s2 :
  allrel leT' s1 s2 -> sorted leT_lex s1 -> sorted leT_lex s2 ->
  sorted leT_lex (merge s1 s2).

End Stability.

Hypothesis leT_total : total leT.

Let leElex : leT =2 [rel x y | leT x y && (leT y x ==> true)].

Lemma merge_path x s1 s2 :
  path leT x s1 -> path leT x s2 -> path leT x (merge s1 s2).

Lemma merge_sorted s1 s2 :
  sorted leT s1 -> sorted leT s2 -> sorted leT (merge s1 s2).

Hypothesis leT_tr : transitive leT.

Lemma sorted_merge s t : sorted leT (s ++ t) -> merge s t = s ++ t.

Lemma sorted_sort s : sorted leT s -> sort s = s.

Lemma mergeA : associative merge.

End SortSeq.

Arguments merge {T} relT !s1 !s2 : rename.
Arguments size_merge {T} leT s1 s2.
Arguments allrel_merge {T leT s1 s2}.
Arguments pairwise_sort {T leT s}.
Arguments merge_path {T leT} leT_total {x s1 s2}.
Arguments merge_sorted {T leT} leT_total {s1 s2}.
Arguments sorted_merge {T leT} leT_tr {s t}.
Arguments sorted_sort {T leT} leT_tr {s}.
Arguments mergeA {T leT} leT_total leT_tr.

Section SortMap.
Variables (T T' : Type) (f : T' -> T).

Section Monotonicity.

Variables (leT' : rel T') (leT : rel T).
Hypothesis f_mono : {mono f : x y / leT' x y >-> leT x y}.

Lemma map_merge : {morph map f : s1 s2 / merge leT' s1 s2 >-> merge leT s1 s2}.

Lemma map_sort : {morph map f : s1 / sort leT' s1 >-> sort leT s1}.

End Monotonicity.

Variable leT : rel T.

Lemma merge_map s1 s2 :
  merge leT (map f s1) (map f s2) = map f (merge (relpre f leT) s1 s2).

Lemma sort_map s : sort leT (map f s) = map f (sort (relpre f leT) s).

End SortMap.

Arguments map_merge {T T' f leT' leT}.
Arguments map_sort {T T' f leT' leT}.
Arguments merge_map {T T' f leT}.
Arguments sort_map {T T' f leT}.

Lemma sorted_sort_in T (P : {pred T}) (leT : rel T) :
  {in P & &, transitive leT} ->
  forall s : seq T, all P s -> sorted leT s -> sort leT s = s.

Arguments sorted_sort_in {T P leT} leT_tr {s}.

Section EqSortSeq.

Variables (T : eqType) (leT : rel T).

Lemma perm_merge s1 s2 : perm_eql (merge leT s1 s2) (s1 ++ s2).

Lemma mem_merge s1 s2 : merge leT s1 s2 =i s1 ++ s2.

Lemma merge_uniq s1 s2 : uniq (merge leT s1 s2) = uniq (s1 ++ s2).

Lemma perm_sort s : perm_eql (sort leT s) s.

Lemma mem_sort s : sort leT s =i s. Proof. exact/perm_mem/permPl/perm_sort. Qed.

Lemma sort_uniq s : uniq (sort leT s) = uniq s.

Lemma eq_count_merge (p : pred T) s1 s1' s2 s2' :
  count p s1 = count p s1' -> count p s2 = count p s2' ->
  count p (merge leT s1 s2) = count p (merge leT s1' s2').

End EqSortSeq.

Lemma perm_iota_sort (T : Type) (leT : rel T) x0 s :
  {i_s : seq nat | perm_eq i_s (iota 0 (size s)) &
                   sort leT s = map (nth x0 s) i_s}.

Lemma all_merge (T : Type) (P : {pred T}) (leT : rel T) s1 s2 :
  all P (merge leT s1 s2) = all P s1 && all P s2.

Lemma all_sort (T : Type) (P : {pred T}) (leT : rel T) s :
  all P (sort leT s) = all P s.

Lemma size_sort (T : Type) (leT : rel T) s : size (sort leT s) = size s.

Lemma ltn_sorted_uniq_leq s : sorted ltn s = uniq s && sorted leq s.

Lemma gtn_sorted_uniq_geq s : sorted gtn s = uniq s && sorted geq s.

Lemma iota_sorted i n : sorted leq (iota i n).

Lemma iota_ltn_sorted i n : sorted ltn (iota i n).

Section Stability_iota.

Variables (leN : rel nat) (leN_total : total leN).

Let lt_lex := [rel n m | leN n m && (leN m n ==> (n < m))].

Let Fixpoint push_invariant (ss : seq (seq nat)) :=
  if ss is s :: ss' then
    [&& sorted lt_lex s, allrel gtn s (flatten ss') & push_invariant ss']
  else
    true.

Let push_stable s1 ss :
  push_invariant (s1 :: ss) -> push_invariant (merge_sort_push leN s1 ss).

Let pop_stable s1 ss :
  push_invariant (s1 :: ss) -> sorted lt_lex (merge_sort_pop leN s1 ss).

Lemma sort_iota_stable n : sorted lt_lex (sort leN (iota 0 n)).

End Stability_iota.

Lemma sort_pairwise_stable T (leT leT' : rel T) :
  total leT -> forall s : seq T, pairwise leT' s ->
  sorted [rel x y | leT x y && (leT y x ==> leT' x y)] (sort leT s).

Lemma sort_stable T (leT leT' : rel T) :
  total leT -> transitive leT' -> forall s : seq T, sorted leT' s ->
  sorted [rel x y | leT x y && (leT y x ==> leT' x y)] (sort leT s).

Lemma sort_stable_in T (P : {pred T}) (leT leT' : rel T) :
  {in P &, total leT} -> {in P & &, transitive leT'} ->
  forall s : seq T, all P s -> sorted leT' s ->
  sorted [rel x y | leT x y && (leT y x ==> leT' x y)] (sort leT s).

Lemma filter_sort T (leT : rel T) :
  total leT -> transitive leT ->
  forall p s, filter p (sort leT s) = sort leT (filter p s).

Lemma filter_sort_in T (P : {pred T}) (leT : rel T) :
  {in P &, total leT} -> {in P & &, transitive leT} ->
  forall p s, all P s -> filter p (sort leT s) = sort leT (filter p s).

Section Stability_mask.

Variables (T : Type) (leT : rel T).
Variables (leT_total : total leT) (leT_tr : transitive leT).

Lemma mask_sort s m :
  {m_s : bitseq | mask m_s (sort leT s) = sort leT (mask m s)}.

Lemma sorted_mask_sort s m :
  sorted leT (mask m s) -> {m_s | mask m_s (sort leT s) = mask m s}.

End Stability_mask.

Section Stability_mask_in.

Variables (T : Type) (P : {pred T}) (leT : rel T).
Hypothesis leT_total : {in P &, total leT}.
Hypothesis leT_tr : {in P & &, transitive leT}.

Let le_sT := relpre (val : sig P -> _) leT.
Let le_sT_total : total le_sT := in2_sig leT_total.
Let le_sT_tr : transitive le_sT := in3_sig leT_tr.

Lemma mask_sort_in s m :
  all P s -> {m_s : bitseq | mask m_s (sort leT s) = sort leT (mask m s)}.

Lemma sorted_mask_sort_in s m :
  all P s -> sorted leT (mask m s) -> {m_s | mask m_s (sort leT s) = mask m s}.

End Stability_mask_in.

Section Stability_subseq.

Variables (T : eqType) (leT : rel T).
Variables (leT_total : total leT) (leT_tr : transitive leT).

Lemma subseq_sort : {homo sort leT : t s / subseq t s}.

Lemma sorted_subseq_sort t s :
  subseq t s -> sorted leT t -> subseq t (sort leT s).

Lemma mem2_sort s x y : leT x y -> mem2 s x y -> mem2 (sort leT s) x y.

End Stability_subseq.

Section Stability_subseq_in.

Variables (T : eqType) (leT : rel T).

Lemma subseq_sort_in t s :
  {in s &, total leT} -> {in s & &, transitive leT} ->
  subseq t s -> subseq (sort leT t) (sort leT s).

Lemma sorted_subseq_sort_in t s :
  {in s &, total leT} -> {in s & &, transitive leT} ->
  subseq t s -> sorted leT t -> subseq t (sort leT s).

Lemma mem2_sort_in s :
  {in s &, total leT} -> {in s & &, transitive leT} ->
  forall x y, leT x y -> mem2 s x y -> mem2 (sort leT s) x y.

End Stability_subseq_in.

Lemma sort_sorted T (leT : rel T) :
  total leT -> forall s, sorted leT (sort leT s).

Lemma sort_sorted_in T (P : {pred T}) (leT : rel T) :
  {in P &, total leT} -> forall s : seq T, all P s -> sorted leT (sort leT s).

Arguments sort_sorted {T leT} leT_total s.
Arguments sort_sorted_in {T P leT} leT_total {s}.

Lemma perm_sortP (T : eqType) (leT : rel T) :
  total leT -> transitive leT -> antisymmetric leT ->
  forall s1 s2, reflect (sort leT s1 = sort leT s2) (perm_eq s1 s2).

Lemma perm_sort_inP (T : eqType) (leT : rel T) (s1 s2 : seq T) :
  {in s1 &, total leT} -> {in s1 & &, transitive leT} ->
  {in s1 &, antisymmetric leT} ->
  reflect (sort leT s1 = sort leT s2) (perm_eq s1 s2).

Lemma homo_sort_map (T : Type) (T' : eqType) (f : T -> T') leT leT' :
  antisymmetric (relpre f leT') -> transitive (relpre f leT') -> total leT ->
  {homo f : x y / leT x y >-> leT' x y} ->
  forall s : seq T, sort leT' (map f s) = map f (sort leT s).

Lemma homo_sort_map_in
      (T : Type) (T' : eqType) (P : {pred T}) (f : T -> T') leT leT' :
  {in P &, antisymmetric (relpre f leT')} ->
  {in P & &, transitive (relpre f leT')} -> {in P &, total leT} ->
  {in P &, {homo f : x y / leT x y >-> leT' x y}} ->
  forall s : seq T, all P s ->
        sort leT' [seq f x | x <- s] = [seq f x | x <- sort leT s].

(* Function trajectories. *)

Notation fpath f := (path (coerced_frel f)).
Notation fcycle f := (cycle (coerced_frel f)).
Notation ufcycle f := (ucycle (coerced_frel f)).

Prenex Implicits path next prev cycle ucycle mem2.

Section Trajectory.

Variables (T : Type) (f : T -> T).

Fixpoint traject x n := if n is n'.+1 then x :: traject (f x) n' else [::].

Lemma trajectS x n : traject x n.+1 = x :: traject (f x) n.

Lemma trajectSr x n : traject x n.+1 = rcons (traject x n) (iter n f x).

Lemma last_traject x n : last x (traject (f x) n) = iter n f x.

Lemma traject_iteri x n :
  traject x n = iteri n (fun i => rcons^~ (iter i f x)) [::].

Lemma size_traject x n : size (traject x n) = n.

Lemma nth_traject i n : i < n -> forall x, nth x (traject x n) i = iter i f x.

Lemma trajectD m n x :
  traject x (m + n) = traject x m ++ traject (iter m f x) n.

Lemma take_traject n k x : k <= n -> take k (traject x n) = traject x k.

End Trajectory.

Section EqTrajectory.

Variables (T : eqType) (f : T -> T).

Lemma eq_fpath f' : f =1 f' -> fpath f =2 fpath f'.

Lemma eq_fcycle f' : f =1 f' -> fcycle f =1 fcycle f'.

Lemma fpathE x p : fpath f x p -> p = traject f (f x) (size p).

Lemma fpathP x p : reflect (exists n, p = traject f (f x) n) (fpath f x p).

Lemma fpath_traject x n : fpath f x (traject f (f x) n).

Definition looping x n := iter n f x \in traject f x n.

Lemma loopingP x n :
  reflect (forall m, iter m f x \in traject f x n) (looping x n).

Lemma trajectP x n y :
  reflect (exists2 i, i < n & y = iter i f x) (y \in traject f x n).

Lemma looping_uniq x n : uniq (traject f x n.+1) = ~~ looping x n.

End EqTrajectory.

Arguments fpathP {T f x p}.
Arguments loopingP {T f x n}.
Arguments trajectP {T f x n y}.
Prenex Implicits traject.

Section Fcycle.
Variables (T : eqType) (f : T -> T) (p : seq T) (f_p : fcycle f p).

Lemma nextE (x : T) (p_x : x \in p) : next p x = f x.

Lemma mem_fcycle : {homo f : x / x \in p}.

Lemma inj_cycle : {in p &, injective f}.

End Fcycle.

Section UniqCycle.

Variables (n0 : nat) (T : eqType) (e : rel T) (p : seq T).

Hypothesis Up : uniq p.

Lemma prev_next : cancel (next p) (prev p).

Lemma next_prev : cancel (prev p) (next p).

Lemma cycle_next : fcycle (next p) p.

Lemma cycle_prev : cycle (fun x y => x == prev p y) p.

Lemma cycle_from_next : (forall x, x \in p -> e x (next p x)) -> cycle e p.

Lemma cycle_from_prev : (forall x, x \in p -> e (prev p x) x) -> cycle e p.

Lemma next_rot : next (rot n0 p) =1 next p.

Lemma prev_rot : prev (rot n0 p) =1 prev p.

End UniqCycle.

Section UniqRotrCycle.

Variables (n0 : nat) (T : eqType) (p : seq T).

Hypothesis Up : uniq p.

Lemma next_rotr : next (rotr n0 p) =1 next p. Proof. exact: next_rot. Qed.

Lemma prev_rotr : prev (rotr n0 p) =1 prev p. Proof. exact: prev_rot. Qed.

End UniqRotrCycle.

Section UniqCycleRev.

Variable T : eqType.
Implicit Type p : seq T.

Lemma prev_rev p : uniq p -> prev (rev p) =1 next p.

Lemma next_rev p : uniq p -> next (rev p) =1 prev p.

End UniqCycleRev.

Section MapPath.

Variables (T T' : Type) (h : T' -> T) (e : rel T) (e' : rel T').

Definition rel_base (b : pred T) :=
  forall x' y', ~~ b (h x') -> e (h x') (h y') = e' x' y'.

Lemma map_path b x' p' (Bb : rel_base b) :
    ~~ has (preim h b) (belast x' p') ->
  path e (h x') (map h p') = path e' x' p'.

End MapPath.

Section MapEqPath.

Variables (T T' : eqType) (h : T' -> T) (e : rel T) (e' : rel T').

Hypothesis Ih : injective h.

Lemma mem2_map x' y' p' : mem2 (map h p') (h x') (h y') = mem2 p' x' y'.

Lemma next_map p : uniq p -> forall x, next (map h p) (h x) = h (next p x).

Lemma prev_map p : uniq p -> forall x, prev (map h p) (h x) = h (prev p x).

End MapEqPath.

Definition fun_base (T T' : eqType) (h : T' -> T) f f' :=
  rel_base h (frel f) (frel f').

Section CycleArc.

Variable T : eqType.
Implicit Type p : seq T.

Definition arc p x y := let px := rot (index x p) p in take (index y px) px.

Lemma arc_rot i p : uniq p -> {in p, arc (rot i p) =2 arc p}.

Lemma left_arc x y p1 p2 (p := x :: p1 ++ y :: p2) :
  uniq p -> arc p x y = x :: p1.

Lemma right_arc x y p1 p2 (p := x :: p1 ++ y :: p2) :
  uniq p -> arc p y x = y :: p2.

Variant rot_to_arc_spec p x y :=
    RotToArcSpec i p1 p2 of x :: p1 = arc p x y
                          & y :: p2 = arc p y x
                          & rot i p = x :: p1 ++ y :: p2 :
    rot_to_arc_spec p x y.

Lemma rot_to_arc p x y :
  uniq p -> x \in p -> y \in p -> x != y -> rot_to_arc_spec p x y.

End CycleArc.

Prenex Implicits arc.
```

## mathcomp-classical 1.16 — extraits pour la théorie des graphes (infinis, ensembles classiques, cardinalités)

`rocq-mathcomp-classical` 1.16.0 (sources dans
`~/.opam/default/lib/coq/user-contrib/mathcomp/classical/`) est la couche
*classique* de mathcomp : tiers exclu, extensionnalité, choix, puis le type
`set T` sur un `T : Type` **arbitraire** (donc éventuellement infini), les
cardinalités relationnelles `#<=` / `#=`, et les fonctions à domaine et
codomaine ensemblistes. C'est le seul outillage disponible dès qu'un énoncé
sort du monde `finType` / `{set T}` : graphes infinis, ℵ₀ / non-dénombrable,
groupes abéliens infinis, ℝ « vrai ». Les scopes à ouvrir sont
`classical_set_scope` (`` `&` ``, `` `|` ``, `` `<=` ``, `\bigcup_`) et
`card_scope` (`#<=`, `#=`).

### `boolp.v` / `contra.v` — axiomes classiques et allers-retours `bool` ↔ `Prop`

Les trois axiomes sont posés en clair ; tout le reste en est dérivé. En
pratique on n'utilise presque jamais les axiomes directement : `pselect` (le
tiers exclu en `Type`, qui se `case:`) et `asbool` (`` `[< P >] ``, la vue
booléenne d'une `Prop`) suffisent. Les lemmes `not_*P` / `*NE` poussent les
négations à travers `/\`, `\/`, `forall`, `exists` — indispensables pour
transformer « il n'existe pas de coloration » en « pour toute coloration … ».

```coq
Axiom functional_extensionality_dep :
       forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
       (forall x : A, f x = g x) -> f = g.
Axiom propositional_extensionality :
       forall P Q : Prop, P <-> Q -> P = Q.
Axiom constructive_indefinite_description :
  forall (A : Type) (P : A -> Prop),
  (exists x : A, P x) -> {x : A | P x}.
Notation cid := constructive_indefinite_description.

Lemma cid2 (A : Type) (P Q : A -> Prop) :
  (exists2 x : A, P x & Q x) -> {x : A | P x & Q x}.
Lemma choice X Y (P : X -> Y -> Prop) :
  (forall x, exists y, P x y) -> {f & forall x, P x (f x)}.

(* Tiers exclu, sous ses trois formes. *)
Theorem EM P : P \/ ~ P.
Lemma lem (P : Prop): P \/ ~P.
Lemma pselect (P : Prop): {P} + {~P}.
Lemma pselectT T : (T -> False) + T.
Lemma decide_or P Q : P \/ Q -> {P} + {Q}.

(* Extensionnalité : égalité de Prop, de fonctions, de prédicats. *)
Lemma propext (P Q : Prop) : (P <-> Q) -> (P = Q).
Lemma propeqE (P Q : Prop) : (P = Q) = (P <-> Q).
Lemma propeqP (P Q : Prop) : (P = Q) <-> (P <-> Q).
Lemma funext {T U : Type} (f g : T -> U) : (f =1 g) -> f = g.
Lemma funeqE {T U : Type} (f g : T -> U) : (f = g) = (f =1 g).
Lemma funeqP {T U : Type} (f g : T -> U) : (f = g) <-> (f =1 g).
Lemma predeqE {T} (P Q : T -> Prop) : (P = Q) = (forall x, P x <-> Q x).
Lemma predeqP {T} (A B : T -> Prop) : (A = B) <-> (forall x, A x <-> B x).
Lemma Prop_irrelevance (P : Prop) (x y : P) : x = y.
Lemma propT {P : Prop} : P -> P = True.
Lemma propF (P : Prop) : ~ P -> P = False.
Lemma trueE : true = True :> Prop.
Lemma falseE : false = False :> Prop.
Lemma reflect_eq (P : Prop) (b : bool) : reflect P b -> P = b.

(* eqType / choiceType sur un Type quelconque : indispensable pour poser
   un {fset T} ou un [set` s] sur un type de sommets non structuré. *)
Lemma gen_choiceMixin (T : Type) : hasChoice T.
Definition gen_eqMixin (T : Type) : hasDecEq T := hasDecEq.Build T (@gen_eqP T).
Notation "'{classic' T }" := (classicType T).   (* T + eqType + choiceType *)
Notation "'{eclassic' T }" := (eclassicType T). (* T : eqType + choiceType *)
Lemma Peq : canonical Type eqType.
Lemma Pchoice : canonical Type choiceType.
Lemma eqPchoice : canonical eqType choiceType.

(* asbool : la vue booléenne d'une Prop. `[< P >] : bool. *)
Definition asbool (P : Prop) := if pselect P then true else false.
Notation "`[< P >]" := (asbool P) : bool_scope.
Lemma asboolE (P : Prop) : `[<P>] = P :> Prop.
Lemma asboolP (P : Prop) : reflect P `[<P>].
Lemma asboolPn (P : Prop) : reflect (~ P) (~~ `[<P>]).
Lemma asboolT (P : Prop) : P -> `[<P>].
Lemma asboolF (P : Prop) : ~ P -> `[<P>] = false.
Lemma asboolW (P : Prop) : `[<P>] -> P.
Lemma asbool_neg {P : Prop} : `[<~ P>] = ~~ `[<P>].
Lemma asbool_or {P Q : Prop} : `[<P \/ Q>] = `[<P>] || `[<Q>].
Lemma asbool_and {P Q : Prop} : `[<P /\ Q>] = `[<P>] && `[<Q>].
Lemma asbool_imply {P Q : Prop} : `[<P -> Q>] = `[<P>] ==> `[<Q>].
Lemma or_asboolP (P Q : Prop) : reflect (P \/ Q) (`[< P >] || `[< Q >]).
Lemma or3_asboolP (P Q R : Prop) :
  reflect [\/ P, Q | R] [|| `[< P >], `[< Q >] | `[< R >]].
Lemma imply_asboolP {P Q : Prop} : reflect (P -> Q) (`[<P>] ==> `[<Q>]).
Lemma imply_asboolPn (P Q : Prop) : reflect (P /\ ~ Q) (~~ `[<P -> Q>]).
Lemma forall_asboolP {T : Type} (P : T -> Prop) :
  reflect (forall x, `[<P x>]) (`[<forall x, P x>]).
Lemma exists_asboolP {T : Type} (P : T -> Prop) :
  reflect (exists x, `[<P x>]) (`[<exists x, P x>]).
Lemma forallp_asboolPn {T} {P : T -> Prop} :
  reflect (forall x : T, ~ P x) (~~ `[<exists x : T, P x>]).
Lemma existsp_asboolPn {T} {P : T -> Prop} :
  reflect (exists x : T, ~ P x) (~~ `[<forall x : T, P x>]).
Lemma asbool_forallNb {T : Type} (P : pred T) :
  `[< forall x : T, ~~ (P x) >] = ~~ `[< exists x : T, P x >].
Lemma asbool_existsNb {T : Type} (P : pred T) :
  `[< exists x : T, ~~ (P x) >] = ~~ `[< forall x : T, P x >].
Lemma is_true_inj : injective is_true.
Lemma eq_opE (T : eqType) (x y : T) : (x == y : Prop) = (x = y).

(* Négation classique : pousser ~ à travers les connecteurs. *)
Lemma contrapT P : ~ ~ P -> P.
Lemma not_notP (P : Prop) : ~ ~ P <-> P.       Notation notP := not_notP.
Lemma not_notE (P : Prop) : (~ ~ P) = P.       Notation notE := not_notE.
Lemma notK : involutive not.
Lemma not_andE (P Q : Prop) : (~ (P /\ Q)) = (~ P \/ ~ Q).
Lemma not_andP (P Q : Prop) : ~ (P /\ Q) <-> ~ P \/ ~ Q.
Lemma not_and3P (P Q R : Prop) : ~ [/\ P, Q & R] <-> [\/ ~ P, ~ Q | ~ R].
Lemma not_orE (P Q : Prop) : (~ (P \/ Q)) = (~ P /\ ~ Q).
Lemma not_orP (P Q : Prop) : ~ (P \/ Q) <-> ~ P /\ ~ Q.
Lemma not_implyE (P Q : Prop) : (~ (P -> Q)) = (P /\ ~ Q).
Lemma not_implyP (P Q : Prop) : ~ (P -> Q) <-> P /\ ~ Q.
Lemma implyE (P Q : Prop) : (P -> Q) = (~ P \/ Q).
Lemma forallNE {T} (P : T -> Prop) : (forall x, ~ P x) = (~ exists x, P x).
Lemma existsNE {T} (P : T -> Prop) : (exists x, ~ P x) = (~ forall x, P x).
Lemma existsNP T (P : T -> Prop) : (exists x, ~ P x) <-> ~ forall x, P x.
Lemma forallNP T (P : T -> Prop) : (forall x, ~ P x) <-> ~ exists x, P x.
Lemma not_existsP T (P : T -> Prop) : (exists x, P x) <-> ~ forall x, ~ P x.
Lemma not_forallP T (P : T -> Prop) : (forall x, P x) <-> ~ exists x, ~ P x.
Lemma exists2E A P Q : (exists2 x : A, P x & Q x) = (exists x, P x /\ Q x).
Lemma forallPNP T (P Q : T -> Prop) :
  (forall x, P x -> ~ Q x) <-> ~ (exists2 x, P x & Q x).
Lemma existsPNP T (P Q : T -> Prop) :
  (exists2 x, P x & ~ Q x) <-> ~ (forall x, P x -> Q x).

(* Contraposition mixte bool/Prop (les vues à utiliser avec apply:/move/). *)
Lemma contra_notP (Q P : Prop) : (~ Q -> P) -> ~ P -> Q.
Lemma contraPP (Q P : Prop) : (~ Q -> ~ P) -> P -> Q.
Lemma contra_notT b (P : Prop) : (~~ b -> P) -> ~ P -> b.
Lemma contraPT (P : Prop) b : (~~ b -> ~ P) -> P -> b.
Lemma contraTP b (Q : Prop) : (~ Q -> ~~ b) -> b -> Q.
Lemma contraNP (P : Prop) (b : bool) : (~ P -> b) -> ~~ b -> P.
Lemma contra_neqP (T : eqType) (x y : T) P : (~ P -> x = y) -> x != y -> P.
Lemma contra_eqP (T : eqType) (x y : T) Q : (~ Q -> x != y) -> x = y -> Q.
Lemma wlog_neg P : (~ P -> P) -> P.
Lemma iff_notr (P Q : Prop) : (P <-> ~ Q) <-> (~ P <-> Q).
Lemma inhabitedE : inhabited T = exists x : T, True.
Lemma inhabited_witness : inhabited T -> T.

(* contra.v : tactiques (pas des lemmes) — voir l'en-tête du fichier.
   assume_not  : ajoute ~ but en hypothèse (marche aussi sur un but en Type)
   absurd_not  : raisonnement par l'absurde, remplace le but par False
   contra      : (A -> B)  devient  (~ B -> ~ A), simplifie les négations
   contra: t   :=  move: t; contra
   absurd / absurd: t / absurd term
   Lemma assume_not {P} : (~ P -> P) -> P.
   Lemma absurd_not {P} : (~ P -> False) -> P.
   Lemma absurd T : False -> T.
   Definition notP {nP P} := MoveView (@lax_notP false nP P). (* vue move/notP *)
   witness : extrait un témoin d'une Prop existentielle (move/witness). *)
```

### `classical_sets.v` — `set T` sur un type arbitraire

`set T := T -> Prop` : aucune finitude, aucun `eqType` requis. Le `\in`
booléen existe quand même (`in_set A x := `[< A x >]`), avec les deux ponts
`mem_set` / `set_mem` et la réécriture `inE`. Pour prouver une égalité
d'ensembles : `apply/seteqP; split` (ou `rewrite eqEsubset`) ; pour une
appartenance sous `{in A, …}` : `in_setP`. Le reste est l'algèbre booléenne
usuelle, plus `\bigcup` / `\bigcap` indexés par un `set I` (et non par un
`finType`), `trivIset` / `cover` / `partition` (la version infinie des
partitions de `finset.v`), et le lemme de Zorn.

```coq
Definition set T := T -> Prop.
Definition in_set T (A : set T) : pred T := (fun x => `[<A x>]).
Canonical set_predType T := @PredType T (set T) (@in_set T).
Definition inE := (inE, in_setE).

Lemma in_setE T (A : set T) x : x \in A = A x :> Prop.
Lemma mem_set {A} {u : T} : A u -> u \in A.
Lemma set_mem {A} {u : T} : u \in A -> A u.
Lemma memNset (A : set T) (u : T) : ~ A u -> u \in A = false.
Lemma notin_setE (A : set T) x : (x \notin A : Prop) = (~ A x).
Lemma in_setP {U} (A : set U) (P : U -> Prop) :
  {in A, forall x, P x} <-> forall x, A x -> P x.
Lemma in_set2P {U V} (A : set U) (B : set V) (P : U -> V -> Prop) :
  {in A & B, forall x y, P x y} <-> (forall x y, A x -> B y -> P x y).
Lemma set_valP {A} (x : A) : A (val x).   (* A : set T vu comme sous-type *)

(* Constructeurs. *)
Definition mkset {T} (P : T -> Prop) : set T := P.
Notation "[ 'set' x : T | P ]" := (mkset (fun x : T => P)) : classical_set_scope.
Notation "[ 'set' x | P ]" := [set x : _ | P] : classical_set_scope.
Definition image {T rT} (A : set T) (f : T -> rT) :=
  [set y | exists2 x, A x & f x = y].
Notation "[ 'set' E | x 'in' A ]" := (image A (fun x => E)) : classical_set_scope.
Definition image2 {TA TB rT} (A : set TA) (B : set TB) (f : TA -> TB -> rT) :=
  [set z | exists2 x, A x & exists2 y, B y & f x y = z].
Definition preimage f Y : set T := [set t | Y (f t)].
Definition setT := [set _ : T | True].
Definition set0 := [set _ : T | False].
Definition set1 (t : T) := [set x : T | x = t].
Definition setI A B := [set x | A x /\ B x].
Definition setU A B := [set x | A x \/ B x].
Definition nonempty A := exists a, A a.
Definition setC A := [set a | ~ A a].
Definition setD A B := [set x | A x /\ ~ B x].
Definition setX T1 T2 (A1 : set T1) (A2 : set T2) := [set z | A1 z.1 /\ A2 z.2].
Definition setY {T : Type} (A B : set T) := (A `\` B) `|` (B `\` A).
Definition bigcap T I (P : set I) (F : I -> set T) := [set a | forall i, P i -> F i a].
Definition bigcup T I (P : set I) (F : I -> set T) := [set a | exists2 i, P i & F i a].
Definition subset A B := forall t, A t -> B t.
Definition disj_set A B := setI A B == set0.
Definition proper A B := A `<=` B /\ ~ (B `<=` A).
Definition set_system U := set (set U).

Notation range F := [set F i | i in setT].
Notation "[ 'set' a ]" := (set1 a) : classical_set_scope.
Notation "[ 'set' : T ]" := (@setT T) : classical_set_scope.
Notation "A `|` B" := (setU A B) : classical_set_scope.
Notation "a |` A" := ([set a] `|` A) : classical_set_scope.
Notation "[ 'set' a1 ; a2 ; .. ; an ]" :=
  (setU .. (a1 |` [set a2]) .. [set an]) : classical_set_scope.
Notation "A `&` B" := (setI A B) : classical_set_scope.
Notation "A `*` B" := (setX A B) : classical_set_scope.
Notation "~` A" := (setC A) : classical_set_scope.
Notation "[ 'set' ~ a ]" := (~` [set a]) : classical_set_scope.
Notation "A `\` B" := (setD A B) : classical_set_scope.
Notation "A `\ a" := (A `\` [set a]) : classical_set_scope.
Notation "A `+` B" := (setY A B) : classical_set_scope.   (* diff. symétrique *)
Notation "[ 'disjoint' A & B ]" := (disj_set A B) : classical_set_scope.
Notation "A `<=` B" := (subset A B) : classical_set_scope.
Notation "A `<` B" := (proper A B) : classical_set_scope.
Notation "A `<=>` B" := ((A `<=` B) /\ (B `<=` A)) : classical_set_scope.
Notation "f @^-1` A" := (preimage f A) : classical_set_scope.
Notation "f @` A" := (image A f) (only parsing) : classical_set_scope.
Notation "A !=set0" := (nonempty A) : classical_set_scope.
Notation "[ 'set`' p ]":= [set x | is_true (x \in p)] : classical_set_scope.
Notation "'`I_' n" := [set k | is_true (k < n)%N].
Notation "\bigcup_ ( i 'in' P ) F" := (bigcup P (fun i => F)) : classical_set_scope.
Notation "\bigcup_ ( i : T ) F" := (\bigcup_(i in @setT T) F) : classical_set_scope.
Notation "\bigcup_ ( i < n ) F" := (\bigcup_(i in `I_n) F) : classical_set_scope.
Notation "\bigcup_ ( i >= n ) F" :=
  (\bigcup_(i in [set i | (n <= i)%N]) F) : classical_set_scope.
Notation "\bigcup_ i F" := (\bigcup_(i : _) F) : classical_set_scope.
Notation "\bigcap_ ( i 'in' P ) F" := (bigcap P (fun i => F)) : classical_set_scope.
Notation "\bigcap_ ( i < n ) F" := (\bigcap_(i in `I_n) F) : classical_set_scope.
Notation "\bigcap_ i F" := (\bigcap_(i : _) F) : classical_set_scope.

(* Inclusion, égalité, vide. *)
Lemma subsetP A B : {subset A <= B} <-> (A `<=` B).
Lemma eqEsubset A B : (A = B) = (A `<=>` B).
Lemma seteqP A B : (A = B) <-> (A `<=>` B).
Lemma subset_refl A : A `<=` A.
Lemma subset_trans B A C : A `<=` B -> B `<=` C -> A `<=` C.
Lemma sub0set A : set0 `<=` A.          Lemma subsetT A : A `<=` setT.
Lemma subset0 A : (A `<=` set0) = (A = set0).
Lemma subTset A : (setT `<=` A) = (A = setT).
Lemma sub1set x A : ([set x] `<=` A) = (x \in A).
Lemma set0P A : (A != set0) <-> (A !=set0).
Lemma nonemptyPn A : ~ (A !=set0) <-> A = set0.
Lemma setTPn (A : set T) : A != setT <-> exists t, ~ A t.
Lemma subset_nonempty A B : A `<=` B -> A !=set0 -> B !=set0.
Lemma nonsubset A B : ~ (A `<=` B) -> A `&` ~` B !=set0.
Lemma properW A B : A `<` B -> A `<=` B.
Lemma properxx A : ~ A `<` A.
Lemma properEneq A B : (A `<` B) = (A != B /\ A `<=` B).
Lemma subset_set1 A a : A `<=` [set a] -> A = set0 \/ A = [set a].
Lemma subset_set2 A a b : A `<=` [set a; b] ->
  [\/ A = set0, A = [set a], A = [set b] | A = [set a; b]].
Definition is_subset1 {T} (A : set T) := forall x y, A x -> A y -> x = y.

(* Algèbre booléenne (extrait ; tout setIC/setUA/setCK/… est présent). *)
Lemma setDE A B : A `\` B = A `&` ~` B.
Lemma setCK : involutive (@setC T).
Lemma setCU A B : ~`(A `|` B) = ~` A `&` ~` B.
Lemma setCI A B : ~` (A `&` B) = ~` A `|` ~` B.
Lemma setIUl : left_distributive (@setI T) (@setU T).
Lemma setD_eq0 A B : (A `\` B = set0) = (A `<=` B).
Lemma setDUK A B : A `<=` B -> A `|` (B `\` A) = B.
Lemma setD1K a A : A a -> a |` A `\ a = A.
Lemma not_setD1 a A : ~ A a -> A `\ a = A.
Lemma setIidPl A B : A `&` B = A <-> A `<=` B.
Lemma subsetI A B C : (A `<=` B `&` C) = ((A `<=` B) /\ (A `<=` C)).
Lemma subUset A B C : (B `|` C `<=` A) = ((B `<=` A) /\ (C `<=` A)).
Lemma subIsetl A B : A `&` B `<=` A.     Lemma subIsetr A B : A `&` B `<=` B.
Lemma subDsetl A B : A `\` B `<=` A.     Lemma subDsetr A B : A `\` B `<=` ~` B.
Lemma setSD C A B : A `<=` B -> A `\` C `<=` B `\` C.
Lemma setSI C A B : A `<=` B -> A `&` C `<=` B `&` C.
Lemma setSU C A B : A `<=` B -> A `|` C `<=` B `|` C.
Lemma subsetC A B : A `<=` B -> ~` B `<=` ~` A.
Lemma subsetCP A B : ~` A `<=` ~` B <-> B `<=` A.
Lemma subsetI_neq0 A B C D :
  A `<=` B -> C `<=` D -> A `&` C !=set0 -> B `&` D !=set0.
Lemma subsetI_eq0 A B C D :
  A `<=` B -> C `<=` D -> B `&` D = set0 -> A `&` C = set0.

(* Disjonction. *)
Lemma disj_set2E A B : [disjoint A & B] = (A `&` B == set0).
Lemma disj_set2P {A B} : reflect (A `&` B = set0) [disjoint A & B]%classic.
Lemma disj_setPS {A B} : reflect (A `&` B `<=` set0) [disjoint A & B]%classic.
Lemma disj_set_sym A B : [disjoint B & A] = [disjoint A & B].
Lemma disj_setPLR {A B} : reflect (A `<=` ~` B) [disjoint A & B]%classic.
Lemma subsets_disjoint A B : A `<=` B <-> A `&` ~` B = set0.
Lemma disjoints_subset A B : A `&` B = set0 <-> A `<=` ~` B.

(* Ponts avec les prédicats booléens / seq / {fset} / finType. *)
Lemma set_mem_set A : [set` A] = A.
Lemma set_true : [set` predT] = setT :> set T.
Lemma set_false : [set` pred0] = set0 :> set T.
Lemma set_predC (P : {pred T}) : [set` predC P] = ~` [set` P].
Lemma set_andb (P Q : {pred T}) : [set` predI P Q] = [set` P] `&` [set` Q].
Lemma set_orb (P Q : {pred T}) : [set` predU P Q] = [set` P] `|` [set` Q].
Lemma set_nil (T : eqType) : [set` [::]] = @set0 T.
Lemma set_seq_eq0 (T : eqType) (S : seq T) : ([set` S] == set0) = (S == [::]).
Lemma set_fsetI A B : [set` (A `&` B)%fset] = [set` A] `&` [set` B].
Lemma fdisjoint_cset (T : choiceType) (A B : {fset T}) :
  [disjoint A & B]%fset = [disjoint [set` A] & [set` B]].
Lemma II0 : `I_0 = set0.        Lemma II1 : `I_1 = [set 0].
Lemma IIS n : `I_n.+1 = `I_n `|` [set n].
Lemma IIDn n : `I_n.+1 `\ n = `I_n.
Lemma setI_II m n : `I_m `&` `I_n = `I_(minn m n).
Lemma setU_II m n : `I_m `|` `I_n = `I_(maxn m n).
Lemma Iiota (n : nat) : [set` iota 0 n] = `I_n.
Lemma setC_I n : ~` `I_n = [set k | n <= k].
Definition ordII {n} (k : 'I_n) : `I_n := SigSub (@mem_set _ `I_n _ (ltn_ord k)).
Definition IIord {n} (k : `I_n) := Ordinal (set_valP k).

(* Images et préimages. *)
Lemma imageP f A a : A a -> (f @` A) (f a).
Lemma imageT (f : aT -> rT) (a : aT) : range f (f a).
Lemma image_inj {f A a} : injective f -> (f @` A) (f a) = A a.
Lemma image_set0 f : f @` set0 = set0.
Lemma image_set1 f t : f @` [set t] = [set f t].
Lemma image_setU f A B : f @` (A `|` B) = f @` A `|` f @` B.
Lemma sub_image_setI f A B : f @` (A `&` B) `<=` f @` A `&` f @` B.
Lemma image_subset f A B : A `<=` B -> f @` A `<=` f @` B.
Lemma image_subP {A Y f} : f @` A `<=` Y <-> {homo f : x / A x >-> Y x}.
Lemma homo_setP {A Y f} :
  {homo f : x / x \in A >-> x \in Y} <-> {homo f : x / A x >-> Y x}.
Lemma nonempty_image f A : f @` A !=set0 -> A !=set0.
Lemma image_nonempty f A : A !=set0 -> f @` A !=set0.
Lemma image_comp T1 T2 T3 (f : T1 -> T2) (g : T2 -> T3) A : g @` (f @` A) = (g \o f) @` A.
Lemma preimage_set0 f : f @^-1` set0 = set0.
Lemma preimage_setT f : f @^-1` setT = setT.
Lemma preimage_image f A : A `<=` f @^-1` (f @` A).
Lemma image_preimage_subset f Y : f @` (f @^-1` Y) `<=` Y.
Lemma image_preimage f Y : f @` setT = setT -> f @` (f @^-1` Y) = Y.
Lemma preimage_setU f Y1 Y2 : f @^-1` (Y1 `|` Y2) = f @^-1` Y1 `|` f @^-1` Y2.
Lemma preimage_setI f Y1 Y2 : f @^-1` (Y1 `&` Y2) = f @^-1` Y1 `&` f @^-1` Y2.
Lemma preimage_setC f Y : ~` (f @^-1` Y) = f @^-1` (~` Y).
Lemma preimage_subset f Y1 Y2 : Y1 `<=` Y2 -> f @^-1` Y1 `<=` f @^-1` Y2.
Lemma preimage_bigcup {I} (P : set I) f (F : I -> set rT) :
  f @^-1` (\bigcup_(i in P) F i) = \bigcup_(i in P) (f @^-1` F i).
Lemma preimage_bigcap {I} (P : set I) f (F : I -> set rT) :
  f @^-1` (\bigcap_(i in P) F i) = \bigcap_(i in P) (f @^-1` F i).
Lemma inTT_bij [T1 T2 : Type] [f : T1 -> T2] :
  {in [set: T1], bijective f} -> bijective f.

(* Unions / intersections indexées par un set I quelconque. *)
Lemma bigcup_sup i P F : P i -> F i `<=` \bigcup_(j in P) F j.
Lemma bigcap_inf i P F : P i -> \bigcap_(j in P) F j `<=` F i.
Lemma bigcup_sub F A P : (forall i, P i -> F i `<=` A) -> \bigcup_(i in P) F i `<=` A.
Lemma sub_bigcap F A P : (forall i, P i -> A `<=` F i) -> A `<=` \bigcap_(i in P) F i.
Lemma subset_bigcup P F G : (forall i, P i -> F i `<=` G i) ->
  \bigcup_(i in P) F i `<=` \bigcup_(i in P) G i.
Lemma subset_bigcap P F G : (forall i, P i -> F i `<=` G i) ->
  \bigcap_(i in P) F i `<=` \bigcap_(i in P) G i.
Lemma bigcup_subset P Q F : P `<=` Q -> \bigcup_(i in P) F i `<=` \bigcup_(i in Q) F i.
Lemma setC_bigcup P F : ~` (\bigcup_(i in P) F i) = \bigcap_(i in P) ~` F i.
Lemma setC_bigcap P F : ~` (\bigcap_(i in P) (F i)) = \bigcup_(i in P) ~` F i.
Lemma eq_bigcupr P F G : (forall i, P i -> F i = G i) ->
  \bigcup_(i in P) F i = \bigcup_(i in P) G i.
Lemma bigcup_set0 F : \bigcup_(i in set0) F i = set0.
Lemma bigcup_set1 F i : \bigcup_(j in [set i]) F j = F i.
Lemma bigcup_nonempty P F :
  (\bigcup_(i in P) F i !=set0) <-> exists2 i, P i & F i !=set0.
Lemma bigcup0P P F : (\bigcup_(i in P) F i = set0) <-> forall i, P i -> F i = set0.
Lemma setI_bigcupr F P A : A `&` \bigcup_(i in P) F i = \bigcup_(i in P) (A `&` F i).
Lemma bigcup_setU F (X Y : set I) :
  \bigcup_(i in X `|` Y) F i = \bigcup_(i in X) F i `|` \bigcup_(i in Y) F i.
Lemma bigcup_setD1 (x : I) F (X : set I) : X x ->
  \bigcup_(i in X) F i = F x `|` \bigcup_(i in X `\ x) F i.
Lemma bigcup_image {aT rT I} (P : set aT) (f : aT -> I) (F : I -> set rT) :
  \bigcup_(x in f @` P) F x = \bigcup_(x in P) F (f x).
Lemma image_bigcup rT P F (f : T -> rT) :
  f @` (\bigcup_(i in P) F i) = \bigcup_(i in P) f @` F i.
Lemma bigcup_mkord n F : \bigcup_(i < n) F i = \big[setU/set0]_(i < n) F i.
Lemma bigcup_splitn n F :
  \bigcup_i F i = \big[setU/set0]_(i < n) F i `|` \bigcup_i F (n + i).
Lemma bigcup_recl T (F : nat -> set T) : \bigcup_i F i = F 0 `|` \bigcup_i F i.+1.
Lemma bigcup_seq (s : seq T) (f : T -> set U) :
  \bigcup_(t in [set` s]) (f t) = \big[setU/set0]_(t <- s) (f t).
Lemma bigcup_pred [T : finType] [U : Type] (P : {pred T}) (f : T -> set U) :
  \bigcup_(t in [set` P]) f t = \big[setU/set0]_(t in P) f t.
Lemma bigcup_fset {I : choiceType} {U : Type} (F : I -> set U) (X : {fset I}) :
  \bigcup_(i in [set i | i \in X]) F i = \big[setU/set0]_(i <- X) F i :> set U.
Definition smallest := \bigcap_(A in [set M | C M /\ G `<=` M]) A.
Lemma smallest_sub X : C X -> G `<=` X -> smallest `<=` X.

(* Partitions infinies : trivIset / cover / partition / pblock. *)
Definition trivIset T I (D : set I) (F : I -> set T) :=
  forall i j : I, D i -> D j -> F i `&` F j !=set0 -> i = j.
Definition cover T I D (F : I -> set T) := \bigcup_(i in D) F i.
Definition partition T I D (F : I -> set T) (A : set T) :=
  [/\ cover D F = A, trivIset D F & forall i, D i -> F i !=set0].
Definition pblock_index T (I : pointedType) D (F : I -> set T) (x : T) :=
  [get i | D i /\ F i x].
Definition pblock T (I : pointedType) D (F : I -> set T) (x : T) :=
  F (pblock_index D F x).
Lemma trivIsetP {T} {I : eqType} {D : set I} {F : I -> set T} :
  trivIset D F <->
  forall i j : I, D i -> D j -> i != j -> F i `&` F j = set0.
Lemma trivIset1 T I (i : I) (F : I -> set T) : trivIset [set i] F.
Lemma sub_trivIset I T (D D' : set I) (F : I -> set T) :
  D `<=` D' -> trivIset D' F -> trivIset D F.
Lemma trivIset_setIl (T I : Type) (D : set I) (F : I -> set T) (G : I -> set T) :
  trivIset D F -> trivIset D (fun i => G i `&` F i).
Lemma trivIset_image T I I' (D : set I) (f : I -> I') (F : I' -> set T) :
  trivIset D (F \o f) -> trivIset (f @` D) F.
Lemma trivIset_preimage1 {aT rT} D (f : aT -> rT) :
  trivIset D (fun x => f @^-1` [set x]).
Lemma trivIset_bigcup (I T : Type) (J : eqType) (D : J -> set I) (F : I -> set T) :
  (forall n, trivIset (D n) F) ->
  (forall n m i j, n != m -> D n i -> D m j -> F i `&` F j !=set0 -> i = j) ->
  trivIset (\bigcup_k D k) F.
Definition maximal_disjoint_subcollection T I (F : I -> set T) (A B : set I) :=
  [/\ A `<=` B, trivIset A F & forall C,
      A `<` C -> C `<=` B -> ~ trivIset C F ].
Lemma ex_maximal_disjoint_subcollection :
  { E | maximal_disjoint_subcollection B E D }.

(* Zorn (la forme utile pour « tout graphe a un ... maximal »). *)
Definition total_on T (A : set T) (R : T -> T -> Prop) :=
  forall s t, A s -> A t -> R s t \/ R t s.
Definition premaximal T (R : T -> T -> Prop) (t : T) := forall s, R t s -> R s t.
Lemma Zorn (T : Type) (R : rel T) :
  (forall t, R t t) -> (forall r s t, R r s -> R s t -> R r t) ->
  (forall s t, R s t -> R t s -> s = t) ->
  (forall A : set T, total_on A R -> exists t, forall s, A s -> R s t) ->
  exists t, forall s, R t s -> s = t.
Lemma Zorn_bigcup :          (* P : set (set T), chaîne -> union dans P *)
    (forall F : set (set T), F `<=` P -> total_on F subset ->
      P (\bigcup_(X in F) X)) ->
  exists A, P A /\ forall B, A `<` B -> ~ P B.
Lemma ZL_preorder (T : Type) (t0 : T) (R : rel T) :
  (forall t, R t t) -> (forall r s t, R r s -> R s t -> R r t) ->
  (forall A : set T, total_on A R -> exists t, forall s, A s -> R s t) ->
  exists t, premaximal R t.

(* Choix concret dans un ensemble : xget / get / squash. *)
Definition xget {T : choiceType} x0 (P : set T) : T :=
  if pselect (exists x : T, `[<P x>]) isn't left exP then x0
  else projT1 (sigW exP).
Notation get := (xget point).
Notation "[ 'get' x | E ]" := (get (fun x => E)) : form_scope.
Lemma xgetPex {T : choiceType} x0 (P : set T) : (exists x, P x) -> P (xget x0 P).
Lemma getPex (P : set T) : (exists x, P x) -> P (get P).   (* T : pointedType *)
Variant squashed T : Prop := squash (x : T).
Notation "$| T |" := (squashed T) : form_scope.
Definition unsquash {T} (s : $|T|) : T.
Lemma unsquashK {T} : cancel (@unsquash T) squash.
Lemma Ppointed : quasi_canonical Type pointedType.
```

### `cardinality.v` — `#<=`, `#=`, `finite_set`, `countable`

Théorie *relationnelle* des cardinaux : pas de type des cardinaux, seulement
`A #<= B` (injection de `A` dans `B`) et `A #= B` (bijection). `finite_set A`
est `exists n, A #= `I_n`, équivalent à « `A` est un `{fset}` »
(`finite_fsetP`) et à « `[set: nat]` ne s'injecte pas dans `A` »
(`finite_setPn`). C'est exactement le pont dont on a besoin pour énoncer un
résultat sur les graphes infinis et le spécialiser aux graphes finis :
`finite_finset` donne la finitude gratuite sur un `finType`, `fset_set` rend
le `{fset T}` sous-jacent, et `card_fset_set` relie `#|` … |` au `#=`.
`countable A := A #<= [set: nat]` est le ℵ₀ ; « non dénombrable » s'écrit
`~ countable A`, et `infiniteP` donne la caractérisation de Dedekind.

```coq
Definition card_le T U (A : set T) (B : set U) :=
  `[< $|{injfun [set: A] >-> [set: B]}| >].
Notation "A '#<=' B" := (card_le A B) : card_scope.
Notation "A '#>=' B" := (card_le B A) (only parsing) : card_scope.
Definition card_eq T U (A : set T) (B : set U) :=
  `[< $|{bij [set: A] >-> [set: B]}| >].
Notation "A '#=' B" := (card_eq A B) : card_scope.
Notation "A '#!=' B" := (~~ (card_eq A B)) : card_scope.
Definition finite_set {T} (A : set T) := exists n, A #= `I_n.
Notation infinite_set A := (~ finite_set A).
Notation cofinite_set A := (finite_set (~` A)).
Definition countable T (A : set T) := A #<= @setT nat.

(* Vues : passer de #<= / #= à une vraie fonction. *)
Lemma card_leP {T U} {A : set T} {B : set U} :
  reflect $|{injfun [set: A] >-> [set: B]}| (A #<= B).
Lemma pcard_injP {T} {U : pointedType} {A : set T} :
  reflect (exists f : T -> U, {in A &, injective f}) (A #<= [set: U]).
Lemma pcard_leP {T} {U : pointedType} {A : set T} {B : set U} :
   reflect $|{injfun A >-> B}| (A #<= B).
Lemma card_eqP {T U} {A : set T} {B : set U} :
  reflect $|{bij [set: A] >-> [set: B]}| (A #= B).
Lemma pcard_eqP {T} {U : pointedType} {A : set T} {B : set U} :
  reflect $|{bij A >-> B}| (A #= B).
Lemma card_set_bijP {T} {U : pointedType} {A : set T} {B : set U} :
  reflect (exists f : T -> U, set_bij A B f) (A #= B).
Lemma inj_card_le {T U} {A : set T} {B : set U} : {injfun A >-> B} -> (A #<= B).
Lemma pcard_eq {T U} {A : set T} {B : set U} : {bij A >-> B} -> A #= B.
Lemma card_subP T U (A : set T) (B : set U) :
  reflect (exists2 C, C #= A & C `<=` B) (A #<= B).
Lemma injPex {T U} {A : set T} : $|{inj A >-> U}| <-> exists f : T -> U, set_inj A f.
Lemma bijPex {T U} {A : set T} {B : set U} :
  $|{bij A >-> B}| <-> exists f, set_bij A B f.

(* Ordre / équivalence. *)
Theorem Cantor_Bernstein T U (A : set T) (B : set U) :
  A #<= B -> B #<= A -> A #= B.
Lemma card_lexx T (A : set T) : A #<= A.
Lemma card_leT T (S : set T) : S #<= [set: T].
Lemma card_ge0 T U (S : set U) : @set0 T #<= S.
Lemma card_le0 T U (A : set T) : (A #<= @set0 U) = (A == set0).
Lemma subset_card_le T (A B : set T) : A `<=` B -> A #<= B.
Lemma card_le_trans (T U V : Type) (B : set U) (A : set T) (C : set V) :
  A #<= B -> B #<= C -> A #<= C.
Lemma card_eqxx T (A : set T) : A #= A.
Lemma card_esym T U (A : set T) (B : set U) : A #= B -> B #= A.
Lemma card_eq_sym T U (A : set T) (B : set U) : (A #= B) = (B #= A).
Lemma card_eq_trans T U V (A : set T) (B : set U) (C : set V) :
  A #= B -> B #= C -> A #= C.
Lemma card_eqPle T U (A : set T) (B : set U) : reflect (A #<= B /\ B #<= A) (A #= B).
Lemma card_eq0 {T U} {A : set T} : (A #= @set0 U) = (A == set0).
Lemma card_image_le {T U} (f : T -> U) (A : set T) : f @` A #<= A.
Lemma inj_card_eq {T U} {A} {f : T -> U} : {in A &, injective f} -> f @` A #= A.
Lemma card_image {T U} {A : set T} (f : {inj A >-> U}) : f @` A #= A.
Lemma card_setT T (A : set T) : [set: A] #= A.
Lemma surj_card_ge {T U} {A : set T} {B : set U} : {surj B >-> A} -> A #<= B.
Lemma card_le_II n m : (`I_n #<= `I_m) = (n <= m)%N.
Lemma card_eq_II {n m} : reflect (n = m) (`I_n #= `I_m).
Lemma card_IID {n k} : `I_n `\` `I_k #= `I_(n - k)%N.
Lemma pigeonhole m n (f : nat -> nat) : {in `I_m &, injective f} ->
  f @` `I_m `<=` `I_n -> (m <= n)%N.

(* finite_set : les quatre caractérisations + la stabilité. *)
Lemma finite_setP T (A : set T) : finite_set A <-> exists n, A #= `I_n.
Lemma finite_set_leP T (A : set T) : finite_set A <-> exists n, A #<= `I_n.
Lemma finite_fsetP {T : choiceType} {A : set T} :
  finite_set A <-> exists X : {fset T}, A = [set` X].
Lemma finite_seqP {T : eqType} A : finite_set A <-> exists s : seq T, A = [set` s].
Lemma finite_setPn T (A : set T) : finite_set A <-> ~ ([set: nat] #<= A).
Lemma infiniteP T (A : set T) : infinite_set A <-> [set: nat] #<= A.
Lemma finite_finset {T : finType} {X : set T} : finite_set X.
Lemma finite_finpred {T : finType} {pT : predType T} (P : pT) : finite_set [set` P].
Lemma finite_fset {T : choiceType} (X : {fset T}) : finite_set [set` X].
Lemma finite_seq {T : eqType} (s : seq T) : finite_set [set` s].
Lemma finite_II n : finite_set `I_n.
Lemma card_II {n} : `I_n #= [set: 'I_n].
Lemma finite_set0 T : finite_set (set0 : set T).
Lemma finite_set1 T (x : T) : finite_set [set x].
Lemma finite_subfset {T : choiceType} (X : {fset T}) {A : set T} :
  A `<=` [set` X] -> finite_set A.
Lemma card_le_finite T U (A : set T) (B : set U) : A #<= B -> finite_set B -> finite_set A.
Lemma sub_finite_set T (A B : set T) : A `<=` B -> finite_set B -> finite_set A.
Lemma sub_infinite_set T (A B : set T) : A `<=` B -> infinite_set A -> infinite_set B.
Lemma eq_finite_set T U (A : set T) (B : set U) : A #= B -> finite_set A = finite_set B.
Lemma infinite_setN0 {T} (A : set T) : infinite_set A -> A !=set0.
Lemma finite_setU T (A B : set T) :
  finite_set (A `|` B) = (finite_set A /\ finite_set B).
Lemma finite_setI T (A B : set T) : (finite_set A \/ finite_set B) -> finite_set (A `&` B).
Lemma finite_setD T (A B : set T) : finite_set A -> finite_set (A `\` B).
Lemma finite_setX T T' (A : set T) (B : set T') :
  finite_set A -> finite_set B -> finite_set (A `*` B).
Lemma finite_setX_or T T' (A : set T) (B : set T') :
  finite_set (A `*` B) -> finite_set A \/ finite_set B.
Lemma infinite_setX {T} {A B : set T} :
  infinite_set A -> infinite_set B -> infinite_set (A `*` B).
Lemma infinite_setD {T} (A B : set T) :
  infinite_set A -> finite_set B -> infinite_set (A `\` B).
Lemma finite_image T T' A (f : T -> T') : finite_set A -> finite_set (f @` A).
Lemma finite_image2 [aT bT rT : Type] [A : set aT] [B : set bT] (f : aT -> bT -> rT) :
  finite_set A -> finite_set B -> finite_set [set f x y | x in A & y in B].
Lemma card_ge_preimage {T U} (B : set U) (f : T -> U) :
  {in f @^-1` B &, injective f} -> f @^-1` B #<= B.
Corollary finite_preimage {T U} (B : set U) (f : T -> U) :
  {in f @^-1` B &, injective f} -> finite_set B -> finite_set (f @^-1` B).
Lemma bigcup_finite {I T} (D : set I) (F : I -> set T) :
    finite_set D -> (forall i, D i -> finite_set (F i)) ->
  finite_set (\bigcup_(i in D) F i).
Lemma cofinite_set_infinite {T} (A : set T) : infinite_set [set: T] ->
  cofinite_set A -> infinite_set A.

(* fset_set : le {fset T} sous-jacent, et le pont avec #|` … |. *)
Definition fset_set (T : choiceType) (A : set T) :=
  if pselect (finite_set A) is left Afin
  then projT1 (cid (finite_fsetP.1 Afin)) else fset0.
Lemma fset_setK (T : choiceType) (A : set T) : finite_set A -> [set` fset_set A] = A.
Lemma in_fset_set (T : choiceType) (A : set T) : finite_set A -> fset_set A =i A.
Lemma set_fsetK (T : choiceType) (A : {fset T}) : fset_set [set` A] = A.
Lemma fset_set_sub (T : choiceType) (A B : set T) :
  finite_set A -> finite_set B -> A `<=` B = (fset_set A `<=` fset_set B)%fset.
Lemma fset_set0 {T : choiceType} : fset_set (set0 : set T) = fset0.
Lemma fset_setU {T : choiceType} (A B : set T) : finite_set A -> finite_set B ->
  fset_set (A `|` B) = (fset_set A `|` fset_set B)%fset.
Lemma fset_set_inj {T : choiceType} (A B : set T) :
  finite_set A -> finite_set B -> fset_set A = fset_set B -> A = B.
Lemma card_eq_fsetP {T : choiceType} {A : {fset T}} {n} :
  reflect (#|` A| = n) ([set` A] #= `I_n).
Lemma card_fset_set {T : choiceType} (A : set T) n : A #= `I_n -> #|`fset_set A| = n.
Lemma geq_card_fset_set {T : choiceType} (A : set T) n :
  A #<= `I_n -> (#|`fset_set A| <= n)%N.
Lemma leq_card_fset_set {T : choiceType} (A : set T) n :
  finite_set A -> A #>= `I_n -> (#|`fset_set A| >= n)%N.
Lemma fcard_eq {T T' : choiceType} (A : set T) (B : set T') :
    finite_set A -> finite_set B ->
  reflect (#|`fset_set A| = #|`fset_set B|) (A #= B).
Lemma infinite_set_fsetP {T : choiceType} (A : set T) :
  infinite_set A <->
   forall n, exists2 B : {fset T}, [set` B] `<=` A & (#|` B| >= n)%N.
Lemma finite_set_bij T (A : set T) n S : A != set0 ->
    A #= `I_n -> S `<=` A ->
  exists (f : {bij `I_n >-> A}) k, (k <= n)%N /\ `I_n `&` (f @^-1` S) = `I_k.
Lemma trivIset_sum_card (T : choiceType) (F : nat -> set T) n :
  (forall n, finite_set (F n)) -> trivIset [set: nat] F ->
  (\sum_(i < n) #|` fset_set (F i)| =
   #|` fset_set (\big[setU/set0]_(k < n) F k)|)%N.

(* countable = ℵ₀ ; « non dénombrable » = ~ countable. *)
Lemma countableP (T : countType) (A : set T) : countable A.
Lemma countable0 T : countable (@set0 T).
Lemma countable_fset (T : choiceType) (X : {fset T}) : countable [set` X].
Lemma countable_injP T (A : set T) :
  reflect (exists f : T -> nat, {in A &, injective f}) (countable A).
Lemma countable_bijP T (A : set T) : reflect (exists B : set nat, (A #= B)%card) (countable A).
Lemma sub_countable T U (A : set T) (B : set U) : A #<= B -> countable B -> countable A.
Lemma eq_countable T U (A : set T) (B : set U) : A #= B -> countable A = countable B.
Lemma finite_set_countable T (A : set T) : finite_set A -> countable A.
Lemma bigcup_countable {I T} (D : set I) (F : I -> set T) :
    countable D -> (forall i, D i -> countable (F i)) ->
  countable (\bigcup_(i in D) F i).
Lemma countableX T1 T2 (D1 : set T1) (D2 : set T2) :
  countable D1 -> countable D2 -> countable (D1 `*` D2).
Lemma countable_n_subset {T : Type} (D : set T) n :
  countable D -> countable [set A | A `<=` D /\ A #= `I_n].
Lemma countable_finite_subset {T : Type} (D : set T) :
  countable D -> countable [set A | A `<=` D /\ finite_set A ].
Lemma fset_subset_countable {T : pointedType} (D : set T) :
  countable D -> countable [set A : {fset T} | {subset A <= D}].
Lemma Pcountable {T : Type} : countable [set: T] -> {T' : countType | T = T' :> Type}.
Lemma choicePcountable {T : choiceType} : countable [set: T] ->
  {T' : countType | T = T' :> Type}.
Lemma infinite_nat : ~ finite_set [set: nat].
Lemma eq_card_nat T (A : set T) : countable A -> infinite_set A -> A #= [set: nat].
Lemma card_nat2 : [set: nat * nat] #= [set: nat].
Lemma card_rat : [set: rat] #= [set: nat].
Lemma infinite_rat : infinite_set [set: rat].

(* Fonctions à image finie (un coloriage d'un graphe infini par k couleurs). *)
Notation "{ 'fimfun' aT >-> T }" := (@FImFun.type aT T) : form_scope.
Definition fimfun : {pred aT -> rT} := mem [set f | finite_set (range f)].
Lemma fimfun_inP {aT rT} (f : {fimfun aT >-> rT}) (D : set aT) :
  finite_set (f @` D).
```

### `functions.v` — injections / surjections / bijections **relativisées à un ensemble**

Un morphisme entre graphes infinis n'est pas une `injective f` globale mais
une `{in A &, injective f}` : c'est précisément `set_inj A f`. Les trois
prédicats `set_fun` / `set_inj` / `set_surj` (et leur conjonction `set_bij`)
sont la forme à utiliser dans un énoncé ; les types empaquetés
`{fun A >-> B}`, `{injfun A >-> B}`, `{bij A >-> B}` sont la forme à utiliser
dans une preuve (ils portent l'inverse partiel). On passe de l'un à l'autre
par `Pinj` / `Pfun` / `Psurj` / `Pbij` (`move=> /Pbij[{}f ->]`) ;
`setTT_bijective` identifie `set_bij setT setT f` et `bijective f`, ce qui
permet de retomber sur un isomorphisme usuel. `pinv` fournit l'inverse
partiel d'une fonction injective sur `A`, à valeur arbitraire hors de l'image.

```coq
Definition set_fun := {homo f : x / A x >-> B x}.     (* A : set aT, B : set rT *)
Definition set_surj := B `<=` f @` A.
Definition set_inj := {in A &, injective f}.
Definition set_bij := [/\ set_fun, set_inj & set_surj].

HB.mixin Record isFun {aT rT} (A : set aT) (B : set rT) (f : aT -> rT) :=
  { funS : set_fun A B f }.
Notation "{ 'fun' A >-> B }" := (@Fun.type _ _ A B) : form_scope.
Notation "{ 'oinv' aT >-> rT }" := (@OInversible.type aT rT) : type_scope.
Notation "{ 'inj' A >-> rT }" := (@Inject.type _ rT A) : type_scope.
Notation "{ 'injfun' A >-> B }" := (@InjFun.type _ _ A B) : type_scope.
Notation "{ 'surj' A >-> B }" := (@Surject.type _ _ A B) : type_scope.
Notation "{ 'surjfun' A >-> B }" := (@SurjFun.type _ _ A B) : type_scope.
Notation "{ 'bij' A >-> B }" := (@Bij.type _ _ A B) : type_scope.
Notation "{ 'splitbij' A >-> B }" := (@SplitBij.type _ _ A B) : type_scope.
Definition funin (A : set aT) (f : aT -> rT) := f.
Notation "[ 'fun' f 'in' A ]" := (funin A f) : function_scope.
(* projections, via les notations à phantôme : 'funS_f, 'inj_f, 'surj_f, 'bij_f *)
Lemma surj {aT rT} {A : set aT} {B : set rT} {f : {surj A >-> B}} : set_surj A B f.
Lemma bij {aT rT} {A : set aT} {B : set rT} {f : {bij A >-> B}} : set_bij A B f.
Lemma injT {aT rT} {f : {inj [set: aT] >-> rT}} : injective f.
Lemma funK {aT rT : Type} {A : set aT} {s : {splitinj A >-> rT}} :
  {in A, cancel s s^-1}.
Lemma invK {aT rT} {A : set aT} {B : set rT} {f : {splitsurj A >-> B}} :
   {in B, cancel f^-1 f}.
Lemma image_eq {aT rT} {A : set aT} {B : set rT} (f : {surjfun A >-> B}) : f @` A = B.

(* Aller-retour entre la propriété et le type empaqueté. *)
Lemma Pinj : {i : {inj A >-> rT} | f = i}.             (* f : {in A &, injective f} *)
Lemma Psurj : {s : {surj A >-> B} | f = s}.
Lemma Pbij : {s : {bij A >-> B} | f = s}.
Lemma PbijTT : {s : {splitbij [set: aT] >-> [set: rT]} | f = s}. (* bijective f *)
Lemma injPfun : {i : {injfun A >-> B} | f = i :> (_ -> _)}.
Lemma surjPfun : {s : {surjfun A >-> B} | f = s :> (_ -> _)}.
Lemma setTT_bijective aT rT (f : aT -> rT) :
  set_bij [set: aT] [set: rT] f = bijective f.
Lemma bijTT {aT rT} {f : {bij [set: aT] >-> [set: rT]}} : bijective f.

(* Calcul sur set_bij. *)
Lemma set_bij_inj : {in A &, injective f}.
Lemma set_bij_homo : {homo f : x / A x >-> B x}.
Lemma set_bij_sub : f @` A `<=` B.
Lemma set_bij_surj : set_surj A B f.
Lemma inj_bij A f : {in A &, injective f} -> set_bij A (f @` A) f.
Lemma set_bij_comp T1 T2 T3 (A : set T1) (B : set T2) (C : set T3) f g :
  set_bij A B f -> set_bij B C g -> set_bij A C (g \o f).
Lemma bij_subl A B C D (f : {bij A >-> B}) : C `<=` A -> f @` C = D ->
  set_bij C D f.
Lemma bij_sub A B C D (f : {bij A >-> B}) : C `<=` A -> D `<=` B ->
  f @` C = D -> set_bij C D f.
Lemma surjE f A B : set_surj A B f = (B `<=` f @` A).
Lemma surj_image_eq B A f : f @` A `<=` B -> set_surj A B f -> f @` A = B.
Lemma surj_comp T1 T2 T3 (A : set T1) (B : set T2) (C : set T3) f g :
  set_surj A B f -> set_surj B C g -> set_surj A C (g \o f).
Lemma set_fun_image : set_fun A (f @` A) f.

(* Inverse partiel : 'pinv_ dflt A f, et pinv := 'pinv_(fun=> point). *)
Definition pinv_ f := ('split_dflt [fun f in A])^-1.
Notation "''pinv_' dflt" := (pinv_ dflt) : form_scope.
Notation pinv := 'pinv_(fun=> point).
Lemma pinvK f : {in f @` A, cancel (pinv f) f}.
Lemma pinvKV f : {in A &, injective f} -> {in A, cancel f (pinv f)}.
Lemma injpinv_surj f : {in A &, injective f} -> set_surj (f @` A) A (pinv f).
Lemma injpinv_image f : {in A &, injective f} -> pinv f @` (f @` A) = A.
Lemma injpinv_bij f : {in A &, injective f} -> set_bij (f @` A) A (pinv f).
Lemma surjpK B f : set_surj A B f -> {in B, cancel (pinv f) f}.
Lemma surjpinv_inj B f : set_surj A B f -> {in B &, injective (pinv f)}.
Lemma bijpinv_bij B f : set_bij A B f -> set_bij B A (pinv f).

(* Restrictions / recollements (utiles pour un morphisme défini par morceaux). *)
Definition patch (f : aT -> rT) u := if u \in A then f u else d u.
Notation restrict := (patch (fun=> point)).
Notation "f \_ D" := (restrict D f) : function_scope.
Lemma eq_restrictP (f g : U -> V) : {in A, f =1 g} <-> restrict f = restrict g.
Definition glue {T T'} {X Y : set T} {A B : set T'}
  & [disjoint X & Y] & [disjoint A & B] :=
  fun (f g : T -> T') (u : T) => if u \in X then f u else g u.
Definition sigL (f : U -> V) : A -> V := f \o set_val.   (* A -> V *)
Definition sigLR := sigR \o (@sigLfun U V A B).          (* A -> B *)
Lemma sigL_injP (f : U -> V) : injective (rl f) <-> {in A &, injective f}.
Lemma sigLRfun_bijP f : bijective (sigLR f) <-> set_bij A B f.
Definition set_val : A -> T := eqincl (set_mem_set A) \o val.
Definition to_setT {T} (x : T) : [set: T].
Definition incl (AB : A `<=` B) := @id T.
Definition mkfun f (fAB : isfun f) := f.  (* isfun f := {homo f : x / A x >-> B x} *)
```

### `set_interval.v`, `fsbigop.v`, `wochoice.v`, `classical_orders.v` — le strict nécessaire

`wochoice.v` est la brique « bon ordre / Zorn » **sans** `classical_sets`
(tout y est en `{pred T}` booléen) : c'est la bonne porte d'entrée pour
« tout graphe possède un couplage/ensemble indépendant maximal », et
`well_ordering_principle` donne un bon ordre sur un type de sommets
arbitraire (utile pour les preuves par récurrence transfinie sur un graphe
infini). `fsbigop.v` donne une somme `\sum_(i \in A)` sur un support fini
d'un ensemble *classique* (degré d'un sommet dans un graphe localement fini).
`set_interval.v` et `classical_orders.v` ne servent que pour les rangées
géométriques / ordres infinis ; on n'en retient que les conversions.

```coq
(* wochoice.v : bon ordre, chaînes, Zorn, Hausdorff — en {pred T}. *)
Definition nonempty {T: Type} (A : {pred T}) := exists x, x \in A.
Notation "{ 'in' <= S , P }" := (prop_within (mem S) (inPhantom P)).
Definition maximal z := forall x, R z x -> R x z.
Definition minimal z := forall x, R x z -> R z x.
Definition upper_bound A z := {in A, forall x, R x z}.
Definition lower_bound A z := {in A, forall x, R z x}.
Definition preorder := reflexive R /\ transitive R.
Definition partial_order := preorder /\ antisymmetric R.
Definition total_order := partial_order /\ total R.
Definition minimum_of A z := z \in A /\ lower_bound A z.
Definition maximum_of A z := z \in A /\ upper_bound A z.
Definition well_order := forall A, nonempty A -> exists! z, minimum_of A z.
Definition chain C := {in C &, total R}.
Definition wo_chain C := {in <= C, well_order}.
Lemma wo_chainW (T : eqType) R C : @wo_chain T R C -> chain R C.
Lemma antisymmetric_well_order :
    antisymmetric R -> (forall A, nonempty A -> exists z, minimum_of A z) ->
  well_order.
Lemma Zorn's_lemma (T : eqType) (R : rel T) (S : {pred T}) :
  {in S, reflexive R} -> {in S & &, transitive R} ->
  {in <= S, forall C, wo_chain R C -> exists2 z, z \in S & upper_bound R C z} ->
  {z : T | z \in S & {in S, maximal R z}}.
Theorem Hausdorff_maximal_principle T R (S C : {pred T}) :
  {in S, reflexive R} -> {in S & &, transitive R} -> chain R C -> {subset C <= S} ->
  {M : {pred T} |
    [/\ {subset C <= M}, {subset M <= S}
      & forall X, chain R X -> {subset M <= X} -> {subset X <= S} -> M = X]}.
Theorem well_ordering_principle (T : eqType) : {R : rel T | well_order R}.

(* fsbigop.v : \sum_(i \in A) F i, support fini dans un set classique. *)
Definition finite_support {I : choiceType} {T : Type} (idx : T) (D : set I)
    (F : I -> T) : seq I :=
  locked_with finite_index_key (fset_set (D `&` F @^-1` [set~ idx] : set I)).
Notation "\big [ op / idx ]_ ( i '\in' D ) F" :=
    (\big[op/idx]_(i <- finite_support idx D (fun i => F)) F) : big_scope.
Notation "\sum_ ( i '\in' A ) F" := (\big[+%R/0%R]_(i \in A) F) : ring_scope.
Lemma fsumr_lt0 (R : realDomainType) (I : choiceType) (P : set I) (F : I -> R) :
  \sum_(i \in P) F i < 0 -> exists2 i, P i & F i < 0.
Lemma in_finite_support (T : Type) (J : choiceType) (i : T) (P : set J)
    (F : J -> T) : finite_set (P `&` F @^-1` [set~ i]) ->
  finite_support i P F =i P `&` F @^-1` [set~ i].
Lemma fsbig_finite (R : Type) (idx : R) (op : Monoid.com_law idx) (T : choiceType)
    (D : set T) (F : T -> R) : finite_set D ->
  \big[op/idx]_(x \in D) F x = \big[op/idx]_(x <- fset_set D) F x.
Lemma reindex_fsbig {I J : choiceType} (h : I -> J) P Q
    (F : J -> R) : set_bij P Q h ->
  \big[op/idx]_(j \in Q) F j = \big[op/idx]_(i \in P) F (h i).
Lemma fsbig_image {I J : choiceType} P (h : I -> J) (F : J -> R) : set_inj P h ->
  \big[op/idx]_(j \in h @` P) F j = \big[op/idx]_(i \in P) F (h i).
(* + eq_fsbigl, eq_fsbigr, fsbig_mkcond, fsbigID, fsbigU, fsbigD1, fsbig_split,
     fsbig_set0, fsbig_set1, fsbig_seq, fsbig_ord, fsumr_ge0, pfsumr_eq0. *)

(* set_interval.v : conversion intervalle mathcomp <-> set classique. *)
Definition neitv i := [set` i] != set0.
Lemma set_itvP i j : [set` i] = [set` j] :> set _ <-> i =i j.
Lemma subset_itvP i j : {subset i <= j} <-> [set` i] `<=` [set` j].
Lemma set_itvoo x y : `]x, y[%classic = [set z | (x < z < y)%O].
Lemma set_itvcc x y : `[x, y]%classic = [set z | (x <= z <= y)%O].
Lemma set_itvNyy : `]-oo, +oo[%classic = @setT T.
Lemma set_itvcy x : `[x, +oo[%classic = [set z | (x <= z)%O].
(* + set_itvE (multirègle intervalle -> inégalités), set_itv_infty_set0. *)

(* classical_orders.v : ordre lexicographique sur un produit dénombrable
   (utile pour bien ordonner les suites de sommets / les rayons). *)
Definition big_lexi_order {I : Type} (T : I -> Type) : Type := forall i, T i.
Definition same_prefix n (t1 t2 : forall n, K n) :=
  forall m, (m < n)%O -> t1 m = t2 m.
Definition first_diff (t1 t2 : forall n, K n) : option nat :=
  xget None (Some @` [set n | same_prefix n t1 t2 /\ t1 n != t2 n]).
Definition big_lexi_le
    (R : forall n, K n -> K n -> bool) (t1 t2 : forall n, K n) :=
  if first_diff t1 t2 is Some n then R n (t1 n) (t2 n) else true.
Lemma first_diff_NoneP t1 t2 : t1 = t2 <-> first_diff t1 t2 = None.
Lemma big_lexi_le_total R : (forall n, total (R n)) -> total (big_lexi_le R).

(* mathcomp_extra.v : dépannages mathcomp récents (mise à jour de fonction). *)
Definition proj {I} {T : I -> Type} i (f : forall i, T i) := f i.
Definition dfwith i (x : T i) (j : I) : T j :=
  if (i =P j) is ReflectT ij then ecast j (T j) ij x else f j.
Lemma dfwithin i x : dfwith x i = x.
Lemma dfwithout i (x : T i) j : i != j -> dfwith x j = f j.
Lemma projK i (x : T i) : cancel (@dfwith i) (proj i).
Lemma card_fset_sum1 (T : choiceType) (A : {fset T}) : #|` A| = (\sum_(i <- A) 1)%N.
```

### Utilisation dans ce dépôt

- `digraph-theory/theories/foundations/prelude.v` est le **seul** fichier qui
  importe la bibliothèque (`From mathcomp Require Import boolp classical_sets.`,
  avec `Local Open Scope classical_set_scope`). Il ne s'en sert pour l'instant
  que comme *smoke checks* (`prelude_classical` via `pselect`, `prelude_set`
  via `A `<=` setT`) : la couche classique est ouverte « pour la suite »
  (décision D4 de `docs/DESIGN.md` : étendre le noyau fini combinatoire à des
  types de sommets arbitraires). Le contenu mathématique du fichier
  (`card_classes`, `card_classes_inj`) reste, lui, en `finType` / `{set T}`.
- `infinite-graph-theory/theories/foundations/igraph.v` est le carrier
  Prop-level des graphes infinis (`iGraph`, `iadj`, `ray`, `Komega`,
  `end_equiv`, `unfriendly`, `K4_free`…). Il **n'importe pas**
  `classical_sets`/`cardinality` et réimplémente à la main les notions
  correspondantes :
  - `countable_graph G := exists f : iV G -> nat, injective f`
    — c'est `countable [set: iV G]` (`countable_injP`) ;
  - `card_le A B P Q := exists f : {x | P x} -> {y | Q y}, injective f`
    — c'est `#<=` (`card_le` / `pcard_injP`) ;
  - `infinite_graph G := exists f : nat -> iV G, injective f`
    — c'est `infinite_set [set: iV G]` (`infiniteP`) ;
  - `finite_sub G P := exists n g, forall x, P x -> exists i : 'I_n, g i = x`
    — c'est `finite_set P` (`finite_set_leP`, `finite_setP`).
  Le choix Prop-level est délibéré (pas d'`eqType` sur `iV G`) mais
  `boolp.gen_eqMixin` / `{classic T}` lèveraient exactement cette contrainte.
- `meta/STATEMENT_IMPROVEMENTS.md`, section « Suspected unfaithful or proxy
  encodings », recense les énoncés dont le support infini est remplacé par un
  proxy fini : les rangées « groupe abélien » quantifiées sur `finGroupType`
  alors que l'énoncé source parle de groupes abéliens quelconques, et les
  rangées géométriques quantifiées sur `rcfType` en place de ℝ. Les premières
  se réécriraient avec `set T` + `#<=` / `countable` ; les secondes relèvent
  plutôt de `mathcomp-analysis` (`reals`), dont `classical_sets` est la base.
- Aucun autre fichier du dépôt n'utilise `functions`, `cardinality`,
  `fsbigop`, `set_interval`, `wochoice` ni `classical_orders` : les rangées
  infinies (D4, D4doa) passent toutes par les primitives maison d'`igraph.v`.
  Un `countable_graph` / `infinite_graph` factorisé dans `base/theories`
  (ou une version d'`igraph.v` construite sur `countable` et `#<=`) éviterait
  la divergence entre les deux vocabulaires.
