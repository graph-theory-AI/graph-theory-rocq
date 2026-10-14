(** Public-only clients of [Minor.foundations.prism_configurations].  They import only
    GTBase, the public containment vocabulary and the prism module.

    - The 3-prism itself is a prism configuration; a graph on fewer than six vertices is not.
    - The triangle restriction has teeth: [prism_split], the 3-prism whose triangle edge
      [(0,1)] is subdivided once (new vertex 6), IS a subdivision of [prism_base]
      ([prism_split_is_subdivision], an explicit spanning and exact model), but it is NOT a
      prism configuration ([prism_split_not_prism]): its only triangle is [{3,4,5}], while
      a prism configuration has two vertex-disjoint triangles. *)
From GTBase Require Import base.
From Minor.foundations Require Import containment prism_configurations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The 3-prism, and fewer than six vertices *)

Example prism_base_is_prism : prism_configuration prism_base.
Proof. exact: prism_configuration_base. Qed.

Example K5_not_prism : ~ prism_configuration 'K_5.
Proof. by move/prism_configuration_card; rewrite card_ord. Qed.

(** ** One triangle edge subdivided *)

Definition prism_split : sgraph :=
  el_graph 7 [:: (0,6); (6,1); (1,2); (0,2); (3,4); (4,5); (3,5); (0,3); (1,4); (2,5)].

(** Branch vertices: [i] goes to [i]; the subdivision vertex [6] sits on the edge [(0,1)]. *)
Definition split_branch (u : prism_base) : prism_split := widen_ord (isT : 6 <= 7) u.

Definition split_mid : prism_split := @Ordinal 7 6 isT.

Definition split_path (u v : prism_base) : seq prism_split :=
  if ((val u == 0) && (val v == 1)) || ((val u == 1) && (val v == 0)) then [:: split_mid]
  else [::].

Definition prism_v0 : prism_base := @Ordinal 6 0 isT.
Definition prism_v1 : prism_base := @Ordinal 6 1 isT.

Lemma split_branch_inj : injective split_branch.
Proof. by move=> u v /(congr1 val) e; apply/val_inj. Qed.

Lemma split_pathP (u v : prism_base) :
  u -- v -> sd_path (split_branch u) (split_branch v) (split_path u v).
Proof. by case: u => [[|[|[|[|[|[|//]]]]]] ?]; case: v => [[|[|[|[|[|[|//]]]]]] ?]. Qed.

Lemma split_pathC (u v : prism_base) : u -- v -> split_path v u = rev (split_path u v).
Proof. by case: u => [[|[|[|[|[|[|//]]]]]] ?]; case: v => [[|[|[|[|[|[|//]]]]]] ?]. Qed.

Lemma split_avoid (u v w : prism_base) (x : prism_split) :
  u -- v -> x \in split_path u v -> x != split_branch w.
Proof.
move=> _; rewrite /split_path; case: ifP => _; last by rewrite in_nil.
rewrite inE => /eqP ->; apply/eqP => /(congr1 val) /= e.
by have := ltn_ord w; rewrite -e.
Qed.

(** A nonempty subdivision path belongs to the model edge [{0,1}]. *)
Lemma split_path_pair (u v : prism_base) (x : prism_split) :
  x \in split_path u v -> [set u; v] = [set prism_v0; prism_v1].
Proof.
rewrite /split_path; case: ifP => [|_]; last by rewrite in_nil.
case/orP => /andP[/eqP a /eqP b] _.
- have -> : u = prism_v0 by apply/val_inj.
  by have -> : v = prism_v1 by apply/val_inj.
- have -> : u = prism_v1 by apply/val_inj.
  have -> : v = prism_v0 by apply/val_inj.
  exact: setUC.
Qed.

Lemma split_disj (u v u' v' : prism_base) (x : prism_split) :
  u -- v -> u' -- v' -> x \in split_path u v -> x \in split_path u' v' ->
  [set u; v] = [set u'; v'].
Proof. by move=> _ _ /split_path_pair -> /split_path_pair ->. Qed.

Definition split_model : subdiv_model prism_base prism_split :=
  @SubdivModel prism_base prism_split split_branch split_branch_inj split_path
    split_pathP split_pathC split_avoid split_disj.

(** Every vertex is used and every edge of [prism_split] is a model edge. *)
Lemma split_model_rep : subdiv_rep split_model.
Proof.
split=> [x|x y].
- have [x6|x6] := ltnP (val x) 6.
  + by left; exists (Ordinal x6); apply/val_inj.
  + right; exists prism_v0, prism_v1; split; first by [].
    have -> : x = split_mid.
      by apply/val_inj; apply/eqP; rewrite /= eqn_leq x6 andbT -ltnS ltn_ord.
    by rewrite /= /split_path /= inE.
- pose o (i : nat) (h : i < 6) : prism_base := Ordinal h.
  case: x => [[|[|[|[|[|[|[|//]]]]]]] hx]; case: y => [[|[|[|[|[|[|[|//]]]]]]] hy] // _;
  first [ by exists prism_v0, prism_v1; split
        | by exists (o 1 isT), (o 2 isT); split
        | by exists (o 0 isT), (o 2 isT); split
        | by exists (o 3 isT), (o 4 isT); split
        | by exists (o 4 isT), (o 5 isT); split
        | by exists (o 3 isT), (o 5 isT); split
        | by exists (o 0 isT), (o 3 isT); split
        | by exists (o 1 isT), (o 4 isT); split
        | by exists (o 2 isT), (o 5 isT); split ].
Qed.

Example prism_split_is_subdivision : is_subdivision_of prism_split prism_base.
Proof. by exists split_model; exact: split_model_rep. Qed.

(** Every vertex of a triangle of [prism_split] is one of [3], [4], [5]. *)
Lemma split_triangle (x y z : prism_split) :
  x -- y -> y -- z -> x -- z -> (3 <= val x) && (val x <= 5).
Proof.
by case: x => [[|[|[|[|[|[|[|//]]]]]]] ?]; case: y => [[|[|[|[|[|[|[|//]]]]]]] ?];
  case: z => [[|[|[|[|[|[|[|//]]]]]]] ?].
Qed.

Example prism_split_not_prism : ~ prism_configuration prism_split.
Proof.
case/prism_configuration_triangles => a [b [ha hb hab]].
have range (c : 'I_3 -> prism_split) :
    (forall i j : 'I_3, i != j -> c i -- c j) -> forall i, (3 <= val (c i)) && (val (c i) <= 5).
  move=> hc.
  have e (i j : nat) (hi : i < 3) (hj : j < 3) : i != j -> c (Ordinal hi) -- c (Ordinal hj).
    by move=> ij; apply: hc; exact: ij.
  case=> [[|[|[|//]]] hi].
  - exact: (split_triangle (e 0 1 hi isT isT) (e 1 2 isT isT isT) (e 0 2 hi isT isT)).
  - exact: (split_triangle (e 1 0 hi isT isT) (e 0 2 isT isT isT) (e 1 2 hi isT isT)).
  - exact: (split_triangle (e 2 0 hi isT isT) (e 0 1 isT isT isT) (e 2 1 hi isT isT)).

pose f (s : 'I_3 + 'I_3) : prism_split := match s with inl i => a i | inr j => b j end.
have frange (s : 'I_3 + 'I_3) : (3 <= val (f s)) && (val (f s) <= 5).
  by case: s => [i|j]; [exact: (range a ha i) | exact: (range b hb j)].
have ainj (c : 'I_3 -> prism_split) :
    (forall i j : 'I_3, i != j -> c i -- c j) -> injective c.
  move=> hc i j e; apply/eqP; apply: contraTT isT => ij.
  by have := hc i j ij; rewrite e sg_irrefl.
have finj : injective f.
  move=> [i|i] [j|j] /= e.
  - by rewrite (ainj _ ha i j e).
  - by move/eqP: (hab i j); rewrite e.
  - by move/eqP: (hab j i); rewrite e.
  - by rewrite (ainj _ hb i j e).
pose h (s : 'I_3 + 'I_3) : 'I_3 := inord (val (f s) - 3).
have hinj : injective h.
  move=> s t /(congr1 (@nat_of_ord 3)); rewrite /h !inordK; first last.
  - by case/andP: (frange s) => s3 s5; rewrite ltn_subLR // addnC.
  - by case/andP: (frange t) => t3 t5; rewrite ltn_subLR // addnC.
  move=> e; apply: finj; apply/val_inj.
  case/andP: (frange s) => s3 _; case/andP: (frange t) => t3 _.
  by rewrite -(subnK s3) -(subnK t3) e.
by have := leq_card h hinj; rewrite card_sum !card_ord.
Qed.
