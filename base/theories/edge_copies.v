(** Images of simple-graph edges and two list-decomposition conventions.
    An injective edge image need not lie in the host graph. An embedded copy
    also preserves adjacency. Equal overlapping parts may repeat; exact-count
    decompositions count repeated nonempty parts separately. No tree, nonempty
    pattern or nonempty-part restriction belongs in these definitions. *)
From GTBase Require Import base common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition edge_image (G T : sgraph) (f : T -> G) : {set {set G}} :=
  [set e : {set G} |
     [exists p : T * T, (p.1 -- p.2) && (e == [set f p.1; f p.2])]].

Definition injective_edge_image (G T : sgraph) (F : {set {set G}}) : Prop :=
  exists f : T -> G, injective f /\ F = edge_image f.

Definition embedded_edge_copy (G T : sgraph) (A : {set {set G}}) : Prop :=
  exists f : T -> G,
    [/\ injective f,
        (forall x y : T, x -- y -> f x -- f y)
      & A = edge_image f].

Definition edge_decomposition_by_equal_parts (G T : sgraph) : Prop :=
  exists parts : seq {set {set G}},
    (forall F : {set {set G}}, F \in parts -> @injective_edge_image G T F) /\
    (forall F : {set {set G}}, F \in parts -> F \subset E(G)) /\
    (forall e : {set G}, e \in E(G) ->
      exists F : {set {set G}}, F \in parts /\ e \in F) /\
    forall (F1 F2 : {set {set G}}) (e : {set G}),
      F1 \in parts -> F2 \in parts -> e \in F1 -> e \in F2 -> F1 = F2.

Definition edge_decomposition_exact (G T : sgraph) (D : seq {set {set G}}) : Prop :=
  (forall A, A \in D -> embedded_edge_copy T A) /\
  (forall e : {set G},
     count (fun A : {set {set G}} => e \in A) D = ((e \in E(G)) : nat)).

Lemma edge_imageE (G T : sgraph) (f : T -> G) (e : {set G}) :
  (e \in edge_image f) =
  [exists p : T * T, (p.1 -- p.2) && (e == [set f p.1; f p.2])].
Proof. by rewrite /edge_image inE. Qed.

Lemma edge_image_nested (G T : sgraph) (f : T -> G) :
  edge_image f = [set e : {set G} |
    [exists x : T, [exists y : T, (x -- y) && (e == [set f x; f y])]]].
Proof.
apply/setP => e; rewrite edge_imageE inE; apply/existsP/existsP.
- by case=> [[x y]] /= h; exists x; apply/existsP; exists y.
- by case=> x /existsP [y] h; exists (x, y).
Qed.

(** The copy/image conversion for the nested-quantifier form of an injective image. *)
Lemma injective_edge_image_nested (G T : sgraph) (F : {set {set G}}) :
  injective_edge_image T F <->
  exists f : T -> G,
    injective f /\
    F = [set e : {set G} |
          [exists x : T, [exists y : T, (x -- y) && (e == [set f x; f y])]]].
Proof. by split=> -[f [inj eF]]; exists f; split=> //; rewrite eF edge_image_nested. Qed.

Lemma edge_image_id (G : sgraph) : edge_image (fun x : G => x) = E(G).
Proof.
apply/setP => e; rewrite edge_imageE; apply/existsP/edgesP.
- case=> [[x y]] /= /andP [xy /eqP ->].
  by exists x, y.
- case=> x [y [-> xy]]; exists (x, y).
  by rewrite xy eqxx.
Qed.

Lemma edge_image_sub (G T : sgraph) (f : T -> G) :
  (forall x y : T, x -- y -> f x -- f y) -> edge_image f \subset E(G).
Proof.
move=> hom; apply/subsetP => e; rewrite edge_imageE => /existsP [[x y]] /=.
by case/andP => xy /eqP ->; rewrite in_edges (hom x y xy).
Qed.

Lemma embedded_edge_copy_sub (G T : sgraph) (A : {set {set G}}) :
  embedded_edge_copy T A -> A \subset E(G).
Proof. by case=> f [_ hom ->]; exact: edge_image_sub hom. Qed.

Lemma injective_edge_image_contained (G T : sgraph) (A : {set {set G}}) :
  (injective_edge_image T A /\ A \subset E(G)) <-> embedded_edge_copy T A.
Proof.
split.
- case=> [[f [inj eA]] sub]; rewrite eA in sub *.
  exists f; split=> // x y xy.
  have ep : [set f x; f y] \in edge_image f.
    rewrite edge_imageE; apply/existsP; exists (x, y).
    by rewrite xy eqxx.
  by have := subsetP sub _ ep; rewrite in_edges.
- case=> f [inj hom ->]; split; last exact: edge_image_sub hom.
  by exists f.
Qed.

Lemma embedded_edge_copy_self (G : sgraph) : embedded_edge_copy G E(G).
Proof.
exists (fun x : G => x); split=> //.
by rewrite edge_image_id.
Qed.

(** Removing repeated equal parts preserves all coverage and copy witnesses. *)
Lemma edge_decomposition_equal_parts_exact (G T : sgraph) :
  edge_decomposition_by_equal_parts G T ->
  exists D : seq {set {set G}}, edge_decomposition_exact T D.
Proof.
case=> parts [Hcopy [Hsub [Hcov Hdis]]].
exists (undup parts); split.
- move=> A; rewrite mem_undup => Ap.
  exact: (proj1 (injective_edge_image_contained T A)) (conj (Hcopy A Ap) (Hsub A Ap)).
- move=> e; case: (boolP (e \in E(G))) => eE /=.
  + have [F [Fp eF]] := Hcov e eE.
    rewrite (@eq_in_count _ _ (pred1 F)) ?count_uniq_mem ?undup_uniq ?mem_undup ?Fp //.
    move=> A; rewrite mem_undup => Ap /=.
    apply/idP/eqP => [eA|->//]; exact: Hdis Ap Fp eA eF.
  + apply/eqP; rewrite -leqn0 leqNgt -has_count; apply/negP => /hasP [A].
    rewrite mem_undup => Ap eA.
    by move: eE; rewrite (subsetP (Hsub A Ap) e eA).
Qed.

Lemma edge_decomposition_exact_nil (G T : sgraph) :
  E(G) = set0 -> @edge_decomposition_exact G T [::].
Proof.
move=> E0; split=> // e.
by rewrite E0 inE.
Qed.

Lemma edge_decomposition_equal_parts_nil (G T : sgraph) :
  E(G) = set0 -> edge_decomposition_by_equal_parts G T.
Proof.
move=> E0; exists [::]; split=> //; split=> //; split=> //.
by move=> e; rewrite E0 inE.
Qed.

Lemma edge_decomposition_exact_self (G : sgraph) :
  edge_decomposition_exact G [:: E(G)].
Proof.
split.
- by move=> A; rewrite inE => /eqP ->; exact: embedded_edge_copy_self.
- by move=> e; rewrite /= addn0.
Qed.

Lemma edge_decomposition_exact_double_not (G : sgraph) (e : {set G}) :
  e \in E(G) -> ~ edge_decomposition_exact G [:: E(G); E(G)].
Proof. by move=> eE [_ cnt]; have := cnt e; rewrite /= eE. Qed.

Lemma tree_has_edge (T : sgraph) : 1 < #|T| -> is_tree [set: T] -> 0 < #|E(T)|.
Proof.
move=> T1 [_ con].
have [a [b [_ _ ab]]] := card_gt1P T1.
have [u [v uv]] : exists u v : T, u -- v.
  have := connectedTE con a b; case/connectP => p pth la.
  case: p pth la => [|z p] /= ; first by move=> _ e; rewrite e eqxx in ab.
  by case/andP => az _ _; exists a, z.
by apply/card_gt0P; exists [set u; v]; rewrite in_edges.
Qed.
