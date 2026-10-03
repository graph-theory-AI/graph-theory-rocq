(** * Finite bipartitions and their representation adapters

    The supplied-side predicate is upstream [bipartition] on [diGraph].
    These adapters retain supplied versus existential witnesses, Boolean versus
    propositional crossings, exact part sizes, and arbitrary edge deletions.
    No interface requires nonempty parts, positive sizes, or symmetric arcs.
    Registry: meta/library_primitives/bipartition.json. *)
From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph connectivity.
From GTBase Require Import common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** An arbitrary finite relation admits a Boolean colouring.  This expression
    remains convertible to [GTBase.base.bipartite] on simple-graph adjacency;
    in particular its consumers do not require propositional extensionality. *)
Definition bipartite_relation (T : finType) (r : rel T) : Prop :=
  exists f : T -> bool, forall x y : T, r x y -> f x != f y.

(** Two supplied parts, with the Boolean crossing interface used by digraphs. *)
Definition bipartition_parts (G : diGraph) (A B : {set G}) : Prop :=
  [disjoint A & B] /\ A :|: B = [set: G] /\
  forall x y : G, x -- y ->
    ((x \in A) && (y \in B)) || ((x \in B) && (y \in A)).

(** Supplied equal-sized parts.  Size zero is intentionally allowed. *)
Definition balanced_bipartition (G : diGraph) (A B : {set G}) (n : nat) : Prop :=
  [disjoint A & B] /\ A :|: B = [set: G] /\ #|A| = n /\ #|B| = n /\
  forall x y : G, x -- y ->
    ((x \in A) && (y \in B)) || ((x \in B) && (y \in A)).

(** Existential parts of separately prescribed sizes, with Prop crossings. *)
Definition bipartition_sizes (G : diGraph) (a b : nat) : Prop :=
  exists A B : {set G},
    [disjoint A & B] /\ A :|: B = [set: G] /\ #|A| = a /\ #|B| = b /\
    forall x y : G, x -- y ->
      (x \in A /\ y \in B) \/ (x \in B /\ y \in A).

(** [S] may contain nonedges or sets whose cardinality is not two. *)
Definition bipartite_after_deletion (G : sgraph) (S : {set {set G}}) : Prop :=
  exists A : {set G}, @bipartition (del_edge_set G S) A.

Lemma bipartition_neq (G : diGraph) (A : {set G}) :
  bipartition A <-> forall x y : G, x -- y -> (x \in A) != (y \in A).
Proof.
split=> h x y xy; have := h x y xy;
by rewrite ?inE; case: (x \in A); case: (y \in A).
Qed.

Lemma bipartition_complement (G : diGraph) (A : {set G}) :
  bipartition A <-> bipartition (~: A).
Proof.
rewrite !bipartition_neq; split=> h x y xy;
have := h x y xy; rewrite !inE;
by case: (x \in A); case: (y \in A).
Qed.

Lemma disjoint_cover_complement (T : finType) (A B : {set T}) :
  [disjoint A & B] -> A :|: B = [set: T] -> B = ~: A.
Proof.
move=> /disjoint_setI0 hI hU; apply/setP=> x.
have h1 := congr1 (fun S : {set T} => x \in S) hI.
have h2 := congr1 (fun S : {set T} => x \in S) hU.
move: h1 h2; rewrite !inE.
by case: (x \in A); case: (x \in B).
Qed.

Lemma bipartition_partsP (G : diGraph) (A B : {set G}) :
  bipartition_parts A B <->
  [disjoint A & B] /\ A :|: B = [set: G] /\ bipartition A.
Proof.
split; move=> [d [u h]]; split=> //; split=> //.
- apply/bipartition_neq=> x y xy.
  have Bc := disjoint_cover_complement d u.
  have := h x y xy; rewrite Bc !inE.
  by case: (x \in A); case: (y \in A).
- move=> x y xy; have /bipartition_neq h' := h.
  have Bc := disjoint_cover_complement d u.
  have := h' x y xy; rewrite Bc !inE.
  by case: (x \in A); case: (y \in A).
Qed.

Lemma bipartition_parts_swap (G : diGraph) (A B : {set G}) :
  bipartition_parts A B <-> bipartition_parts B A.
Proof.
have sw : forall A B : {set G}, bipartition_parts A B -> bipartition_parts B A.
  move=> X Y [d [u h]]; split; first by rewrite disjoint_sym.
  split; first by rewrite setUC.
  move=> x y xy; by rewrite orbC; exact: h.
by split; apply: sw.
Qed.

Lemma balanced_bipartitionP (G : diGraph) (A B : {set G}) (n : nat) :
  balanced_bipartition A B n <->
  bipartition_parts A B /\ #|A| = n /\ #|B| = n.
Proof.
split.
- by move=> [d [u [a [b h]]]]; split; [split=> //; split | split].
- by move=> [[d [u h]] [a b]]; split=> //; split=> //; split=> //; split.
Qed.

Lemma bipartition_sizesP (G : diGraph) (a b : nat) :
  bipartition_sizes G a b <->
  exists A B : {set G}, bipartition_parts A B /\ #|A| = a /\ #|B| = b.
Proof.
split.
- move=> [A [B [d [u [aA [bB h]]]]]]; exists A, B; split; last by split.
  split=> //; split=> //; move=> x y xy; apply/orP.
  by case: (h x y xy)=> [[xA yB]|[xB yA]]; [left|right]; apply/andP.
- move=> [A [B [[d [u h]] [aA bB]]]]; exists A, B.
  split=> //; split=> //; split=> //; split=> //; move=> x y xy.
  by case/orP: (h x y xy)=> /andP h'; [left|right].
Qed.

Lemma bipartite_relationP (T : finType) (r : rel T) :
  bipartite_relation r <-> exists A : {set T}, @bipartition (RelType r) A.
Proof.
split.
- move=> [f h]; exists [set x | f x]; apply/bipartition_neq=> x y xy.
  by rewrite !inE; exact: h.
- move=> [A /bipartition_neq h]; exists (fun x => x \in A); exact: h.
Qed.

Lemma bipartite_relation_sub (T : finType) (r s : rel T) :
  subrel r s -> bipartite_relation s -> bipartite_relation r.
Proof. by move=> rs [f h]; exists f=> x y xy; apply: h; exact: rs. Qed.

Lemma bipartite_relation0 (T : finType) :
  bipartite_relation (fun _ _ : T => false).
Proof. by exists (fun _ => false). Qed.

Lemma bipartite_relation_loop (T : finType) (r : rel T) (x : T) :
  r x x -> ~ bipartite_relation r.
Proof. by move=> xx [f h]; have := h x x xx; rewrite eqxx. Qed.

Lemma bipartite_after_deletionP (G : sgraph) (S : {set {set G}}) :
  bipartite_after_deletion S <->
  exists A : {set G}, forall x y : G,
    x -- y -> [set x; y] \notin S -> (x \in A) != (y \in A).
Proof.
split; move=> [A h]; exists A.
- move/bipartition_neq: h=> h x y xy xyS; apply: h.
  by rewrite del_edge_setE xy xyS.
- apply/bipartition_neq=> x y; rewrite del_edge_setE => /andP[xy xyS].
  exact: h xy xyS.
Qed.

Lemma bipartite_after_deletion_full (G : sgraph) :
  bipartite_after_deletion E(G).
Proof.
apply/bipartite_after_deletionP; exists set0=> x y xy.
by rewrite in_edges xy.
Qed.

Lemma bipartite_after_deletion_nonedges (G : sgraph) (S : {set {set G}}) :
  bipartite_after_deletion S <-> bipartite_after_deletion (S :&: E(G)).
Proof.
rewrite !bipartite_after_deletionP; split; move=> [A h]; exists A=> x y xy xyS.
- apply: (h x y xy); move: xyS; by rewrite in_setI in_edges xy andbT.
- apply: (h x y xy); by rewrite in_setI in_edges xy andbT.
Qed.
