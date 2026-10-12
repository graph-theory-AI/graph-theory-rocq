(** Frozen copy and exact-count decomposition contracts at 423936c66e0df86dff050496e86421193ebb1bcd.
    X212's copy image ranges over adjacent pairs of the pattern; a copy also preserves adjacency; a
    decomposition is a supplied list whose members are copies and which counts every 2-element vertex set
    exactly as often as it is an edge of the host, so a repeated nonempty part is excluded while repeated
    empty parts remain allowed. The whole Barat-Thomassen row keeps its nonempty-tree guard, its existential
    k and its divisibility hypothesis. Its texts are unchanged since their creation (d8db810) and depend on
    no earlier migrated helper, so these frozen copies are also its deepest Originals. *)
From GTBase Require Import base common.
From GTBase Require edge_copies.
From Cycle.conjectures Require Import X212.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x212_copy_edges (G T : sgraph) (f : T -> G) : {set {set G}} :=
  [set e : {set G} |
     [exists p : T * T, (p.1 -- p.2) && (e == [set f p.1; f p.2])]].

Definition x212_copy_of (G T : sgraph) (A : {set {set G}}) : Prop :=
  exists f : T -> G,
    [/\ injective f,
        (forall x y : T, x -- y -> f x -- f y)
      & A = Legacy.x212_copy_edges f].

Definition x212_decomposition_into_copies (G T : sgraph)
    (D : seq {set {set G}}) : Prop :=
  (forall A, A \in D -> Legacy.x212_copy_of T A) /\
  (forall e : {set G},
     count (fun A : {set {set G}} => e \in A) D = ((e \in E(G)) : nat)).

End Legacy.

Module X212Legacy.

Definition barat_thomassen_tree_decomposition_statement : Prop :=
  forall T : sgraph,
    0 < #|T| -> is_tree [set: T] ->
    exists k : nat,
      forall G : sgraph,
        k_edge_connected G k ->
        #|E(T)| %| #|E(G)| ->
        exists D : seq {set {set G}}, Legacy.x212_decomposition_into_copies T D.

End X212Legacy.

(** ** Certificates (kernel conversions) *)

Lemma x212_copy_edges_compat (G T : sgraph) (f : T -> G) :
  Legacy.x212_copy_edges f = x212_copy_edges f.
Proof. by []. Qed.

Lemma x212_copy_of_compat (G T : sgraph) (A : {set {set G}}) :
  Legacy.x212_copy_of T A <-> x212_copy_of T A.
Proof. exact: iff_refl. Qed.

Lemma x212_decomposition_into_copies_compat (G T : sgraph) (D : seq {set {set G}}) :
  Legacy.x212_decomposition_into_copies T D <-> x212_decomposition_into_copies T D.
Proof. exact: iff_refl. Qed.

Lemma barat_thomassen_tree_decomposition_statement_compat :
  X212Legacy.barat_thomassen_tree_decomposition_statement <-> barat_thomassen_tree_decomposition_statement.
Proof. exact: iff_refl. Qed.

Print Assumptions x212_copy_edges_compat.
Print Assumptions x212_copy_of_compat.
Print Assumptions x212_decomposition_into_copies_compat.
Print Assumptions barat_thomassen_tree_decomposition_statement_compat.
