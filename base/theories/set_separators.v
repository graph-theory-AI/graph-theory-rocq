(** * GTBase.set_separators — set-to-set vertex separators: upstream [separator] and its sequence view

    Library migration B26, family [set-separator] (meta/library_primitives/set-separator.json).  The
    canonical contract is upstream [GraphTheory.core.connectivity.separator G X Y A]: every packaged path
    from a vertex of [X] to a vertex of [Y] meets [A].  It is the corpus' "[A] separates [X] from [Y]"
    (GTMisc X39 / X40, Packing X26).  Nothing restricts [X], [Y] or [A]; the separator may contain
    endpoints; one-vertex paths count, so every vertex of [X :&: Y] lies in [A] ([separator_cap]); empty
    endpoint sets are separated by anything.  [seq_separatorP] is the sequence view the corpus states:
    no simple set-to-set path ([seq_set_path], GTBase.walks_paths) has a vertex list ([seq_vertices])
    disjoint from [A].  The equivalence is unconditional; it reduces arbitrary packaged paths to
    irredundant ones through upstream [separatorI].  Distinct and untouched: upstream
    [separates x y U], which in addition requires both endpoints outside [U] (see
    [separator_not_separates]), global vertex cutsets, multigraph edge separators and directed cuts.
    Not re-exported by GTBase.base; no conjecture module is imported; no new predicate is introduced. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph connectivity.
From GTBase Require Import base walks_paths.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SetSeparators.
Variable G : sgraph.
Implicit Types (X Y A B : {set G}).

(** The sequence view: no simple [X]-[Y] path avoids [A]. *)
Lemma seq_separatorP X Y A :
  (forall p : seq G, seq_set_path X Y p -> [disjoint seq_vertices p & A] -> False) <->
  separator G X Y A.
Proof.
split=> [h | sep].
- apply: separatorI => a b p Ip aX bY.
  case: (pickP [pred z | (z \in p) && (z \in A)]) => [s /andP[sp sA] | none]; first by exists s.
  exfalso; apply: (h (nodes p)); first exact: seq_set_path_nodes.
  rewrite seq_vertices_nodes; apply/disjointP => z; rewrite inE => zp.
  by move: (none z); rewrite /= zp /= => ->.
- case=> [|x q] //= [xX [lY [_ pth]]] disj.
  have [s sA sp] := sep x (last x q) (Path_of_path pth) xX lY.
  have sq : s \in x :: q by move: sp; rewrite mem_path nodesE.
  move/disjointP: disj => H; have := H s; rewrite in_seq_vertices sq => /(_ isT).
  by move=> /(_ sA).
Qed.

(** Empty endpoint sets are separated by anything; the whole carrier separates anything. *)
Lemma separator_set0l Y A : separator G set0 Y A.
Proof. by move=> a b p; rewrite inE. Qed.

Lemma separator_set0r X A : separator G X set0 A.
Proof. by move=> a b p _; rewrite inE. Qed.

Lemma separator_setT X Y : separator G X Y [set: G].
Proof. by move=> a b p _ _; exists a; rewrite ?inE ?path_begin. Qed.

(** Endpoint hits are allowed: an endpoint set separates itself from anything. *)
Lemma separator_endpointL X Y : separator G X Y X.
Proof. by move=> a b p aX _; exists a; rewrite ?path_begin. Qed.

Lemma separator_endpointR X Y : separator G X Y Y.
Proof. by move=> a b p _ bY; exists b; rewrite ?path_end. Qed.

(** One-vertex paths count: a common vertex of the endpoint sets must be in the separator. *)
Lemma separator_seq1 x A : separator G [set x] [set x] A <-> x \in A.
Proof.
split=> [sep | xA]; first by move/subsetP: (@separator_cap G _ _ _ sep); apply; rewrite !inE eqxx.
by move=> a b p; rewrite !inE => /eqP ea _; exists a; [rewrite ea | exact: path_begin].
Qed.

Lemma separator_mono X Y A B : A \subset B -> separator G X Y A -> separator G X Y B.
Proof.
move=> /subsetP AB sep a b p aX bY; have [s sA sp] := sep a b p aX bY.
by exists s => //; exact: AB.
Qed.

(** Undirected adjacency: reversing paths exchanges the endpoint sets. *)
Lemma separator_sym X Y A : separator G X Y A -> separator G Y X A.
Proof.
move=> sep a b p aY bX; have [s sA sp] := sep b a (prev p) bX aY.
by exists s; rewrite // -mem_prev.
Qed.

(** Upstream [separates] is a different contract: it forbids the endpoints in the separator. *)
Lemma separator_not_separates (x y : G) : separator G [set x] [set y] [set x] /\ ~ separates x y [set x].
Proof. by split; [exact: separator_endpointL | case; rewrite inE eqxx]. Qed.

End SetSeparators.
