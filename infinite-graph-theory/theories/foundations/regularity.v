(** * Infinite.foundations.regularity -- local neighbourhood regularity of an infinite graph

    Library migration D9 (registry entry [regularity], class [infinite-neighbour-enumeration]; report
    meta/migration_reports/regularity.md; record meta/LIBRARY_MIGRATION_D9.md; public client
    theories/examples/regular_igraphs.v).

    [iregular r G]: every vertex [x] of the Prop-level graph [G : iGraph] (arbitrary vertex [Type],
    Prop adjacency [iadj]) has an injective enumeration [e : 'I_r -> iV G] of exactly its neighbours:
    [iadj x w] holds iff [w] is some [e i].  The enumerator is local to each vertex and existential (no
    global selection, choice or decidability), [r] comes before [G], and there is no other guard: an
    empty carrier is regular at every [r], and [r = 0] means that no two vertices are adjacent.  Each
    neighbourhood is then [finite_sub], covered by the same enumerator ([iregular_finite_sub]).  The
    finite supplied-family [Hypergraph.foundations.hypergraph_regularity.hg_regular] and the simple-graph
    [GTBase.base.regular] are different interfaces.

    Axiom-free: no Axiom/Parameter/Admitted. *)
From mathcomp Require Import all_boot.
From Infinite Require Import foundations.igraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition iregular (r : nat) (G : iGraph) : Prop :=
  forall x : iV G, exists e : 'I_r -> iV G,
    injective e /\ (forall w, iadj x w <-> exists i, e i = w).

Section Regularity.
Variable G : iGraph.

(** Every neighbourhood is finite, covered by the same supplied enumerator ([n = r], no choice). *)
Lemma iregular_finite_sub r : iregular r G -> forall x : iV G, finite_sub (fun w => iadj x w).
Proof. by move=> rG x; have [e [_ cov]] := rG x; exists r, e => w /cov. Qed.

(** An empty carrier is regular at every degree. *)
Lemma iregular_void r : (iV G -> False) -> iregular r G.
Proof. by move=> G0 x; case: (G0 x). Qed.

(** Degree 0 means that no two vertices are adjacent. *)
Lemma iregular0 : iregular 0 G <-> forall x y : iV G, ~ iadj x y.
Proof.
split=> [r0 x y xy|nadj x].
  by have [e [_ cov]] := r0 x; have [[m lt0] _] := (cov y).1 xy; rewrite ltn0 in lt0.
have e : 'I_0 -> iV G by case=> m; rewrite ltn0.
exists e; split; first by move=> -[m lt0]; exfalso; move: lt0; rewrite ltn0.
move=> w; split=> [xw|[[m lt0] _]]; first by case: (nadj x w xw).
by rewrite ltn0 in lt0.
Qed.

(** A vertex without neighbours rules out every positive degree. *)
Lemma iregular_isolated r (x : iV G) : 0 < r -> (forall w, ~ iadj x w) -> ~ iregular r G.
Proof.
move=> r0 nx rG; have [e [_ cov]] := rG x.
by apply: (nx (e (Ordinal r0))); apply/cov; exists (Ordinal r0).
Qed.

End Regularity.
