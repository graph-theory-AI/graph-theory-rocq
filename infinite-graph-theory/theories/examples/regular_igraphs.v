(** Public-only client of [Infinite.foundations.regularity] ([iregular r G]: every vertex of the
    Prop-level graph [G] has an injective [r]-indexed enumeration of exactly its neighbours).  No
    conjecture module is imported.  Covered: the empty graph is regular at every [r]; [r = 0] exactly
    when no two vertices are adjacent; an inhabited edgeless graph rejects every positive [r]; the
    two-vertex single-edge graph has an ['I_1] enumeration; and each neighbourhood is [finite_sub],
    covered by the same supplied enumerator, without choice. *)
From mathcomp Require Import all_boot.
From Infinite Require Import foundations.igraph foundations.regularity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Three small Prop-level graphs *)

Definition void_graph : iGraph :=
  @Build_iGraph False (fun _ _ => False) (fun _ _ h => h) (fun _ h => h).

Definition point_graph : iGraph :=
  @Build_iGraph unit (fun _ _ => False) (fun _ _ h => h) (fun _ h => h).

Definition edge_graph : iGraph :=
  @Build_iGraph bool (fun x y => x <> y) (fun x y h e => h (esym e)) (fun x h => h erefl).

(** ** The empty graph: every degree *)

Example void_regular (r : nat) : iregular r void_graph.
Proof. by apply: iregular_void => -[]. Qed.

(** ** Degree 0 is edgelessness *)

Example regular0_iff (G : iGraph) : iregular 0 G <-> forall x y : iV G, ~ iadj x y.
Proof. exact: iregular0. Qed.

Example point_regular0 : iregular 0 point_graph.
Proof. by apply/iregular0 => x y []. Qed.

(** An inhabited edgeless graph rejects every positive degree. *)
Example point_not_regular (r : nat) : 0 < r -> ~ iregular r point_graph.
Proof. by move=> r0; apply: (@iregular_isolated point_graph _ tt r0) => w []. Qed.

(** ** The single edge: an ['I_1] enumeration of each neighbourhood *)

Example edge_regular1 : iregular 1 edge_graph.
Proof.
move=> x; exists (fun _ : 'I_1 => ~~ x); split; first by move=> i j _; rewrite (ord1 i) (ord1 j).
move=> w; split=> [xw|[_ <-]]; last by case: x.
by exists ord0; move: xw; case: x; case: w.
Qed.

(** ** Local finiteness from the same enumerator *)

Example regular_neighbourhoods_finite (r : nat) (G : iGraph) :
  iregular r G -> forall x : iV G, finite_sub (fun w => iadj x w).
Proof. exact: iregular_finite_sub. Qed.

Example edge_neighbourhoods_finite (x : iV edge_graph) : finite_sub (fun w => @iadj edge_graph x w).
Proof. exact: iregular_finite_sub edge_regular1 x. Qed.

Print Assumptions point_not_regular.
Print Assumptions edge_regular1.
Print Assumptions edge_neighbourhoods_finite.
