(** Downstream use of longest directed cycles ([Digraph.foundations.longest_cycles.longest_dicycle]),
    without conjecture imports.  Each example uses public API lemmas only. *)
From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph dipath longest_cycles.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section AnyDigraph.
Variable D : diGraphType.
Implicit Types (c d : seq D) (x : D).

(** The empty sequence is never longest; a singleton is a directed cycle exactly with a loop. *)
Example empty_and_singleton x : ~ longest_dicycle ([::] : seq D) /\ dicycle [:: x] = (x --> x).
Proof. by split; [exact: longest_dicycle_nil | exact: dicycle_seq1]. Qed.

(** A longest directed cycle is duplicate-free, at most [#|D|] long, and bounds every directed cycle. *)
Example projections c d :
  longest_dicycle c -> [/\ uniq c, size c <= #|D| & (dicycle d -> size d <= size c)].
Proof.
move=> lc; split; [exact: longest_dicycle_uniq lc | exact: longest_dicycle_card lc |
  exact: longest_dicycle_max lc].
Qed.

(** A strictly longer directed cycle rules a cycle out; a Hamiltonian directed cycle is longest. *)
Example shorter_and_hamiltonian c d :
  (dicycle d -> size c < size d -> ~ longest_dicycle c) /\
  (dicycle c -> size c = #|D| -> longest_dicycle c).
Proof. by split; [exact: longest_dicycle_shorter | exact: longest_dicycle_hamiltonian]. Qed.

(** Ties, rotation, and existence exactly with an actual directed cycle. *)
Example ties_rotation_existence n c d :
  [/\ longest_dicycle c -> dicycle d -> size d = size c -> longest_dicycle d,
      longest_dicycle (rot n c) <-> longest_dicycle c
    & (exists e : seq D, longest_dicycle e) <-> (exists e : seq D, dicycle e)].
Proof.
by split; [exact: longest_dicycle_tie | exact: longest_dicycle_rot | exact: longest_dicycle_existsP].
Qed.

(** Reversal: a longest cycle of the converse digraph; of [D] itself when its arcs are symmetric. *)
Example reversal c :
  (@longest_dicycle (converse D) (rev c) <-> longest_dicycle c) /\
  ((forall x y : D, (x --> y) = (y --> x)) -> longest_dicycle (rev c) <-> longest_dicycle c).
Proof. by split; [exact: longest_dicycle_rev_converse | exact: longest_dicycle_rev]. Qed.

End AnyDigraph.

(** Concrete corners. *)

(** The empty digraph has no longest directed cycle (no default witness). *)
Definition empty_dg : Type := 'I_0.
HB.instance Definition _ := Finite.on empty_dg.
HB.instance Definition _ := HasArc.Build empty_dg (fun _ _ : 'I_0 => false).

Example empty_digraph (c : seq empty_dg) : ~ longest_dicycle c.
Proof.
move=> lc; move: (longest_dicycle_size lc) (longest_dicycle_card lc); rewrite card_ord.
by case: (size c).
Qed.

(** An arcless singleton has none either; a singleton with a loop is longest. *)
Example singletons : (forall c : seq arcless1, ~ longest_dicycle c) /\ longest_dicycle ([:: ord0] : seq loop1).
Proof. by split; [exact: longest_dicycle_ground_arcless | exact: longest_dicycle_ground_loop]. Qed.

(** A digon is longest with two vertices, and a valid but shorter cycle with three. *)
Example digons :
  longest_dicycle ([:: ord0; ord_max] : seq kd2) /\
  (dicycle ([:: ord0; ord_max] : seq kd3) /\ ~ longest_dicycle ([:: ord0; ord_max] : seq kd3)).
Proof. by split; [exact: longest_dicycle_ground_digon | exact: longest_dicycle_ground_shorter]. Qed.

(** A directed triangle is longest; its reversal is a longest cycle of the converse only. *)
Example triangle :
  let c : seq dtri := [:: ord0; Ordinal (isT : 1 < 3); ord_max] in
  [/\ longest_dicycle c, ~~ dicycle (rev c) & @longest_dicycle (converse dtri) (rev c)].
Proof. exact: longest_dicycle_ground_triangle. Qed.

Print Assumptions reversal.
Print Assumptions empty_digraph.
Print Assumptions triangle.
