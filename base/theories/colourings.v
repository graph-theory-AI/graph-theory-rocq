(** * Supplied vertex colourings over finite palettes

    A colour map is proper when its inhabited fibres form an upstream
    [coloring] of all vertices.  The palette and the map remain supplied data:
    unused labels are allowed, and no quotient by palette permutations is taken.
    Empty graphs and empty palettes require no additional convention or guard.
    This focused module deliberately has no conjecture imports or base reexport.
    Registry: meta/library_primitives/proper-colouring.json. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph dom coloring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition proper_colouring (G : sgraph) (C : finType) (col : G -> C) : bool :=
  coloring (preim_partition col [set: G]) [set: G].

Lemma proper_colouringP (G : sgraph) (C : finType) (col : G -> C) :
  reflect (forall x y : G, x -- y -> col x != col y) (proper_colouring col).
Proof.
apply: (iffP andP).
- move=> [_ /forall_inP hs] x y xy; apply/negP=> /eqP hxy.
  have hx : [set z : G | col x == col z] \in preim_partition col [set: G].
    apply/imsetP; exists x; first by rewrite inE.
    by apply/setP=> z; rewrite !inE.
  have /stableP st := hs _ hx.
  have xx : x \in [set z : G | col x == col z] by rewrite inE eqxx.
  have yy : y \in [set z : G | col x == col z] by rewrite inE hxy eqxx.
  by move: (st x y xx yy); rewrite xy.
- move=> hc; split; first exact: preim_partitionP.
  apply/forall_inP=> A /imsetP[x _ ->]; apply/stableP.
  move=> y z; rewrite !inE /= => /eqP hy /eqP hz.
  by apply/negP=> hyz; have := hc y z hyz; rewrite -hy -hz eqxx.
Qed.

(** Boolean equality is needed when counting or sequencing supplied colourings. *)
Lemma proper_colouringE (G : sgraph) (C : finType) (col : G -> C) :
  proper_colouring col = [forall x : G, [forall y : G, (x -- y) ==> (col x != col y)]].
Proof.
apply/idP/idP.
- move/proper_colouringP=> h; apply/forallP=> x; apply/forallP=> y.
  by apply/implyP; exact: h.
- move/forallP=> h; apply/proper_colouringP=> x y.
  by move: (h x)=> /forallP/(_ y)/implyP.
Qed.

Lemma proper_colouring_upstream (G : sgraph) (C : finType) (col : G -> C) :
  proper_colouring col = coloring (preim_partition col [set: G]) [set: G].
Proof. by []. Qed.

Lemma proper_colouring_injective (G : sgraph) (C : finType) (col : G -> C) :
  injective col -> proper_colouring col.
Proof.
move=> inj; apply/proper_colouringP=> x y xy.
by rewrite (inj_eq inj) (sg_edgeNeq xy).
Qed.

Lemma proper_colouring_relabel (G : sgraph) (C D : finType)
    (col : G -> C) (f : C -> D) :
  injective f -> proper_colouring (f \o col) = proper_colouring col.
Proof.
move=> inj; rewrite !proper_colouringE.
by apply: eq_forallb=> x; apply: eq_forallb=> y; rewrite /= (inj_eq inj).
Qed.

Lemma proper_colouring_ext (G : sgraph) (C : finType) (c d : G -> C) :
  c =1 d -> proper_colouring c = proper_colouring d.
Proof.
move=> cd; rewrite !proper_colouringE.
by apply: eq_forallb=> x; apply: eq_forallb=> y; rewrite !cd.
Qed.

Lemma proper_colouring_K0 (C : finType) (col : 'K_0 -> C) : proper_colouring col.
Proof. by apply/proper_colouringP=> x y _; move: (ltn_ord x); rewrite ltn0. Qed.

Lemma proper_colouring_K1 (C : finType) (col : 'K_1 -> C) : proper_colouring col.
Proof.
by apply/proper_colouringP=> x y; rewrite (ord1 x) (ord1 y) sg_irrefl.
Qed.

Lemma not_proper_colouring_constant (G : sgraph) (C : finType) (c : C) (x y : G) :
  x -- y -> ~~ proper_colouring (fun _ : G => c).
Proof. by move=> xy; apply/negP=> /proper_colouringP/(_ x y xy); rewrite eqxx. Qed.

(** The supplied palette bounds the chromatic number, even with unused labels. *)
Lemma proper_colouring_chi (G : sgraph) (C : finType) (col : G -> C) :
  proper_colouring col -> χ([set: G]) <= #|C|.
Proof.
move=> hp; apply: leq_trans (color_bound hp) _.
pose fiber c := [set x : G | c == col x].
have hs : preim_partition col [set: G] \subset [set fiber c | c in [set: C]].
  apply/subsetP=> A /imsetP[x _ ->]; apply/imsetP.
  exists (col x); first by rewrite inE.
  by apply/setP=> y; rewrite /fiber !inE.
apply: leq_trans (subset_leq_card hs) _.
by have := leq_imset_card fiber [set: C]; rewrite cardsT.
Qed.
