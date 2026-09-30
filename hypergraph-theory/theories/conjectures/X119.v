(** * Hypergraph.conjectures.X119 -- v2 3-uniform Ramsey tower row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X119 vocabulary ***********************************************)

Definition x119_uniform (T : finType) (E : {set {set T}}) (r : nat) : Prop :=
  forall e : {set T}, e \in E -> #|e| = r.

(** No isolated vertices: every vertex of the ground type lies in some edge. *)
Definition x119_no_isolated (T : finType) (E : {set {set T}}) : Prop :=
  forall v : T, exists e : {set T}, e \in E /\ v \in e.

(** *** q-colour monochromatic copy in the complete 3-uniform host. *)

Definition x119_image_edge
    (T : finType) (N : nat) (f : T -> 'I_N) (e : {set T}) : {set 'I_N} :=
  [set y : 'I_N | [exists x : T, (x \in e) && (y == f x)]].

Definition x119_monochromatic_copy
    (T : finType) (E : {set {set T}}) (N q : nat)
    (col : {set 'I_N} -> 'I_q) : Prop :=
  exists (colour : 'I_q) (f : T -> 'I_N),
    injective f /\
    forall e : {set T},
      e \in E -> col (x119_image_edge f e) = colour.

(** [N] vertices force a monochromatic copy under every [q]-colouring of the
    3-subsets of the host. *)
Definition x119_forces_mono
    (T : finType) (E : {set {set T}}) (q N : nat) : Prop :=
  forall col : {set 'I_N} -> 'I_q, x119_monochromatic_copy E col.

(** [R] is the [q]-colour 3-uniform Ramsey number [r_3(H;q)]: the least host
    size forcing a monochromatic copy of [H = (T,E)]. *)
Definition x119_ramsey_number
    (T : finType) (E : {set {set T}}) (q R : nat) : Prop :=
  x119_forces_mono E q R /\
  forall N : nat, x119_forces_mono E q N -> R <= N.

(** Integer ceiling square root: the least [s] with [m <= s^2].  Chosen as an
    upper approximation of [sqrt m] so the tower bound stays an honest upper
    bound; the outer existential [cq] absorbs the O(1) rounding factor. *)
Lemma x119_sqrt_ex (m : nat) : exists s : nat, m <= s ^ 2.
Proof. exists m. by rewrite expnS expn1; case: m => // n; rewrite leq_pmulr. Qed.

Definition x119_sqrt (m : nat) : nat := ex_minn (x119_sqrt_ex m).

(** ** X119 statements *****************************************************)

(** Corpus row: studies:std_conlon_fox_sudakov_problem_on_3_uniform_hypergra
    Site: none
    Review: none
    English statement: (Conlon, Fox and Sudakov, problem on 3-uniform hypergraph Ramsey
      numbers)
      For every number of colours q at least 2 there is a constant c_q such that every
      3-uniform hypergraph H with m hyperedges and no isolated vertices has q-colour Ramsey
      number at most 2 raised to the power 2 raised to the power c_q times the square root of m.
    Definitions: [x119_uniform E r] - every hyperedge has exactly r vertices
      (hypergraph-theory/theories/conjectures/X119.v); [x119_no_isolated E] - every vertex of
      the ground type lies in some hyperedge (same file); [x119_image_edge f e] - the image of a
      hyperedge under f (same file); [x119_monochromatic_copy E col] - there are a colour and an
      injection of the vertices into the host with every image hyperedge of that colour (same
      file); [x119_forces_mono E q N] - every q-colouring of the subsets of an N-element host
      admits such a copy (same file); [x119_ramsey_number E q R] - R is the least host size
      forcing a monochromatic copy of H (same file); [x119_sqrt m] - the least s with m <= s^2,
      i.e. the integer ceiling square root (same file).
    Notes: the constant c_q is quantified after q and before the hypergraph, matching "there
      exists c_q".  The no-isolated-vertices guard is load-bearing: it is what ties the number
      of vertices of H to its number m of hyperedges, without which a bound depending on m alone
      would be false.  The ceiling square root over-approximates the true square root, so the
      upper bound stays honest; the outer existential c_q absorbs the rounding factor. *)
Definition conlon_fox_sudakov_three_uniform_ramsey_tower_statement : Prop :=
  forall q : nat,
    2 <= q ->
    exists cq : nat,
      forall (T : finType) (E : {set {set T}}),
        x119_uniform E 3 ->
        x119_no_isolated E ->
        forall R : nat,
          x119_ramsey_number E q R ->
          R <= 2 ^ (2 ^ (cq * x119_sqrt #|E|)).
