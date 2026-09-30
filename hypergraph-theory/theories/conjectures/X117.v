(** * Hypergraph.conjectures.X117 -- v2 hedgehog Ramsey row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X117 vocabulary ***********************************************)

(** *** The hedgehog H_t as a concrete finite 3-uniform hypergraph.

    Body: [t] vertices, [inl i] for [i : 'I_t].
    Spikes: one distinct vertex [inr s] for every ordered pair [s = (i,j)]
    with [i < j], i.e. exactly [C(t,2)] spikes -- one per unordered pair.
    Hyperedges: [{inl i, inl j, inr s}] for each spike [s = (i,j)].  Each
    spike lies in exactly one edge, each edge has 3 distinct vertices, so
    [H_t] is 3-uniform with body [t] and [C(t,2)] spikes/edges. *)

Definition x117_spike (t : nat) : Type := {p : 'I_t * 'I_t | p.1 < p.2}.

Definition x117_vertex (t : nat) : Type := ('I_t + x117_spike t)%type.

Definition x117_edge (t : nat) (s : x117_spike t) : {set x117_vertex t} :=
  [set inl (sval s).1; inl (sval s).2; inr s].

Definition x117_edges (t : nat) : {set {set x117_vertex t}} :=
  [set x117_edge s | s : x117_spike t].

(** *** Two-colour monochromatic copy in the complete 3-uniform host. *)

Definition x117_image_edge
    (T : finType) (N : nat) (f : T -> 'I_N) (e : {set T}) : {set 'I_N} :=
  [set y : 'I_N | [exists x : T, (x \in e) && (y == f x)]].

Definition x117_monochromatic_copy
    (T : finType) (E : {set {set T}}) (N : nat)
    (col : {set 'I_N} -> bool) : Prop :=
  exists (colour : bool) (f : T -> 'I_N),
    injective f /\
    forall e : {set T},
      e \in E -> col (x117_image_edge f e) = colour.

(** [N] vertices force a monochromatic copy under every 2-colouring of the
    3-subsets of the host. *)
Definition x117_forces_mono
    (T : finType) (E : {set {set T}}) (N : nat) : Prop :=
  forall col : {set 'I_N} -> bool, x117_monochromatic_copy E col.

(** [R] is the two-colour Ramsey number [r(H_t;2)]: the least host size that
    forces a monochromatic copy of [H_t]. *)
Definition x117_ramsey_number (t R : nat) : Prop :=
  x117_forces_mono (x117_edges t) R /\
  forall N : nat, x117_forces_mono (x117_edges t) N -> R <= N.

(** ** X117 statements *****************************************************)

(** Corpus row: studies:std_conlon_fox_r_dl_question_on_hedgehog_ramsey_numb
    Site: none
    Review: none
    English statement: (Conlon, Fox and Rodl, question on hedgehog Ramsey numbers)
      Is the two-colour Ramsey number of the hedgehog H_t equal to t raised to the power
      2 + o(1)?  Formalised two-sidedly: for every positive rational epsilon there is a
      threshold t0 such that for every t at least t0, the two-colour Ramsey number R of H_t
      satisfies t^(2 - epsilon) <= R <= t^(2 + epsilon).
    Definitions: [x117_spike t] - an unordered pair of body vertices, presented as an ordered
      pair with the first index smaller (hypergraph-theory/theories/conjectures/X117.v);
      [x117_vertex t] - a body vertex or a spike vertex (same file); [x117_edge s] - the
      hyperedge consisting of the two body vertices of the spike s together with s itself (same
      file); [x117_edges t] - the hedgehog H_t, i.e. the family of all those hyperedges, a
      3-uniform hypergraph with t body vertices and one spike and one hyperedge per unordered
      pair (same file); [x117_image_edge f e] - the image of a hyperedge under f (same file);
      [x117_monochromatic_copy E col] - there are a colour and an injection of the vertices into
      the host with every image hyperedge of that colour (same file);
      [x117_forces_mono E N] - every two-colouring of the subsets of an N-element host admits
      such a copy (same file); [x117_ramsey_number t R] - R is the least host size forcing a
      monochromatic copy of H_t (same file).
    Notes: "t^(2+o(1))" is read as the two-sided rational-epsilon envelope, with the threshold
      t0 chosen after epsilon.  The exponents are cleared by raising to the power e2, so the two
      inequalities become t^(2*e2 - e1) <= R^e2 and R^e2 <= t^(2*e2 + e1).  Truncated natural
      subtraction only weakens the lower bound when epsilon is at least 2, where it is already
      implied, so the binding content sits at small epsilon. *)
Definition conlon_fox_rodl_hedgehog_ramsey_statement : Prop :=
  forall e1 e2 : nat,
    0 < e1 -> 0 < e2 ->
    exists t0 : nat,
      forall t R : nat,
        t0 <= t ->
        x117_ramsey_number t R ->
        t ^ (2 * e2 - e1) <= R ^ e2 /\ R ^ e2 <= t ^ (2 * e2 + e1).
