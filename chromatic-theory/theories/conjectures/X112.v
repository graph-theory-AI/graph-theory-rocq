(** * Chromatic.conjectures.X112 -- v2 chi-bounded closure (substitution + gluing) row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X112 vocabulary ***********************************************)

(** Clique number of the whole graph, the parameter against which
    chi-boundedness is measured. *)
Definition x112_omega (G : sgraph) : nat := ω([set: G]).

(** A class [D] is chi-bounded: a single [f : nat -> nat] bounds [χ(G)] by
    [f(ω(G))] uniformly over every [G] in the class (∃ f BEFORE ∀ G). *)
Definition x112_chi_bounded (D : sgraph -> Prop) : Prop :=
  exists f : nat -> nat,
    forall G : sgraph, D G -> χ([set: G]) <= f (x112_omega G).

(** [x112_is_substitution G G1 H]: [G] is obtained from [G1] by substituting
    the graph [H] for a single vertex [v] (blow-up of [v] into a copy of [H]).
    Encoded relationally through a quotient map [phi : G -> G1]:
      - the fibre of [v] (the "blob") induces a copy of [H];
      - every OTHER fibre is a single vertex (single-vertex substitution);
      - across distinct fibres the adjacency of [G] is exactly the adjacency of
        the images in [G1].
    The last clause forces every blob vertex to see the same outside vertices as
    [v] did (the module / homogeneous-set property), so [G] is precisely [G1]
    with [v] replaced by [H].  Non-trivially satisfiable: substituting [K2] into
    [K2] yields [K3], etc. *)
Definition x112_is_substitution (G G1 H : sgraph) : Prop :=
  exists (v : G1) (phi : G -> G1),
    inhabited (H ≃ induced (phi @^-1: [set v])) /\
    (forall u : G1, u != v -> #|phi @^-1: [set u]| = 1) /\
    (forall x y : G, phi x != phi y -> (x -- y) = (phi x -- phi y)).

(** [x112_glue_le b G G1 G2]: [G] is a gluing of [G1] and [G2] along at most [b]
    shared vertices.  Its vertex set is covered by two parts [A], [B] with
    [induced A ≃ G1], [induced B ≃ G2], overlap [|A ∩ B| ≤ b] (the glue), and no
    edges between the two PRIVATE parts [A \ B] and [B \ A] — the two graphs meet
    only through the shared vertices.  Non-trivially satisfiable: [b := 0] gives
    the disjoint union of [G1] and [G2]. *)
Definition x112_glue_le (b : nat) (G G1 G2 : sgraph) : Prop :=
  exists A B : {set G},
    (forall z : G, (z \in A) || (z \in B)) /\
    #|A :&: B| <= b /\
    inhabited (G1 ≃ induced A) /\
    inhabited (G2 ≃ induced B) /\
    (forall x y : G,
        x \in A -> x \notin B -> y \in B -> y \notin A -> ~~ (x -- y)).

(** The closure of a class [C] under substitution and gluing along at most [b]
    vertices: the least class containing [C] and closed under both operations. *)
Inductive x112_closure (C : sgraph -> Prop) (b : nat) : sgraph -> Prop :=
| x112_base (G : sgraph) :
    C G -> x112_closure C b G
| x112_subst (G G1 H : sgraph) :
    x112_closure C b G1 -> x112_closure C b H ->
    x112_is_substitution G G1 H -> x112_closure C b G
| x112_glue (G G1 G2 : sgraph) :
    x112_closure C b G1 -> x112_closure C b G2 ->
    x112_glue_le b G G1 G2 -> x112_closure C b G.

(** ** X112 statements *****************************************************)

(** Corpus row: studies:std_chudnovsky_penev_scott_trotignon_conjecture_boun
    Site: none
    Review: none
    English statement: (Chudnovsky, Penev, Scott and Trotignon, studies slice of the corpus)
      For every class C of finite simple graphs and every bound b, if C is chi-bounded then so is
      the closure of C under substitution of a graph for a single vertex and under gluing two graphs
      along at most b common vertices.
    Definitions: [x112_chi_bounded D] - one function f bounds chi(G) by f(omega(G)) for every
      member, the function being chosen before the graphs (this file); [x112_is_substitution G G1 H]
      - G arises from G1 by replacing one vertex by a copy of H, encoded by a quotient map whose
      non-trivial fibre induces H and which preserves adjacency across distinct fibres (this file);
      [x112_glue_le b G G1 G2] - the vertices of G are covered by two sets inducing copies of G1 and
      G2, overlapping in at most b vertices, with no edge between the two private parts (this file);
      [x112_closure C b] - the inductive closure of C under these two operations (this file).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      corpus row is a QUESTION; the Rocq body is its affirmative reading. Substitution is restricted
      to a SINGLE vertex at a time, which generates the same closure as simultaneous substitution. *)
Definition chi_bounded_closure_substitution_gluing_statement : Prop :=
  forall (C : sgraph -> Prop) (b : nat),
    x112_chi_bounded C -> x112_chi_bounded (x112_closure C b).
