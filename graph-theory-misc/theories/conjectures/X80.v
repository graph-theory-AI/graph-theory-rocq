(** * GTMisc.conjectures.X80 -- v2 toroidal cop-number row *)

From GTBase Require Export base.
From Topological.foundations Require Import embedding.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X80 vocabulary ************************************************)

Definition x80_legal_move (G : sgraph) (x y : G) : bool :=
  (x == y) || (x -- y).

Definition x80_cop_positions (G : sgraph) (k : nat) := {ffun 'I_k -> G}.

Definition x80_captured
    (G : sgraph) (k : nat) (c : x80_cop_positions G k) (r : G) : bool :=
  [exists i : 'I_k, c i == r].

Definition x80_cops_move
    (G : sgraph) (k : nat)
    (c c' : x80_cop_positions G k) : Prop :=
  forall i : 'I_k, x80_legal_move (c i) (c' i).

Definition x80_cop_number_at_most (G : sgraph) (k : nat) : Prop :=
  exists (c0 : x80_cop_positions G k)
         (strat : x80_cop_positions G k -> G -> x80_cop_positions G k)
         (W : {set (x80_cop_positions G k * G)})
         (rank : x80_cop_positions G k * G -> nat),
    (forall r : G, x80_captured c0 r \/ (c0, r) \in W) /\
    forall (c : x80_cop_positions G k) (r : G),
      (c, r) \in W ->
      ~~ x80_captured c r ->
      let c' := strat c r in
      x80_cops_move c c' /\
      forall r' : G,
        x80_legal_move r r' ->
        x80_captured c' r' \/
        ((c', r') \in W /\ rank (c', r') < rank (c, r)).

(** ** X80 statements ******************************************************)

(** Corpus row: studies:std_andreae_schr_der_conjecture_toroidal_cop_number
    Site: none
    Review: none
    English statement: (Andreae and Schroeder, toroidal cop-number conjecture)
      Every connected finite simple graph that embeds in the torus has cop number at most 3:
      three cops have a starting position and a strategy that captures the robber from every
      starting vertex, in finitely many rounds.
    Definitions: [x80_legal_move x y] - staying put or moving along an edge (this file);
      [x80_cop_positions G k] - a placement of k cops (this file); [x80_captured c r] - some
      cop occupies the robber's vertex (this file); [x80_cops_move c c'] - every cop makes a
      legal move (this file); [x80_cop_number_at_most G k] - a starting position, a strategy, a
      winning region W and a rank function such that every uncaptured position of W leads,
      after the cops' move and any robber move, either to a capture or to a position of W of
      strictly smaller rank (this file); [toroidal G] - G embeds in a surface of genus 1
      (topological-graph-theory/theories/foundations/embedding.v); [connected] -
      coq-graph-theory.
    Notes: termination of the pursuit is certified by a rank function that strictly decreases
      on the winning region, which is the finite-witness rendering of "the cops win in finitely
      many rounds" and avoids any coinductive or transfinite notion.  Connectedness is carried
      explicitly because the orientable-torus predicate of the topological foundation is exact
      on connected graph embeddings, and because the cop number is conventionally taken per
      connected graph. *)
Definition toroidal_graph_cop_number_three_statement : Prop :=
  forall G : sgraph,
    connected [set: G] ->
    toroidal G ->
    x80_cop_number_at_most G 3.
