(** * Chromatic.conjectures.X161 -- v2 controlled triangle-free four-hole row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X161 vocabulary ***********************************************)

Definition x161_local_chromatic_radius_two (G : sgraph) : nat :=
  \max_(v : G) χ([set: induced (rel_ball (--) 2 v)]).

Definition x161_two_phi_controlled (G : sgraph) (phi : nat -> nat) : Prop :=
  forall S : {set G},
    χ([set: induced S]) <= phi (x161_local_chromatic_radius_two (induced S)).

Definition x161_has_four_hole (G : sgraph) : Prop :=
  exists c : seq G, ucycle (--) c /\ size c = 4.

(** ** X161 statements *****************************************************)

(** Corpus row: arxiv:1509.06563#03
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1509.06563__03/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1509.06563__03.json
    English statement: (Scott and Seymour 2018, informal question on Statement 2.1 for ell = 4, arXiv:1509.06563)
      For every non-decreasing function phi there exists n such that every triangle-free finite
      simple graph that is (2,phi)-controlled and has chromatic number greater than n contains a
      hole with four vertices.
    Definitions: [x161_two_phi_controlled G phi] - every induced subgraph H of G satisfies chi(H)
      <= phi of the maximum, over vertices v of H, of the chromatic number of the ball of radius 2
      around v; this is the radius-2 local-chromatic control condition (this file);
      [x161_local_chromatic_radius_two G] - that maximum (this file); [rel_ball] (coq-graph-theory /
      GTBase); [x161_has_four_hole G] - a [ucycle] with exactly 4 vertices (this file);
      [triangle_free] (GTBase base/theories/base.v).
    Notes: Monotonicity of phi is stated with the mathcomp [mono] idiom. A 4-vertex [ucycle] in a
      triangle-free graph is automatically induced, so requiring a 4-hole and requiring a 4-cycle
      coincide under the triangle-free hypothesis. The corpus row is a QUESTION; the Rocq body is
      its affirmative reading. The row was retargeted in 2026-07-16 from a blocked placeholder, see
      meta/BLOCKED_RETARGETING_FOUNDATIONS.md. *)
Definition controlled_triangle_free_four_hole_statement : Prop :=
  forall phi : nat -> nat,
    {mono phi : x y / x <= y >-> x <= y} ->
    exists n : nat,
      forall G : sgraph,
        triangle_free G ->
        x161_two_phi_controlled G phi ->
        n < χ([set: G]) ->
        x161_has_four_hole G.
