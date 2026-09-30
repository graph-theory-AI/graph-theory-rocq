(** * GTMisc.conjectures.X74 -- v2 induced linear forest row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X74 vocabulary ************************************************)

Definition x74_min_degree_at_least (G : sgraph) (d : nat) : Prop :=
  forall v : G, d <= #|N(v)|.

Definition x74_induced_linear_forest (G : sgraph) (S : {set G}) : Prop :=
  is_forest [set: induced S] /\
  forall v : induced S, #|N(v)| <= 2.

Definition x74_degree_sum_den (G : sgraph) : nat :=
  \prod_(v : G) (#|N(v)|).+1.

Definition x74_scaled_degree_sum (G : sgraph) : nat :=
  \sum_(v : G) (2 * (x74_degree_sum_den G %/ (#|N(v)|).+1)).

(** ** X74 statements ******************************************************)

(** Corpus row: studies:std_akbari_amanihamedani_mousavi_nikpey_sheybani_con
    Site: none
    Review: none
    English statement: (Akbari, Amanihamedani, Mousavi, Nikpey and Sheybani, conjecture on
      large induced linear forests)
      Every finite simple graph G of minimum degree at least 2 contains a vertex set S whose
      induced subgraph is a forest of maximum degree at most 2 - an induced linear forest - and
      whose size satisfies sum over v of 2/(deg(v)+1) <= |S|, the inequality being stated over
      the common denominator product over v of (deg(v)+1).
    Definitions: [x74_min_degree_at_least G d] - every vertex has degree at least d (this
      file); [x74_induced_linear_forest S] - the subgraph induced on S is a forest all of whose
      vertices have degree at most 2 (this file); [x74_degree_sum_den G] - the common
      denominator, the product over v of (deg(v)+1) (this file); [x74_scaled_degree_sum G] -
      the numerator, the sum over v of 2 times the denominator divided by (deg(v)+1) (this
      file); [is_forest], [induced] - coq-graph-theory.
    Notes: the Caro-Wei style rational bound is cleared of denominators by multiplying
      through by the product of the (deg(v)+1), which is exact since each factor divides the
      product.  "Linear forest" is rendered as "forest with maximum degree at most 2", i.e. a
      disjoint union of paths. *)
Definition induced_linear_forest_caro_wei_bound_statement : Prop :=
  forall G : sgraph,
    x74_min_degree_at_least G 2 ->
    exists S : {set G},
      x74_induced_linear_forest S /\
      x74_scaled_degree_sum G <= x74_degree_sum_den G * #|S|.
