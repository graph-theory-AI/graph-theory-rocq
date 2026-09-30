(** * Minor.conjectures.X133 -- v2 K_s-free clique-minor growth row *)

From GraphTheory Require Import minor.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X133 vocabulary ***********************************************)

Definition x133_Ks_free (G : sgraph) (s : nat) : Prop :=
  ω([set: G]) < s.

(** ** X133 statements *****************************************************)

(** Corpus row: studies:std_dvo_k_yepremyan_question_on_clique_minors_in_k_s
    Site: none
    Review: none
    English statement: (Dvorak and Yepremyan, question on clique minors in K_s-free graphs)
      For every s greater than 1 there are a positive rational exponent and a threshold,
      depending on s only, with the following property: for every r at least 1 and every
      finite simple graph G on n vertices that has no clique on s vertices, has independence
      number at most r, and satisfies n at least threshold times r, G has a complete-graph
      minor on t vertices for some t with t at least (n/r) raised to the power one plus that
      exponent.
    Definitions: [x133_Ks_free G s] - the clique number of G is less than s, i.e. G has no
      clique on s vertices (minor-theory/theories/conjectures/X133.v).
    Notes: "polynomially larger than n/r" is read as a fixed positive rational exponent
      e1/e2, chosen after s and before r, n and G.  The bound t >= (n/r)^(1+e1/e2) is
      cross-multiplied into the naturals as n^(e2+e1) <= t^e2 * r^(e2+e1), so no division or
      rational arithmetic is needed.  "n/r large enough" is the threshold condition
      N * r <= n, with N chosen together with e1 and e2.  The guard [1 < s] is needed because
      a K_1-free graph is empty. *)
Definition dvorak_yepremyan_ks_free_clique_minor_polynomial_statement : Prop :=
  forall s : nat,
    1 < s ->
    exists e1 e2 N : nat,
      [/\ 0 < e1, 0 < e2 &
        forall (r n : nat) (G : sgraph),
          0 < r ->
          #|G| = n ->
          x133_Ks_free G s ->
          α(G) <= r ->
          N * r <= n ->
          exists t : nat,
            minor G 'K_t /\
            n ^ (e2 + e1) <= t ^ e2 * r ^ (e2 + e1)].

