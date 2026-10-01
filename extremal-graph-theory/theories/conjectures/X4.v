(** * Extremal.conjectures.X4 -- v2 milestone X4, clean extremal wave

    This file states the first clean X4 sub-batch: finite Ramsey/Folkman rows
    and Turan/triangle-supersaturation rows whose source statements can be
    expressed with the existing finite [sgraph] vocabulary.  Asymptotic
    density rows and rows needing heavier paper-local primitives are deferred. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import sgraph minor.
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local extremal vocabulary *******************************************)

Definition x4_edge_count (G : sgraph) : nat :=
  #|[set p : G * G |
      (p.1 -- p.2) && ((enum_rank p.1) < (enum_rank p.2))%N]|.

Definition x4_mono_complete_copy
    (m q : nat) (H : sgraph) (col : 'I_m -> 'I_m -> 'I_q) : Prop :=
  exists c : 'I_q, exists f : H -> 'I_m,
    injective f /\ forall x y : H, x -- y -> col (f x) (f y) = c.

Definition x4_complete_arrow (q m : nat) (H : sgraph) : Prop :=
  forall col : 'I_m -> 'I_m -> 'I_q,
    (forall x y : 'I_m, col x y = col y x) ->
    @x4_mono_complete_copy m q H col.

Definition x4_red_blue_copy
    (m : nat) (Hred Hblue : sgraph) (col : rel 'I_m) : Prop :=
  (exists f : Hred -> 'I_m,
     injective f /\ forall x y : Hred, x -- y -> col (f x) (f y) = true) \/
  (exists f : Hblue -> 'I_m,
     injective f /\ forall x y : Hblue, x -- y -> col (f x) (f y) = false).

Definition x4_two_colour_arrow (m : nat) (Hred Hblue : sgraph) : Prop :=
  forall col : rel 'I_m, symmetric col -> x4_red_blue_copy Hred Hblue col.

Definition x4_ramsey_two (Hred Hblue : sgraph) (r : nat) : Prop :=
  x4_two_colour_arrow r Hred Hblue /\
  forall m : nat, x4_two_colour_arrow m Hred Hblue -> r <= m.

Definition x4_mono_subgraph_copy
    (q : nat) (G H : sgraph) (col : G -> G -> 'I_q) : Prop :=
  exists c : 'I_q, exists f : H -> G,
    injective f /\
    forall x y : H, x -- y -> (f x -- f y) /\ col (f x) (f y) = c.

Definition x4_graph_arrow (q : nat) (G H : sgraph) : Prop :=
  forall col : G -> G -> 'I_q,
    (forall x y : G, col x y = col y x) ->
    @x4_mono_subgraph_copy q G H col.

Definition x4_palette_on
    (V C : finType) (col : V -> V -> C) (S : {set V}) : {set C} :=
  [set c : C | [exists x : V, [exists y : V,
      [&& x \in S, y \in S, x != y & col x y == c]]]].

Definition x4_edge_in_mono_triangle
    (n : nat) (col : rel 'I_n) (x y : 'I_n) : bool :=
  [exists z : 'I_n,
      [&& z != x, z != y, col x z == col x y & col y z == col x y]].

Definition x4_edges_not_in_mono_triangle (n : nat) (col : rel 'I_n) : nat :=
  #|[set p : 'I_n * 'I_n |
      ((val p.1) < (val p.2))%N && ~~ x4_edge_in_mono_triangle col p.1 p.2]|.

Section X4Book.
Variables (k n : nat).

Definition x4_book_rel : rel ('I_k + 'I_n) :=
  fun x y =>
    match x, y with
    | inl a, inl b => a != b
    | inl _, inr _ => true
    | inr _, inl _ => true
    | inr _, inr _ => false
    end.

Lemma x4_book_rel_sym : symmetric x4_book_rel.
Proof. by case=> a; case=> b //=; rewrite eq_sym. Qed.

Lemma x4_book_rel_irrefl : irreflexive x4_book_rel.
Proof. by case=> a //=; rewrite eqxx. Qed.

Definition x4_book_graph : sgraph :=
  SGraph x4_book_rel_sym x4_book_rel_irrefl.

End X4Book.

Definition x4_K_free (G : sgraph) (t : nat) : Prop := ~ subgraph 'K_t G.

Definition x4_turan_number (r n m : nat) : Prop :=
  (exists G : sgraph,
     [/\ #|G| = n, x4_edge_count G = m & x4_K_free G (r.+1)]) /\
  forall m' : nat,
    (exists G : sgraph,
       [/\ #|G| = n, x4_edge_count G = m' & x4_K_free G (r.+1)]) ->
    m' <= m.

Definition x4_degree_sum (G : sgraph) (S : {set G}) : nat :=
  \sum_(v in S) #|N(v)|.

Definition x4_triangle_set (G : sgraph) (T : {set G}) : bool :=
  (#|T| == 3) && cliqueb T.

Definition x4_triangle_count (G : sgraph) : nat :=
  #|[set T : {set G} | x4_triangle_set T]|.

Definition x4_consecutive_in_cycle (G : sgraph) (c : seq G) (u v : G) : bool :=
  ((u, v) \in zip c (rot 1 c)) || ((v, u) \in zip c (rot 1 c)).

Definition x4_edge_in_c5 (G : sgraph) (x y : G) : bool :=
  [exists c : 5.-tuple G,
      [&& ucycleb (--) (val c), x \in val c, y \in val c
        & x4_consecutive_in_cycle (val c) x y]].

Definition x4_c5_edge_count (G : sgraph) : nat :=
  #|[set p : G * G |
      [&& (p.1 -- p.2), ((enum_rank p.1) < (enum_rank p.2))%N
        & x4_edge_in_c5 p.1 p.2]]|.

Definition x4_edge_set (G : sgraph) : {set {set G}} :=
  simple_edge_set G.

Definition x4_at_most_one_triangle_edge (G : sgraph) (F : {set {set G}}) : Prop :=
  F \subset x4_edge_set G /\
  forall T : {set G},
    x4_triangle_set T -> #|[set e in F | e \subset T]| <= 1.

Definition x4_hits_every_triangle (G : sgraph) (F : {set {set G}}) : Prop :=
  F \subset x4_edge_set G /\
  forall T : {set G},
    x4_triangle_set T -> exists e : {set G}, e \in F /\ e \subset T.

Definition x4_alpha1 (G : sgraph) (a : nat) : Prop :=
  (exists F : {set {set G}}, x4_at_most_one_triangle_edge F /\ #|F| = a) /\
  forall b : nat,
    (exists F : {set {set G}}, x4_at_most_one_triangle_edge F /\ #|F| = b) ->
    b <= a.

Definition x4_tau1 (G : sgraph) (t : nat) : Prop :=
  (exists F : {set {set G}}, x4_hits_every_triangle F /\ #|F| = t) /\
  forall b : nat,
    (exists F : {set {set G}}, x4_hits_every_triangle F /\ #|F| = b) ->
    t <= b.

(** ** X4 statements *******************************************************)

(** Erdos Problems #551. *)
Definition cycle_clique_ramsey_formula_statement : Prop :=
  forall k n : nat,
    n <= k -> 3 <= n -> (n != 3 \/ k != 3) ->
    x4_ramsey_two (cycle_graph k) 'K_n ((k - 1) * (n - 1) + 1).

(** Erdos Problems #556. *)
(** The solved bound R_3(C_n) <= 4n-3 holds only for n sufficiently large
    (Kohayakawa-Simonovits-Skokan et al.); it is FALSE for small n
    (e.g. n = 3, where C_3 = K_3 and R_3(K_3) = 17 > 9 = 4*3-3).  Hence the
    faithful encoding of the asymptotic theorem is "there is a threshold n0
    beyond which the bound holds". *)
Definition three_colour_cycle_ramsey_bound_statement : Prop :=
  exists n0 : nat, forall n : nat, n0 <= n ->
    x4_complete_arrow 3 (4 * n - 3) (cycle_graph n).

(** Erdos Problems #582. *)
Definition folkman_k4_free_triangle_arrow_statement : Prop :=
  exists G : sgraph, x4_K_free G 4 /\ x4_graph_arrow 2 G 'K_3.

(** Erdos Problems #617. *)
Definition missing_colour_complete_edge_colouring_statement : Prop :=
  forall r : nat, 3 <= r ->
    forall col : 'I_(r * r + 1) -> 'I_(r * r + 1) -> 'I_r,
      (forall x y : 'I_(r * r + 1), col x y = col y x) ->
      exists S : {set 'I_(r * r + 1)},
        #|S| = r.+1 /\ #|x4_palette_on col S| < r.

(** Erdos Problems #639. *)
Definition monochromatic_triangle_edge_bound_statement : Prop :=
  forall n : nat, forall col : rel 'I_n,
    symmetric col ->
    4 * x4_edges_not_in_mono_triangle col <= n * n.

(** Erdos Problems #924. *)
Definition folkman_clique_arrow_statement : Prop :=
  forall k l : nat, 2 <= k -> 3 <= l ->
    exists G : sgraph,
      x4_K_free G (l.+1) /\ x4_graph_arrow k G 'K_l.

(** Studies slice: Thomason's conjecture on book Ramsey numbers. *)
Definition thomason_book_ramsey_bound_statement : Prop :=
  forall n k : nat, 0 < n -> 0 < k ->
    x4_complete_arrow 2 (2 ^ k * (n + k - 2) + 2) (x4_book_graph k n).

(** Erdos Problems #904. *)
Definition turan_degree_sum_clique_statement : Prop :=
  forall r n tr : nat, 2 <= r -> r <= n ->
    x4_turan_number r n tr ->
    forall G : sgraph, #|G| = n -> tr <= x4_edge_count G ->
      exists S : {set G},
        #|S| = r /\ clique S /\
        2 * r * x4_edge_count G <= n * x4_degree_sum S.

(** Erdos Problems #905. *)
Definition book_triangle_edge_statement : Prop :=
  forall G : sgraph, forall n : nat,
    #|G| = n -> n * n < 4 * x4_edge_count G ->
    exists x y : G, x -- y /\ n <= 6 * #|N(x) :&: N(y)|.

(** Erdos Problems #608. *)
Definition c5_edge_count_above_turan_statement : Prop :=
  forall G : sgraph, forall n : nat,
    #|G| = n -> n * n < 4 * x4_edge_count G ->
    2 * n * n <= 9 * x4_c5_edge_count G.

(** Erdos Problems #621. *)
Definition triangle_alpha_tau_bound_statement : Prop :=
  forall G : sgraph, forall n a t : nat,
    #|G| = n -> x4_alpha1 G a -> x4_tau1 G t ->
    4 * (a + t) <= n * n.

(** Erdos Problems #1010. *)
Definition triangle_supersaturation_statement : Prop :=
  forall G : sgraph, forall n t : nat,
    #|G| = n -> t < n %/ 2 ->
    x4_edge_count G = n * n %/ 4 + t ->
    t * (n %/ 2) <= x4_triangle_count G.
