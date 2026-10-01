(** * GTMisc.conjectures.X20 -- v2 burning and monochromatic-component rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X20 vocabulary ************************************************)

Fixpoint x20_ball (G : sgraph) (r : nat) (x : G) : {set G} :=
  if r is r'.+1 then x20_ball r' x :|: \bigcup_(z in x20_ball r' x) N(z)
  else [set x].

Definition x20_ceil_sqrt (n t : nat) : Prop :=
  n <= t ^ 2 /\ forall s : nat, n <= s ^ 2 -> t <= s.

Definition x20_burning_cover (G : sgraph) (t : nat) : Prop :=
  exists c : 'I_t -> G,
    forall v : G, exists i : 'I_t,
      v \in x20_ball (t.-1 - val i) (c i).

Definition x20_edge_set (G : sgraph) : {set {set G}} :=
  simple_edge_set G.

Definition x20_colour_rel
    (G : sgraph) (k : nat) (col : {set G} -> 'I_k) (i : 'I_k) : rel G :=
  fun u v => (u -- v) && (col [set u; v] == i).

Definition x20_monochromatic_connected_set
    (G : sgraph) (k : nat) (col : {set G} -> 'I_k) (i : 'I_k)
    (S : {set G}) : Prop :=
  S != set0 /\
  forall u v : G, u \in S -> v \in S ->
    connect (x20_colour_rel col i) u v.

(** ** X20 statements ******************************************************)

(** Studies slice: burning number conjecture. *)
Definition burning_number_conjecture_statement : Prop :=
  forall (G : sgraph) (t : nat),
    0 < #|G| ->
    connected [set: G] ->
    x20_ceil_sqrt #|G| t ->
    x20_burning_cover G t.

(** Studies slice: Gyarfas-Sarkozy monochromatic component conjecture. *)
Definition gyarfas_sarkozy_monochromatic_component_statement : Prop :=
  forall (k : nat) (G : sgraph) (col : {set G} -> 'I_k),
    3 <= k ->
    (forall v : G, k ^ 2 * #|N(v)| >= (k ^ 2 - (k - 1)) * #|G|)%N ->
    exists (i : 'I_k) (S : {set G}),
      x20_monochromatic_connected_set col i S /\
      (#|G| <= (k - 1) * #|S|)%N.
