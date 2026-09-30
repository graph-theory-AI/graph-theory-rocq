(** * Minor.conjectures.X198 -- v2 island colouring number row *)

From GraphTheory Require Import minor.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X198 vocabulary ***********************************************)

Definition x198_t_island (G : sgraph) (S : {set G}) (t : nat) : Prop :=
  S != set0 /\
  forall v : G, v \in S -> #|N(v) :\: S| < t.

Definition x198_col_star_le (C : sgraph -> Prop) (t : nat) : Prop :=
  exists c : nat,
    0 < c /\
    forall (G : sgraph) (A : {set G}),
      C G -> A != set0 ->
      exists S : {set induced A},
        #|S| <= c /\ @x198_t_island (induced A) S t.

Definition x198_join_path_rel (t m : nat) : rel ('I_t.-1 + 'I_m) :=
  fun x y =>
    match x, y with
    | inl _, inl _ => false
    | inl _, inr _ | inr _, inl _ => true
    | inr i, inr j => ((val i).+1 == val j) || ((val j).+1 == val i)
    end.

Definition x198_join_path (t m : nat) : sgraph :=
  @fg_mk_sgraph ('I_t.-1 + 'I_m)%type (@x198_join_path_rel t m).

Definition x198_forbids_Ktm_and_join_path
    (C : sgraph -> Prop) (t m : nat) : Prop :=
  1 <= m /\
  forall G : sgraph,
    C G -> ~ minor G (KB t m) /\ ~ minor G (x198_join_path t m).

(** ** X198 statements *****************************************************)

(** Corpus row: arxiv:1710.02727#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1710.02727__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1710.02727__00.json
    English statement: (Dvorak and Norin 2017, "Islands in minor-closed classes. I. Bounded
      treewidth and separators", Conjecture 4)
      For every t at least 1 and every minor-closed class C of finite simple graphs, C has
      island colouring number col-star at most t if and only if there is an m at least 1 such
      that no graph of C contains the complete bipartite graph K_(t,m) as a minor and no graph
      of C contains the join of an independent set on t-1 vertices with a path on m vertices
      as a minor.
    Definitions: [x198_t_island G S t] - S is a nonempty vertex set each of whose members has
      fewer than t neighbours outside S (minor-theory/theories/conjectures/X198.v);
      [x198_col_star_le C t] - there is one positive bound c, uniform over the class, such that
      for every graph G of C and every nonempty vertex set A the subgraph induced on A contains
      a t-island of at most c vertices (same file); [x198_join_path_rel t m],
      [x198_join_path t m] - the join of an independent set on t-1 vertices with a path on m
      vertices, i.e. I_(t-1) + P_m (same file); [x198_forbids_Ktm_and_join_path C t m] - m is at
      least 1 and no graph of C has K_(t,m) or I_(t-1)+P_m as a minor (same file).
    Notes: the [1 <= t] guard is load-bearing: at t = 0 the source's I_(t-1) is undefined and
      the encoding's 'I_(t.-1) collapses to 'I_0, which makes the biconditional refutable
      axiom-free via the single-vertex minor-closed class; the source's domain is t >= 1
      (verify fix 2026-07-18, meta/BLOCKED_RETARGETING_AUDIT.md, repaired-rows section).
      The source's "K_(t,m) is not in the class" is encoded as "no graph of the class has
      K_(t,m) as a minor", which is equivalent under the minor-closure hypothesis stated just
      before it.  col-star separates the island threshold t from the class-uniform size cap c,
      matching the source definition (a single c for all induced subgraphs of all graphs of
      the class). *)
Definition minor_closed_col_star_obstruction_statement : Prop :=
  forall (C : sgraph -> Prop) (t : nat),
    1 <= t ->
    (forall G H : sgraph, C G -> minor G H -> C H) ->
    x198_col_star_le C t <->
    exists m : nat, x198_forbids_Ktm_and_join_path C t m.
