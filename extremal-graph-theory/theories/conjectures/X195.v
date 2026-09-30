(** * Extremal.conjectures.X195 -- v2 Ramsey-nice eventual row
      (re-authored 2026-09-23 with the recovered "k-nice" definition, wave X223 pass) *)

From GTBase Require Export base.
From Extremal.foundations Require Import edge_colourings.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X195 vocabulary ***********************************************

    The paper-local notions of arXiv:1708.07369 (Aharoni, Alon, Amir, Haxell,
    Hefetz, Jiang, Kronenberg, Naor), recovered from the source at the
    2026-09-23 triage:

    - R_k(F) is the least n such that every k-colouring of the edges of K_n
      contains a monochromatic copy of some member of the family F;
    - F is K-NICE if for EVERY graph G with chi(G) = R_k(F) and every
      k-colouring of E(G) there is a monochromatic copy of some member of F.

    Both notions genuinely depend on k (the colourings take k values), which the
    2026-07-16 encoding did not - see the note on the statement below. *)

Definition x195_contains_forest (k : nat) (Fam : 'I_k -> sgraph) : Prop :=
  exists i : 'I_k, is_forest [set: Fam i].

(** [Host] arrows the family [Fam] in [k] colours: every k-colouring of the
    edges of [Host] has a monochromatic copy of some member of [Fam]. *)
Definition x195_arrows (Host : sgraph) (k r : nat) (Fam : 'I_r -> sgraph) : Prop :=
  forall col : {set Host} -> 'I_k,
    exists (i : 'I_r) (c : 'I_k), mono_copy (Fam i) col c.

(** [n] IS the k-colour Ramsey number R_k(Fam): the least n with
    K_n -> (Fam)_k. *)
Definition x195_ramsey_number (k r : nat) (Fam : 'I_r -> sgraph) (n : nat) : Prop :=
  x195_arrows 'K_n k Fam /\ forall m : nat, m < n -> ~ x195_arrows 'K_m k Fam.

(** [Fam] is K-NICE: every graph whose chromatic number equals R_k(Fam) already
    arrows the family in k colours (not only the complete graph on R_k(Fam)
    vertices). *)
Definition x195_k_nice (k r : nat) (Fam : 'I_r -> sgraph) : Prop :=
  forall n : nat, x195_ramsey_number k Fam n ->
    forall G : sgraph, χ([set: G]) = n -> x195_arrows G k Fam.

(** Corpus row: arxiv:1708.07369#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1708.07369__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1708.07369__00.json
    English statement: (Aharoni, Alon, Amir, Haxell, Hefetz, Jiang, Kronenberg, Naor 2017,
      arXiv:1708.07369 Question 1.1)
      Let F be a non-empty finite family of graphs, indexed by 'I_r, containing at least one
      forest.  Then there is a threshold k0 such that for every k >= k0 the family F is
      k-nice, that is: whenever n is the k-colour Ramsey number R_k(F) -- the least n such
      that every k-colouring of the edges of the complete graph on n vertices has a
      monochromatic copy of some member of F -- every graph G with chromatic number n also
      has, in every k-colouring of its edges, a monochromatic copy of some member of F.
    Definitions: [x195_contains_forest Fam] - some member of the family is a forest (X195.v);
      [x195_arrows Host k Fam] - every k-colouring of E(Host) has a monochromatic copy of some
      member (X195.v); [x195_ramsey_number k Fam n] - n is the least such value for the
      complete graphs (X195.v); [x195_k_nice k Fam] - the predicate above (X195.v);
      [mono_copy F col c] - an injective adjacency-preserving copy of F all of whose edges
      get colour c (Extremal.foundations.edge_colourings); [is_forest] and [chi] written
      [X(_)] are coq-graph-theory / GTBase.
    Notes: RE-AUTHORED on 2026-09-23.  The 2026-07-16 encoding was recorded BLOCKED by the
      2026-07-17 faithfulness audit (meta/BLOCKED_RETARGETING_AUDIT.md) because its
      [x195_k_nice] hard-coded two colours and never used its [k] argument.  The definition
      above is the recovered one: the colourings take k values and k-niceness is compared
      against the k-colour Ramsey number, so the [k] parameter is load-bearing.  A family for
      which R_k(F) does not exist is vacuously k-nice, exactly as in the source, where
      "for every G with chi(G) = R_k(F)" presupposes the Ramsey number.
      SECOND-READER READBACK (2026-09-23): both recovered notions were re-fetched from
      arXiv:1708.07369 and match word for word -- R_k(F) is "the smallest integer n for which
      every k-coloring of the edges of K_n yields a monochromatic copy of some F in F", and
      "F is k-nice if for every graph G with chi(G) = R_k(F) and for every k-coloring of E(G)
      there exists a monochromatic copy of some F in F".  [x195_arrows] quantifies over
      colourings into 'I_k, so k is load-bearing in both, which is exactly what the
      2026-07-17 audit found missing in the previous encoding.  The guard [0 < r] is
      redundant (x195_contains_forest already exhibits an index in 'I_r) but harmless. *)
Definition ramsey_nice_forest_family_eventual_statement : Prop :=
  forall (r : nat) (Fam : 'I_r -> sgraph),
    0 < r ->
    x195_contains_forest Fam ->
    exists k0 : nat,
      forall k : nat, k0 <= k -> x195_k_nice k Fam.
