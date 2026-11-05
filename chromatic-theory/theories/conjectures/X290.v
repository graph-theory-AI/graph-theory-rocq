(** * Chromatic.conjectures.X290 -- v2 row: the Ossona de Mendez-Oum-Wood conjecture, the defective chromatic
      number of the H-minor-free graphs is the connected tree-depth of H minus one *)

From GraphTheory Require Import minor.
From GTBase Require Export base.
From Chromatic.conjectures Require Import X218.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X290 statement ********************************************************* *)

(** Reused vocabulary of wave X218 (X218.v): [x218_ctd_at_most] (connected tree-depth at most k, on X194's vertex
    rankings; meta/library_helper_classification.json puts it in the candidate family ctd_at_most with X194's
    identical x194_ctd_at_most, to be unified by a later migration) and [x218_defective_chromatic_class_le] (the
    defective chromatic number of a graph class at most k).  X290 declares no helper of its own. *)

(** Corpus row: studies:std_ossona_de_mendez_oum_wood_defective_chromatic_nu
    Site: none
    Review: none
    English statement: (Ossona de Mendez, Oum and Wood; studies slice of the corpus, record arXiv:1708.02370)
      For every graph H, the defective chromatic number of the class of H-minor-free graphs is ctd(H) - 1, where
      ctd is the connected tree-depth.
    Definitions: [x218_ctd_at_most H k] - 0 < k and some vertex r of H with td(H - r) <= k - 1, i.e. connected
      tree-depth at most k (Chromatic X218.v, on [x194_treedepth_at_most], X194.v: a ranking of the vertices by
      'I_k in which every path between two vertices of the same rank passes a higher rank);
      [x218_defective_chromatic_class_le F k] - one defect bound m, chosen before the graphs, with a k-colouring of
      every graph of the class F in which each vertex has at most m neighbours of its own colour (X218.v);
      [minor G H] - H is a minor of G (coq-graph-theory).
    Notes: encoded as the source states it: Norin, Scott, Seymour and Wood, arXiv:1708.02370v2,
      ClusteredColouring.arXiv2.tex l.161-166 (Conjecture of Ossona de Mendez, Oum and Wood: dchi(M_H) = ctd(H) - 1),
      with the CONNECTED tree-depth of l.147 (the least depth of a rooted tree whose closure contains H; ctd = td
      unless two components attain td(H), then td(H) + 1).  The studies extraction prints td(H) - 1; with ordinary
      tree-depth the row fails at H = 2K_1 (td = 1, while K_1 is 2K_1-minor-free and needs one colour), so the
      source's ctd is meant, as X194 and X218 encode it (CORPUS_FEEDBACK item 74).  "= k - 1" is the bound k - 1
      together with no bound j < k - 1, for H of connected tree-depth exactly k (X218's form for odd minors); the
      subtraction k - 1 never truncates, since x218_ctd_at_most H k requires 0 < k.  The graph with no vertex has
      no rooted tree, so the body is vacuous there; k = 1 forces H = K_1, whose minor-free class holds only the
      graph with no vertex.  The row is classified under minor-theory; it is authored in chromatic-theory, where
      the connected tree-depth and defective-class vocabulary lives (X218), which minor-theory cannot import.
      Literature status: TRUE at the pin.  Ossona de Mendez, Oum and Wood proved the lower bound (l.168); Liu,
      "Defective coloring is perfect for minors" (arXiv:2208.10729), proved the conjecture, as Hickingbotham, Kang,
      Oum, Steiner and Wood report (arXiv:2308.15721v1 main.tex l.156-158, l.167).  Recorded open at the pin, a
      literature item.  Theorem statements read, proofs not verified. *)
Definition ossona_de_mendez_oum_wood_defective_minor_statement : Prop :=
  forall (H : sgraph) (k : nat),
    x218_ctd_at_most H k -> ~ x218_ctd_at_most H k.-1 ->
    x218_defective_chromatic_class_le (fun G : sgraph => ~ minor G H) (k - 1) /\
    (forall j : nat, j.+1 < k -> ~ x218_defective_chromatic_class_le (fun G : sgraph => ~ minor G H) j).
