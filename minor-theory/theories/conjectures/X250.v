(** * Minor.conjectures.X250 -- v2 duplicate polynomial expansion / twin-width row *)

From Minor.conjectures Require Import X220.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Corpus row: arxiv:2004.14789#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2004.14789__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2004.14789__00.json
    English statement: (Bonnet, Kim, Thomasse and Watrigant 2020, informal conjecture in "Twin-width I: tractable FO model checking", arXiv:2004.14789)
      All classes of polynomial expansion may also have bounded twin-width. The Rocq body is
      literally the X220 statement of the same question in arXiv:2006.09877 ("Twin-width II"),
      reused as a synonym so that this duplicate corpus row cannot drift from it: for every
      class C of finite simple graphs with polynomial expansion (one polynomial p with natural
      coefficients such that every r-shallow minor H of a member of C has at most p(r) times
      the number of vertices of H edges) there is a number d bounding the twin-width of every
      member of C.
    Definitions: [polynomial_expansion_bounded_twin_width_statement] - the X220 encoding
      (X220.v), over [x220_polynomial_expansion C] (one polynomial for every member, depth and
      shallow minor; X220.v, with [x220_shallow_minor G H r] from Minor.foundations
      shallow_minors.v) and [x220_twin_width_le G d] (a sequence of merges from the partition
      into singletons down to at most one part, along which every part has at most d red
      neighbours; X220.v).
    Notes: the source states the question as a remark ("As far as we know, all classes of
      polynomial expansion may also have bounded twin-width"). The corpus relation e069
      (same_conjecture, confirmed) identifies this row with arxiv:2006.09877#01 (X220.v,
      polynomial_expansion_bounded_twin_width_statement): same hypothesis, same conclusion.
      X220's Notes explain the edge-density form of polynomial expansion and the partition form
      of contraction sequences. Corpus status: open (pinned review, 2026-05-15). *)
Definition polynomial_expansion_bounded_twin_width_duplicate_statement : Prop :=
  polynomial_expansion_bounded_twin_width_statement.
