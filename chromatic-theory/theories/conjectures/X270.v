(** * Chromatic.conjectures.X270 -- wave X270: Steinberg's conjecture, Skrekovski's separation-choosability
    conjecture and the Heckman-Thomas conjecture (2026-10-31)

    A three-row wave under the prospective contract of meta/faithfulness_policy.json.  Rows:
    studies:std_steinberg_s_conjecture (every planar graph without 4- and 5-cycles is 3-colourable),
    studies:std_krekovski_conjecture_separation_choosability_of (every planar graph has separation choosability at
    most 3) and studies:std_heckman_thomas_conjecture (every subcubic triangle-free planar graph is fractionally
    8/3-colourable).
    Shared vocabulary: GTBase's [wagner_planar], [subcubic] and [triangle_free] (base.v) and [no_cycle_length]
    (walks_paths.v, the live form of the cycle-lengths family); Chromatic X203's [x203_separation_choosable] and
    X130's [x130_frac_chi_le], used unchanged; coq-graph-theory's chromatic number.
    Local helpers: none.
    Pinned statuses: all three open; literature lines are dated against the corpus pin (graph-conjectures
    b72c5857, 2026-09-23).  The sources are the Mac's deposit coordination/sources/x270-source-mac-20261031 (TeX
    line numbers below).  The grounding certificates are in grounding_X270.v. *)

From GTBase Require Import base.
From Chromatic.conjectures Require Import X130 X203.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X270 statements ********************************************************* *)

(** Corpus row: studies:std_steinberg_s_conjecture
    Site: none
    Review: none
    English statement: (Steinberg 1976, Steinberg's conjecture, studies slice of the corpus)
      Every planar graph without 4- and 5-cycles is 3-colorable.
    Definitions: [wagner_planar G] - G has neither K_5 nor K_(3,3) as a minor, which by Wagner's theorem is
      planarity (GTBase base.v); [no_cycle_length (@edge_rel G) n] - no cycle of G (a duplicate-free closed walk of
      more than two vertices) has exactly n vertices (GTBase walks_paths.v); [χ([set: G])] - the chromatic number
      of G (coq-graph-theory).
    Notes: encoded as stated; pinned status open, but FALSE at the pin.  The studies record cites Dvorak, Kral' and
      Thomas (arXiv:1010.2472v3, 4 March 2016, disk.tex l.339-341: "This conjecture is still open").  Cohen-Addad,
      Hebdige, Kral', Li and Salgado, Steinberg's conjecture is false (arXiv:1604.05108v2, 19 April 2016;
      steinberg.tex l.26-28 the abstract, l.140-143 its main theorem, Theorem 3): there is a planar graph with no
      cycles of length four or five that is not 3-colourable.  That refutes the row as stated; the status
      correction is a separate corpus item, and no kernel proof of the counterexample is given.  The excluded
      cycles are genuine cycles, as in the source: [no_cycle_length] reads ucycles of more than two vertices. *)
Definition steinberg_planar_no_4_5_cycles_three_colourable_statement : Prop :=
  forall G : sgraph, wagner_planar G -> no_cycle_length (@edge_rel G) 4 -> no_cycle_length (@edge_rel G) 5 ->
    χ([set: G]) <= 3.

(** Corpus row: studies:std_krekovski_conjecture_separation_choosability_of
    Site: none
    Review: none
    English statement: (Skrekovski 2001, studies slice of the corpus)
      Every planar graph has separation choosability at most 3.
    Definitions: [wagner_planar G] - G has neither K_5 nor K_(3,3) as a minor (GTBase base.v);
      [x203_separation_choosable G k] - every assignment L of k-element colour sets over any finite palette with
      #|L u :&: L v| <= 1 on every edge uv admits a proper colouring from the lists (Chromatic X203.v, over
      GTBase's [list_colourable]).
    Notes: encoded as stated; pinned status open.  The studies record is Dvorak, Esperet, Kang and Ozeki
      (arXiv:1803.10962v2, 9 October 2020, dp1.tex l.277-278 the definitions, l.300: Skrekovski "conjectured that
      every planar graph has separation choosability at most 3, but this remains open to the best of our
      knowledge").  The original is Skrekovski, A note on choosability with separation for planar graphs (Ars
      Combin. 58 (2001) 169-174; the scanned pages in the deposit): Problem 1 (p.172) asks whether every planar
      graph is (3,1,2)-choosable, where a (p,r) list assignment has |L(v)| >= p and |L(u) cap L(v)| <= p - r on
      adjacent vertices, and (p,q,r)-choosable means q-tuple L-colourable for each of them (p.169); at q = 1 a
      1-tuple colouring is a proper L-colouring.  Lists of exactly 3 colours are equivalent: shrinking each list
      to 3 of its colours keeps the separation condition, and a colouring from the smaller lists is one from the
      larger.  "At most 3" is separation 3-choosability, since separation k-choosability implies (k+1)-choosability
      (drop one colour from each list).  The colours are any finite type: the lists of a finite graph lie in a
      finite set, and every finite set of colours embeds in the positive integers of the source. *)
Definition skrekovski_planar_separation_three_choosable_statement : Prop :=
  forall G : sgraph, wagner_planar G -> x203_separation_choosable G 3.

(** Corpus row: studies:std_heckman_thomas_conjecture
    Site: none
    Review: none
    English statement: (Heckman and Thomas 2006, the Heckman-Thomas conjecture, studies slice of the corpus)
      Every subcubic triangle-free planar graph is fractionally 8/3-colorable.
    Definitions: [wagner_planar G] - G has neither K_5 nor K_(3,3) as a minor (GTBase base.v); [subcubic G] -
      every vertex has at most three neighbours (GTBase base.v); [triangle_free G] - no three mutually adjacent
      vertices (GTBase base.v); [x130_frac_chi_le G p q] - some (a:b)-fold colouring of G with 0 < b and
      a q <= p b, that is a / b <= p / q (Chromatic X130.v).
    Notes: encoded as stated; pinned status open.  The studies record is Dvorak, Lidicky and Postle
      (arXiv:2204.12683v3, 28 March 2025): aic-elevenfour.tex l.240-243 Conjecture 1.2 is this statement,
      l.185-196 define fractional k-colourability, the second of the equivalent conditions being some positive a and
      b with a / b <= k and an assignment of b-subsets of {1, ..., a} disjoint on edges, which is [x130_frac_chi_le
      G 8 3]; l.263-265 (Corollary 1.5) prove 11/4, not 8/3.  The original, Heckman and Thomas, Independent sets in
      triangle-free cubic planar graphs (J. Combin. Theory Ser. B 96 (2006) 253-275; the deposit holds the
      authors' preprint, p.2, text l.63-64), states the same conjecture for maximum degree at most three; the
      3n/8 independence bound it proves is a different statement.  With b > 0 a vertex forces a >= b > 0, and the
      empty graph has a (1:1)-fold colouring, so the source's positive a is implied. *)
Definition heckman_thomas_planar_subcubic_triangle_free_fractional_statement : Prop :=
  forall G : sgraph, wagner_planar G -> subcubic G -> triangle_free G -> x130_frac_chi_le G 8 3.
