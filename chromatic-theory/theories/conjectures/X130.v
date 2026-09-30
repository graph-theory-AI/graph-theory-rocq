(** * Chromatic.conjectures.X130 -- v2 planar girth-5 fractional-chromatic row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X130 vocabulary ************************************************)

(** An (a:b)-fold colouring of G: every vertex receives a b-element subset of an
    a-element palette ['I_a], and adjacent vertices receive DISJOINT subsets.
    (This replicates base/Extremal's [bfold_colouring]; the fractional chromatic
    number χ_f(G) = inf a/b over all such colourings, attained/rational for a
    finite G.) *)
Definition x130_bfold_colouring (G : sgraph) (a b : nat) (f : G -> {set 'I_a}) : Prop :=
  (forall v : G, #|f v| = b) /\ (forall x y : G, x -- y -> [disjoint f x & f y]).

(** [x130_frac_chi_le G p q]: the fractional chromatic number of G is ≤ p/q.
    Since χ_f(G) is the infimum of a/b over (a:b)-colourings and this infimum is
    ATTAINED for a finite graph, "χ_f(G) ≤ p/q" is equivalent to the EXISTENCE of
    an (a:b)-colouring with a/b ≤ p/q, i.e. a·q ≤ p·b (cross-multiplied, q>0).
    Soundness holds unconditionally: any such colouring witnesses χ_f(G) ≤ a/b ≤
    p/q; the converse uses attainment (a genuine theorem for finite graphs). *)
Definition x130_frac_chi_le (G : sgraph) (p q : nat) : Prop :=
  exists (a b : nat) (f : G -> {set 'I_a}),
    [/\ (0 < b)%N, @x130_bfold_colouring G a b f & (a * q <= p * b)%N].

(** ** X130 statements ******************************************************)

(** Corpus row: studies:std_dvo_k_mnich_conjecture_fractional_chromatic_numb
    Site: none
    Review: none
    English statement: (Dvorak and Mnich, studies slice of the corpus)
      There are naturals p and q with q > 0 and p < 3q such that every planar finite simple graph of
      girth at least 5 has fractional chromatic number at most p/q; that is, some rational bound
      strictly below 3 holds uniformly for all such graphs.
    Definitions: [x130_frac_chi_le G p q] - there are a, b with b > 0 and an (a:b)-fold colouring
      of G with a*q <= p*b, the cross-multiplied form of a/b <= p/q (this file);
      [x130_bfold_colouring G a b f] - each vertex gets a b-element subset of an a-element palette
      and adjacent vertices get disjoint subsets (this file); [wagner_planar], [girth_geq] (GTBase
      base/theories/base.v).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      source's real constant c < 3 is captured by a RATIONAL p/q < 3, which is faithful because the
      fractional chromatic number of a finite graph is rational and attained. The bound is uniform,
      quantified before the graphs. The degenerate witness p = 0 is impossible, since it would force
      a colouring over an empty palette on a nonempty graph, so the statement has teeth. *)
Definition dvorak_mnich_planar_girth5_fractional_chromatic_statement : Prop :=
  exists p q : nat,
    [/\ (0 < q)%N, (p < 3 * q)%N &
      forall G : sgraph,
        wagner_planar G ->
        girth_geq G 5 ->
        x130_frac_chi_le G p q].
