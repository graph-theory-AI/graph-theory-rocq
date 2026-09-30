(** * Chromatic.foundations.chi_bounding -- polynomial chi-bounding wrappers (WP4b)

    The chi-boundedness rows of waves X213 and X218 all measure a class of finite
    simple graphs by ONE bounding function of the clique number.  Two wrappers are
    shared here instead of being re-encoded in each conjecture file:

      [chi_bounded_class F]  -- some [f : nat -> nat] bounds chi by f(omega) on F;
      [poly_chi_bounded F]   -- some [c], [d] bound chi by c * omega^d on F,
                                the "polynomially chi-bounded" of the sources.

    Both quantify the bounding data BEFORE the graphs of the class, which is the
    intended reading of "the class is (polynomially) chi-bounded"; a per-graph
    choice would be vacuous.  Neither notion exists in coq-graph-theory or in
    GTBase; [U8.v] owns a [chi_bounded] with the same meaning as
    [chi_bounded_class] (see the note below) and is kept as the citable name of
    the Gyarfas-Sumner row. *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A class [F] of graphs is chi-bounded: one function of the clique number
    bounds the chromatic number over the whole class.  (Definitionally the same
    shape as [U8.chi_bounded]; that name stays the citable one of the
    Gyarfas-Sumner corpus row, this one is the reusable wrapper.) *)
Definition chi_bounded_class (F : sgraph -> Prop) : Prop :=
  exists f : nat -> nat,
    forall G : sgraph, F G -> χ([set: G]) <= f (ω([set: G])).

(** A class [F] is POLYNOMIALLY chi-bounded: the bounding function may be taken
    of the form [t |-> c * t ^ d].  Over the naturals this is exactly "bounded by
    a polynomial in omega", since every polynomial with natural coefficients of
    degree [d] is dominated by (sum of coefficients) * t^d for t >= 1, and the
    t = 0 case is covered because [0 ^ 0 = 1]. *)
Definition poly_chi_bounded (F : sgraph -> Prop) : Prop :=
  exists c d : nat,
    forall G : sgraph, F G -> χ([set: G]) <= c * ω([set: G]) ^ d.

(** ** Sanity lemmas ******************************************************)

(** Non-vacuity: the class of graphs with at most one vertex is polynomially
    chi-bounded ([c = 1], [d = 0]); the witness is concrete, not the empty class. *)
Lemma poly_chi_bounded_small : poly_chi_bounded (fun G : sgraph => #|G| <= 1).
Proof.
exists 1, 0 => G le1; rewrite expn0 muln1.
by apply: leq_trans (leq_chi _) _; rewrite cardsT.
Qed.

(** Structural law: a polynomial bound is a bound. *)
Lemma poly_chi_boundedW (F : sgraph -> Prop) :
  poly_chi_bounded F -> chi_bounded_class F.
Proof. by case=> c [d] H; exists (fun t => c * t ^ d). Qed.

(** Both notions are hereditary along class inclusion. *)
Lemma poly_chi_bounded_sub (F F' : sgraph -> Prop) :
  (forall G, F G -> F' G) -> poly_chi_bounded F' -> poly_chi_bounded F.
Proof. by move=> sub [c [d H]]; exists c, d => G FG; apply: H; apply: sub. Qed.

(** Arithmetic helper: a base of at most one stays at most one under powers
    (the [d = 0] corner uses [0 ^ 0 = 1]). *)
Lemma expn_leq1 (m d : nat) : m <= 1 -> m ^ d <= 1.
Proof.
rewrite leq_eqVlt ltnS leqn0 => /orP[/eqP->|/eqP->]; first by rewrite exp1n.
by case: d => [|d']; rewrite ?expn0 // exp0n.
Qed.

(** Guard has teeth: a class on which the chromatic number is unbounded while
    the clique number stays at most one is NOT polynomially chi-bounded, so the
    wrapper really constrains the class (it is not satisfied by every class). *)
Lemma not_poly_chi_bounded_of_unbounded (F : sgraph -> Prop) :
  (forall n : nat, exists G : sgraph,
      [/\ F G, ω([set: G]) <= 1 & n < χ([set: G])]) ->
  ~ poly_chi_bounded F.
Proof.
move=> unb [c [d H]]; have [G [FG wle clt]] := unb c.
have wle1 := expn_leq1 d wle.
have : χ([set: G]) <= c.
  by apply: leq_trans (H G FG) _; rewrite -{2}(muln1 c) leq_mul2l wle1 orbT.
by rewrite leqNgt clt.
Qed.

(** ** Shared helpers for the chi-bounding edges (wave X218/X65/X66 edge pass)

    Four reusable facts, none of which exists in coq-graph-theory or GTBase:

      [chi_le_palette]        -- a proper colouring into a finite palette [C]
                                 bounds [chi] by [#|C|];
      [chi_le_choosable]      -- a [k]-choosable graph is [k]-colourable
                                 (constant lists), so [chi <= k];
      [omega_le2_triangle_free] -- a triangle-free graph has clique number <= 2;
      [horner_nat_dom]        -- HORNER DOMINATION: a coefficient list evaluated
                                 by Horner at [t >= 1] is at most (sum of the
                                 coefficients) * t ^ (degree).  This is the
                                 arithmetic bridge between the two encodings of
                                 "polynomially chi-bounded" (an arbitrary
                                 coefficient list, X3.v's [x3_poly_eval], versus
                                 the normal form [c * t ^ d] of
                                 [poly_chi_bounded]); the graph-level conversion
                                 built on it lives in [poly_forms.v]. *)

(** A proper colouring of [G] by a finite palette [C] bounds [chi] by [#|C|].
    The colour classes are the [preim_partition] of the colouring map; each is
    stable exactly because the map is proper, and there are at most [#|C|] of
    them. *)
Lemma chi_le_palette (G : sgraph) (C : finType) (f : G -> C) :
  (forall x y : G, x -- y -> f x != f y) -> χ([set: G]) <= #|C|.
Proof.
move=> hf.
pose P := preim_partition f [set: G].
have hp : coloring P [set: G].
  apply/andP; split; first exact: preim_partitionP.
  apply/forall_inP=> A /imsetP[x _ ->]; apply/stableP.
  move=> y z; rewrite !inE /= => /eqP hy /eqP hz.
  by apply/negP=> hyz; have := hf y z hyz; rewrite -hy -hz eqxx.
apply: leq_trans (color_bound hp) _.
pose fiber c := [set x : G | c == f x].
have hsub : P \subset [set fiber c | c in [set: C]].
  apply/subsetP=> A /imsetP[x _ ->]; apply/imsetP.
  exists (f x); first by rewrite inE.
  by apply/setP=> y; rewrite /fiber !inE.
apply: leq_trans (subset_leq_card hsub) _.
by have := leq_imset_card fiber [set: C]; rewrite cardsT.
Qed.

(** A [k]-choosable graph is [k]-colourable: run choosability on the CONSTANT
    list assignment [L v = 'I_k]. *)
Lemma chi_le_choosable (G : sgraph) (k : nat) : choosable G k -> χ([set: G]) <= k.
Proof.
move=> ch.
have hL : forall v : G, k <= #|[set: 'I_k]| by move=> v; rewrite cardsT card_ord.
have [f [_ hf]] := ch 'I_k (fun _ => [set: 'I_k]) hL.
by have := chi_le_palette hf; rewrite card_ord.
Qed.

(** A triangle-free graph has clique number at most two: a clique on three
    vertices is a triangle. *)
Lemma omega_le2_triangle_free (G : sgraph) : triangle_free G -> ω([set: G]) <= 2.
Proof.
move=> tf; case: omegaP => K KM.
rewrite leqNgt; apply/negP => /card_gt2P [x [y [z [[xK yK zK] [xy yz zx]]]]].
have cl := maxclique_clique KM.
by apply: (tf x y z); apply: cl.
Qed.

(** ** Horner domination (F4) *******************************************)

(** Horner evaluation of a coefficient list, the shape of [X3.x3_poly_eval]
    (kept here as a [foldr] so that this foundation file depends on no
    conjecture file; [poly_forms.v] identifies the two). *)
Definition horner_nat (p : seq nat) (x : nat) : nat :=
  foldr (fun a r => a + x * r) 0 p.

(** F4: for [t >= 1] a Horner evaluation is dominated by the normal form
    (sum of the coefficients) * t ^ (size p - 1).  The guard [1 <= t] is
    necessary: at [t = 0] the evaluation is the constant coefficient while the
    right-hand side vanishes as soon as [p] has two or more coefficients. *)
Lemma horner_nat_dom (p : seq nat) (t : nat) :
  1 <= t -> horner_nat p t <= (\sum_(i <- p) i) * t ^ (size p).-1.
Proof.
move=> t1; elim: p => [|a p IH] //=.
have ht k : 1 <= t ^ k by rewrite expn_gt0 t1.
case: p IH => [|b q] IH /=.
  by rewrite muln0 addn0 big_cons big_nil addn0 expn0 muln1.
rewrite big_cons mulnDl; apply: leq_add.
  by rewrite -{1}(muln1 a) leq_mul2l ht orbT.
apply: leq_trans (leq_mul (leqnn t) IH) _.
by rewrite mulnCA -expnS.
Qed.

Print Assumptions poly_chi_bounded_small.
Print Assumptions poly_chi_boundedW.
Print Assumptions not_poly_chi_bounded_of_unbounded.

Print Assumptions chi_le_palette.
Print Assumptions chi_le_choosable.
Print Assumptions omega_le2_triangle_free.
Print Assumptions horner_nat_dom.
