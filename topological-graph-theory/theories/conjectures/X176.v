(** * Topological.conjectures.X176 -- v2 cone crossing asymptotic row *)

From GTBase Require Export base.
From Topological.foundations Require Import crossing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X176 vocabulary ***********************************************)

Definition x176_cone_rel (G : sgraph) : rel (option G) :=
  fun x y =>
    match x, y with
    | Some u, Some v => u -- v
    | Some _, None | None, Some _ => true
    | None, None => false
    end.

Lemma x176_cone_rel_sym (G : sgraph) : symmetric (@x176_cone_rel G).
Proof. by move=> [x|] [y|] //=; rewrite sg_sym. Qed.

Lemma x176_cone_rel_irrefl (G : sgraph) : irreflexive (@x176_cone_rel G).
Proof. by move=> [x|] //=; rewrite sg_irrefl. Qed.

Definition x176_cone (G : sgraph) : sgraph :=
  SGraph (@x176_cone_rel_sym G) (@x176_cone_rel_irrefl G).

Definition x176_simple_cone_crossing_value (k n : nat) : Prop :=
  exists G : sgraph,
    is_crossing_number G k /\
    is_crossing_number (x176_cone G) n /\
    forall (H : sgraph) (m : nat),
      is_crossing_number H k ->
      is_crossing_number (x176_cone H) m ->
      n <= m.

Definition x176_target (k : nat) : nat :=
  k + sqrt_ceil (sqrt_ceil (2 * k ^ 3)).

Definition x176_abs_diff (f g : nat -> nat) (k : nat) : nat :=
  if f k <= g k then g k - f k else f k - g k.

Definition x176_cone_crossing_asymptotic (f : nat -> nat) : Prop :=
  little_o_nat (x176_abs_diff f x176_target) x176_target.

(** ** X176 statements *****************************************************)

(** Corpus row: arxiv:1608.07680#02
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1608.07680__02/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1608.07680__02.json
    English statement: (Alfaro, Arroyo, Derunar, Mohar, arXiv:1608.07680, "Conjecture on
      f_s(k) asymptotics")
      Corpus claim: f_s(k) = k + sqrt(2) * k^(3/4) * (1 + o(1)), where f_s(k) is the MAXIMUM
      of cr(cone(G)) over simple graphs G with cr(G) = k.  Back-translation of the Rocq body:
      there is a function f from naturals to naturals such that for every k some simple graph
      G has split-crossing number k whose cone has split-crossing number f(k), and f(k) is
      MINIMAL among the cone crossing numbers of all graphs of split-crossing number k; and
      the absolute difference between f and the target k + ceil-sqrt(ceil-sqrt(2 * k^3)) is
      little-o of that target.
    Definitions: [x176_cone G] - the cone over G: one new vertex joined to every vertex of G
      (this file); [x176_simple_cone_crossing_value k n] - the extremal predicate described
      above (this file); [x176_target k] - the root-free integer rendering
      k + ceil-sqrt(ceil-sqrt(2 * k^3)) of k + sqrt(2) * k^(3/4) (this file, on
      [sqrt_ceil], base/theories/asymptotics.v); [x176_abs_diff] - truncated absolute
      difference of two nat functions (this file); [little_o_nat f g] - for all positive
      rationals a/b, eventually b * f(n) <= a * g(n) (base/theories/asymptotics.v);
      [is_crossing_number] - the split-planarization crossing number
      (topological-graph-theory/theories/foundations/crossing.v).
    Notes: BLOCKED - recorded by the 2026-07-17 faithfulness audit
      (meta/BLOCKED_RETARGETING_AUDIT.md), which found a double weakening.  (1) MIS-QUANTIFIED
      EXTREMAL: the paper's f_s(k) is the MAXIMUM of cr(cone G) over graphs with cr(G) = k
      (worst-case cone blow-up; f_s(1) = 3 = cr(K6) = cr(cone K5)), but
      [x176_simple_cone_crossing_value] pins the value by [forall H m, is_cr H k ->
      is_cr (cone H) m -> n <= m], i.e. the MINIMUM cone crossing number over that class -
      the wrong extremum, so the encoded quantity is not f_s.  (2) The underlying crossing
      number is the split-planarization PROXY of crossing.v, not the drawing crossing number.
      Additionally the "simple graph" restriction of the paper is automatic here (sgraph is
      simple and loopless) and the irrational constant sqrt(2) * k^(3/4) is approximated by
      an integer ceiling expression, which shifts the target by a bounded amount but is only
      claimed up to little-o of the target itself. *)
Definition simple_cone_crossing_function_asymptotic_statement : Prop :=
  exists f : nat -> nat,
    (forall k : nat, x176_simple_cone_crossing_value k (f k)) /\
    x176_cone_crossing_asymptotic f.
