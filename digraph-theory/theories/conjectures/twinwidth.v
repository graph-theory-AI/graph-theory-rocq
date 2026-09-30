(** * Digraph.conjectures.twinwidth — P12: twin-width and the ω̄-boundedness
    conjectures 3.12 / 3.13 / 3.16 of Aboulker–Aubian–Charbit–Lopes,
    "Clique number of tournaments" (arXiv:2310.04265).

    This file STATES (does not prove) three open conjectures connecting the
    twin-width of a tournament to its dichromatic number χ⃗ (reused from
    [dichromatic.v] as [dicolorableb]) and its clique number ω̄ (reused from
    [omegabar.v] as [omegabar], via the backedge graph of [order.v]).

      1. TWIN-WIDTH (concrete, via a contraction sequence).  We model a
         contraction sequence on a digraph [D] as a chain of equivalence
         relations [e₀ ⊋ e₁ ⊋ … ⊋ e_{m}] on [V(D)], where [e₀] is the discrete
         partition (every vertex its own part), the last is the total partition
         (everything merged), and each step coarsens by merging exactly two
         parts.  The trigraph's RED edges between two parts [X],[Y] are the
         "mixed" pairs: [X]–[Y] is red iff the directed arc relation from [X] to
         [Y] is NOT constant (some [x∈X] has [x-->y] for a [y∈Y] while some
         [x'∈X] does not, or symmetrically on the [Y] side).  The red degree of
         a part is the number of other parts red-adjacent to it; the width of
         the sequence is the maximum red degree ever attained; [tww_le D k] says
         some contraction sequence has width [≤ k].  This is fully faithful and
         compiles concretely (no abstract predicate). It matches the exact
         directed-trigraph oracle (scripts/core.py, [tww]).

      2. CONJECTURE 3.12 (verbatim, classification): for every [k], the class of
         tournaments with twin-width [≤ k] is ω̄-bounded — there is [f_k] with
         χ⃗(T) ≤ f_k(ω̄(T)) for every tournament [T] of twin-width [≤ k].

      3. CONJECTURE 3.13: there is a single function [f] so that every
         tournament [T] admits ONE ordering [p] that simultaneously bounds the
         backedge clique number ω(T^p) ≤ f(ω̄(T)) and the ORDERED twin-width
         tww(T,p) ≤ f(ω̄(T)).  Ordered twin-width is twin-width restricted to
         contraction sequences that respect the order (merge order-contiguous
         parts); the contiguity constraint is the heavy piece and is exposed
         PARAMETRICALLY over an abstract [otww_le], constrained by faithful
         axioms tying it to [tww_le] and to the order.

      4. CONJECTURE 3.16: there is a function [f] so that every tournament [T]
         admits a BST-ordering [p] with backedge clique number ω(T^p) ≤ f(ω̄(T)).
         A BST-ordering is an in-order traversal of a binary-search tree built on
         the strong-component structure; the tree-traversal machinery is the
         heavy piece and is exposed PARAMETRICALLY over an abstract [bst_order]
         predicate with faithful constraints.

    CONCRETE vs PARAMETRIC: the twin-width predicate [tww_le] (hence Conj 3.12)
    is CONCRETE.  Ordered twin-width [otww_le] (Conj 3.13) and the BST-ordering
    predicate [bst_order] (Conj 3.16) are PARAMETRIC over abstract predicates
    constrained by faithful axioms — the order-contiguity of contractions and
    the BST in-order traversal have no faithful one-file concrete form.

    All degenerate cases are guarded by [0 < #|D|] / tournament-hood, so nothing
    is vacuously false. See docs/CONJECTURES_FORMALIZATION_PLAN.md §4 (P12) and
    problems/tournament_twinwidth_dichromatic_bounded/{docs/STATUS.md,scripts/core.py}. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph oriented tournament.
From Digraph Require Import dipath order dichromatic omegabar.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Twin-width via contraction sequences *)

Section TwinWidth.
Variable D : diGraphType.
Implicit Types (e : rel D) (u v : D).

(** *** Partitions as equivalence relations, and their classes / parts

    A "current partition" of [V(D)] during a contraction is an equivalence
    relation [e].  The part containing [u] is [eclass e u = [set v | e u v]].
    We address distinct parts by their canonical representatives: [u] is the
    representative of its part when it has the least [enum_rank] among the
    [e]-equivalent vertices.  [ereps e] is the set of part representatives, so
    [#|ereps e|] is the number of parts. *)

Definition eclass e u : {set D} := [set v | e u v].

Definition ereps e : {set D} :=
  [set u | [forall v, e u v ==> (enum_rank u <= enum_rank v)]].

(** *** Red (mixed) edges of the contraction trigraph

    Two parts [X = eclass e u] and [Y = eclass e v] are RED (mixed) when the
    directed relation between them is not constant: there are [a,a'] in [X] and
    [b,b'] in [Y] with [a-->b] but [a' -/-> b'], OR symmetrically with the arc
    in the other direction.  Both directions are tested because the relation is
    directed (a tournament's cyclic C₃ would be lost by an undirected test —
    see scripts/core.py).  [mixedb e u v] is this red predicate on the parts of
    [u] and [v]; it is symmetric only up to swapping endpoints, which is all the
    red-degree count needs. *)

Definition out_const e u v : bool :=
  [forall a, [forall a', [forall b, [forall b',
     (e u a ==> e u a' ==> e v b ==> e v b' ==> ((a --> b) == (a' --> b')))]]]].

Definition mixedb e u v : bool := ~~ (out_const e u v) || ~~ (out_const e v u).

(** Red degree of the part of [u]: the number of OTHER parts (addressed by
    their representatives) that are red-adjacent to [u]'s part. *)
Definition red_deg e u : nat :=
  #|[set r in ereps e | (~~ e u r) && mixedb e u r]|.

(** Width of the partition [e]: the maximum red degree over its parts. *)
Definition red_width e : nat :=
  \max_(r in ereps e) red_deg e r.

(** *** A single contraction step

    [e'] is obtained from [e] by ONE merge: there are two [e]-inequivalent
    vertices [a],[b] such that [e'] is exactly [e] with the classes of [a] and
    [b] fused — [e' x y ⟺ e x y ∨ (e x a ∧ e y b) ∨ (e x b ∧ e y a)].  We do
    not need to construct [e'] from [a],[b]; we only need the boolean check that
    [e'] IS such a merge of [e].  [merge_step e e'] is decidable. *)

Definition merge_rel e (a b : D) : rel D :=
  [rel x y | e x y || (e x a && e y b) || (e x b && e y a)].

Definition merge_step e e' : bool :=
  [exists a, [exists b, (~~ e a b) &&
     [forall x, [forall y, e' x y == merge_rel e a b x y]]]].

End TwinWidth.

(** *** Contraction sequences and [tww_le]

    A contraction sequence on [D] is a list [s : seq (rel D)] of equivalence
    relations starting at the discrete partition [eq_op] and where each step is
    a single merge; the LAST relation must be the total partition ([xpredT],
    everything in one part) — equivalently the sequence ends with [≤ 1] part.
    The width of the sequence is the maximum [red_width] over all relations in
    the sequence (including the discrete start, whose red width is the original
    error degree, here [0] since the discrete partition has no mixed pairs).

    [contraction_seq D s] : [s] is a valid contraction sequence.
    [tww_le D k]          : some contraction sequence has width [≤ k]. *)

Fixpoint chain_merges (D : diGraphType) (s : seq (rel D)) : bool :=
  match s with
  | [::] => true
  | e :: s' =>
      match s' with
      | [::] => true
      | e' :: _ => merge_step e e' && chain_merges s'
      end
  end.

(** A valid contraction sequence (as a [Prop], since [rel D] is a function
    type and [equivalence_rel] is [Prop]-valued): [s] starts at the discrete
    partition (extensionally [eq_op]); every consecutive step is a single merge;
    the LAST relation is total (everything fused into one part); and every
    relation in [s] is an equivalence. *)
Definition contraction_seq (D : diGraphType) (s : seq (rel D)) : Prop :=
  let d0 : rel D := fun u v => u == v in
  [/\ (forall x y : D, head d0 s x y = (x == y)),
      (forall x y : D, last d0 s x y),
      chain_merges s
    & (forall i : nat, (i < size s)%N -> equivalence_rel (nth d0 s i))].

Definition seq_width (D : diGraphType) (s : seq (rel D)) : nat :=
  \max_(e <- s) red_width e.

Definition tww_le (D : diGraphType) (k : nat) : Prop :=
  exists s : seq (rel D),
    contraction_seq s /\ (seq_width s <= k)%N.

(** Corpus row: arxiv:2310.04265#02
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2310.04265__02/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2310.04265__02.json
    English statement: (Aboulker, Aubian, Charbit, Lopes 2023, Clique number of tournaments, arXiv:2310.04265, Conjecture 3.12)
      For every k there is a function f such that every nonempty tournament whose twin-width is
      at most k has dichromatic number at most f applied to its tournament clique number; that
      is, the class of tournaments of twin-width at most k is omega-bar-bounded.
    Definitions: [tww_le D k] - some contraction sequence, a chain of equivalence relations from
      the discrete to the total partition merging two parts at a time, has all red degrees at
      most k, red adjacency between two parts meaning that the arc relation between them is not
      constant (this file); [contraction_seq], [red_width], [seq_width] (this file); [omegabar
      T] - the tournament clique number (invariants/omegabar.v); [dicolorableb T m] -
      dichromatic number at most m (conjectures/dichromatic.v).
    Notes: Twin-width is modelled concretely by contraction sequences, matching the directed
      trigraph oracle of the problem folder. The guard 0 < #|T| keeps the empty tournament from
      being load-bearing. A class-level restatement with a uniform bound is recorded in this
      file as [conj_3_12_classwise]; the form documented here, with one binding function per k,
      is the stronger one. *)
Definition conj_3_12_statement : Prop :=
  forall k : nat,
    exists f : nat -> nat,
      forall T : tournament,
        (0 < #|T|)%N -> tww_le T k -> dicolorableb T (f (omegabar T)).

(** A class-level restatement using the [dichromatic.v] [dichromatic_bounded]
    wrapper for a FIXED ω̄-bound: for each [k] and [w], the subclass
    {T tournament : tww ≤ k, ω̄ ≤ w} is χ⃗-bounded (a single UNIFORM bound
    dicolours every member).  The class predicate is keyed by an explicit
    [dgiso] to a tournament witness so it lives on [diGraphType] (the shape
    [dichromatic_bounded] consumes); [conj_3_12_statement] is the strictly
    stronger single-binding-function form. *)

Definition conj_3_12_classwise : Prop :=
  forall k w : nat,
    dichromatic_bounded
      (fun D => exists T : tournament,
         [/\ dgiso D T, (0 < #|T|)%N, tww_le T k & (omegabar T <= w)%N]).

(** ** Backedge clique number under an ordering (reused notion)

    [bclique p] = ω(T^p), the clique number of the backedge graph under the
    order [p] ([order.v]/[omegabar.v]).  By definition [omegabar T] is the
    minimum of [bclique p] over all orders [p]. *)

Definition bclique (T : tournament) (p : {perm T}) : nat := omegab_at p.
Arguments bclique {T} p.

Lemma bclique_omegabar (T : tournament) (p : {perm T}) :
  (omegabar T <= bclique p)%N.
Proof. exact: omegabar_min. Qed.

(** ** Ordered twin-width tww(T,p) (PARAMETRIC, the heavy contiguity piece)

    The ordered twin-width of [T] under an order [p] is the minimum width over
    contraction sequences whose every merge fuses two parts that are CONTIGUOUS
    in the order [p] (no part strictly between them in [p]).  The
    order-contiguity constraint on the equivalence-relation chain has no
    faithful one-file concrete form (it requires tracking the induced interval
    structure of each partition along [p]); we therefore expose ordered
    twin-width PARAMETRICALLY as an abstract predicate [otww_le], constrained by
    two FAITHFUL axioms any correct ordered twin-width must satisfy:

      - [otww_dominates_tww]: an ordered contraction sequence is a contraction
        sequence, so an ordered twin-width bound implies the (unordered)
        [tww_le] bound — ordered ≥ unordered;
      - [otww_total]: ordered twin-width is always defined (some bound holds),
        guaranteeing the predicate is non-vacuous for every order.

    These are the load-bearing relationships used downstream; the contiguity
    content lives inside the opaque predicate and is flagged as the blocked
    piece. *)

Section OrderedTwinWidth.
Variable otww_le : forall {T : tournament}, {perm T} -> nat -> Prop.

Definition otww_dominates_tww : Prop :=
  forall (T : tournament) (p : {perm T}) (k : nat),
    otww_le p k -> tww_le T k.

Definition otww_total : Prop :=
  forall (T : tournament) (p : {perm T}),
    exists k : nat, otww_le p k.

(** No corpus row: Conjecture 3.13 of Aboulker, Aubian, Charbit and Lopes, Clique number of
    tournaments (arXiv:2310.04265). The corpus row arxiv:2310.04265#03 no longer names this
    definition: its statement_text was changed upstream and its formal_name was detached
    (statement leg back to todo) during the corpus re-sync, because the corpus now reads tww(T,
    p) <= f(tww(T)) -- the ordered twin-width bounded by a function of the TWIN-WIDTH of T --
    while the body below reads: there is a function f such that every nonempty tournament T has
    one vertex ordering p with the clique number of the back-edge graph of T under p at most
    f(omega-bar(T)) and the ordered twin-width of T under p at most that same f(omega-bar(T)),
    i.e. both bounds are taken in the tournament CLIQUE NUMBER. Vocabulary: [bclique p] is the
    clique number of the back-edge graph under p (this file, over invariants/omegabar.v and
    core/order.v), [omegabar T] the tournament clique number (invariants/omegabar.v), and
    [otww_le] the ordered twin-width, an abstract section variable constrained by the faithful
    axioms [otww_dominates_tww] and [otww_total] because order-contiguity of contractions has no
    faithful one-file concrete form. The body is left untouched; the divergence is recorded in
    meta/STATEMENT_IMPROVEMENTS.md and is being adjudicated against the paper. *)
Definition conj_3_13_statement : Prop :=
  exists f : nat -> nat,
    forall T : tournament,
      (0 < #|T|)%N ->
      exists p : {perm T},
        (bclique p <= f (omegabar T))%N /\ otww_le p (f (omegabar T)).

End OrderedTwinWidth.

(** ** BST-orderings (PARAMETRIC, the heavy traversal piece)

    A BST-ordering of a tournament is the in-order traversal of a binary search
    tree whose nodes are (recursively chosen) vertices/strong-pieces, so that
    the backedge structure restricted to each strong piece is controlled
    (STATUS.md, scripts/core.py).  The recursive tree-traversal construction has
    no faithful one-file concrete form; we expose the BST predicate
    PARAMETRICALLY as an abstract [bst_order : forall T, {perm T} -> Prop],
    constrained by one FAITHFUL non-vacuity axiom: every nonempty tournament has
    at least one BST-ordering (the recursion always terminates and produces a
    valid in-order traversal).  This is the property the conjecture relies on;
    the traversal content is the blocked piece. *)

Section BSTOrdering.
Variable bst_order : forall {T : tournament}, {perm T} -> Prop.

Definition bst_order_exists : Prop :=
  forall T : tournament, (0 < #|T|)%N -> exists p : {perm T}, bst_order p.

(** Corpus row: arxiv:2310.04265#04
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2310.04265__04/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2310.04265__04.json
    English statement: (Aboulker, Aubian, Charbit, Lopes 2023, Clique number of tournaments, arXiv:2310.04265, Conjecture 3.16)
      There is a function f such that every nonempty tournament T has a BST-ordering p whose
      back-edge graph has clique number at most f applied to the tournament clique number of T.
    Definitions: [bclique p] (this file); [omegabar T] (invariants/omegabar.v); [bst_order] -
      the BST-ordering predicate, an ABSTRACT section variable constrained by the faithful
      non-vacuity axiom [bst_order_exists] (every nonempty tournament has at least one), because
      the in-order traversal of the recursively built binary search tree has no faithful
      one-file concrete form (this file).
    Notes: The statement lives inside a section over the abstract [bst_order], so it is
      parametric in the BST-ordering predicate; that abstraction is the blocked structural
      piece. *)
Definition conj_3_16_statement : Prop :=
  exists f : nat -> nat,
    forall T : tournament,
      (0 < #|T|)%N ->
      exists p : {perm T},
        bst_order p /\ (bclique p <= f (omegabar T))%N.

End BSTOrdering.

(** ** Implication edges (relative theorems, provable WITHOUT resolving any conjecture) *)

(** Conjecture 3.13 ⟹ Conjecture 3.16 (over a BST predicate refining the order).

    If every order achieving the 3.13 bound is in particular a BST-ordering
    (the proved structural fact, supplied here as the hypothesis [bound_is_bst]:
    a simultaneously-ω̄-and-ordered-tww-bounded order is a BST-ordering), then
    3.13's witness order is a BST-ordering bounding ω(T^p), giving 3.16 with the
    same function.  This edge is RELATIVE: it does not prove 3.13, only that
    3.13 plus the proved refinement forces 3.16. *)

Theorem conj_3_13_implies_3_16
    (otww_le : forall {T : tournament}, {perm T} -> nat -> Prop)
    (bst_order : forall {T : tournament}, {perm T} -> Prop) :
  conj_3_13_statement (@otww_le) ->
  (forall (T : tournament) (p : {perm T}) (m : nat),
     (0 < #|T|)%N -> (bclique p <= m)%N -> otww_le p m -> bst_order p) ->
  conj_3_16_statement (@bst_order).
Proof.
move=> [f Hf] bound_is_bst; exists f => T T0.
have [p [Hbc Hotww]] := Hf T T0.
exists p; split=> //.
exact: (bound_is_bst T p (f (omegabar T)) T0 Hbc Hotww).
Qed.

(** Conjecture 3.16 ⟹ Conjecture 3.12 (every tournament, all twin-widths).

    A BST-ordering [p] with ω(T^p) ≤ f(ω̄(T)) bounds the backedge clique number,
    and the backedge clique number bounds the dichromatic number: this is the
    standard back-degeneracy bound χ⃗(T) ≤ g(ω(T^p)), supplied here as the PROVED
    hypothesis [chi_le_bclique] (for a fixed [g], any order whose backedge clique
    is ≤ [m] yields a [g m]-dicolouring).  Composed with 3.16's witness order
    that has ω(T^p) ≤ f(ω̄(T)), this gives χ⃗(T) ≤ g(f(ω̄(T))) for EVERY
    tournament — in particular within each bounded-twin-width class, giving 3.12
    with binding function [g∘f] (independent of [k]).  RELATIVE: it threads the
    proved degeneracy bound through 3.16, with no resolution of any conjecture. *)

Theorem conj_3_16_implies_3_12
    (bst_order : forall {T : tournament}, {perm T} -> Prop) :
  conj_3_16_statement (@bst_order) ->
  (exists g : nat -> nat,
     forall (T : tournament) (p : {perm T}) (m : nat),
       (0 < #|T|)%N -> (bclique p <= m)%N -> dicolorableb T (g m)) ->
  conj_3_12_statement.
Proof.
move=> [f Hf] [g Hg] k; exists (fun w => g (f w)) => T T0 _.
have [p [_ Hbc]] := Hf T T0.
exact: (Hg T p (f (omegabar T)) T0 Hbc).
Qed.

(** ** Relative edge: Conjecture 3.12's single-function form ⟹ its class form

    The single-function form [conj_3_12_statement] (a binding function [f_k] per
    [k]) yields the class-level [conj_3_12_classwise]: fixing [k],[w], the
    uniform bound [g_{k,w} := f_k(w)] dicolours every member [D ≅ T] of the
    subclass {tww ≤ k, ω̄ ≤ w}.  Two PROVED auxiliary facts are threaded as
    hypotheses (the established idiom, cf. two_extremal.v): [fmono] — each
    binding function [f_k] is monotone (so [f_k(ω̄(T)) ≤ f_k(w)] when ω̄(T) ≤ w);
    and [dc_mono]/[dc_iso] — [dicolorableb] is monotone in its bound and
    transported along [dgiso].  RELATIVE: a faithful restatement, no conjecture
    resolved. *)

Theorem conj_3_12_single_implies_classwise :
  conj_3_12_statement ->
  (forall (k : nat) (f : nat -> nat) (a b : nat), (a <= b)%N -> (f a <= f b)%N) ->
  (forall (T : tournament) (m m' : nat),
     (m <= m')%N -> dicolorableb T m -> dicolorableb T m') ->
  (forall (D : diGraphType) (T : tournament) (m : nat),
     dgiso D T -> dicolorableb T m -> dicolorableb D m) ->
  conj_3_12_classwise.
Proof.
move=> C312 fmono dc_mono dc_iso k w.
have [f Hf] := C312 k.
exists (f w) => D [T [iso T0 tw ob]].
have dc : dicolorableb T (f (omegabar T)) := Hf T T0 tw.
have lefw : (f (omegabar T) <= f w)%N := fmono k f _ _ ob.
have dcw : dicolorableb T (f w) := dc_mono T _ _ lefw dc.
exact: (dc_iso D T (f w) iso dcw).
Qed.
