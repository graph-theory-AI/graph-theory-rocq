(** * Digraph.foundations.longest_cycles — longest directed cycles (library migration B14)

    [longest_dicycle c] states that [c] is a directed cycle ([Digraph.core.dipath.dicycle]:
    nonempty, duplicate-free, consecutive entries and the closing pair joined by arcs) at least
    as long as every directed cycle of the WHOLE digraph, other components included (registry
    meta/library_primitives/longest-dicycle.json).  [dicycle] is reused unchanged: a singleton
    with a loop and a digon (both arcs) are directed cycles and can be longest, the empty
    sequence and repeated entries are rejected, and length is [size c].  "Longest" is maximum
    length, not inclusion maximality.  No orientation, looplessness, connectivity, symmetry,
    inhabited-carrier or minimum-length premise enters the predicate; in particular B13's
    undirected [seq_longest_cycle] (length greater than two) is a different contract.

    Upstream audit (2026-10-03; MathComp 2.5.0, coq-graph-theory 0.9.7, Digraph core).  Neither
    library names a longest directed cycle of a raw sequence.  The Digraph core supplies
    [dicycle] with [dicycle_rot], [converse] with [converse_arcE]; MathComp supplies [rev_cycle],
    [rev_uniq], the cardinality bound of duplicate-free sequences ([card_uniqP], [max_card]) and
    [ex_maxnP], used for the conditional existence below.

    Specification, every clause proved below:
    - projections: a directed cycle, duplicate-free and nonempty, and no directed cycle is
      longer; the empty sequence is never longest, a singleton is a directed cycle exactly when
      its vertex has a loop;
    - bounds and ties: the length is at most [#|D|]; longest cycles have equal length; a directed
      cycle of the same length as a longest one is longest; a directed cycle strictly longer than
      [c] makes [c] not longest; a Hamiltonian directed cycle ([size c = #|D|]) is longest;
    - invariance under [rot]; reversal gives a longest cycle of the [converse] digraph, and of the
      same digraph under the hypothesis that its arc relation is symmetric, a sufficient
      condition;
    - existence exactly when some directed cycle exists: no witness is chosen by default.
    Grounding: an arcless singleton has no longest cycle; a singleton with a loop is longest; a
    digon of the loopless two-vertex complete digraph is longest; the directed triangle on ['I_3] is
    longest, its reversal is not a directed cycle of it but is longest in the converse; a digon
    of the loopless three-vertex complete digraph is a directed cycle that is not longest. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph dipath.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section LongestDicycle.
Variable D : diGraphType.
Implicit Types (c d : seq D) (x : D).

(** [c] is a directed cycle at least as long as every directed cycle of [D]. *)
Definition longest_dicycle c : Prop :=
  dicycle c /\ forall d, dicycle d -> (size d <= size c)%N.

Lemma longest_dicycle_dicycle c : longest_dicycle c -> dicycle c.
Proof. by case. Qed.

Lemma longest_dicycle_uniq c : longest_dicycle c -> uniq c.
Proof. by case=> /and3P[]. Qed.

Lemma longest_dicycle_size c : longest_dicycle c -> 0 < size c.
Proof. by case=> /and3P[]; case: c. Qed.

Lemma longest_dicycle_max c d : longest_dicycle c -> dicycle d -> size d <= size c.
Proof. by case=> _ mx; apply: mx. Qed.

Lemma longest_dicycle_nil : ~ longest_dicycle [::].
Proof. by case. Qed.

(** A singleton is a directed cycle exactly when its vertex has a loop. *)
Lemma dicycle_seq1 x : dicycle [:: x] = (x --> x).
Proof. by rewrite /dicycle /= !andbT. Qed.

Lemma longest_dicycle_card c : longest_dicycle c -> size c <= #|D|.
Proof. by move/longest_dicycle_uniq/card_uniqP <-; apply: max_card. Qed.

(** Ties: longest cycles have equal length, and a directed cycle of that length is longest. *)
Lemma longest_dicycle_size_eq c d : longest_dicycle c -> longest_dicycle d -> size c = size d.
Proof.
move=> lc ld; apply/eqP; rewrite eqn_leq.
by rewrite (longest_dicycle_max ld (longest_dicycle_dicycle lc))
           (longest_dicycle_max lc (longest_dicycle_dicycle ld)).
Qed.

Lemma longest_dicycle_tie c d :
  longest_dicycle c -> dicycle d -> size d = size c -> longest_dicycle d.
Proof. by move=> lc cd sd; split=> // e ce; rewrite sd; apply: longest_dicycle_max lc ce. Qed.

(** A strictly longer directed cycle rules [c] out. *)
Lemma longest_dicycle_shorter c d : dicycle d -> size c < size d -> ~ longest_dicycle c.
Proof. by move=> cd lt lc; move: (longest_dicycle_max lc cd); rewrite leqNgt lt. Qed.

(** A Hamiltonian directed cycle is longest. *)
Lemma longest_dicycle_hamiltonian c : dicycle c -> size c = #|D| -> longest_dicycle c.
Proof.
move=> cc sc; split=> // d /and3P[_ _ /card_uniqP <-].
by rewrite sc; apply: max_card.
Qed.

Lemma longest_dicycle_rot n c : longest_dicycle (rot n c) <-> longest_dicycle c.
Proof. by rewrite /longest_dicycle dicycle_rot size_rot. Qed.

Lemma longest_dicycle_rotr n c : longest_dicycle (rotr n c) <-> longest_dicycle c.
Proof. exact: longest_dicycle_rot. Qed.

(** Without a directed cycle there is no longest one. *)
Lemma longest_dicycle_none : (forall d, ~~ dicycle d) -> forall c, ~ longest_dicycle c.
Proof. by move=> none c /longest_dicycle_dicycle; apply/negP/none. Qed.

(** On the finite carrier a longest directed cycle exists exactly when a directed cycle does. *)
Lemma longest_dicycle_exists : (exists c, dicycle c) -> exists c, longest_dicycle c.
Proof.
case=> c0 cc0.
pose P n := [exists t : n.-tuple D, dicycle t].
have bnd : forall n, P n -> n <= #|D|.
  move=> n /existsP[t /and3P[_ _ /card_uniqP ut]].
  by rewrite -(size_tuple t) -ut max_card.
have ex : exists n, P n by exists (size c0); apply/existsP; exists (in_tuple c0).
case: (ex_maxnP ex bnd) => n /existsP[t ct] mx.
exists t; split=> // d cd; rewrite size_tuple; apply: mx.
by apply/existsP; exists (in_tuple d).
Qed.

Lemma longest_dicycle_existsP : (exists c, longest_dicycle c) <-> (exists c, dicycle c).
Proof.
split=> -[c h]; last exact: longest_dicycle_exists (ex_intro _ c h).
by exists c; apply: longest_dicycle_dicycle h.
Qed.

End LongestDicycle.

(** ** Reversal: the converse digraph, and symmetric arcs *)

Lemma dicycle_rev_converse (D : diGraphType) (c : seq D) :
  @dicycle (converse D) (rev c) = dicycle c.
Proof. by rewrite /dicycle /nilp size_rev rev_uniq rev_cycle. Qed.

Lemma longest_dicycle_rev_converse (D : diGraphType) (c : seq D) :
  @longest_dicycle (converse D) (rev c) <-> longest_dicycle c.
Proof.
rewrite /longest_dicycle dicycle_rev_converse size_rev.
split=> -[cc mx]; split=> // d cd.
  by rewrite -(size_rev d); apply: mx; exact: (etrans (dicycle_rev_converse d) cd).
have cd' : @dicycle D (rev d) by rewrite -(dicycle_rev_converse (D := D) (rev d)) revK.
by rewrite -(revK d) size_rev; apply: mx.
Qed.

(** Same-digraph reversal under the sufficient hypothesis of a symmetric arc relation. *)
Lemma dicycle_rev (D : diGraphType) (c : seq D) :
  (forall x y : D, (x --> y) = (y --> x)) -> dicycle (rev c) = dicycle c.
Proof.
move=> sym; rewrite /dicycle /nilp size_rev rev_uniq rev_cycle.
by rewrite (@eq_cycle _ (fun x y : D => y --> x) arc) // => x y; rewrite sym.
Qed.

Lemma longest_dicycle_rev (D : diGraphType) (c : seq D) :
  (forall x y : D, (x --> y) = (y --> x)) -> longest_dicycle (rev c) <-> longest_dicycle c.
Proof. by move=> sym; rewrite /longest_dicycle dicycle_rev // size_rev. Qed.

(** ** Grounding *)

Section LongestDicycleGrounding.

(** One vertex without a loop: no directed cycle, hence no longest one. *)
Definition arcless1 : Type := 'I_1.
HB.instance Definition _ := Finite.on arcless1.
HB.instance Definition _ := HasArc.Build arcless1 (fun _ _ : 'I_1 => false).

Lemma longest_dicycle_ground_arcless (c : seq arcless1) : ~ longest_dicycle c.
Proof.
apply: longest_dicycle_none => d; apply/negP => /and3P[nn cd _].
by case: d nn cd => [|x [|y d]].
Qed.

(** One vertex with a loop: the singleton is a longest directed cycle. *)
Definition loop1 : Type := 'I_1.
HB.instance Definition _ := Finite.on loop1.
HB.instance Definition _ := HasArc.Build loop1 (fun _ _ : 'I_1 => true).

Lemma longest_dicycle_ground_loop : longest_dicycle ([:: ord0] : seq loop1).
Proof. by apply: longest_dicycle_hamiltonian; rewrite // card_ord. Qed.

(** The loopless complete digraphs on two and three vertices. *)
Definition kd2 : Type := 'I_2.
HB.instance Definition _ := Finite.on kd2.
HB.instance Definition _ := HasArc.Build kd2 (fun u v : 'I_2 => u != v).

Definition kd3 : Type := 'I_3.
HB.instance Definition _ := Finite.on kd3.
HB.instance Definition _ := HasArc.Build kd3 (fun u v : 'I_3 => u != v).

(** A digon is a longest directed cycle of the two-vertex digraph ... *)
Lemma longest_dicycle_ground_digon : longest_dicycle ([:: ord0; ord_max] : seq kd2).
Proof. by apply: longest_dicycle_hamiltonian; rewrite // card_ord. Qed.

(** ... while in the three-vertex digraph a digon is a directed cycle that is not longest. *)
Lemma longest_dicycle_ground_shorter :
  dicycle ([:: ord0; ord_max] : seq kd3) /\ ~ longest_dicycle ([:: ord0; ord_max] : seq kd3).
Proof.
split; first by [].
by apply: (@longest_dicycle_shorter _ _ ([:: ord0; Ordinal (isT : 1 < 3); ord_max] : seq kd3)).
Qed.

(** The directed triangle on ['I_3] ([v = u + 1 mod 3]) is longest; its reversal is not a directed
    cycle of it but is a longest directed cycle of the converse. *)
Definition dtri : Type := 'I_3.
HB.instance Definition _ := Finite.on dtri.
HB.instance Definition _ := HasArc.Build dtri (fun u v : 'I_3 => (v : nat) == u.+1 %% 3).

Lemma longest_dicycle_ground_triangle :
  let c : seq dtri := [:: ord0; Ordinal (isT : 1 < 3); ord_max] in
  [/\ longest_dicycle c, ~~ dicycle (rev c) & @longest_dicycle (converse dtri) (rev c)].
Proof.
move=> c; have lc : longest_dicycle c by apply: longest_dicycle_hamiltonian; rewrite // card_ord.
by split=> //; apply/longest_dicycle_rev_converse.
Qed.

End LongestDicycleGrounding.
