(** * Extremal.conjectures.implications_X215 -- corpus relation edges unlocked by wave X215.

    The X215 rows own exactly one confirmed [implies] relation of
    meta/corpus_relations.json with both endpoints formalised, namely e239
    (bm:bm-033 => bm:bm-039, Erdos-Sos implies the Burr-Erdos tree Ramsey bound).
    It is discharged below as a Qed-closed relative theorem, so the edge is
    recorded with status=verified.

    The remaining X215 rows (bm-034 even-cycle Turan, bm-037 and bm-038, both
    BLOCKED) are endpoints of no confirmed corpus relation. *)

From GTBase Require Import base.
From Stdlib Require Import Lia.
From Extremal.foundations Require Import edge_colourings.
From Extremal.conjectures Require Import X195 X215.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The textbook reduction: in a 2-colouring of K_{2k} one colour class carries
    at least half of the 'C(2k,2) = k(2k-1) edges, which already exceeds the
    Erdos-Sos threshold n(k-1)/2 = 2k(k-1)/2 for n = 2k. *)
Theorem erdos_sos_implies_burr_erdos_tree_ramsey :
  erdos_sos_tree_embedding_statement -> burr_erdos_tree_ramsey_statement.
Proof.
move=> ES T k N tT eT vT k0 -> col.
have bin2_double : forall m : nat, 'C(2 * m, 2) = m * (2 * m).-1.
  by move=> m; rewrite bin2 mul2n -doubleMl doubleK.
have arith : forall m : nat, 0 < m -> 2 * m * m < m * (2 * m).-1 + 2 * m.
  case=> // j _.
  have -> : (2 * j.+1).-1 = (2 * j).+1 by rewrite mulnS.
  by apply/ltP; rewrite -!plusE -!multE; lia.
have [c Hc] := majority_colour col.
rewrite card_edge_Kn bin2_double in Hc.
have cardV : #|colour_class col (pred1 c)| = 2 * k by rewrite card_ord.
have HG : #|colour_class col (pred1 c)| * k
        < 2 * #|E(colour_class col (pred1 c))|
          + #|colour_class col (pred1 c)|.
  rewrite cardV.
  apply: leq_trans (_ : k * (2 * k).-1 + 2 * k <= _); last by rewrite leq_add2r.
  exact: (arith k k0).
by exists c; apply/mono_copyP; exact: (ES _ _ _ tT eT vT HG).
Qed.

(*@EDGE from=erdos_sos_tree_embedding_statement to=burr_erdos_tree_ramsey_statement kind=implies status=verified proof=erdos_sos_implies_burr_erdos_tree_ramsey cite="gc:e239" *)

Print Assumptions erdos_sos_implies_burr_erdos_tree_ramsey.

(** ** Wave-V vocabulary equivalence (2026-09-24) ************************

    meta/X211-X229_faithfulness_audit.md records that [x195_arrows] /
    [x195_ramsey_number] (X195, a FAMILY of targets and [k] colours) strictly
    subsume [x215_arrows] / [x215_ramsey_number] (X215, the diagonal two-colour
    arrow) -- written in the same package on the same day.  The instance is
    [x215_arrows N k = x195_arrows 'K_N 2 (fun _ : 'I_1 => 'K_k)] "modulo the
    colour type": X215 colours the edges with [bool], X195 with [['I_k]].  The
    lemmas below make that precise, so that a later pass can delete the X215
    vocabulary and rewrite its two statements with [x195_arrows].

    No statement body is changed. *)

(** The two-element colour type as [['I_2]] and back. *)
Definition b2i2 (b : bool) : 'I_2 := @Ordinal 2 b (leq_b1 b).
Definition i22b (i : 'I_2) : bool := (i : nat) == 1.

Lemma b2i2K : cancel b2i2 i22b.
Proof. by case. Qed.

Lemma i22bK : cancel i22b b2i2.
Proof. by move=> i; apply/val_inj; case: i => -[|[|m]]. Qed.

(** The diagonal two-colour arrow is the [k = 2], one-member-family instance of
    the X195 arrow relation. *)
Lemma x215_arrows_equiv_x195_arrows (N k : nat) :
  x215_arrows N k <-> x195_arrows 'K_N 2 (fun _ : 'I_1 => 'K_k).
Proof.
split=> H col.
- have [c Hc] := H (fun e => i22b (col e)).
  exists ord0, (b2i2 c); case: Hc => emb [inj hom mono].
  exists emb; split=> // x y xy.
  by rewrite -[col _]i22bK (mono _ _ xy).
- have [i [c Hc]] := H (fun e => b2i2 (col e)).
  exists (i22b c); case: Hc => emb [inj hom mono].
  exists emb; split=> // x y xy.
  by rewrite -[col _]b2i2K (mono _ _ xy).
Qed.

(** Consequently the two "N is the Ramsey number" wrappers agree as well. *)
Lemma x215_ramsey_number_equiv_x195_ramsey_number (k N : nat) :
  x215_ramsey_number k N <-> x195_ramsey_number 2 (fun _ : 'I_1 => 'K_k) N.
Proof.
split=> [[arrN min]|[arrN min]]; split.
- by apply/x215_arrows_equiv_x195_arrows.
- by move=> M MN /x215_arrows_equiv_x195_arrows; exact: min.
- by apply/x215_arrows_equiv_x195_arrows.
- by move=> M MN; move/x215_arrows_equiv_x195_arrows; exact: min.
Qed.

Print Assumptions x215_arrows_equiv_x195_arrows.
Print Assumptions x215_ramsey_number_equiv_x195_ramsey_number.
