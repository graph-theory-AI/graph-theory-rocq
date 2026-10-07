(** * GTBase.walk_usage — pair usage along a vertex sequence: a finite Boolean view and an alternating view

    Library migration B28, family [walk-uses] (meta/library_primitives/walk-uses.json).  Two separate public views,
    with no identification between them:

    - [seq_consecutiveb s u v] (an [eqType] carrier): the Boolean form of B3's
      [GTBase.walks_paths.seq_consecutive s u v], the same body with [||] for [\/]: [u] and [v] are adjacent entries
      of [s], in either order.  It reflects [seq_consecutive] ([seq_consecutivebP]) and is MathComp's [infix] test
      ([seq_consecutivebE]).  It asserts no graph edge, path, uniqueness or distinct endpoints: [[::]] and one-entry
      sequences use nothing, a repeated adjacent value [x, x] uses [(x, x)], and the pair closing a cyclic reading is
      not used unless it also occurs adjacently.  GTMisc D7's [walk_uses s p u v] is [seq_consecutiveb (s :: p) u v]
      by conversion.
    - [alt_uses b x p a c] (any [Type], propositional equality): along [x :: p] read with polarity [b] at the first
      step and flipped at every further step, some step is the pair [(a, c)] in its current orientation: from [x] to
      the next entry [y], [x = a] and [y = c] at polarity [true], [y = a] and [x = c] at polarity [false].  It
      asserts no arc or alternating-walk validity and uses no decidable equality, choice or inhabitance.  Infinite
      D4inf4's [walk_uses b x p a c] is its instance at the vertex type of a digraph.

    The views differ: [alt_uses] fixes orientations by parity, [seq_consecutiveb] forgets them.  On an [eqType]
    carrier [alt_uses_consecutive] states the one valid direction (usage implies consecutive occurrence); the
    converse fails, and a wrong orientation is not usage ([alt_uses_true1]).  Not re-exported by GTBase.base; no
    conjecture module is imported. *)

From mathcomp Require Import all_boot.
From GTBase Require Import base walks_paths.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FiniteUsage.
Variable T : eqType.
Implicit Types (s : seq T) (u v x y : T).

(** [u] and [v] are adjacent entries of [s], in either order (Boolean). *)
Definition seq_consecutiveb s u v : bool :=
  ((u, v) \in zip s (behead s)) || ((v, u) \in zip s (behead s)).

Lemma seq_consecutivebP s u v : reflect (seq_consecutive s u v) (seq_consecutiveb s u v).
Proof. exact: orP. Qed.

Lemma seq_consecutivebE s u v : seq_consecutiveb s u v = infix [:: u; v] s || infix [:: v; u] s.
Proof. by rewrite /seq_consecutiveb !mem_zip_behead. Qed.

Lemma seq_consecutiveb_sym s u v : seq_consecutiveb s u v = seq_consecutiveb s v u.
Proof. by rewrite /seq_consecutiveb orbC. Qed.

Lemma seq_consecutiveb_nil u v : seq_consecutiveb [::] u v = false.
Proof. by []. Qed.

Lemma seq_consecutiveb_seq1 x u v : seq_consecutiveb [:: x] u v = false.
Proof. by []. Qed.

Lemma seq_consecutiveb_cons2 x y s u v :
  seq_consecutiveb [:: x, y & s] u v =
  [|| (u == x) && (v == y), (u == y) && (v == x) | seq_consecutiveb (y :: s) u v].
Proof.
rewrite /seq_consecutiveb /= !in_cons !xpair_eqE.
by case: (u == x); case: (v == y); case: (u == y); case: (v == x); rewrite /= ?orbT ?orbF.
Qed.

Lemma seq_consecutiveb_repeat x s : seq_consecutiveb [:: x, x & s] x x.
Proof. by rewrite seq_consecutiveb_cons2 eqxx. Qed.

End FiniteUsage.

Section AlternatingUsage.
Variable T : Type.
Implicit Types (b : bool) (x y a c : T) (p : seq T).

(** Some step of [x :: p], read with polarity [b] flipping at every step, is the pair [(a, c)]. *)
Fixpoint alt_uses b x p a c : Prop :=
  match p with
  | [::] => False
  | y :: p' =>
      ((b = true /\ x = a /\ y = c) \/ (b = false /\ y = a /\ x = c))
      \/ alt_uses (~~ b) y p' a c
  end.

Lemma alt_uses_nil b x a c : ~ alt_uses b x [::] a c.
Proof. by []. Qed.

Lemma alt_uses_cons b x y p a c :
  alt_uses b x (y :: p) a c <->
  ((b = true /\ x = a /\ y = c) \/ (b = false /\ y = a /\ x = c)) \/ alt_uses (~~ b) y p a c.
Proof. exact: iff_refl. Qed.

(** Orientation of the first step: forward at polarity [true], backward at polarity [false]. *)
Lemma alt_uses_head_true x y p : alt_uses true x (y :: p) x y.
Proof. by left; left. Qed.

Lemma alt_uses_head_false x y p : alt_uses false x (y :: p) y x.
Proof. by left; right. Qed.

(** Parity: later steps are read with the flipped polarity. *)
Lemma alt_uses_step b x y p a c : alt_uses (~~ b) y p a c -> alt_uses b x (y :: p) a c.
Proof. by right. Qed.

Lemma alt_uses1 b x y a c :
  alt_uses b x [:: y] a c <-> (b = true /\ x = a /\ y = c) \/ (b = false /\ y = a /\ x = c).
Proof. by split=> [[h | []] | h] //; left. Qed.

(** A single forward step is used exactly in its forward orientation. *)
Lemma alt_uses_true1 x y a c : alt_uses true x [:: y] a c <-> x = a /\ y = c.
Proof. by rewrite alt_uses1; split=> [[[_ h] | [] //] | h]; [| left]. Qed.

(** Usage on a prefix persists on any extension. *)
Lemma alt_uses_cat b x p q a c : alt_uses b x p a c -> alt_uses b x (p ++ q) a c.
Proof.
elim: p b x => [|y p IH] b x //= [h | h]; first by left.
by right; apply: IH.
Qed.

End AlternatingUsage.

(** The one valid cross-view direction, on an [eqType] carrier: an alternating usage of [(a, c)] is a consecutive
    occurrence of [a] and [c] in [x :: p].  The converse fails (orientation and parity are forgotten). *)
Lemma alt_uses_consecutive (T : eqType) (b : bool) (x : T) (p : seq T) (a c : T) :
  alt_uses b x p a c -> seq_consecutiveb (x :: p) a c.
Proof.
elim: p b x => [|y p IH] b x //= [[[_ [-> ->]] | [_ [-> ->]]] | h]; rewrite seq_consecutiveb_cons2.
- by rewrite !eqxx.
- by rewrite !eqxx orbT.
- by rewrite (IH _ _ h) !orbT.
Qed.
