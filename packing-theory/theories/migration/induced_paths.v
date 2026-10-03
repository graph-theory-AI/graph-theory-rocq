(** * Packing.migration.induced_paths — B22 certificates: the U9 induced path and the Lovasz path-removal row

    Frozen verbatim at the private baseline (byte-identical at B21 66279eb and C20 97605dd): U9's
    Boolean full-endpoint induced path [is_induced_path] ([spath] / [uniq] / index-based [consec]) and
    the complete row [lovasz_path_removal_statement] (opg:lovasz_path_removal_conjecture).  Since B22
    the live [is_induced_path x y p] is a transparent alias of
    [GTBase.induced_paths.induced_path_between x y p]; U9's [spath] and [consec] stay live and
    unchanged.  The two encodings are not convertible: the certificate is an explicit iff.  Its
    index bridge needs the membership premises that U9's bounded quantifier supplies and the
    duplicate-freeness of the list ([seq_consecutive_index]); no unconditional index bridge is
    claimed.  The row copy keeps the live [k_connected] and [k_connected_on] (unmigrated). *)

From GTBase Require Import base induced_paths.
From Packing.conjectures Require Import U9.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition is_induced_path (G : sgraph) (x y : G) (p : seq G) : Prop :=
  [/\ spath x y p, uniq p
    & {in p &, forall a b : G, a -- b -> consec p a b}].

End Legacy.

Module U9Legacy.

Definition lovasz_path_removal_statement : Prop :=
  exists f : nat -> nat,
    forall (k : nat) (G : sgraph) (x y : G),
      x != y -> k_connected G (f k) ->
      exists p : seq G,
        Legacy.is_induced_path x y p /\
        k_connected_on ([set: G] :\: [set z in p]) k.

End U9Legacy.

(** ** The Boolean encoding and the canonical full-endpoint view *)

(** On a duplicate-free list, U9's index test [consec] is consecutiveness for members. *)
Lemma consec_seq_consecutive (G : sgraph) (p : seq G) (a b : G) :
  uniq p -> a \in p -> b \in p -> consec p a b <-> seq_consecutive p a b.
Proof.
move=> up ap bp; rewrite /consec; have [L R] := seq_consecutive_index up ap bp.
split=> [/orP[/eqP e | /eqP e] | h]; first by apply: R; left.
- by apply: R; right.
- by case: (L h) => e; apply/orP; [left | right]; apply/eqP.
Qed.

Lemma is_induced_path_compat (G : sgraph) (x y : G) (p : seq G) :
  Legacy.is_induced_path x y p <-> is_induced_path x y p.
Proof.
case: p => [|z q].
  by split=> [[sp _ _] | //]; move: sp; rewrite /spath /= ?eqxx.
split.
- case=> sp up cons; move: sp; rewrite /spath => /and4P[_ hz lst srt].
  move/eqP: hz => hz; move/eqP: lst => lst; rewrite /= in hz lst srt.
  do ?split=> //.
  by move=> u v uq vq uv ne; apply/(consec_seq_consecutive up uq vq); exact: cons.
- case=> hz [lst [up [srt c]]]; subst z; split=> //.
    by rewrite /spath /= lst !eqxx srt.
  move=> u v uq vq uv; have ne : u != v by rewrite (sg_edgeNeq uv).
  by apply/(consec_seq_consecutive up uq vq); exact: c.
Qed.

Lemma lovasz_path_removal_statement_compat :
  U9Legacy.lovasz_path_removal_statement <-> lovasz_path_removal_statement.
Proof.
split=> -[f hf]; exists f => k G x y xy kc; have [p [ip kco]] := hf k G x y xy kc;
  by exists p; split=> //; apply/is_induced_path_compat.
Qed.

Print Assumptions consec_seq_consecutive.
Print Assumptions is_induced_path_compat.
Print Assumptions lovasz_path_removal_statement_compat.
