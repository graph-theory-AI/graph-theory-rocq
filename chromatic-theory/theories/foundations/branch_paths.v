(** * Injective branch maps with separate connecting paths

    [branch_paths_at_least G H ell] is the exact weak branch-path contract
    used by X177, X185 and X186. Each oriented edge of H has its own existential
    tail path in G. The tail excludes its starting vertex and includes its end,
    so [size p] counts edges. Internal path vertices avoid all branch vertices.
    There is no inducedness, disjointness between different paths, reversal
    coherence, or simultaneous supplied path map. In particular this predicate
    is not a definition of induced subdivision; the existing blocked readings
    of those three statements are not repaired by this library migration.

    The upstream path/uniq primitives provide this exact representation. No
    stronger minor or subdivision structure is substituted for these clauses. *)
From GTBase Require Import base.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition branch_paths_at_least (G H : sgraph) (ell : nat) : Prop :=
  exists branch : H -> G,
    injective branch /\
    forall x y : H,
      x -- y ->
      exists p : seq G,
        [/\ path (--) (branch x) p,
            last (branch x) p = branch y,
            ell <= size p,
            uniq (branch x :: p) &
            forall z : G,
              z \in p -> z != branch y -> forall u : H, z != branch u].

Lemma branch_paths_at_leastW (G H : sgraph) (ell k : nat) :
  k <= ell -> branch_paths_at_least G H ell -> branch_paths_at_least G H k.
Proof.
move=> kle [br [inj paths]]; exists br; split=> // x y xy.
case: (paths x y xy) => p [pth endp lenp uqp avoid].
exists p; split=> //; exact: leq_trans kle lenp.
Qed.

(** The zero-bound view keeps precisely the four path clauses used by X186. *)
Lemma branch_paths_zeroE (G H : sgraph) :
  branch_paths_at_least G H 0 <->
  exists branch : H -> G,
    injective branch /\
    forall x y : H,
      x -- y ->
      exists p : seq G,
        [/\ path (--) (branch x) p,
            last (branch x) p = branch y,
            uniq (branch x :: p) &
            forall z : G,
              z \in p -> z != branch y -> forall u : H, z != branch u].
Proof.
split=> -[br [inj paths]]; exists br; split=> // x y xy.
- case: (paths x y xy) => p [pth endp _ uqp avoid].
  by exists p; split.
- case: (paths x y xy) => p [pth endp uqp avoid].
  by exists p; split.
Qed.

Lemma branch_paths_card (G H : sgraph) (ell : nat) :
  branch_paths_at_least G H ell -> #|H| <= #|G|.
Proof. by case=> br [inj _]; exact: (@leq_card _ _ br inj). Qed.

Lemma branch_paths_empty_pattern (G : sgraph) (ell : nat) :
  branch_paths_at_least G 'K_0 ell.
Proof.
have absurd : forall x : 'I_0, False by move=> x; have := ltn_ord x; rewrite ltn0.
exists (fun x => False_rect G (absurd x)); split.
- by move=> x; case: (absurd x).
- by move=> x; case: (absurd x).
Qed.

Lemma not_branch_paths_empty_host (H : sgraph) (x : H) (ell : nat) :
  ~ branch_paths_at_least 'K_0 H ell.
Proof.
case=> br _; have := ltn_ord (br x); by rewrite ltn0.
Qed.

Lemma branch_paths_edgelessE (G H : sgraph) (ell : nat) :
  (forall x y : H, ~~ (x -- y)) ->
  (branch_paths_at_least G H ell <-> exists br : H -> G, injective br).
Proof.
move=> noedges; split; first by case=> br [inj _]; exists br.
case=> br inj; exists br; split=> // x y xy.
by move: (noedges x y); rewrite xy.
Qed.

(** A supplied injective edge-preserving map gives direct paths of one edge.
    Extra host edges are permitted. *)
Lemma branch_paths_of_embedding (G H : sgraph) (br : H -> G) :
  injective br ->
  (forall x y : H, x -- y -> br x -- br y) ->
  branch_paths_at_least G H 1.
Proof.
move=> inj edges; exists br; split=> // x y xy.
have edge : br x -- br y := edges x y xy.
have neq : br x != br y by apply: contraTneq edge => ->; rewrite sgP.
exists [:: br y]; split=> //=.
- by rewrite edge.
- by rewrite in_cons in_nil orbF neq.
- move=> z; rewrite mem_seq1 => /eqP->; by rewrite eqxx.
Qed.

Lemma branch_paths_refl (G : sgraph) : branch_paths_at_least G G 1.
Proof. by apply: (@branch_paths_of_embedding G G id); [exact: inj_id | move=> x y]. Qed.
