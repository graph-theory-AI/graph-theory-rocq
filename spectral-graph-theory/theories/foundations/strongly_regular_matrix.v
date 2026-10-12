(** * Spectral.foundations.strongly_regular_matrix -- the adjacency-matrix identity of strongly regular parameters

    Over [int], with the area adjacency matrix [A = adjmx int G] (vertices indexed by [enum_val]), the classical
    identity [A^2 = k I + lam A + mu (J - I - A)] is [strongly_regular_matrix_identity G k lam mu].  For ALL [k lam mu]
    (no guard) it is equivalent to the GTBase counting clauses [strongly_regular_parameters G k lam mu]
    ([strongly_regular_matrix_identityP]); the bridge is [adjmx_sqr_common_nbr]: the [(i, j)] entry of [A^2] counts the
    common neighbours of [enum_val i] and [enum_val j].  [connected_nontrivial_strongly_regular_matrix G] carries the
    same three guards as GTBase's [connected_nontrivial_strongly_regular G] (connected, [0 < k], [k < #|G|.-1]) and is
    equivalent to it ([connected_nontrivial_strongly_regular_matrixP]).  Nothing is said about the unguarded existential
    beyond the parameter-wise identity.  The theory and its proofs were introduced in
    [Spectral.conjectures.grounding_D5] (technique 3), whose qualified names remain as proved wrappers.
    Registry: meta/library_primitives/strongly-regular.json (A33). *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph bij.
From GTBase Require Import base strongly_regular.
From mathcomp Require Import all_algebra perm.
From Spectral Require Import foundations.spectral.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

(** The product of two 0/1 integers is the 0/1 image of the conjunction. *)
Lemma int01_mul (P Q : bool) :
  ((if P then 1 else 0) : int) * (if Q then 1 else 0) = if P && Q then 1 else 0.
Proof. by case: P; case: Q; rewrite ?mul0r ?mul1r ?mulr0. Qed.

(** Counting a predicate through the vertex enumeration. *)
Lemma card_enum_val_pred (G:sgraph) (Q : pred G) :
  #|[set k : 'I_#|G| | Q (enum_val k)]| = #|[set v : G | Q v]|.
Proof.
have -> : [set v : G | Q v]
        = enum_val @: [set k : 'I_#|G| | Q (enum_val k)].
  apply/setP => v; rewrite inE; apply/idP/imsetP.
  - move=> Qv; exists (enum_rank v); last by rewrite enum_rankK.
    by rewrite inE enum_rankK.
  - by move=> [k]; rewrite inE => Qk ->.
by rewrite (card_imset _ (@enum_val_inj _ G)).
Qed.

Lemma card_common_nbr_enum (G:sgraph) (a b : G) :
  #|[set k : 'I_#|G| | (a -- enum_val k) && (enum_val k -- b)]| = #|common_nbr a b|.
Proof.
rewrite (card_enum_val_pred (fun v => (a -- v) && (v -- b))).
suff -> : [set v : G | (a -- v) && (v -- b)] = common_nbr a b by [].
rewrite /common_nbr; apply/setP => v; rewrite !inE.
by rewrite (@sg_sym G v b).
Qed.

(** The [(i, j)] entry of [A^2] is the number of common neighbours of [enum_val i] and [enum_val j]. *)
Lemma adjmx_sqr_common_nbr (G:sgraph) (i j : 'I_#|G|) :
  (adjmx int G *m adjmx int G) i j
   = #|common_nbr (enum_val i) (enum_val j)|%:R.
Proof.
rewrite mxE.
under eq_bigr => k _ do rewrite !mxE int01_mul.
rewrite -big_mkcond.
rewrite (eq_bigr (fun _ => (1%N)%:R : int)); last by move=> k _; rewrite mulr1n.
rewrite -natr_sum sum1dep_card; congr (_ %:R).
by move: (enum_val i) (enum_val j) => a b; exact: card_common_nbr_enum.
Qed.

(** The classical identity [A^2 = k I + lam A + mu (J - I - A)] over [int]. *)
Definition strongly_regular_matrix_identity (G : sgraph) (k lam mu : nat) : Prop :=
  adjmx int G *m adjmx int G
    = k%:R%:M + lam%:R *: adjmx int G
      + mu%:R *: (const_mx 1 - 1%:M - adjmx int G).

Lemma int_natr_inj (a b : nat) : (a%:R = b%:R :> int) -> a = b.
Proof. by move=> /eqP; rewrite eqr_nat => /eqP. Qed.

Lemma strongly_regular_rhs_diag (G:sgraph) (k lam mu:nat) (i:'I_#|G|) :
  (k%:R%:M + lam%:R *: adjmx int G + mu%:R *: (const_mx 1 - 1%:M - adjmx int G)) i i = k%:R.
Proof.
by rewrite !mxE eqxx sg_irrefl mulr0 mulr1n subr0 addr0 mulr0 addr0.
Qed.

Lemma strongly_regular_rhs_off (G:sgraph) (k lam mu:nat) (i j:'I_#|G|) : i != j ->
  (k%:R%:M + lam%:R *: adjmx int G + mu%:R *: (const_mx 1 - 1%:M - adjmx int G)) i j
  = lam%:R * (if enum_val i -- enum_val j then 1 else 0)
    + mu%:R * (if enum_val i -- enum_val j then 0 else 1).
Proof.
move=> nij; rewrite !mxE (negbTE nij) mulr0n add0r subr0.
by case: (enum_val i -- enum_val j); rewrite ?subrr ?subr0.
Qed.

(** For all parameters, the matrix identity is the counting clauses. *)
Lemma strongly_regular_matrix_identityP (G:sgraph) (k lam mu : nat) :
  strongly_regular_matrix_identity G k lam mu <-> strongly_regular_parameters G k lam mu.
Proof.
rewrite /strongly_regular_matrix_identity /strongly_regular_parameters; split.
- move=> Heq; split.
  + move=> v; move: Heq => /matrixP/(_ (enum_rank v) (enum_rank v)).
    rewrite adjmx_sqr_common_nbr strongly_regular_rhs_diag => /int_natr_inj.
    by rewrite enum_rankK /common_nbr setIid.
  + move=> u v uv; have nij : enum_rank u != enum_rank v.
      by rewrite (inj_eq enum_rank_inj) (sg_edgeNeq uv).
    move: Heq => /matrixP/(_ (enum_rank u) (enum_rank v)).
    rewrite adjmx_sqr_common_nbr (strongly_regular_rhs_off _ _ _ nij) !enum_rankK uv.
    by rewrite mulr1 mulr0 addr0 => /int_natr_inj.
  + move=> u v ne nadj; have nij : enum_rank u != enum_rank v.
      by rewrite (inj_eq enum_rank_inj) (negbTE ne).
    move: Heq => /matrixP/(_ (enum_rank u) (enum_rank v)).
    rewrite adjmx_sqr_common_nbr (strongly_regular_rhs_off _ _ _ nij) !enum_rankK (negbTE nadj).
    by rewrite mulr0 mulr1 add0r => /int_natr_inj.
- move=> [rk hlam hmu]; apply/matrixP => i j.
  rewrite adjmx_sqr_common_nbr.
  case: (eqVneq i j) => [->|nij].
  + by rewrite strongly_regular_rhs_diag /common_nbr setIid (rk (enum_val j)).
  + rewrite (strongly_regular_rhs_off _ _ _ nij).
    case: (boolP (enum_val i -- enum_val j)) => [adj|nadj].
    * by rewrite mulr1 mulr0 addr0 (hlam _ _ adj).
    * rewrite mulr0 mulr1 add0r hmu //.
      by apply: contra_neq nij => /enum_val_inj ->.
Qed.

(** The matrix form of GTBase's [connected_nontrivial_strongly_regular], with the same three guards. *)
Definition connected_nontrivial_strongly_regular_matrix (G : sgraph) : Prop :=
  exists k lam mu : nat,
    [/\ connected [set: G], (0 < k)%N /\ (k < (#|G|).-1)%N & strongly_regular_matrix_identity G k lam mu].

Lemma connected_nontrivial_strongly_regular_matrixP (G : sgraph) :
  connected_nontrivial_strongly_regular G <-> connected_nontrivial_strongly_regular_matrix G.
Proof.
split.
- case=> k [lam] [mu] [conn kk P].
  by exists k, lam, mu; split=> //; apply/strongly_regular_matrix_identityP.
- case=> k [lam] [mu] [conn kk /strongly_regular_matrix_identityP P].
  by exists k, lam, mu; split.
Qed.
