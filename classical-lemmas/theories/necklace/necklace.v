(** * ClassicalLemmas.necklace — Alon's Splitting Necklace Theorem

    Reference: F. Meunier, "Simplotopal maps and necklace splitting",
    Discrete Mathematics 323 (2014) 14–26 (Theorem 3.1), in the classical
    "multiple of [q]" form of Alon (1987).

    A necklace is [n] beads in a row, bead [i] having type [c i : 'I_t].  A
    [q]-splitting is an assignment [a : 'I_n -> 'I_q] of beads to thieves; a
    *cut* is a position [i] with [a i != a i.+1] (this is exactly "cut the
    necklace into intervals and distribute the intervals").  The theorem says
    that if every type count is a multiple of [q], a fair splitting with at
    most [t*(q-1)] cuts exists.

    Structure (following §3.1 of the paper):
    - [necklace_splitting_stmt q]   : the statement for a fixed number [q] of thieves;
    - [necklace_seq_mul]            : the "well-known trick": splittings for [q1]
      and [q2] thieves compose into one for [q1*q2] thieves;
    - [necklace_seq_of_prime]       : hence the theorem for all [q] follows from
      the prime case;
    - the prime case is [necklace_prime.necklace_prime], the content of
      Meunier's §3.2–3.4 (the ℤ_p-simplotopal Tucker lemma of [tucker.v] plus
      the "winner" map λ);
    - [necklace_splitting] is the theorem itself, for every [q > 0]. *)

(** ** Provenance, sources, and what corresponds to what

    HOW THIS FILE WAS OBTAINED.  It was written with Claude Code (Anthropic),
    driving Rocq interactively through the rocq-mcp-evolve MCP server ("build"
    to list the open goals of a file, "open"/"step"/"try"/"check" to drive a
    single proof), so that a failing tactic was diagnosed on the spot instead
    of by recompiling.  rocq-mcp-evolve is developed by the LLM4Rocq project,
    https://github.com/LLM4Rocq/rocq-mcp-evolve (Apache-2.0; the opam package
    still carries its former slug LLM4Rocq/rocq-tools); it is gratefully
    acknowledged here.  Every error that recurred, together with the tactic
    that fixed it, is recorded in tactics-playbook.md at the root of the
    repository.  No result is admitted: "Print Assumptions" on the results of
    this file answers "Closed under the global context".

    MODELS AND ESTIMATED TOKEN COST FOR THIS FILE.

        Claude Fable 5.1    275k tokens   (09-14 21:05 -> 09-14 21:49 UTC)
        Claude Opus 5       277k tokens   (09-15 09:23 -> 09-15 16:27 UTC)
        TOTAL               551k tokens   of which 207k were output

      Method: the figures are estimated from the logs of the Claude Code
      session of 14-15 September 2026.  For every assistant message they count
      input + cache-creation + output tokens, i.e. the tokens processed anew,
      excluding the cached conversation that is re-read at each turn (772M
      over the project); a message is charged to the file its tool calls were
      acting on.  Three whole-session context rebuilds (compaction or resume),
      1.61M tokens in all, are charged to no file.  Project totals: 4.10M
      tokens of per-file work, 1.61M of context rebuilds, 5.70M overall.

    SOURCES.

      [A87]  N. Alon, "Splitting necklaces", Advances in Mathematics 63 (1987)
             247-253.  (Reference [1] of [M14]; not available locally.)

      [M14]  F. Meunier, "Simplotopal maps and necklace splitting",
             Discrete Mathematics 323 (2014) 14-26.
             Local copy: classical-lemmas/Meunier2014-Simplotopal_Necklace_web.pdf

    WHAT CORRESPONDS TO WHAT.

      [M14, Sect. 3.1]: the statement of the Splitting Necklace Theorem, the
      reduction of [A87] / [M14, Theorem 3.1] to a prime number of thieves, and
      the final assembly.

      - [A87] / [M14, Theorem 3.1], "every necklace with A_i beads of type i
        for 1 <= i <= t has a q-splitting requiring at most t(q-1) cuts"
                                    -> necklace_splitting_stmt,
                                       necklace_splitting,
                                       splitting_necklace_theorem
                                       (and splitting_necklace_seq, the same
                                       statement on sequences)
      - [M14, Sect. 3.1], "by a well-known trick (see [1,10]), it is enough to
        prove Theorem 3.1 for prime q": a q1-splitting followed, on each
        thief's sub-necklace, by a q2-splitting, is a (q1*q2)-splitting, and
        the cut counts add up as t(q1-1) + q1*t(q2-1) = t(q1*q2-1)
                                    -> glue, glue_inv, glue_count, glue_cuts,
                                       cuts_arith, necklace_seq_mul,
                                       necklace_seq_of_prime
      - the prime case, i.e. [M14, Sect. 3.2-3.4], is imported from
        necklace_prime.v
                                    -> necklace_splitting_prime
      - bookkeeping with no counterpart in [M14]: the theorem is proved on
        sequences (where the "well-known trick" is natural) and stated on
        functions from a finite type of beads (where it reads best), so the two
        readings of "number of cuts" have to be identified
                                    -> cuts_sum, cuts_seq_sum, cuts_seq_mapE,
                                       necklace_seq_of_stmt,
                                       necklace_stmt_of_seq *)

From mathcomp Require Import all_boot.
From ClassicalLemmas Require necklace.necklace_prime.
Set SsrOldRewriteGoalsOrder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Headline statement, over ordinals ************************************)

(** Number of cuts of the thief assignment [a]: positions [i] with [a i != a i.+1],
    encoded as the pairs of consecutive beads [(i, i.+1)] receiving distinct thieves. *)
Definition cuts (n q : nat) (a : 'I_n -> 'I_q) : nat :=
  #|[set p : 'I_n * 'I_n | (p.2 == p.1.+1 :> nat) && (a p.1 != a p.2)]|.

(** Every thief gets exactly a [1/q] share of every type. *)
Definition fair (n t q : nat) (c : 'I_n -> 'I_t) (a : 'I_n -> 'I_q) : Prop :=
  forall (k : 'I_t) (j : 'I_q),
    #|[set i | (c i == k) && (a i == j)]| = #|[set i | c i == k]| %/ q.

Definition necklace_splitting_stmt (q : nat) : Prop :=
  forall (n t : nat) (c : 'I_n -> 'I_t),
    (forall k : 'I_t, q %| #|[set i | c i == k]|) ->
    exists a : 'I_n -> 'I_q, cuts a <= t * q.-1 /\ fair c a.

(** ** Sequence form ********************************************************)

(** The same notions on sequences; this is the form in which the reduction to
    prime [q] is carried out. *)
Definition cuts_seq (Q : eqType) (s : seq Q) : nat :=
  count (fun p : Q * Q => p.1 != p.2) (zip s (behead s)).

Definition count_pair (T Q : eqType) (k : T) (j : Q) (c : seq T) (a : seq Q) : nat :=
  count (fun p : T * Q => (p.1 == k) && (p.2 == j)) (zip c a).

Definition necklace_seq_stmt (q : nat) : Prop :=
  forall (t : nat) (c : seq 'I_t),
    (forall k : 'I_t, q %| count (pred1 k) c) ->
    exists a : seq 'I_q,
      [/\ size a = size c, cuts_seq a <= t * q.-1 &
          forall (k : 'I_t) (j : 'I_q), count_pair k j c a = count (pred1 k) c %/ q].

(** *** Elementary facts about [cuts_seq] and [count_pair] *)

Lemma cuts_seq_cons2 (Q : eqType) (x y : Q) (s : seq Q) :
  cuts_seq (x :: y :: s) = (x != y) + cuts_seq (y :: s).
Proof. by []. Qed.

Lemma leq_cuts_seq_behead (Q : eqType) (s : seq Q) :
  cuts_seq (behead s) <= cuts_seq s.
Proof. by case: s => [|x [|y s]] //; rewrite cuts_seq_cons2 leq_addl. Qed.

Lemma cuts_seq_nseq (Q : eqType) (n : nat) (x : Q) : cuts_seq (nseq n x) = 0.
Proof.
elim: n => [|[|n] IH] //.
by rewrite [nseq _ _]/= cuts_seq_cons2 eqxx add0n; exact: IH.
Qed.

Lemma zip_nseqr (T Q : Type) (c : seq T) (x : Q) :
  zip c (nseq (size c) x) = [seq (y, x) | y <- c].
Proof. by elim: c => //= y c ->. Qed.

Lemma cuts_seq_map (Q Q' : eqType) (f : Q -> Q') (s : seq Q) :
  injective f -> cuts_seq (map f s) = cuts_seq s.
Proof.
move=> inj_f; elim: s => [|x [|y s]] // IH.
by rewrite !map_cons !cuts_seq_cons2 (inj_eq inj_f) -IH.
Qed.

Lemma count_pair_map (T Q Q' : eqType) (f : Q -> Q') (c : seq T) (a : seq Q) k j :
  injective f -> count_pair k (f j) c (map f a) = count_pair k j c a.
Proof.
move=> inj_f; rewrite /count_pair; elim: c a => [|x c IH] [|y a] //=.
by rewrite (inj_eq inj_f) IH.
Qed.

Lemma count_mask_pair (T Q : eqType) (k : T) (r : Q) (c : seq T) (a : seq Q) :
  count (pred1 k) (mask (map (pred1 r) a) c) = count_pair k r c a.
Proof.
rewrite /count_pair; elim: a c => [|x a IH] [|y c] //=.
by case: (x == r); rewrite /= IH ?andbT ?andbF ?add0n.
Qed.

(** *** One thief *)

Lemma necklace_seq1 : necklace_seq_stmt 1.
Proof.
move=> t c _; exists (nseq (size c) ord0); split.
- exact: size_nseq.
- by rewrite cuts_seq_nseq.
- move=> k j; rewrite divn1 /count_pair zip_nseqr count_map.
  by apply: eq_count => y /=; rewrite [j]ord1 eqxx andbT.
Qed.

(** *** Composing two splittings (the "well-known trick" of §3.1) *)

Section Glue.
Variables (q1 q2 : nat) (j0 : 'I_q2).

(** [glue a b] assigns bead [i] to the pair (first-round thief [a i], second-round
    thief chosen by [b (a i)] on the sub-necklace of [a i]). *)
Fixpoint glue (a : seq 'I_q1) (b : 'I_q1 -> seq 'I_q2) : seq ('I_q1 * 'I_q2) :=
  if a is r :: a' then
    (r, head j0 (b r)) :: glue a' (fun r' => if r' == r then behead (b r) else b r')
  else [::].

Lemma size_glue a b : size (glue a b) = size a.
Proof. by elim: a b => //= r a IH b; rewrite IH. Qed.

(** The invariant carried along [glue]: thief [r]'s second-round sequence has
    exactly one entry per bead of [r]. *)
Lemma glue_inv (r0 : 'I_q1) (a : seq 'I_q1) (b : 'I_q1 -> seq 'I_q2) :
  (forall r, size (b r) = count (pred1 r) (r0 :: a)) ->
  forall r', size (if r' == r0 then behead (b r0) else b r') = count (pred1 r') a.
Proof.
move=> hb r'; case: (r' =P r0) => [->|/eqP neq].
- by rewrite size_behead hb /= eqxx.
- by rewrite hb /= eq_sym (negbTE neq).
Qed.

Lemma glue_count (T : eqType) (c : seq T) a b (k : T) r j :
  (forall r, size (b r) = count (pred1 r) a) ->
  count_pair k (r, j) c (glue a b)
  = count_pair k j (mask (map (pred1 r) a) c) (b r).
Proof.
elim: a c b => [|r0 a IH] [|x c] b hb; rewrite /count_pair //=;
  try by case: (b r).
have IH' := IH c _ (glue_inv hb); rewrite /count_pair in IH'.
case: (r0 =P r) => [hr|/eqP neq]; last first.
  have er : (r0 == r) = false by exact: negbTE.
  have er' : (r == r0) = false by rewrite eq_sym.
  by rewrite xpair_eqE er !andbF add0n IH' er'.
move: IH' (hb r0); rewrite -hr /= !eqxx /= => IH' hsz.
case: (b r0) IH' hsz => [|hd tl] //= IH' _.
by rewrite xpair_eqE eqxx /= IH'.
Qed.

Lemma glue_cuts a b :
  (forall r, size (b r) = count (pred1 r) a) ->
  cuts_seq (glue a b) <= cuts_seq a + \sum_(r : 'I_q1) cuts_seq (b r).
Proof.
elim: a b => [|r0 a IH] b hb //.
have IH' := IH _ (glue_inv hb).
have sumb' : \sum_(r : 'I_q1) cuts_seq (if r == r0 then behead (b r0) else b r)
    = cuts_seq (behead (b r0)) + \sum_(r | r != r0) cuts_seq (b r).
  by rewrite (bigD1 r0) //= eqxx; congr (_ + _); apply: eq_bigr => r /negbTE ->.
rewrite sumb' in IH'; rewrite (bigD1 r0) //=.
case: a IH IH' hb => [|r1 a'] IH IH' hb //.
rewrite [glue _ _]/= cuts_seq_cons2 [X in _ <= X + _]cuts_seq_cons2.
apply: leq_trans (leq_add (leqnn _) IH') _.
rewrite addnCA [(r0 != r1) + _]addnC -[(_ + (r0 != r1)) + _]addnA leq_add2l.
rewrite !addnA leq_add2r.
case: (r0 =P r1) => [hr|/eqP neq]; last first.
  by apply: leq_add; [exact: leq_b1 | exact: leq_cuts_seq_behead].
move: (hb r0); rewrite -hr /= !eqxx /= => hsz.
case: (b r0) hsz => [|h [|h' tl]] //= _.
by rewrite xpair_eqE eqxx /= cuts_seq_cons2.
Qed.

End Glue.

(** *** Pairs of thieves as a single set of [q1 * q2] thieves *)

Lemma card_ord_prod (q1 q2 : nat) : #|{: 'I_q1 * 'I_q2}| = q1 * q2.
Proof. by rewrite card_prod !card_ord. Qed.

Definition pair_ord (q1 q2 : nat) (p : 'I_q1 * 'I_q2) : 'I_(q1 * q2) :=
  cast_ord (card_ord_prod q1 q2) (enum_rank p).

Lemma pair_ord_inj (q1 q2 : nat) : injective (@pair_ord q1 q2).
Proof. by move=> p p' /cast_ord_inj /enum_rank_inj. Qed.

Lemma pair_ord_onto (q1 q2 : nat) (j : 'I_(q1 * q2)) :
  exists p, pair_ord p = j.
Proof.
exists (enum_val (cast_ord (esym (card_ord_prod q1 q2)) j)).
by rewrite /pair_ord enum_valK cast_ordKV.
Qed.

Lemma cuts_arith (t q1 q2 : nat) :
  0 < q1 -> 0 < q2 ->
  t * q1.-1 + q1 * (t * q2.-1) = t * (q1 * q2).-1.
Proof.
case: q1 q2 => [|q1] [|q2] // _ _ /=.
rewrite mulnS !plusE !mulnDr mulSn mulnCA addnCA addnA addnC.
by [].
Qed.

Lemma necklace_seq_mul (q1 q2 : nat) :
  0 < q1 -> 0 < q2 ->
  necklace_seq_stmt q1 -> necklace_seq_stmt q2 -> necklace_seq_stmt (q1 * q2).
Proof.
move=> q1_gt0 q2_gt0 H1 H2 t c hc.
have hc1 k : q1 %| count (pred1 k) c.
  by apply: dvdn_trans (hc k); exact: dvdn_mulr.
have [a1 [sz1 cut1 fair1]] := H1 t c hc1.
pose sub r := mask (map (pred1 r) a1) c.
have hsub r k : q2 %| count (pred1 k) (sub r).
  by rewrite /sub count_mask_pair fair1 dvdn_divRL // mulnC; exact: hc.
have hb r : exists b : seq 'I_q2,
    [/\ size b = size (sub r), cuts_seq b <= t * q2.-1 &
        forall (k : 'I_t) (j : 'I_q2),
          count_pair k j (sub r) b = count (pred1 k) (sub r) %/ q2].
  exact: H2 (hsub r).
have [b hbP] := fin_all_exists hb.
have hsize r : size (b r) = count (pred1 r) a1.
  case: (hbP r) => -> _ _; rewrite /sub size_mask ?size_map ?sz1 //.
  by rewrite count_map; apply: eq_count.
pose j0 : 'I_q2 := Ordinal q2_gt0.
exists (map (@pair_ord q1 q2) (glue j0 a1 b)); split.
- by rewrite size_map size_glue.
- rewrite cuts_seq_map; last exact: pair_ord_inj.
  apply: leq_trans (glue_cuts _ hsize) _.
  rewrite -cuts_arith // -[q1 in _ + q1 * _]card_ord -sum_nat_const.
  by apply: leq_add => //; apply: leq_sum => r _; case: (hbP r).
- move=> k j; have [[r j'] <-] := pair_ord_onto j.
  rewrite count_pair_map; last exact: pair_ord_inj.
  rewrite (glue_count j0 c k r j' hsize) -/(sub r); case: (hbP r) => _ _ ->.
  by rewrite /sub count_mask_pair fair1 divnMA.
Qed.

(** *** Reduction to prime [q] *)

Theorem necklace_seq_of_prime :
  (forall p : nat, prime p -> necklace_seq_stmt p) ->
  forall q : nat, 0 < q -> necklace_seq_stmt q.
Proof.
move=> hp; elim/ltn_ind => q IH q_gt0.
case: (leqP q 1) => [q_le1|q_gt1].
  suff -> : q = 1 by exact: necklace_seq1.
  by apply/eqP; rewrite eqn_leq q_le1 q_gt0.
have p_pr : prime (pdiv q) := pdiv_prime q_gt1.
have p_dv : pdiv q %| q := pdiv_dvd q.
have p_gt0 : 0 < pdiv q := prime_gt0 p_pr.
rewrite -(divnK p_dv) mulnC.
apply: necklace_seq_mul => //.
- by rewrite divn_gt0 // dvdn_leq.
- exact: hp.
- apply: IH; last by rewrite divn_gt0 // dvdn_leq.
  by rewrite ltn_Pdiv // prime_gt1.
Qed.

(** ** Back to the ordinal form ********************************************)

Lemma card_set_count (n : nat) (P : pred 'I_n) :
  #|[set i | P i]| = count P (enum 'I_n).
Proof.
rewrite cardsE cardE /enum_mem -enumT size_filter.
by rewrite filter_predT.
Qed.

(** [cuts_seq] as a count over positions. *)
Lemma cuts_seq_nth (Q : eqType) (x0 : Q) (s : seq Q) :
  cuts_seq s
  = count (fun m => (m.+1 < size s) && (nth x0 s m != nth x0 s m.+1)) (iota 0 (size s)).
Proof.
elim: s => [|x [|y s]] // IH.
rewrite cuts_seq_cons2 IH /=.
congr (_ + _); congr (_ + _).
rewrite -[2]/(1+1) iotaDl count_map.
by apply: eq_count => m /=; rewrite !ltnS add1n.
Qed.

(** *** From counts over [iota] to sums over ordinals *)

Lemma sum_count (T : eqType) (P : pred T) (s : seq T) :
  count P s = \sum_(x <- s) (P x : nat).
Proof. by elim: s => [|x s IH]; rewrite ?big_nil // big_cons /= IH. Qed.

Lemma zip_map2 (T T1 T2 : Type) (f : T -> T1) (g : T -> T2) (s : seq T) :
  zip [seq f i | i <- s] [seq g i | i <- s] = [seq (f i, g i) | i <- s].
Proof. by elim: s => //= x s ->. Qed.

(** The two readings of "number of cuts" agree. *)
Lemma cuts_sum (n q : nat) (a : 'I_n -> 'I_q) (i0 : 'I_n) :
  cuts a = \sum_(i : 'I_n)
    ((i.+1 < n) && (a (nth i0 (enum 'I_n) i) != a (nth i0 (enum 'I_n) i.+1))).
Proof.
rewrite /cuts -sum1dep_card.
rewrite -(pair_big_dep xpredT
  (fun i i' : 'I_n => (i' == i.+1 :> nat) && (a i != a i')) (fun _ _ => 1)) /=.
apply: eq_bigr => i _; rewrite nth_ord_enum.
case: (ltnP i.+1 n) => [hi|hi]; last first.
  rewrite big1 // => i' /andP[/eqP hi' _].
  by move: (ltn_ord i'); rewrite hi' ltnNge hi.
rewrite (nth_ord_enum i0 (Ordinal hi)) /=.
have hpr : forall j : 'I_n, ((j == i.+1 :> nat) && (a i != a j))
                          = (a i != a (Ordinal hi)) && (j == Ordinal hi).
  move=> j; case: (j =P Ordinal hi) => [hj|/eqP hj].
    by rewrite hj eqxx andbT.
  rewrite andbF; apply/negbTE; rewrite negb_and negbK.
  by apply/orP; left; apply: contra hj => /eqP hv; apply/eqP/val_inj.
rewrite (eq_bigl _ _ hpr).
case: (a i != a (Ordinal hi)); last by rewrite big_pred0.
by rewrite (big_pred1 (Ordinal hi)).
Qed.

Lemma cuts_seq_sum (n q : nat) (a : 'I_n -> 'I_q) (i0 : 'I_n) :
  cuts_seq [seq a i | i <- enum 'I_n] = \sum_(i : 'I_n)
    ((i.+1 < n) && (a (nth i0 (enum 'I_n) i) != a (nth i0 (enum 'I_n) i.+1))).
Proof.
rewrite (cuts_seq_nth (a i0)) size_map size_enum_ord sum_count.
rewrite [RHS](_ : _ = \sum_(0 <= m < n)
   ((m.+1 < n) && (a (nth i0 (enum 'I_n) m) != a (nth i0 (enum 'I_n) m.+1))));
  last by rewrite big_mkord.
rewrite /index_iota subn0; apply: eq_bigr => m _.
case: (ltnP m.+1 n) => [hm|hm]; last by [].
rewrite (nth_map i0 (a i0) a (s := enum 'I_n) (n := m)) ?size_enum_ord ?(ltnW hm) //.
by rewrite (nth_map i0 (a i0) a (s := enum 'I_n) (n := m.+1)) ?size_enum_ord.
Qed.

Lemma cuts_seq_mapE (n q : nat) (a : 'I_n -> 'I_q) :
  cuts_seq [seq a i | i <- enum 'I_n] = cuts a.
Proof.
case: (posnP n) => [n0|n_gt0]; last first.
  by rewrite (cuts_seq_sum a (Ordinal n_gt0)) (cuts_sum a (Ordinal n_gt0)).
have he : enum 'I_n = [::] by apply: size0nil; rewrite size_enum_ord.
rewrite he /= /cuts_seq /=.
apply/esym/eqP; rewrite -leqn0 /cuts.
by apply: leq_trans (max_card _) _; rewrite card_prod card_ord n0.
Qed.

(** *** The two forms of the statement are equivalent *)

Lemma count_enum_map (n t : nat) (c : 'I_n -> 'I_t) (k : 'I_t) :
  count (pred1 k) [seq c i | i <- enum 'I_n] = #|[set i | c i == k]|.
Proof. by rewrite count_map card_set_count. Qed.

Lemma count_pair_map2 (n t q : nat) (cf : 'I_n -> 'I_t) (a : 'I_n -> 'I_q)
    (k : 'I_t) (j : 'I_q) :
  count_pair k j [seq cf i | i <- enum 'I_n] [seq a i | i <- enum 'I_n]
  = #|[set i : 'I_n | (cf i == k) && (a i == j)]|.
Proof. by rewrite /count_pair zip_map2 count_map card_set_count. Qed.

Lemma necklace_seq_of_stmt (q : nat) :
  necklace_splitting_stmt q -> necklace_seq_stmt q.
Proof.
move=> H t c hc.
pose cf (i : 'I_(size c)) : 'I_t := tnth (in_tuple c) i.
have hcE : [seq cf i | i <- enum 'I_(size c)] = c by exact: map_tnth_enum.
have hcnt k : count (pred1 k) c = #|[set i | cf i == k]|.
  by have := count_enum_map cf k; rewrite hcE => ->.
have hc' k : q %| #|[set i | cf i == k]| by rewrite -hcnt; exact: hc.
have [a [hcut hfair]] := H (size c) t cf hc'.
exists [seq a i | i <- enum 'I_(size c)]; split.
- by rewrite size_map size_enum_ord.
- by rewrite cuts_seq_mapE.
move=> k j; have := count_pair_map2 cf a k j.
by rewrite hcE => ->; rewrite hfair hcnt.
Qed.

Lemma necklace_stmt_of_seq (q : nat) :
  0 < q -> necklace_seq_stmt q -> necklace_splitting_stmt q.
Proof.
move=> q_gt0 H n t c hc.
pose j0 : 'I_q := Ordinal q_gt0.
pose cs : seq 'I_t := [seq c i | i <- enum 'I_n].
have hsz : size cs = n by rewrite size_map size_enum_ord.
have hc' k : q %| count (pred1 k) cs by rewrite count_enum_map; exact: hc.
have [s [hs1 hs2 hs3]] := H t cs hc'.
pose a (i : 'I_n) : 'I_q := nth j0 s i.
have haE : [seq a i | i <- enum 'I_n] = s.
  rewrite (_ : [seq a i | i <- enum 'I_n] = mkseq (nth j0 s) n); last first.
    by rewrite /mkseq -val_enum_ord -map_comp.
  by rewrite -[n]hsz -hs1 mkseq_nth.
exists a; split.
  by rewrite -cuts_seq_mapE haE.
move=> k j; rewrite -(count_pair_map2 c a k j) -/cs haE hs3.
by rewrite count_enum_map.
Qed.

Theorem necklace_splitting_of_prime :
  (forall p : nat, prime p -> necklace_seq_stmt p) ->
  forall q : nat, 0 < q -> necklace_splitting_stmt q.
Proof.
move=> hp q q_gt0; apply: necklace_stmt_of_seq => //.
exact: necklace_seq_of_prime.
Qed.

(** ** The Splitting Necklace Theorem *****************************************)

(** The prime case, from Meunier's §3.2–3.4 (file [necklace_prime.v]). *)
Lemma necklace_splitting_prime (p : nat) : prime p -> necklace_splitting_stmt p.
Proof.
move=> p_prime n t c hc.
have [a [hcut hfair]] := @necklace_prime.necklace_prime n t p c p_prime.
by exists a; split=> // k j; apply: hfair; exact: hc.
Qed.

Theorem necklace_splitting (q : nat) : 0 < q -> necklace_splitting_stmt q.
Proof.
move=> q_gt0; apply: necklace_stmt_of_seq => //.
apply: necklace_seq_of_prime => // p p_prime.
by apply: necklace_seq_of_stmt; exact: necklace_splitting_prime.
Qed.

(** Alon's Splitting Necklace Theorem, spelled out: an open necklace with [n]
    beads, bead [i] of type [c i], whose every type count is a multiple of the
    number [q] of thieves, admits a fair [q]-splitting using at most [t(q-1)]
    cuts. *)
Theorem splitting_necklace_theorem (n t q : nat) (c : 'I_n -> 'I_t) :
  0 < q -> (forall k : 'I_t, q %| #|[set i | c i == k]|) ->
  exists a : 'I_n -> 'I_q,
    #|[set pr : 'I_n * 'I_n | (pr.2 == pr.1.+1 :> nat) && (a pr.1 != a pr.2)]|
      <= t * q.-1
    /\ forall (k : 'I_t) (j : 'I_q),
         #|[set i | (c i == k) && (a i == j)]| = #|[set i | c i == k]| %/ q.
Proof. by move=> q_gt0 hc; exact: (necklace_splitting q_gt0 hc). Qed.

(** The sequence form, for the record. *)
Theorem splitting_necklace_seq (q : nat) : 0 < q -> necklace_seq_stmt q.
Proof.
move=> q_gt0; apply: necklace_seq_of_prime => // p p_prime.
by apply: necklace_seq_of_stmt; exact: necklace_splitting_prime.
Qed.

Print Assumptions necklace_splitting.
Print Assumptions splitting_necklace_theorem.
Print Assumptions splitting_necklace_seq.
