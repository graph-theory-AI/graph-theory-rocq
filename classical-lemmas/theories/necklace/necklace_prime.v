(** * ClassicalLemmas.necklace_prime — Alon's Splitting Necklace Theorem for a
      prime number of thieves, derived from the ℤ_p-simplotopal Tucker lemma.

    Reference: F. Meunier, "Simplotopal maps and necklace splitting", Discrete
    Math. 323 (2014) 14–26, §3.2 and §3.3 (Lemmas 3.2 and 3.4).

    The necklace has [n] beads, bead [b : 'I_n] occupying the interval
    [[b, b+1)] and having type [c b : 'I_t]; there are [p] thieves.

    §3.2's encoding: a vertex [v : 'I_N -> cut] of [K] is a list of [N]
    cut positions with a thief attached to each ([v j = Some (k, r)] is the
    cut at position [k+1] together with the thief [r]; [v j = None] is the
    cut at position 0).  The resulting splitting assigns bead [b] to the
    thief carried by the FIRST coordinate whose cut lies strictly to the
    right of [b] — this is exactly [covers (v j) b], and the resulting
    assignment is [own v b] below.  [lam v i] is Meunier's [i]-winner: the
    thief owning the largest number of beads of type [i], ties broken by the
    rightmost such bead. *)

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

        Claude Opus 5       346k tokens   (09-15 15:20 -> 09-15 16:35 UTC)
        TOTAL               346k tokens   of which 135k were output

      Method: the figures are estimated from the logs of the Claude Code
      session of 14-15 September 2026.  For every assistant message they count
      input + cache-creation + output tokens, i.e. the tokens processed anew,
      excluding the cached conversation that is re-read at each turn (772M
      over the project); a message is charged to the file its tool calls were
      acting on.  Three whole-session context rebuilds (compaction or resume),
      1.61M tokens in all, are charged to no file.  Project totals: 4.10M
      tokens of per-file work, 1.61M of context rebuilds, 5.70M overall.

    SOURCES.

      [M14]  F. Meunier, "Simplotopal maps and necklace splitting",
             Discrete Mathematics 323 (2014) 14-26.
             Local copy: classical-lemmas/Meunier2014-Simplotopal_Necklace_web.pdf

    WHAT CORRESPONDS TO WHAT.

      [M14, Sect. 3.2 to 3.4]: the "winner" map lambda, the proof that it is an
      equivariant simplotopal map ([M14, Lemma 3.2]), and the extraction of a
      fair splitting from the face produced by [M14, Theorem 3.3]
      ([M14, Lemma 3.4]).  This yields Alon's theorem for a PRIME number of
      thieves.

      - [M14, Sect. 3.2], "denote by x the left endpoint of that subnecklace
        and by y its right endpoint ... take v_j = (k,r) with the smallest j
        such that k >= y; the thief r is the one who gets the l-th
        subnecklace", read one bead at a time (the condition "k >= y" for the
        subnecklace containing bead b is exactly "covers (v j) b")
                                    -> jw (the first covering coordinate),
                                       own (the thief who gets a bead)
      - [M14, Sect. 3.2], "since there is a j such that v_j = (n,r), one of
        these cuts is at position n and is therefore not a real cut; we have
        thus indeed at most t(p-1) cuts"
                                    -> jw_mono, card_cutset
      - [M14, Sect. 3.2], "define lambda_i(v) as the thief who gets the largest
        amount of beads of type i ... in case of equality, the thief with the
        i-bead at the rightmost position is considered as advantaged"
                                    -> Bs, cnt, rk, sc, lam
        The lexicographic order (count, then rightmost bead) is packed into the
        single integer sc = cnt * n.+1 + rk, which is what makes the maximiser
        unique (sc_inj) -- and uniqueness, not just the existence of an argmax,
        is what equivariance needs.
      - [M14, Lemma 3.2], "the equivariance is straightforward"
                                    -> shiftp_inj, own_shift, lam_shift,
                                       lam_equivariant
      - [M14, Lemma 3.2], "we denote by d_i the number of these cuts sliding on
        i-beads"
                                    -> Sb (cuts sliding on a given bead),
                                       Si, di, sum_Sb, sum_di
      - [M14, Lemma 3.2], "since two cuts sliding on distinct beads keep their
        relative positions, we can choose the positions of the sliding cuts
        independently for each i"
                                    -> own_dep, own_depi, Bs_depi, sc_depi,
                                       lam_depi
      - [M14, Lemma 3.2], the hypergraph H_i, its edges F, and the head of an
        edge (the thief who gets that bead in the special vertex)
                                    -> Fb, hd, Gset, g
      - [M14, Lemma 3.2], "we select now a special position for the d sliding
        cuts ... we get in such a way our special vertex v"
                                    -> Topt, Tst, vst, scw_min
      - [M14, Lemma 3.2], CLAIM 1   -> claim1
      - [M14, Lemma 3.2], CLAIM 2   -> claim2
      - [M14, Lemma 3.2], CLAIM 3   -> card_Fb (via Jb, psi, card_Jb)
      - [M14, Lemma 3.2], the final count "|W_i| <= d_i + 1 for all i"
                                    -> card_compet, sum_g, card_W
        Note that only CLAIM 2 and CLAIM 3 are needed for this bound; CLAIM 1
        is used only in Lemma 3.4.
      - [M14, Lemma 3.2], the conclusion
                                    -> lam_simplotopal
      - [M14, Lemma 3.4], "since sum_i d_i = t(p-1), we have d_i = p-1 for each
        type i, and all inequalities are equalities in (4) ... each thief gets
        a_i or a_i + 1 beads of type i; it is a p-splitting"
                                    -> fair_vst (with cnt_exact for the final
                                       arithmetic)
      - [M14, Theorem 3.1] for prime p
                                    -> necklace_prime_core, necklace_prime

      ONE POINT WHERE THIS FILE DEPARTS FROM [M14].  [M14] states Lemma 3.2 for
      every necklace, but lambda cannot be simultaneously equivariant and
      simplotopal when some type has no bead at all: d_i is then 0 on every
      face, which forces lambda_i to be constant on K, while equivariance
      forbids a constant.  The core theorem is therefore proved under the
      hypothesis that every type occurs (c_onto), and necklace_prime recovers
      the general statement by relabelling the types that do occur
      (enum_rank_in / enum_val on the set of occurring types); this only
      decreases t, so the bound t(p-1) is preserved. *)

From mathcomp Require Import all_boot.
From ClassicalLemmas Require Import necklace.necklace_complex necklace.tucker.
Set SsrOldRewriteGoalsOrder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope nat_scope.

(** ** Two numerical helpers *)

Lemma sum_leq_eq (I : finType) (P : pred I) (f g : I -> nat) :
  (forall i, P i -> f i <= g i) ->
  \sum_(i | P i) g i <= \sum_(i | P i) f i ->
  forall i, P i -> f i = g i.
Proof.
move=> hfg hsum i hi.
apply/eqP; rewrite eqn_leq hfg //=.
move: hsum; rewrite (bigD1 i) //= [X in _ <= X](bigD1 i) //= => hsum.
rewrite -(leq_add2r (\sum_(j | P j && (j != i)) g j)).
apply: leq_trans hsum _; rewrite leq_add2l.
by apply: leq_sum => j /andP[hj _]; exact: hfg.
Qed.

Section Winner.

Variables (n t p : nat).
Hypothesis n_gt0 : 0 < n.
Hypothesis p_gt0 : 0 < p.
Variable c : 'I_n -> 'I_t.
(** Every type occurs: otherwise no equivariant [lam] can be simplotopal. *)
Hypothesis c_onto : forall i : 'I_t, exists b, c b == i.

Local Notation NN := (N t p).
Local Notation vtx := (vertex n t p).
Local Notation ct := (cut n p).

Definition r0 : 'I_p := Ordinal p_gt0.
Definition b0 : 'I_n := Ordinal n_gt0.
Definition j0 : 'I_NN := Ordinal (ltn0Sn (t * p.-1)).

(** The bead a nonempty cut sits on, and the thief it carries. *)
Definition bdo (x : ct) : 'I_n := if x is Some kr then kr.1 else b0.
Definition thf (x : ct) : 'I_p := if x is Some kr then kr.2 else r0.

Lemma covers_slideE (x : ct) (b : 'I_n) :
  covers (slide x) b = if x is Some kr then (b < kr.1) else false.
Proof.
case: x => [[k r]|] //=; case: (k =P 0 :> nat) => [->|/eqP hk] /=.
  by rewrite ltn0.
by rewrite -ltnS prednK // lt0n.
Qed.

Lemma covers_isS (x : ct) (b : 'I_n) : covers x b -> x != None.
Proof. by case: x. Qed.

Lemma covers_leqb (x : ct) (b b' : 'I_n) : b <= b' -> covers x b' -> covers x b.
Proof. by case: x => [[k r]|] //= hb; apply: leq_trans. Qed.

Lemma vertE (u : vtx) (T : {set 'I_NN}) (j : 'I_NN) :
  vert u T j = if j \in T then slide (u j) else u j.
Proof. by rewrite /vert ffunE. Qed.

Lemma covers_vertE (u : vtx) (T : {set 'I_NN}) (j : 'I_NN) (b : 'I_n) :
  covers (vert u T j) b = covers (u j) b && ~~ ((j \in T) && (bdo (u j) == b)).
Proof.
rewrite vertE; case: ifP => hj; last by rewrite andbT.
rewrite covers_slideE /=; case: (u j) => [[k r]|] //=.
by rewrite ltn_neqAle andbC eq_sym.
Qed.

(** ** The splitting encoded by a vertex *)

Definition jw (v : vtx) (b : 'I_n) : 'I_NN :=
  nth j0 (enum 'I_NN) (find (fun j : 'I_NN => covers (v j) b) (enum 'I_NN)).

Lemma jw_has (v : vtx) (b : 'I_n) (j : 'I_NN) : covers (v j) b ->
  has (fun k : 'I_NN => covers (v k) b) (enum 'I_NN).
Proof. by move=> hj; apply/hasP; exists j; rewrite ?mem_enum. Qed.

Lemma jw_hasX (v : vtx) (b : 'I_n) : in_X v ->
  has (fun k : 'I_NN => covers (v k) b) (enum 'I_NN).
Proof. by move=> /forallP/(_ b)/existsP[j hj]; exact: jw_has hj. Qed.

Lemma jw_val (v : vtx) (b : 'I_n) :
  has (fun k : 'I_NN => covers (v k) b) (enum 'I_NN) ->
  val (jw v b) = find (fun k : 'I_NN => covers (v k) b) (enum 'I_NN).
Proof.
rewrite has_find size_enum_ord => hh.
by rewrite /jw (_ : find _ _ = val (Ordinal hh)) // nth_ord_enum.
Qed.

Lemma jw_cov (v : vtx) (b : 'I_n) : in_X v -> covers (v (jw v b)) b.
Proof. by move=> hv; rewrite /jw; exact: (nth_find j0 (jw_hasX b hv)). Qed.

Lemma jw_min (v : vtx) (b : 'I_n) (j : 'I_NN) : covers (v j) b -> jw v b <= j.
Proof.
move=> hj; rewrite leqNgt; apply/negP => hlt.
have hh := jw_has hj.
move: hlt; rewrite (jw_val hh) => hlt.
by move: (before_find j0 hlt); rewrite nth_ord_enum hj.
Qed.

Lemma jw_eq (v v' : vtx) (b : 'I_n) :
  (forall j, covers (v j) b = covers (v' j) b) -> jw v b = jw v' b.
Proof. by move=> he; rewrite /jw (eq_find (a2 := fun k : 'I_NN => covers (v' k) b)). Qed.

(** The thief who gets bead [b] in the splitting encoded by [v]. *)
Definition own (v : vtx) (b : 'I_n) : 'I_p := thf (v (jw v b)).

(** [jw] is nondecreasing: later beads are covered later. *)
Lemma jw_mono (v : vtx) (b b' : 'I_n) : in_X v -> b <= b' -> jw v b <= jw v b'.
Proof.
move=> hv hbb; apply: jw_min.
by apply: covers_leqb hbb _; exact: jw_cov.
Qed.

(** ** Meunier's [i]-winner *)

(** Beads of type [i] owned by thief [r]. *)
Definition Bs (v : vtx) (i : 'I_t) (r : 'I_p) : {set 'I_n} :=
  [set b | (c b == i) && (own v b == r)].
Definition cnt (v : vtx) (i : 'I_t) (r : 'I_p) : nat := #|Bs v i r|.
(** The rightmost such bead, as [position + 1] (so [0] if there is none). *)
Definition rk (v : vtx) (i : 'I_t) (r : 'I_p) : nat := \max_(b in Bs v i r) (val b).+1.
(** Meunier's order on thieves: number of [i]-beads first, rightmost one to break ties. *)
Definition sc (v : vtx) (i : 'I_t) (r : 'I_p) : nat := cnt v i r * n.+1 + rk v i r.
Definition lam (v : vtx) (i : 'I_t) : 'I_p := [arg max_(r > r0) sc v i r].

Lemma rk_le (v : vtx) (i : 'I_t) (r : 'I_p) : rk v i r <= n.
Proof. by apply/bigmax_leqP => b _; exact: ltn_ord. Qed.

Lemma sc_eq_Bs (v v' : vtx) (i i' : 'I_t) (r r' : 'I_p) :
  Bs v i r = Bs v' i' r' -> sc v i r = sc v' i' r'.
Proof. by rewrite /sc /cnt /rk => ->. Qed.

Lemma cnt_of_sc (v v' : vtx) (i i' : 'I_t) (r r' : 'I_p) :
  sc v i r <= sc v' i' r' -> cnt v i r <= cnt v' i' r'.
Proof.
move=> h; rewrite leqNgt; apply/negP => hlt.
have h1 : (cnt v' i' r').+1 * n.+1 <= cnt v i r * n.+1 by rewrite leq_mul2r hlt orbT.
have h2 : cnt v i r * n.+1 <= cnt v' i' r' * n.+1 + n.
  apply: leq_trans (leq_trans (leq_addr (rk v i r) _) h) _.
  by rewrite leq_add2l rk_le.
by move: (leq_trans h1 h2); rewrite mulSn addnC leq_add2l ltnn.
Qed.

Lemma sc_max (v : vtx) (i : 'I_t) (r : 'I_p) : sc v i r <= sc v i (lam v i).
Proof.
rewrite /lam; case: (arg_maxnP (fun r : 'I_p => sc v i r) (isT : xpredT r0)) => x _.
by move=> /(_ r isT).
Qed.

Lemma cnt_le (v : vtx) (i : 'I_t) (r : 'I_p) : cnt v i r <= cnt v i (lam v i).
Proof. by apply: cnt_of_sc; exact: sc_max. Qed.

Lemma rk_wit (v : vtx) (i : 'I_t) (r : 'I_p) : 0 < cnt v i r ->
  exists2 b, b \in Bs v i r & rk v i r = (val b).+1.
Proof.
rewrite /cnt /rk => hc.
by have [b hb hmax] := eq_bigmax_cond (fun b : 'I_n => (val b).+1) hc; exists b.
Qed.

Lemma sc_inj (v : vtx) (i : 'I_t) (r r' : 'I_p) :
  0 < cnt v i r -> sc v i r = sc v i r' -> r = r'.
Proof.
move=> hc he.
have hd : forall m x : nat, x <= n -> (m * n.+1 + x) %/ n.+1 = m.
  by move=> m x hx; rewrite divnMDl // divn_small ?addn0 // ltnS.
have hm : forall m x : nat, x <= n -> (m * n.+1 + x) %% n.+1 = x.
  by move=> m x hx; rewrite modnMDl modn_small // ltnS.
have hcnt : cnt v i r = cnt v i r'.
  by rewrite -(hd (cnt v i r) _ (rk_le v i r)) -(hd (cnt v i r') _ (rk_le v i r'))
             -/(sc v i r) -/(sc v i r') he.
have hrk : rk v i r = rk v i r'.
  by rewrite -(hm (cnt v i r) _ (rk_le v i r)) -(hm (cnt v i r') _ (rk_le v i r'))
             -/(sc v i r) -/(sc v i r') he.
have [b hb hbe] := rk_wit hc.
have hc' : 0 < cnt v i r' by rewrite -hcnt.
have [b' hb' hbe'] := rk_wit hc'.
move: hb hb'; rewrite !inE => /andP[_ /eqP hq] /andP[_ /eqP hq'].
rewrite -hq -hq'; congr own; apply/val_inj/succn_inj.
by rewrite -hbe -hbe' hrk.
Qed.

Lemma lam_cnt_gt0 (v : vtx) (i : 'I_t) : (exists b, c b == i) ->
  0 < cnt v i (lam v i).
Proof.
move=> [b hb]; apply: leq_trans (cnt_le v i (own v b)).
by rewrite /cnt card_gt0; apply/set0Pn; exists b; rewrite inE hb eqxx.
Qed.

(** ** Equivariance *)

Lemma shiftp_inj : injective (shiftp p_gt0).
Proof.
have main : forall x y : 'I_p, x <= y -> shiftp p_gt0 x = shiftp p_gt0 y -> x = y.
  move=> x y hxy /(congr1 val) /= he.
  apply/val_inj/eqP; rewrite eqn_leq hxy /=.
  rewrite -subn_eq0 -leqn0 leqNgt; apply/negP => h0.
  have hdv : p %| y - x by rewrite -(subSS x y) -eqn_mod_dvd // he.
  move: (dvdn_leq h0 hdv); rewrite leqNgt => /negP; apply.
  exact: leq_ltn_trans (leq_subr _ _) (ltn_ord y).
move=> x y he; case: (leqP x y) => h; first exact: main.
by apply/esym; apply: main => //; exact: ltnW.
Qed.

Lemma shiftp_surj (r' : 'I_p) : exists r, shiftp p_gt0 r = r'.
Proof.
have [f hf1 hf2] := injF_bij shiftp_inj.
by exists (f r'); exact: hf2.
Qed.

Lemma covers_shift_cut (x : ct) (b : 'I_n) :
  covers (shift_cut p_gt0 x) b = covers x b.
Proof. by case: x => [[k r]|]. Qed.

Lemma own_shift (v : vtx) (b : 'I_n) : in_X v ->
  own (shift_vertex p_gt0 v) b = shiftp p_gt0 (own v b).
Proof.
move=> hv.
have hj : jw (shift_vertex p_gt0 v) b = jw v b.
  by apply: jw_eq => j; rewrite ffunE covers_shift_cut.
rewrite /own hj ffunE.
by move: (jw_cov b hv); case: (v (jw v b)) => [[k r]|].
Qed.

Lemma Bs_shift (v : vtx) (i : 'I_t) (r : 'I_p) : in_X v ->
  Bs (shift_vertex p_gt0 v) i (shiftp p_gt0 r) = Bs v i r.
Proof.
move=> hv; apply/setP => b; rewrite !inE (own_shift b hv).
by rewrite (inj_eq shiftp_inj).
Qed.

Lemma cnt_shift (v : vtx) (i : 'I_t) (r : 'I_p) : in_X v ->
  cnt (shift_vertex p_gt0 v) i (shiftp p_gt0 r) = cnt v i r.
Proof. by move=> hv; rewrite /cnt (Bs_shift i r hv). Qed.

Lemma sc_shift (v : vtx) (i : 'I_t) (r : 'I_p) : in_X v ->
  sc (shift_vertex p_gt0 v) i (shiftp p_gt0 r) = sc v i r.
Proof. by move=> hv; apply: sc_eq_Bs; exact: Bs_shift. Qed.

Lemma lam_shift (v : vtx) (i : 'I_t) : in_X v -> (exists b, c b == i) ->
  lam (shift_vertex p_gt0 v) i = shiftp p_gt0 (lam v i).
Proof.
move=> hv hi; apply/esym; apply: (@sc_inj (shift_vertex p_gt0 v) i).
  by rewrite (cnt_shift i (lam v i) hv); exact: lam_cnt_gt0.
apply/eqP; rewrite eqn_leq sc_max /=.
have [r hr] := shiftp_surj (lam (shift_vertex p_gt0 v) i).
by rewrite -hr !sc_shift //; exact: sc_max.
Qed.

(** ** Faces of K, and the cuts that slide *)

Section Face.

Variables (u : vtx) (S : {set 'I_NN}).
Hypothesis hface : face u S.

Lemma face_someS (j : 'I_NN) : j \in S -> u j != None.
Proof. by move: hface => /andP[/forall_inP h _]; exact: h. Qed.

Lemma face_inX (T : {set 'I_NN}) : T \subset S -> in_X (vert u T).
Proof.
move=> hT; move: hface => /andP[_ /forall_inP h]; apply: h.
by rewrite powersetE.
Qed.

Lemma vert0 : vert u set0 = u.
Proof. by apply/ffunP => j; rewrite vertE inE. Qed.

Lemma u_inX : in_X u.
Proof. by rewrite -vert0; apply: face_inX; exact: sub0set. Qed.

Lemma thf_vert (T : {set 'I_NN}) (j : 'I_NN) (b : 'I_n) :
  covers (vert u T j) b -> thf (vert u T j) = thf (u j).
Proof.
rewrite vertE; case: ifP => hj //.
rewrite covers_slideE; case: (u j) => [[k r]|] //= hbk.
by rewrite /slide; case: eqP => // hk0; rewrite hk0 ltn0 in hbk.
Qed.

Lemma own_vert (T : {set 'I_NN}) (b : 'I_n) : T \subset S ->
  own (vert u T) b = thf (u (jw (vert u T) b)).
Proof. by move=> hT; apply: thf_vert; apply: jw_cov; exact: face_inX. Qed.

(** Cuts of the face sliding on bead [b], resp. on beads of type [i]. *)
Definition Sb (b : 'I_n) : {set 'I_NN} := [set j in S | bdo (u j) == b].
Definition Si (i : 'I_t) : {set 'I_NN} := [set j in S | c (bdo (u j)) == i].
Definition di (i : 'I_t) : nat := #|Si i|.

Lemma Sb_sub_Si (b : 'I_n) : Sb b \subset Si (c b).
Proof.
apply/subsetP => j; rewrite !inE.
by move=> /andP[hj /eqP ->]; rewrite hj eqxx.
Qed.

Lemma Si_sub (i : 'I_t) : Si i \subset S.
Proof. by apply/subsetP => j; rewrite inE => /andP[]. Qed.

Lemma Sb_sub (b : 'I_n) : Sb b \subset S.
Proof. by apply/subsetP => j; rewrite inE => /andP[]. Qed.

(** The owner of bead [b] depends on the face vertex only through the cuts
    sliding on [b]. *)
Lemma own_dep (T T' : {set 'I_NN}) (b : 'I_n) :
  T \subset S -> T' \subset S -> T :&: Sb b = T' :&: Sb b ->
  own (vert u T) b = own (vert u T') b.
Proof.
move=> hT hT' he.
have hmem : (T :&: Sb b) =i (T' :&: Sb b) by move=> j; rewrite he.
have hcov : forall j, covers (vert u T j) b = covers (vert u T' j) b.
  move=> j; rewrite !covers_vertE; case hc : (covers (u j) b) => //=.
  case hb : (bdo (u j) == b); last by rewrite !andbF.
  rewrite !andbT; congr (~~ _); apply/idP/idP => hjT.
    have : j \in T :&: Sb b by rewrite in_setI hjT inE (subsetP hT _ hjT) hb.
    by rewrite hmem in_setI => /andP[].
  have : j \in T' :&: Sb b by rewrite in_setI hjT inE (subsetP hT' _ hjT) hb.
  by rewrite -hmem in_setI => /andP[].
by rewrite !own_vert // (jw_eq hcov).
Qed.

Lemma own_depi (T T' : {set 'I_NN}) (b : 'I_n) :
  T \subset S -> T' \subset S -> T :&: Si (c b) = T' :&: Si (c b) ->
  own (vert u T) b = own (vert u T') b.
Proof.
move=> hT hT' he; apply: own_dep => //.
have hAB : forall A : {set 'I_NN}, A :&: Sb b = A :&: Si (c b) :&: Sb b.
  move=> A; apply/setP => j; rewrite !in_setI -andbA; congr (_ && _).
  case hj : (j \in Sb b); last by rewrite andbF.
  by rewrite andbT (subsetP (Sb_sub_Si b) _ hj).
by rewrite (hAB T) (hAB T') he.
Qed.

Lemma Bs_depi (T T' : {set 'I_NN}) (i : 'I_t) (r : 'I_p) :
  T \subset S -> T' \subset S -> T :&: Si i = T' :&: Si i ->
  Bs (vert u T) i r = Bs (vert u T') i r.
Proof.
move=> hT hT' he; apply/setP => b; rewrite !inE.
case hb : (c b == i) => //=.
move/eqP: hb => hb.
by rewrite (@own_depi T T' b hT hT') // hb.
Qed.

Lemma sc_depi (T T' : {set 'I_NN}) (i : 'I_t) (r : 'I_p) :
  T \subset S -> T' \subset S -> T :&: Si i = T' :&: Si i ->
  sc (vert u T) i r = sc (vert u T') i r.
Proof. by move=> hT hT' he; apply: sc_eq_Bs; exact: Bs_depi. Qed.

Lemma lam_uniqP (v : vtx) (i : 'I_t) (r : 'I_p) :
  0 < cnt v i r -> (forall r', sc v i r' <= sc v i r) -> lam v i = r.
Proof.
move=> hc hm; apply: (@sc_inj v i); first exact: leq_trans hc (cnt_le v i r).
by apply/eqP; rewrite eqn_leq sc_max hm.
Qed.

Lemma lam_depi (T T' : {set 'I_NN}) (i : 'I_t) :
  T \subset S -> T' \subset S -> T :&: Si i = T' :&: Si i ->
  lam (vert u T) i = lam (vert u T') i.
Proof.
move=> hT hT' he; apply: lam_uniqP.
  rewrite /cnt (Bs_depi (lam (vert u T') i) hT hT' he) -/(cnt (vert u T') i _).
  exact: lam_cnt_gt0 (c_onto i).
by move=> r'; rewrite !(sc_depi _ hT hT' he); exact: sc_max.
Qed.

(** ** The special vertex of §3.2 *)

Definition scw (T : {set 'I_NN}) (i : 'I_t) : nat := sc (vert u T) i (lam (vert u T) i).

Lemma scw_depi (T T' : {set 'I_NN}) (i : 'I_t) :
  T \subset S -> T' \subset S -> T :&: Si i = T' :&: Si i -> scw T i = scw T' i.
Proof.
by move=> hT hT' he; rewrite /scw (lam_depi hT hT' he) (sc_depi _ hT hT' he).
Qed.

Definition Topt (i : 'I_t) : {set 'I_NN} := [arg min_(A < set0 | A \subset Si i) scw A i].
Definition Tst : {set 'I_NN} := \bigcup_(i : 'I_t) Topt i.
Definition vst : vtx := vert u Tst.

Lemma Topt_sub (i : 'I_t) : Topt i \subset Si i.
Proof.
rewrite /Topt; case: arg_minnP; first exact: sub0set.
by move=> A hA _.
Qed.

Lemma Topt_minP (i : 'I_t) (A : {set 'I_NN}) :
  A \subset Si i -> scw (Topt i) i <= scw A i.
Proof.
rewrite /Topt; case: arg_minnP; first exact: sub0set.
by move=> A' _ hm; exact: hm.
Qed.

Lemma Topt_subS (i : 'I_t) : Topt i \subset S.
Proof. exact: subset_trans (Topt_sub i) (Si_sub i). Qed.

Lemma Tst_sub : Tst \subset S.
Proof. by apply/bigcupsP => i _; exact: Topt_subS. Qed.

Lemma Tst_Si (i : 'I_t) : Tst :&: Si i = Topt i.
Proof.
apply/setP => j; rewrite in_setI; apply/idP/idP; last first.
  by move=> hj; rewrite (subsetP (Topt_sub i) _ hj) andbT; apply/bigcupP; exists i.
move=> /andP[/bigcupP[i' _ hj'] hji].
have hi' : c (bdo (u j)) = i'.
  by move: (subsetP (Topt_sub i') _ hj'); rewrite inE => /andP[_ /eqP].
have hi : c (bdo (u j)) = i by move: hji; rewrite inE => /andP[_ /eqP].
by rewrite -hi -hi' in hj' *.
Qed.

Lemma scw_min (i : 'I_t) (T : {set 'I_NN}) : T \subset S -> scw Tst i <= scw T i.
Proof.
move=> hT.
have h1 : scw Tst i = scw (Topt i) i.
  apply: scw_depi (Tst_sub) (Topt_subS i) _.
  by rewrite Tst_Si; apply/esym; apply/setIidPl; exact: Topt_sub.
have h2 : scw (T :&: Si i) i = scw T i.
  apply: scw_depi _ hT _; first exact: subset_trans (subsetIr _ _) (Si_sub i).
  by rewrite -setIA setIid.
rewrite h1 -h2; apply: Topt_minP; exact: subsetIr.
Qed.

(** ** The thieves who can get a given bead (Meunier's hypergraph [H_i]) *)

Definition Fb (b : 'I_n) : {set 'I_p} := [set own (vert u T) b | T in powerset S].
Definition Jb (b : 'I_n) : {set 'I_NN} := [set jw (vert u T) b | T in powerset S].
Definition jm (b : 'I_n) : 'I_NN := jw u b.
Definition psi (b : 'I_n) (j : 'I_NN) : 'I_NN :=
  [arg max_(k > jm b | covers (u k) b && (k < j)) k].

Lemma jm_cov (b : 'I_n) : covers (u (jm b)) b.
Proof. exact: jw_cov u_inX. Qed.

Lemma Jb_cov (b : 'I_n) (j : 'I_NN) : j \in Jb b -> covers (u j) b.
Proof.
case/imsetP => T; rewrite powersetE => hT ->.
by have := jw_cov b (face_inX hT); rewrite covers_vertE => /andP[].
Qed.

Lemma Jb_ge (b : 'I_n) (j : 'I_NN) : j \in Jb b -> jm b <= j.
Proof. by move=> hj; apply: jw_min; exact: Jb_cov hj. Qed.

Lemma psiP (b : 'I_n) (j : 'I_NN) : jm b < j ->
  [/\ covers (u (psi b j)) b, psi b j < j &
      forall k : 'I_NN, covers (u k) b -> k < j -> k <= psi b j].
Proof.
move=> hlt; rewrite /psi; case: arg_maxnP; first by rewrite jm_cov hlt.
by move=> k /andP[hc hk] hm; split=> // k' hc' hk'; apply: hm; rewrite hc' hk'.
Qed.

Lemma psi_in_Sb (b : 'I_n) (T : {set 'I_NN}) : T \subset S ->
  jm b < jw (vert u T) b -> psi b (jw (vert u T) b) \in Sb b.
Proof.
move=> hT hlt; have [hc hlt2 _] := psiP hlt.
have hnc : ~~ covers (vert u T (psi b (jw (vert u T) b))) b.
  by apply/negP => hcov; move: (jw_min hcov); rewrite leqNgt hlt2.
move: hnc; rewrite covers_vertE hc /= negbK => /andP[hin heq].
by rewrite inE (subsetP hT _ hin) heq.
Qed.

Lemma card_Jb (b : 'I_n) : #|Jb b| <= (#|Sb b|).+1.
Proof.
have hlt : forall j, j \in Jb b :\ jm b -> jm b < j.
  move=> j; rewrite in_setD1 => /andP[hne hj].
  by rewrite ltn_neqAle (Jb_ge hj) andbT val_eqE eq_sym.
have hinj : {in Jb b :\ jm b &, injective (psi b)}.
  have main : forall j j' : 'I_NN, j \in Jb b :\ jm b -> j' \in Jb b :\ jm b ->
      psi b j = psi b j' -> (j < j')%N -> False.
    move=> j j' hj hj' he hlt2.
    have [_ hp _] := psiP (hlt _ hj).
    have [_ _ hmax] := psiP (hlt _ hj').
    have hcj : covers (u j) b by apply: Jb_cov; move: hj; rewrite in_setD1 => /andP[].
    by move: (hmax j hcj hlt2); rewrite -he leqNgt hp.
  move=> j j' hj hj' he; case: (ltngtP (val j) (val j')) => [h|h|h].
  - by exfalso; exact: main j j' hj hj' he h.
  - by exfalso; exact: main j' j hj' hj (esym he) h.
  - exact: val_inj.
have hsub : [set psi b j | j in Jb b :\ jm b] \subset Sb b.
  apply/subsetP => k /imsetP[j hj ->].
  have [T hT hjT] : exists2 T : {set 'I_NN}, T \subset S & j = jw (vert u T) b.
    move: hj; rewrite in_setD1 => /andP[_ /imsetP[T]].
    by rewrite powersetE => hT hjT; exists T.
  by rewrite hjT; apply: psi_in_Sb => //; rewrite -hjT; exact: hlt.
rewrite (cardsD1 (jm b) (Jb b)) -add1n; apply: leq_add; first exact: leq_b1.
by rewrite -(card_in_imset hinj); exact: subset_leq_card hsub.
Qed.

(** CLAIM 3 of Meunier's proof of Lemma 3.2. *)
Lemma card_Fb (b : 'I_n) : #|Fb b| <= (#|Sb b|).+1.
Proof.
apply: leq_trans (card_Jb b).
have hsub : Fb b \subset [set thf (u j) | j in Jb b].
  apply/subsetP => r /imsetP[T]; rewrite powersetE => hT ->.
  by rewrite own_vert //; apply: imset_f; apply: imset_f; rewrite powersetE.
by apply: leq_trans (subset_leq_card hsub) _; exact: leq_imset_card.
Qed.

(** ** The [i]-winners over the face, and the counting of Lemma 3.2 *)

Definition W (i : 'I_t) : {set 'I_p} := image_set lam u S i.
Definition hd (b : 'I_n) : 'I_p := own vst b.
Definition Gset (i : 'I_t) (r : 'I_p) : {set 'I_n} :=
  [set b : 'I_n | [&& c b == i, r \in Fb b & hd b != r]].
Definition g (i : 'I_t) (r : 'I_p) : nat := #|Gset i r|.

Lemma hd_Fb (b : 'I_n) : hd b \in Fb b.
Proof. by apply: imset_f; rewrite powersetE Tst_sub. Qed.

Lemma WP (i : 'I_t) (r : 'I_p) :
  reflect (exists2 T : {set 'I_NN}, T \subset S & lam (vert u T) i = r) (r \in W i).
Proof.
apply: (iffP imsetP) => [[T]|[T hT hr]].
  by rewrite powersetE => hT hr; exists T.
by exists T; rewrite ?powersetE.
Qed.

Lemma W_lam (i : 'I_t) (T : {set 'I_NN}) : T \subset S -> lam (vert u T) i \in W i.
Proof. by move=> hT; apply/WP; exists T. Qed.

Lemma W_wi (i : 'I_t) : lam vst i \in W i.
Proof. exact: W_lam Tst_sub. Qed.

(** CLAIM 1 of Meunier's proof of Lemma 3.2. *)
Lemma claim1 (i : 'I_t) (r : 'I_p) : r \in W i ->
  cnt vst i (lam vst i) <= g i r + cnt vst i r.
Proof.
move=> /WP[T hT hr].
have hsc : sc vst i (lam vst i) <= sc (vert u T) i r by rewrite -hr; exact: scw_min.
apply: leq_trans (cnt_of_sc hsc) _.
rewrite /cnt -(cardsID (Bs vst i r) (Bs (vert u T) i r)) addnC; apply: leq_add.
  rewrite /g; apply: subset_leq_card; apply/subsetP => b.
  rewrite in_setD !inE => /andP[hnb /andP[hci /eqP hown]].
  rewrite hci /=; apply/andP; split.
    by rewrite -hown; apply: imset_f; rewrite powersetE.
  by rewrite /hd; move: hnb; rewrite hci.
exact: subset_leq_card (subsetIr _ _).
Qed.

(** CLAIM 2 of Meunier's proof of Lemma 3.2. *)
Lemma claim2 (i : 'I_t) (r : 'I_p) : r \in W i -> r != lam vst i -> 0 < g i r.
Proof.
move=> hrW hne; rewrite lt0n; apply/negP => /eqP hg0.
have hempty : Gset i r = set0.
  by apply/eqP; rewrite -cards_eq0 -/(g i r) hg0.
move: hrW => /WP[T hT hlam].
have hsub : Bs (vert u T) i r \subset Bs vst i r.
  apply/subsetP => b; rewrite !inE => /andP[hci /eqP hown].
  rewrite hci /=.
  have hnG : b \notin Gset i r by rewrite hempty inE.
  move: hnG; rewrite inE hci /=.
  have -> : r \in Fb b by rewrite -hown; apply: imset_f; rewrite powersetE.
  by rewrite /= negbK /hd.
have hsc : sc vst i (lam vst i) <= sc (vert u T) i r by rewrite -hlam; exact: scw_min.
have hcT := cnt_of_sc hsc.
have hBeq : Bs (vert u T) i r = Bs vst i r.
  apply/eqP; rewrite eqEcard hsub /= -/(cnt vst i r) -/(cnt (vert u T) i r).
  exact: leq_trans (cnt_le vst i r) hcT.
have hsceq : sc (vert u T) i r = sc vst i r by exact: sc_eq_Bs hBeq.
have hpos : 0 < cnt vst i r.
  rewrite /cnt -hBeq -/(cnt (vert u T) i r); apply: leq_trans hcT.
  exact: lam_cnt_gt0 (c_onto i).
move/eqP: hne; apply; apply: (@sc_inj vst i) => //.
by apply/eqP; rewrite eqn_leq sc_max /= -hsceq.
Qed.

(** CLAIM 3 packaged: the number of thieves of [W i] competing for bead [b]
    (other than its owner in the special vertex) is at most [#|Sb b|]. *)
Lemma card_compet (i : 'I_t) (b : 'I_n) :
  #|[set r : 'I_p | (r \in W i) && ((r \in Fb b) && (hd b != r))]| <= #|Sb b|.
Proof.
have hsub : [set r : 'I_p | (r \in W i) && ((r \in Fb b) && (hd b != r))]
            \subset Fb b :\ hd b.
  apply/subsetP => r; rewrite !inE => /andP[_ /andP[hf hne]].
  by rewrite hf andbT eq_sym.
apply: leq_trans (subset_leq_card hsub) _.
by move: (card_Fb b); rewrite (cardsD1 (hd b) (Fb b)) hd_Fb add1n ltnS.
Qed.

Lemma sum_Sb (i : 'I_t) : \sum_(b : 'I_n | c b == i) #|Sb b| = di i.
Proof.
rewrite /di -sum1_card (eq_bigr (fun b => \sum_(j in Sb b) 1)); last first.
  by move=> b _; rewrite sum1_card.
rewrite (exchange_big_dep (fun j => j \in Si i)) /=; last first.
  by move=> b j hb; rewrite inE => /andP[hjS /eqP hbd]; rewrite inE hjS hbd hb.
apply: eq_bigr => j hj; rewrite (big_pred1 (bdo (u j))) // => b /=.
move: hj; rewrite inE => /andP[hjS /eqP hbd].
rewrite inE hjS /=; apply/idP/idP.
  by move=> /andP[_ /eqP ->].
by move=> /eqP hb; rewrite hb hbd !eqxx.
Qed.

Lemma sum_di : \sum_(i : 'I_t) di i = #|S|.
Proof.
rewrite /di -sum1_card (eq_bigr (fun i => \sum_(j in Si i) 1)); last first.
  by move=> i _; rewrite sum1_card.
rewrite (exchange_big_dep (fun j => j \in S)) /=; last first.
  by move=> i j _; rewrite inE => /andP[].
apply: eq_bigr => j hj; rewrite (big_pred1 (c (bdo (u j)))) // => i /=.
by rewrite inE hj /= eq_sym.
Qed.

Lemma sum_g (i : 'I_t) : \sum_(r in W i) g i r <= di i.
Proof.
rewrite -(sum_Sb i).
rewrite (eq_bigr (fun r => \sum_(b : 'I_n | [&& c b == i, r \in Fb b & hd b != r]) 1));
  last by move=> r _; rewrite /g /Gset -sum1dep_card.
rewrite (exchange_big_dep (fun b : 'I_n => c b == i)) /=; last first.
  by move=> r b _ /and3P[].
apply: leq_sum => b _.
rewrite sum1dep_card; apply: leq_trans (card_compet i b).
apply: subset_leq_card; apply/subsetP => r.
by rewrite !inE => /andP[hr /and3P[_ hf hne]]; rewrite hr hf hne.
Qed.

(** Meunier's Lemma 3.2 for a single type. *)
Lemma card_W (i : 'I_t) : #|W i| <= (di i).+1.
Proof.
rewrite (cardsD1 (lam vst i) (W i)) W_wi add1n ltnS.
apply: leq_trans (sum_g i).
rewrite -sum1_card (eq_bigl (fun r : 'I_p => (r \in W i) && (r != lam vst i)));
  last by move=> r /=; rewrite in_setD1 andbC.
rewrite [X in _ <= X](bigID (fun r : 'I_p => r != lam vst i)) /=.
apply: leq_trans (leq_addr _ _).
by apply: leq_sum => r /andP[hr hne]; exact: claim2.
Qed.

Lemma vst_inX : in_X vst.
Proof. by apply: face_inX; exact: Tst_sub. Qed.

End Face.

(** ** [lam] satisfies the hypotheses of the ℤ_p-simplotopal Tucker lemma *)

Lemma lam_equivariant : equivariant p_gt0 lam.
Proof. by move=> v hv i; apply: lam_shift => //; exact: c_onto. Qed.

Lemma lam_simplotopal : simplotopal lam.
Proof.
move=> u S hface; rewrite -(sum_di u S).
by apply: leq_sum => i _; rewrite leq_subLR add1n; exact: card_W.
Qed.

(** ** The number of cuts of the splitting encoded by a vertex *)

Lemma card_cutset (v : vtx) : in_X v ->
  #|[set pr : 'I_n * 'I_n | (pr.2 == pr.1.+1 :> nat) && (own v pr.1 != own v pr.2)]|
  <= t * p.-1.
Proof.
move=> hv; set C := [set pr : _ | _].
have hsnd : forall pr : 'I_n * 'I_n, pr \in C -> val pr.2 = (val pr.1).+1.
  by move=> pr; rewrite inE => /andP[/eqP].
have hlt : forall pr, pr \in C -> jw v pr.1 < jw v pr.2.
  move=> pr hpr; have h2 := hsnd _ hpr.
  rewrite ltn_neqAle; apply/andP; split; last by apply: jw_mono => //; rewrite h2.
  move: hpr; rewrite inE => /andP[_ hne]; apply: contra hne => /eqP hq.
  by rewrite /own (_ : jw v pr.1 = jw v pr.2) //; exact: val_inj.
have hinj : {in C &, injective (fun pr : 'I_n * 'I_n => jw v pr.2)}.
  have main : forall pr pr' : 'I_n * 'I_n, pr \in C -> pr' \in C ->
      jw v pr.2 = jw v pr'.2 -> (val pr.1 < val pr'.1)%N -> False.
    move=> pr pr' hpr hpr' he hlt2.
    have h12 : jw v pr.2 <= jw v pr'.1 by apply: jw_mono => //; rewrite (hsnd _ hpr).
    by move: h12; rewrite he leqNgt (hlt _ hpr').
  move=> pr pr' hpr hpr' he; have h2 := hsnd _ hpr; have h2' := hsnd _ hpr'.
  have h1 : pr.1 = pr'.1.
    case: (ltngtP (val pr.1) (val pr'.1)) => [h|h|h].
    - by exfalso; exact: main pr pr' hpr hpr' he h.
    - by exfalso; exact: main pr' pr hpr' hpr (esym he) h.
    - exact: val_inj.
  have h2b : pr.2 = pr'.2 by apply: val_inj; rewrite h2 h2' h1.
  by apply/eqP; rewrite -pair_eqE /= h1 h2b !eqxx.
have himg : [set jw v pr.2 | pr in C] \subset [set~ jw v b0].
  apply/subsetP => k /imsetP[pr hpr ->]; rewrite !inE.
  apply/negP => /eqP hk.
  have hb : jw v b0 <= jw v pr.1 by apply: jw_mono.
  by move: hb; rewrite -hk leqNgt (hlt _ hpr).
rewrite -(card_in_imset hinj).
apply: leq_trans (subset_leq_card himg) _.
by rewrite cardsC1 card_ord.
Qed.

(** ** Meunier's Lemma 3.4 *)

Lemma sum_cnt (v : vtx) (i : 'I_t) :
  \sum_(r : 'I_p) cnt v i r = #|[set b : 'I_n | c b == i]|.
Proof.
rewrite /cnt -sum1_card (eq_bigr (fun r => \sum_(b in Bs v i r) 1)); last first.
  by move=> r _; rewrite sum1_card.
rewrite (exchange_big_dep (fun b : 'I_n => c b == i)) /=; last first.
  by move=> r b _; rewrite inE => /andP[].
rewrite (eq_bigl (fun b : 'I_n => b \in [set b : 'I_n | c b == i])); last first.
  by move=> b /=; rewrite inE.
apply: eq_bigr => b; rewrite inE => hb.
by rewrite (big_pred1 (own v b)) // => r /=; rewrite inE hb /= eq_sym.
Qed.

Lemma cnt_exact (M A : nat) (f : 'I_p -> nat) :
  (forall r, f r <= M) -> (forall r, M <= 1 + f r) ->
  \sum_(r : 'I_p) f r = A -> p %| A -> forall r, f r = A %/ p.
Proof.
move=> hub hlb hsum hdvd r; set a := A %/ p.
have hA : A = p * a by rewrite /a mulnC divnK.
have hlow : forall r', M - 1 <= f r' by move=> r'; rewrite leq_subLR; exact: hlb.
have h1 : p * (M - 1) <= A.
  rewrite -hsum -[X in X * _]card_ord -sum_nat_const.
  by apply: leq_sum => r' _; exact: hlow.
have h2 : A <= p * M.
  rewrite -hsum -[X in X * _]card_ord -sum_nat_const.
  by apply: leq_sum => r' _; exact: hub.
have hMa : M - 1 <= a by rewrite -(leq_pmul2l p_gt0) -hA.
have haM : a <= M by rewrite -(leq_pmul2l p_gt0) -hA.
case: (a =P M) => [ha|/eqP hne].
  rewrite ha; apply: (@sum_leq_eq _ xpredT f (fun _ => M)) => //.
  by rewrite sum_nat_const card_ord hsum hA ha.
have hlt : a < M by rewrite ltn_neqAle hne haM.
have hM0 : 0 < M by apply: leq_ltn_trans hlt.
have haE : a = M - 1 by apply/eqP; rewrite eqn_leq hMa andbT subn1 -ltnS prednK.
rewrite haE; apply/esym.
apply: (@sum_leq_eq _ xpredT (fun _ => M - 1) f) => //.
by rewrite sum_nat_const card_ord hsum hA haE.
Qed.

Lemma fair_vst (u : vtx) (S : {set 'I_NN}) :
  face u S -> #|S| = t * p.-1 -> (forall i, image_set lam u S i = setT) ->
  forall (i : 'I_t) (r : 'I_p),
    p %| #|[set b : 'I_n | c b == i]| ->
    cnt (vst u S) i r = #|[set b : 'I_n | c b == i]| %/ p.
Proof.
move=> hface hcard hfull i r hdvd.
have hWp : forall i', #|W u S i'| = p by move=> i'; rewrite /W hfull cardsT card_ord.
have hdi : forall i', di u S i' = p.-1.
  move=> i'; apply/esym.
  apply: (@sum_leq_eq _ xpredT (fun _ => p.-1) (di u S)) => // [i'' _|].
    by rewrite -ltnS prednK // -(hWp i''); exact: card_W.
  by rewrite (sum_di u S) hcard sum_nat_const card_ord.
pose wi := lam (vst u S) i.
have hwiW : wi \in W u S i by exact: W_wi.
have hsum1 : \sum_(r' in W u S i | r' != wi) g u S i r'
           <= \sum_(r' in W u S i | r' != wi) 1.
  apply: leq_trans (_ : \sum_(r' in W u S i) g u S i r' <= _).
    rewrite [X in _ <= X](bigID (fun r' : 'I_p => r' != wi)) /=.
    exact: leq_addr.
  apply: leq_trans (sum_g hface i) _.
  move: (hWp i); rewrite (cardsD1 wi (W u S i)) hwiW add1n => hh.
  rewrite sum1_card hdi -ltnS prednK //.
  rewrite (_ : #|(fun i0 : 'I_p => (i0 \in W u S i) && (i0 != wi))|
             = #|W u S i :\ wi|) ?hh //.
  by apply: eq_card => r'; rewrite !inE andbC.
have hg1 : forall r', r' \in W u S i -> r' != wi -> g u S i r' = 1.
  move=> r' h1 h2; apply/esym.
  apply: (@sum_leq_eq _ (fun r'' : 'I_p => (r'' \in W u S i) && (r'' != wi))
                        (fun _ => 1) (g u S i)) => //.
  - by move=> r'' /andP[ha hb]; exact: claim2.
  - by rewrite h1 h2.
have hub : forall r', cnt (vst u S) i r' <= cnt (vst u S) i wi.
  by move=> r'; exact: cnt_le.
have hlb : forall r', cnt (vst u S) i wi <= 1 + cnt (vst u S) i r'.
  move=> r'; case: (r' =P wi) => [->|/eqP hne]; first exact: leq_addl.
  have hrW : r' \in W u S i by rewrite /W hfull inE.
  by rewrite -(hg1 r' hrW hne) /wi; exact: (claim1 hface hrW).
by apply: (cnt_exact hub hlb) => //; exact: sum_cnt.
Qed.

(** ** The prime case, for a necklace in which every type occurs *)

Theorem necklace_prime_core : prime p -> 0 < t ->
  exists a : 'I_n -> 'I_p,
    #|[set pr : 'I_n * 'I_n | (pr.2 == pr.1.+1 :> nat) && (a pr.1 != a pr.2)]|
      <= t * p.-1
    /\ (forall (k : 'I_t) (j : 'I_p), p %| #|[set b : 'I_n | c b == k]| ->
          #|[set b : 'I_n | (c b == k) && (a b == j)]|
          = #|[set b : 'I_n | c b == k]| %/ p).
Proof.
move=> p_prime t_gt0.
have [u [S [hface hcard hfull]]] :=
  zp_tucker_prime p_prime t_gt0 n_gt0 lam_equivariant lam_simplotopal.
exists (own (vst u S)); split.
  by apply: card_cutset; exact: vst_inX hface.
move=> k j hdvd.
have h := @fair_vst u S hface hcard hfull k j hdvd.
by move: h; rewrite /cnt /Bs.
Qed.

End Winner.

(** ** The prime case in general: types that do not occur are relabelled away *)

Theorem necklace_prime (n t p : nat) (c : 'I_n -> 'I_t) : prime p ->
  exists a : 'I_n -> 'I_p,
    #|[set pr : 'I_n * 'I_n | (pr.2 == pr.1.+1 :> nat) && (a pr.1 != a pr.2)]|
      <= t * p.-1
    /\ (forall (k : 'I_t) (j : 'I_p), p %| #|[set b : 'I_n | c b == k]| ->
          #|[set b : 'I_n | (c b == k) && (a b == j)]|
          = #|[set b : 'I_n | c b == k]| %/ p).
Proof.
move=> p_prime; have p_gt0 := prime_gt0 p_prime.
case: (posnP n) => [n0|n_gt0].
  have hemp : forall (A : pred 'I_n), #|A| = 0.
    move=> A; apply/eqP; rewrite -leqn0.
    by apply: leq_trans (max_card A) _; rewrite card_ord n0.
  have hemp2 : forall (A : pred ('I_n * 'I_n)), #|A| = 0.
    move=> A; apply/eqP; rewrite -leqn0.
    by apply: leq_trans (max_card A) _; rewrite card_prod card_ord n0.
  exists (fun _ => Ordinal p_gt0); split; first by rewrite hemp2.
  by move=> k j _; rewrite !hemp div0n.
pose b00 : 'I_n := Ordinal n_gt0.
pose P : {set 'I_t} := [set k | [exists b, c b == k]].
have hPb : forall b : 'I_n, c b \in P.
  by move=> b; rewrite inE; apply/existsP; exists b.
have hx0 : c b00 \in P := hPb b00.
pose c' (b : 'I_n) : 'I_#|P| := enum_rank_in hx0 (c b).
have hc'K : forall b, enum_val (c' b) = c b.
  by move=> b; rewrite /c' (enum_rankK_in hx0 (hPb b)).
have c'_onto : forall i : 'I_#|P|, exists b, c' b == i.
  move=> i; have : enum_val i \in P := enum_valP i.
  rewrite inE => /existsP[b /eqP hb].
  by exists b; rewrite /c' hb enum_valK_in.
have t'_gt0 : 0 < #|P| by rewrite card_gt0; apply/set0Pn; exists (c b00).
have [a [hcut hfair]] := necklace_prime_core n_gt0 p_gt0 c'_onto p_prime t'_gt0.
exists a; split.
  apply: leq_trans hcut _; apply: leq_mul => //.
  by apply: leq_trans (max_card (mem P)) _; rewrite card_ord.
move=> k j hdvd.
have [hk|hk] := boolP (k \in P); last first.
  have e1 : #|[set b : 'I_n | c b == k]| = 0.
    apply: eq_card0 => b; rewrite inE.
    by apply/negbTE; apply: contra hk => /eqP <-; exact: hPb.
  rewrite e1 div0n; apply: eq_card0 => b; rewrite inE.
  by apply/negbTE; rewrite negb_and; apply/orP; left;
     apply: contra hk => /eqP <-; exact: hPb.
have hEq : forall b : 'I_n, (c b == k) = (c' b == enum_rank_in hx0 k).
  move=> b; apply/idP/idP => [/eqP hb|/eqP hb]; first by rewrite /c' hb.
  by rewrite -(hc'K b) hb (enum_rankK_in hx0 hk).
have e1 : #|[set b : 'I_n | c b == k]|
        = #|[set b : 'I_n | c' b == enum_rank_in hx0 k]|.
  by apply: eq_card => b; rewrite !inE hEq.
have e2 : #|[set b : 'I_n | (c b == k) && (a b == j)]|
        = #|[set b : 'I_n | (c' b == enum_rank_in hx0 k) && (a b == j)]|.
  by apply: eq_card => b; rewrite !inE hEq.
by rewrite e1 e2; apply: hfair; rewrite -e1.
Qed.

Print Assumptions necklace_prime.
