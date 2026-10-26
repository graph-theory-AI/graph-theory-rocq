(** * Digraph.applications.forward_cover_disproof -- arXiv:2304.03567, Conjecture 1 is false

    This refutes X231.logarithmic_forward_cover_statement: strong digraphs need not have
    forward covers of size O(log n). The diamond chain D_m (m >= 2) has the vertices c_k, a_k,
    b_k for k in Z_m and the arcs c_k -> c_(k+1), c_k -> a_k -> c_(k+1) and
    c_k -> b_k -> c_(k+1); it is strong and has 3m vertices. The twins a_i and b_i have the
    single in-neighbour c_i and the single out-neighbour c_(i+1), so a forward path between
    them runs once around the c-cycle, from c_(i+1) to c_i, and forces c_j before c_(j+1) for
    every j other than i ([dc_twin_forces]). Two twin pairs forward connected in one ordering
    would force the whole c-cycle to increase, which is impossible ([dc_one_pair]), so every
    forward cover has at least m members ([dc_cover_size]). With m = 2^k and n = 3 * 2^k,
    c * floor(log2 n) <= c * (k + 1) < 2^k for k large, contradicting any constants c and n0.
    The construction is the one of the LLM attack write-up attacks/2304.03567__04 (deposited
    in coordination/sources/2304.03567__04); the write-up asks for m >= 3, the proof works
    from m = 2. *)
From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph strong X231.
From mathcomp Require Import zify.
From Stdlib Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ConnectCuts.
Variable T : finType.
Variable e : rel T.

(** A walk that starts inside [S] and ends outside it leaves [S] through an arc; if every arc
    leaving [S] starts at [w], the walk passes through [w]. *)
Lemma connect_exit (S : {pred T}) (w x y : T) :
  x \in S -> y \notin S ->
  (forall u v, u \in S -> v \notin S -> e u v -> u = w) ->
  connect e x y -> connect e w y.
Proof.
move=> xS yS hw /connectP [p pth yE].
elim: p x xS pth yE => [|z p IH] x xS /= pth yE.
  by move: yS; rewrite yE xS.
case/andP: pth => exz pth.
have [zS|zS] := boolP (z \in S); first exact: IH zS pth yE.
rewrite -(hw x z xS zS exz).
by apply/connectP; exists (z :: p) => //=; rewrite exz.
Qed.

(** Dually, a walk from outside [R] into [R] enters it through an arc; if every arc entering [R]
    ends at [z], the walk reaches [z]. *)
Lemma connect_entry (R : {pred T}) (z x y : T) :
  x \notin R -> y \in R ->
  (forall u v, u \notin R -> v \in R -> e u v -> v = z) ->
  connect e x y -> connect e x z.
Proof.
move=> xR yR hz /connectP [p pth yE].
elim: p x xR pth yE => [|z' p IH] x xR /= pth yE.
  by move: yR; rewrite yE (negbTE xR).
case/andP: pth => exz pth.
have [zR|zR] := boolP (z' \in R).
  by rewrite -(hz x z' xR zR exz); exact: connect1.
exact: connect_trans (connect1 exz) (IH z' zR pth yE).
Qed.

(** Along a relation that raises a rank, connected vertices are equal or strictly ordered. *)
Lemma connect_rank (r : T -> nat) (x y : T) :
  (forall u v, e u v -> r u < r v) -> connect e x y -> (x == y) || (r x < r y).
Proof.
move=> hr /connectP [p pth ->] {y}.
elim: p x pth => [|z p IH] x /=; first by rewrite eqxx.
case/andP => exz pth.
apply/orP; right; have := IH z pth; case/orP => [/eqP <-|hz]; first exact: hr.
exact: ltn_trans (hr _ _ exz) hz.
Qed.

End ConnectCuts.

From mathcomp Require Import all_algebra.
Import GRing.Theory.

(** ** The diamond chain D_m (m >= 2): vertices (k, t), k in Z_m, t = 0 (c_k), 1 (a_k), 2 (b_k);
    arcs c_k -> c_(k+1), c_k -> a_k -> c_(k+1), c_k -> b_k -> c_(k+1). *)
Section DiamondChain.
Variable m' : nat.
Local Notation m := m'.+2.
Local Open Scope ring_scope.

Definition dc_arc (u v : 'Z_m * 'I_3) : bool :=
  if u.2 == ord0 then (if v.2 == ord0 then v.1 == u.1 + 1 else v.1 == u.1)
  else (v.2 == ord0) && (v.1 == u.1 + 1).

Definition dchain : Type := ('Z_m * 'I_3)%type.
HB.instance Definition _ := Finite.on dchain.
HB.instance Definition _ := HasArc.Build dchain dc_arc.

Lemma dc_arcE (u v : dchain) : (u --> v) = dc_arc u v.
Proof. by []. Qed.

(** Every arc either advances the cycle index to a c-vertex, or goes from c_k to a_k / b_k. *)
Lemma dc_arc_cases (u v : dchain) :
  u --> v -> ((v.1 == u.1 + 1) && (v.2 == ord0)) || [&& v.1 == u.1, u.2 == ord0 & v.2 != ord0].
Proof.
rewrite dc_arcE /dc_arc; case: (u.2 == ord0) => /=; case: (v.2 == ord0) => //= /eqP ->;
  rewrite ?eqxx ?orbT //.
Qed.

(** Cyclic distance from s to k along the c-cycle. *)
Definition cdist (s k : 'Z_m) : nat := val (k - s).

Lemma cdist_lt (s k : 'Z_m) : (cdist s k < m)%N.
Proof. exact: ltn_ord. Qed.

Lemma cdist_inj (s k k' : 'Z_m) : cdist s k = cdist s k' -> k = k'.
Proof. by move/val_inj/addIr. Qed.

Lemma cdist_pred (i : 'Z_m) : cdist (i + 1) i = m.-1.
Proof. by rewrite /cdist opprD addrA subrr add0r /= modn_small. Qed.

Lemma cdist_succ (s k : 'Z_m) : (cdist s k < m.-1)%N -> cdist s (k + 1) = (cdist s k).+1.
Proof.
rewrite /cdist addrAC; move: (k - s) => w h.
case: w h => v hv /= h.
rewrite modn_small.
  have -> : Zp_trunc m = m' by [].
  by rewrite (modn_small (isT : (1 < m'.+2)%N)) addn1 ltnS.
by rewrite (modn_small (isT : (1 < m'.+2)%N)) addn1.
Qed.

Definition dc_c (k : 'Z_m) : dchain := (k, ord0).

(** a_k and b_k have the single out-neighbour c_(k+1) and the single in-neighbour c_k. *)
Lemma dc_twin_out (i : 'Z_m) (t : 'I_3) (v : dchain) :
  t != ord0 -> ((i, t) : dchain) --> v -> v = dc_c (i + 1).
Proof.
move=> t0; rewrite dc_arcE /dc_arc /= (negbTE t0) => /andP [/eqP v2 /eqP v1].
by case: v v1 v2 => k t' /= -> ->.
Qed.

Lemma dc_twin_in (i : 'Z_m) (t : 'I_3) (u : dchain) :
  t != ord0 -> u --> ((i, t) : dchain) -> u = dc_c i.
Proof.
move=> t0; rewrite dc_arcE /dc_arc /= (negbTE t0).
case: u => k t' /=.
by case: eqP => [-> /eqP -> //|].
Qed.

(** THE KEY LEMMA: forward-connecting the twins a_i, b_i forces c_j < c_(j+1) for every j != i. *)
Lemma dc_twin_forces (r : dchain -> nat) (i : 'Z_m) (t1 t2 : 'I_3) :
  t1 != ord0 -> t2 != ord0 -> t1 != t2 ->
  connect (x231_forward_arc r) (i, t1) (i, t2) ->
  forall j : 'Z_m, j != i -> (r (dc_c j) < r (dc_c (j + 1)%R))%N.
Proof.
move=> t10 t20 t12 hconn j ji.
(* a_i's only out-neighbour is c_(i+1) *)
have hstart : connect (x231_forward_arc r) (dc_c (i + 1)) (i, t2).
  case/connectP: hconn => [[|z p]] /=.
    by move=> _ [] /eqP; rewrite eq_sym (negbTE t12).
  case/andP => /andP [/dc_twin_out-/(_ t10) -> _] pth hlast.
  by apply/connectP; exists p.
pose s := i + 1.
pose dj := cdist s j.
have hjm : (dj < m.-1)%N.
  have hlt : (dj <= m.-1)%N by rewrite -ltnS prednK //; exact: cdist_lt.
  rewrite ltn_neqAle hlt andbT.
  apply/negP => /eqP hdj; move/negP: ji; apply; apply/eqP.
  by apply: (cdist_inj (s := s)); rewrite -/dj hdj cdist_pred.
(* S: the cycle segment from c_(i+1) up to c_j, left only through c_j *)
pose S := [pred v : dchain | (cdist s v.1 < dj)%N || (v == dc_c j)].
have hs0 : cdist s s = 0%N by rewrite /cdist subrr.
have hsS : dc_c (i + 1) \in S.
  rewrite inE /= -/s hs0.
  case: (eqVneq dj 0%N) => [dj0|djn0]; last by apply/orP; left; rewrite lt0n.
  apply/orP; right; apply/eqP; congr dc_c.
  by apply: (cdist_inj (s := s)); rewrite hs0 -dj0.
have hyS : ((i, t2) : dchain) \notin S.
  have hi : cdist s i = m.-1 := cdist_pred i.
  rewrite inE /= negb_or hi -leqNgt (ltnW hjm) /=.
  by apply/negP => /eqP [_ /eqP]; rewrite (negbTE t20).
have hexits : forall u v : dchain, u \in S -> v \notin S -> x231_forward_arc r u v -> u = dc_c j.
  move=> u v uS vS /andP [/dc_arc_cases harc _].
  move: uS; rewrite inE /= => /orP [hu|/eqP //]; exfalso; move: vS; rewrite inE /= negb_or.
  case/orP: harc => [/andP [/eqP v1 /eqP v2]|/and3P [/eqP v1 _ _]]; last by rewrite v1 hu.
  have hsu : cdist s v.1 = (cdist s u.1).+1 by rewrite v1 cdist_succ // (ltn_trans hu hjm).
  case/andP => hnlt; apply/negP; rewrite negbK.
  have hvj : cdist s v.1 = dj.
    by apply/eqP; rewrite eqn_leq -(negbK (dj <= _)%N) -ltnNge hnlt andbT hsu; exact: hu.
  apply/eqP; case: v v1 v2 hsu hvj {hnlt} => vk vt /= _ -> _ hvj.
  by congr (_, _); apply: (cdist_inj (s := s)).
have hmid : connect (x231_forward_arc r) (dc_c j) (i, t2) := connect_exit hsS hyS hexits hstart.
(* R: the cycle segment after c_j, entered only at c_(j+1) *)
pose R := [pred v : dchain | (dj < cdist s v.1)%N].
have hjR : dc_c j \notin R by rewrite inE /= ltnn.
have hyR : ((i, t2) : dchain) \in R by rewrite inE /= (cdist_pred i).
have hentries : forall u v : dchain, u \notin R -> v \in R -> x231_forward_arc r u v -> v = dc_c (j + 1).
  move=> u v; rewrite !inE /= -leqNgt => hu hv /andP [/dc_arc_cases harc _].
  case/orP: harc => [/andP [/eqP v1 /eqP v2]|/and3P [/eqP v1 _ _]].
    2: by move: hv; rewrite v1 ltnNge hu.
  have hsu : cdist s v.1 = (cdist s u.1).+1 by rewrite v1 cdist_succ // (leq_ltn_trans hu hjm).
  have huj : u.1 = j.
    apply: (cdist_inj (s := s)); apply/eqP; rewrite -/dj eqn_leq hu /=.
    by move: hv; rewrite hsu ltnS.
  by case: v v1 v2 {hv hsu} => vk vt /= -> ->; rewrite huj.
have hjj := connect_entry hjR hyR hentries hmid.
have := connect_rank (r := r) (fun u v (h : x231_forward_arc r u v) => proj2 (andP h)) hjj.
case/orP => [/eqP [] /eqP|//].
by rewrite -subr_eq0 opprD addrA subrr add0r oppr_eq0 oner_eq0.
Qed.

(** No ranking increases strictly all around the c-cycle. *)
Lemma dc_cycle_absurd (r : dchain -> nat) :
  ~ (forall j : 'Z_m, (r (dc_c j) < r (dc_c (j + 1)%R))%N).
Proof.
move=> h; case: (arg_minnP (fun j : 'Z_m => r (dc_c j)) (isT : predT 0)) => j0 _ hmin.
have := h (j0 - 1); rewrite subrK.
by rewrite ltnNge hmin.
Qed.

Definition dc_a (k : 'Z_m) : dchain := (k, @Ordinal 3 1 isT).
Definition dc_b (k : 'Z_m) : dchain := (k, @Ordinal 3 2 isT).

(** A ranking forward-covers the twin pair {a_i, b_i}. *)
Definition dc_covers (r : dchain -> nat) (i : 'Z_m) : bool :=
  connect (x231_forward_arc r) (dc_a i) (dc_b i) || connect (x231_forward_arc r) (dc_b i) (dc_a i).

Lemma dc_covers_forces (r : dchain -> nat) (i j : 'Z_m) :
  dc_covers r i -> j != i -> (r (dc_c j) < r (dc_c (j + 1)%R))%N.
Proof. by case/orP => h; apply: (dc_twin_forces _ _ _ h). Qed.

(** One ranking forward-covers at most one twin pair. *)
Lemma dc_one_pair (r : dchain -> nat) (i k : 'Z_m) :
  dc_covers r i -> dc_covers r k -> i = k.
Proof.
move=> hi hk; apply/eqP/negPn/negP => ik; apply: (dc_cycle_absurd (r := r)) => j.
have [ji|ji] := eqVneq j i; last exact: dc_covers_forces hi ji.
by apply: (dc_covers_forces hk); rewrite ji.
Qed.

(** Any family of rankings that forward-covers every twin pair has at least m members. *)
Lemma dc_cover_size (rs : seq (dchain -> nat)) :
  (forall i : 'Z_m, has (fun r => dc_covers r i) rs) -> (m <= size rs)%N.
Proof.
move=> h.
have hf : forall i : 'Z_m, (find (dc_covers^~ i) rs < size rs)%N by move=> i; rewrite -has_find.
pose f (i : 'Z_m) : 'I_(size rs) := Ordinal (hf i).
have finj : injective f.
  move=> i k /(congr1 val) /= hik.
  have ci := nth_find (fun _ => 0%N) (h i).
  have ck := nth_find (fun _ => 0%N) (h k).
  by rewrite hik in ci; exact: dc_one_pair ci ck.
have := leq_card f finj.
by rewrite !card_ord.
Qed.

(** ** D_m is strongly connected *)
Lemma dc_cc_arc (k : 'Z_m) : dc_c k --> dc_c (k + 1).
Proof. by rewrite dc_arcE /dc_arc /= eqxx. Qed.

Lemma dc_cc_connect (k : 'Z_m) (n : nat) : connect (@arc dchain) (dc_c k) (dc_c (k + n%:R)).
Proof.
elim: n => [|n IH]; first by rewrite addr0 connect0.
apply: connect_trans IH _.
by rewrite -[n.+1]addn1 natrD addrA; apply/connect1/dc_cc_arc.
Qed.

Lemma dc_strong : strongb dchain.
Proof.
apply/strongP => -[k t] [k' t'].
have hck : forall k1 k2 : 'Z_m, connect (@arc dchain) (dc_c k1) (dc_c k2).
  by move=> k1 k2; have := dc_cc_connect k1 (val (k2 - k1)); rewrite natr_Zp addrC subrK.
have hout : connect (@arc dchain) ((k, t) : dchain) (dc_c k) \/ connect (@arc dchain) ((k, t) : dchain) (dc_c (k + 1)).
  case: (eqVneq t ord0) => [->|t0]; first by left; exact: connect0.
  right; apply: connect1; by rewrite dc_arcE /dc_arc /= (negbTE t0) !eqxx.
have hin : connect (@arc dchain) (dc_c k') ((k', t') : dchain).
  case: (eqVneq t' ord0) => [->|t0]; first exact: connect0.
  apply: connect1; rewrite dc_arcE /dc_arc /=.
  by rewrite (negbTE t0) eqxx.
case: hout => h; exact: connect_trans h (connect_trans (hck _ _) hin).
Qed.

End DiamondChain.

(** ** Arithmetic *)
Lemma sq_lt_exp2 (k : nat) : 5 <= k -> k * k < 2 ^ k.
Proof.
elim: k => [//|k IH] hk.
case: (eqVneq k 4) => [-> //|k4].
have hk' : 4 < k by rewrite ltn_neqAle eq_sym k4 -ltnS.
have := IH hk'; rewrite expnS; move: (2 ^ k) => X hX.
nia.
Qed.

Lemma trunc_log_3pow2 (k : nat) : trunc_log 2 (3 * 2 ^ k) <= k.+1.
Proof.
have h3 : 0 < 3 * 2 ^ k by rewrite muln_gt0 expn_gt0.
have := trunc_logP (isT : 1 < 2) h3.
have hlt : 3 * 2 ^ k < 2 ^ k.+2 by rewrite !expnS mulnA ltn_pmul2r ?expn_gt0.
move=> hle; have := leq_ltn_trans hle hlt; rewrite ltn_exp2l //.
Qed.


(** ** The disproof: D_m with m = 2^k needs m orderings, which beats c * log(3m). *)
Theorem logarithmic_forward_cover_disproved : ~ logarithmic_forward_cover_statement.
Proof.
move=> [c [n0 h]].
pose k := c + n0 + 5.
have hk5 : 5 <= k by rewrite /k leq_addl.
have hkpos : 1 < 2 ^ k by rewrite -{1}(expn0 2) ltn_exp2l //; lia.
pose m' := (2 ^ k).-2.
have hm : m'.+2 = 2 ^ k by rewrite /m' -subn2 -subSn ?subSS ?subn0 //; lia.
have hcard : #|{: dchain m'}| = 3 * 2 ^ k by rewrite /dchain card_prod !card_ord mulnC hm.
have hn0 : n0 <= #|{: dchain m'}|.
  rewrite hcard; have := sq_lt_exp2 hk5; rewrite /k; move: (2 ^ _) => X; nia.
have [rs [[_ hcov] hsize]] := h (dchain m') (dc_strong m') hn0.
have hall : forall i : 'Z_m'.+2, has (fun r : {ffun dchain m' -> nat} => dc_covers r i) rs.
  move=> i; have := hcov (dc_a i) (dc_b i).
  by rewrite /dc_a /dc_b xpair_eqE eqxx /=; apply.
have hlow : m'.+2 <= size rs.
  have := @dc_cover_size m' [seq (fun x : dchain m' => r x) | r : {ffun dchain m' -> nat} <- rs].
  rewrite size_map; apply => i; rewrite has_map; exact: hall i.
have hlog := trunc_log_3pow2 k.
have hsq := sq_lt_exp2 hk5.
move: (leq_trans hlow hsize); rewrite hm hcard => hbad.
have hb2 : 2 ^ k <= c * k.+1 by apply: (leq_trans hbad); rewrite leq_mul2l hlog orbT.
move: hb2 hsq; rewrite /k; move: (2 ^ _) => X; nia.
Qed.
Print Assumptions logarithmic_forward_cover_disproved.
