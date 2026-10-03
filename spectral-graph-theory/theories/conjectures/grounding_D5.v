(** * Spectral.conjectures.grounding_D5 — grounding lemmas for milestone D5.

    SIMPLE, Qed-closed sanity results validating the NEW area-specific primitives
    introduced in [D5.v].  D5's spectral matrix vocabulary ([adjmx], [Lapmx],
    [is_signing], [spectral_radius_le], [is_spectrum], [cospectral], the labelled-graph
    density [total_count]/[determined_count]) lives in the area-local foundation
    [Spectral.foundations.spectral]; the genuinely NEW combinatorial primitives DEFINED
    in [D5.v] are four:

      - [strongly_regular]  (Row 1, with the PRIMITIVITY guards: connected, 0<k<n-1),
      - [proper_colb]       (Row 4, proper boolean colouring),
      - [csf_coeff]         (Row 4, chromatic-symmetric-function monomial coefficient),
      - [same_csf]          (Row 4, equality of chromatic symmetric functions).

    For each we record a SATISFIABLE witness AND at least one textbook identity.  These
    are statement-validation lemmas, NOT the (open) conjectures themselves.

    Headline witness: [strongly_regular 'K_2,2].  The complete bipartite graph
    [K_{2,2}] = [C_4] is the smallest PRIMITIVE strongly-regular graph (parameters
    [(n,k,lam,mu) = (4,2,0,2)]); proving it satisfies the GUARDED [strongly_regular]
    shows the faithfulness fix (adding connectedness and [0 < k < n-1]) did NOT make the
    predicate vacuously unsatisfiable — a genuine SRG still qualifies, while the trivial
    edgeless / complete / matching graphs are now excluded.  Being triangle-free
    ([tf_K22]) it would even be a candidate witness for Row 1's existential. *)

From GTBase Require Import base.
From mathcomp Require Import all_algebra perm.
From Spectral Require Import foundations.spectral.
From Spectral.conjectures Require Import D5.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ============================================================================
    Row 1 — [strongly_regular] (guarded).
    ========================================================================== *)

(** SATISFIABLE WITNESS.  The complete bipartite graph [K_{2,2}] = [C_4] is strongly
    regular with parameters [k = 2], [lam = 0], [mu = 2]: connected, [2]-regular,
    [0 < 2 < 4-1 = 3], adjacent vertices (opposite sides) share no neighbour, and
    distinct non-adjacent vertices (same side) share both vertices of the other side.
    This certifies that the PRIMITIVITY-guarded definition is still inhabited. *)
Lemma sr_K22 : strongly_regular 'K_2,2.
Proof.
exists 2, 0, 2; split.
- exact: (@Knm_connected 1 1).
- by split=> //; rewrite card_sum !card_ord.
- by move=> [x|y]; rewrite ?deg_Knm_l ?deg_Knm_r.
- move=> [x|x] [y|y] uv //.
  + rewrite /common_nbr opn_Knm_l opn_Knm_r.
    apply/eqP; rewrite cards_eq0; apply/eqP/setP => z; rewrite !inE.
    by case: z => z; apply/andP => -[/imsetP[? _ ?] /imsetP[? _ ?]].
  + rewrite /common_nbr opn_Knm_l opn_Knm_r.
    apply/eqP; rewrite cards_eq0; apply/eqP/setP => z; rewrite !inE.
    by case: z => z; apply/andP => -[/imsetP[? _ ?] /imsetP[? _ ?]].
- move=> [x|x] [y|y] _ nadj //.
  + by rewrite /common_nbr !opn_Knm_l setIid card_imset ?cardsT ?card_ord //; exact: inr_inj.
  + by rewrite /common_nbr !opn_Knm_r setIid card_imset ?cardsT ?card_ord //; exact: inl_inj.
Qed.

(** TEXTBOOK IDENTITY.  [K_{2,2}] is triangle-free (bipartite), so [sr_K22] is in fact a
    candidate witness for the Row-1 existential, and confirms the [lam = 0] reading. *)
Lemma tf_K22 : triangle_free 'K_2,2.
Proof. by move=> [x|x] [y|y] [z|z]. Qed.

(** TEXTBOOK IDENTITY (projection).  Every strongly-regular graph is connected and
    regular for some degree — the guards are genuine consequences. *)
Lemma strongly_regular_connected (G : sgraph) :
  strongly_regular G -> connected [set: G].
Proof. by case=> k [lam] [mu] [] . Qed.

Lemma strongly_regular_regular (G : sgraph) :
  strongly_regular G -> exists k, regular G k.
Proof. by case=> k [lam] [mu] [_ _ rk _ _]; exists k. Qed.

(** ============================================================================
    Row 4 — [proper_colb].
    ========================================================================== *)

(** TEXTBOOK IDENTITY.  A "rainbow" (injective) colouring is always proper: distinct
    colours on every vertex trivially separate adjacent ones. *)
Lemma proper_colb_inj (G : sgraph) k (c : {ffun G -> 'I_k}) :
  injective c -> proper_colb c.
Proof.
exact: colourings.proper_colouring_injective.
Qed.

(** SATISFIABLE WITNESS.  The identity colouring of [K_2] (a [2]-colouring of an edge)
    is proper. *)
Lemma proper_colb_K2 : proper_colb [ffun x : 'K_2 => x].
Proof. by apply: proper_colb_inj => a b; rewrite !ffunE. Qed.

(** ============================================================================
    Row 4 — [csf_coeff].
    ========================================================================== *)

(** Helper / TEXTBOOK IDENTITY.  The colour classes of any [k]-colouring partition the
    vertex set, so their sizes sum to [#|G|]. *)
Lemma csf_fibre_sum (G : sgraph) k (c : {ffun G -> 'I_k}) :
  \sum_(b : 'I_k) #|[set x | c x == b]| = #|G|.
Proof.
rewrite -sum1_card (partition_big c predT) //=.
by apply: eq_bigr => b _; rewrite sum1dep_card.
Qed.

(** TEXTBOOK IDENTITY.  A monomial coefficient of the chromatic symmetric function
    vanishes unless the prescribed colour-class sizes [a] form a composition of [#|G|]:
    [csf_coeff] is supported on the compositions of [n]. *)
Lemma csf_coeff_eq0 (G : sgraph) k (a : 'I_k -> nat) :
  \sum_(b : 'I_k) a b != #|G| -> csf_coeff G a = 0.
Proof.
move=> Hne; apply/eqP; rewrite cards_eq0 -subset0; apply/subsetP => c.
rewrite !inE => /andP[_ /forallP Hsz]; exfalso.
move/negP: Hne; apply; apply/eqP.
rewrite -(csf_fibre_sum c); apply: eq_bigr => b _.
by rewrite (eqP (Hsz b)).
Qed.

(** SATISFIABLE WITNESS.  The one-vertex graph [K_1] has a non-zero monomial
    coefficient for the size-vector [a = (1)] (its single proper [1]-colouring), so
    [csf_coeff] is not identically zero. *)
Lemma csf_coeff_K1 : 0 < csf_coeff ('K_1) (fun _ : 'I_1 => 1).
Proof.
rewrite /csf_coeff card_gt0; apply/set0Pn; exists [ffun _ => ord0].
rewrite inE; apply/andP; split.
- exact: colourings.proper_colouring_K1.
apply/forallP=> b; rewrite (ord1 b) /=.
by rewrite (eq_card1 (x := ord0)) // => x; rewrite !inE ffunE eqxx (ord1 x).
Qed.

(** ============================================================================
    Row 4 — [same_csf].
    ========================================================================== *)

(** SATISFIABLE WITNESS + TEXTBOOK IDENTITY.  [same_csf] is an equivalence relation:
    reflexive (every graph has the same CSF as itself — the witness), symmetric, and
    transitive. *)
Lemma same_csf_refl (G : sgraph) : same_csf G G.
Proof. by move=> k a. Qed.

Lemma same_csf_sym (G H : sgraph) : same_csf G H -> same_csf H G.
Proof. by move=> h k a; rewrite h. Qed.

Lemma same_csf_trans (G H K : sgraph) :
  same_csf G H -> same_csf H K -> same_csf G K.
Proof. by move=> h1 h2 k a; rewrite h1 h2. Qed.

(** ============================================================================
    Rows 2, 3, 5 — the area-local SPECTRAL foundation vocabulary
    ([is_signing], [spectral_radius_le], [total_count]/[is_lgraph],
    [is_deg_sorted], [is_spectrum]) that D5's three spectral rows are built on.
    These records are appended AFTER the Row-1/Row-4 lemmas so that opening
    [ring_scope] here does not affect any of the combinatorial lemmas above.
    ========================================================================== *)

From mathcomp Require Import order.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** SATISFIABLE WITNESS (Row 2).  The plain adjacency matrix is itself a symmetric
    signing (all edge entries [+1]); this inhabits [is_signing], so the Row-2
    existential [exists S, is_signing S /\ ...] is not over an empty domain. *)
Lemma is_signing_adjmx (R:rcfType) (G:sgraph) : is_signing (adjmx R G).
Proof.
split.
- by move=> i j; rewrite !mxE (@sg_sym G (enum_val i) (enum_val j)).
- move=> i j; rewrite !mxE; case: (enum_val i -- enum_val j).
  + by left.
  + by [].
Qed.

(** GUARD-HAS-TEETH (Row 2).  On [K_2] (which has an edge) the ZERO matrix is NOT a
    signing: the edge clause forces a [±1] entry, so [is_signing] genuinely
    constrains edges and is not vacuously satisfiable by the trivial matrix. *)
Lemma is_signing_zero_no_teeth (R:rcfType) :
  ~ is_signing (G:='K_2) (0 : 'M[R]_(#|'K_2|)).
Proof.
move=> [_ He].
have Hab : (ord0 : 'K_2) -- (@Ordinal 2 1 isT : 'K_2).
  by rewrite /edge_rel /=.
move: (He (enum_rank (ord0 : 'K_2)) (enum_rank (@Ordinal 2 1 isT : 'K_2))).
rewrite !enum_rankK Hab !mxE.
move=> [] /eqP; first by rewrite eq_sym oner_eq0.
by rewrite eq_sym oppr_eq0 oner_eq0.
Qed.

(** STRUCTURAL LAW (Row 2).  [spectral_radius_le] is monotone in the bound [b]:
    if all eigenvalues are [<= b] and [b <= b'] then they are [<= b'].  Confirms
    the intended "all eigenvalues bounded by [b]" reading of the predicate. *)
Lemma spectral_radius_le_mono (R:rcfType) n (A:'M[R]_n) (b b':R) :
  b <= b' -> spectral_radius_le A b -> spectral_radius_le A b'.
Proof. move=> hb H x /H hx; exact: (Order.le_trans hx hb). Qed.

(** BOUND ARITHMETIC AT [d = 2] (Row 2).  At the smallest Ramanujan degree [d = 2]
    the target bound [2*sqrt(d-1)] appearing in the Row-2 statement collapses to
    exactly [2 = d], since [sqrt(2-1) = sqrt 1 = 1].  This records the numeric reason
    [d = 2] is the boundary: a Gershgorin/Perron-type bound (every eigenvalue of a
    [d]-regular adjacency matrix has magnitude [<= d]) would meet the Ramanujan target
    [2*sqrt(d-1)] EXACTLY when [d = 2] and STRICTLY fails it for [d >= 3] (there
    [2*sqrt(d-1) < d]), where the full Marcus-Spielman-Srivastava interlacing-families
    theorem is required.  NOTE: this is ONLY the arithmetic of the bound expression at
    [d = 2]; it is NOT the eigenvalue-magnitude bound (that bound is not available in
    the imported libraries — see the D5 ledger blocker). *)
Lemma ramanujan_bound_d2 (R:rcfType) :
  2%:R * Num.sqrt (2%N.-1)%:R = 2%:R :> R.
Proof. by rewrite /= sqrtr1 mulr1. Qed.

(** SATISFIABLE WITNESS (Row 3).  There is always at least one labelled [n]-graph
    (the edgeless one), so [total_count n > 0] and the spectral-determination
    density [determined_count n / total_count n] has a non-zero denominator. *)
Lemma total_count_gt0 (n:nat) : (0 < total_count n)%N.
Proof.
rewrite /total_count card_gt0; apply/set0Pn.
exists [ffun _ => false].
rewrite inE /is_lgraph; apply/andP; split.
- by apply/forallP => p; rewrite !ffunE.
- by apply/forallP => i; rewrite ffunE.
Qed.

(** SATISFIABLE WITNESS (Row 5).  The non-increasing sort of the degree sequence is
    a valid [is_deg_sorted] witness (a permutation of [degseq G] that is [geq]-
    sorted), so the Row-5 body [forall d, is_deg_sorted G d -> ...] is not vacuous. *)
Lemma is_deg_sorted_sort (G:sgraph) : is_deg_sorted G (sort geq (degseq G)).
Proof.
split; first by rewrite perm_sort.
by apply: sort_sorted => x y; exact: leq_total.
Qed.

(** SATISFIABLE WITNESS (Row 5).  The empty spectrum is the spectrum of the [0x0]
    matrix ([char_poly] of a [0x0] matrix is [1 = \prod_(x <- [::]) ...]), so the
    factorisation predicate [is_spectrum] the Row-5 [forall] hinges on is inhabited. *)
Lemma is_spectrum_nil (R:rcfType) (A:'M[R]_0) : is_spectrum A [::].
Proof.
split=> //.
by rewrite big_nil /char_poly det_mx00.
Qed.

(** ============================================================================
    TECHNIQUE #3 — independent re-encodings + proved [<->].

    Two load-bearing definitions of this package are each given a SECOND,
    structurally unrelated encoding, and the two are proved equivalent (Qed,
    axiom-free).  Agreement between the two independent formalisations is the
    faithfulness evidence.

    (1) [liso] (foundations/spectral): the combinatorial "relation-preserving
        vertex bijection" definition, re-encoded ALGEBRAICALLY as permutation-
        matrix similarity of the integer adjacency matrices
        ([ladjmx r' = P^-1 A P] with [P = perm_mx s]).  Bridge [lisoE].

    (2) [strongly_regular] (conjectures/D5): the combinatorial neighbour-counting
        definition, re-encoded as the classical SRG MATRIX identity
        [A^2 = k I + lam A + mu (J - I - A)] over [int].  Bridge [strongly_regularE].
    ========================================================================== *)

(** ---- (1) [liso] : combinatorial bijection  <->  permutation-matrix similarity ---- *)

(** ALGEBRAIC re-encoding: [r] and [r'] are isomorphic iff their integer adjacency
    matrices are conjugate by a permutation matrix (simultaneous row+column
    relabelling), the textbook "similar via a permutation matrix" characterisation. *)
Definition liso2 (n : nat) (r r' : ladj n) : bool :=
  [exists s : 'S_n, ladjmx r' == perm_mx s *m ladjmx r *m perm_mx s^-1].

(** Entry of the conjugated matrix: [(P A P^-1) i j = A (s i) (s j)]. *)
Lemma ladjmx_conjE (n:nat) (r:ladj n) (s:'S_n) (i j : 'I_n) :
  (perm_mx s *m ladjmx r *m perm_mx s^-1) i j = ladjmx r (s i) (s j).
Proof. by rewrite -col_permE -row_permE !mxE. Qed.

(** The 0/1 image of a boolean injects into [int]. *)
Lemma int01_inj (b c : bool) :
  ((if b then 1 else 0) : int) = (if c then 1 else 0) -> b = c.
Proof.
by case: b; case: c => //= /eqP; rewrite ?oner_eq0 // eq_sym oner_eq0.
Qed.

(** For a FIXED permutation [s], relation-preservation and matrix conjugation agree. *)
Lemma liso_clause_matE (n:nat) (r r':ladj n) (s:'S_n) :
  [forall i, [forall j, r (s i, s j) == r' (i, j)]]
   = (ladjmx r' == perm_mx s *m ladjmx r *m perm_mx s^-1).
Proof.
apply/idP/idP.
- move=> /forallP H; apply/eqP/matrixP => i j.
  move: (H i) => /forallP /(_ j) /eqP Hij.
  by rewrite ladjmx_conjE !mxE Hij.
- move=> /eqP /matrixP H; apply/forallP => i; apply/forallP => j; apply/eqP.
  move: (H i j); rewrite ladjmx_conjE !mxE => /int01_inj ->.
  by [].
Qed.

(** MAIN BRIDGE (1): the combinatorial and matrix isomorphism predicates coincide. *)
Lemma lisoE (n:nat) (r r':ladj n) : liso r r' = liso2 r r'.
Proof.
by apply: eq_existsb => s; rewrite liso_clause_matE.
Qed.

(** ---- (2) [strongly_regular] : neighbour counting  <->  adjacency-matrix identity ---- *)
Lemma mulif (P Q : bool) :
  ((if P then 1 else 0) : int) * (if Q then 1 else 0) = if P && Q then 1 else 0.
Proof. by case: P; case: Q; rewrite ?mul0r ?mul1r ?mulr0. Qed.

Lemma card_evpre (G:sgraph) (Q : pred G) :
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

Lemma count_cn (G:sgraph) (a b : G) :
  #|[set k : 'I_#|G| | (a -- enum_val k) && (enum_val k -- b)]| = #|common_nbr a b|.
Proof.
rewrite (card_evpre (fun v => (a -- v) && (v -- b))).
suff -> : [set v : G | (a -- v) && (v -- b)] = common_nbr a b by [].
rewrite /common_nbr; apply/setP => v; rewrite !inE.
by rewrite (@sg_sym G v b).
Qed.

Lemma adjmx2_common (G:sgraph) (i j : 'I_#|G|) :
  (adjmx int G *m adjmx int G) i j
   = #|common_nbr (enum_val i) (enum_val j)|%:R.
Proof.
rewrite mxE.
under eq_bigr => k _ do rewrite !mxE mulif.
rewrite -big_mkcond.
rewrite (eq_bigr (fun _ => (1%N)%:R : int)); last by move=> k _; rewrite mulr1n.
rewrite -natr_sum sum1dep_card; congr (_ %:R).
by move: (enum_val i) (enum_val j) => a b; exact: count_cn.
Qed.

Definition sr_clauses (G:sgraph) (k lam mu : nat) : Prop :=
  [/\ regular G k,
      (forall u v : G, u -- v -> #|common_nbr u v| = lam) &
      (forall u v : G, u != v -> ~~ (u -- v) -> #|common_nbr u v| = mu)].

Definition sr_mateq (G : sgraph) (k lam mu : nat) : Prop :=
  adjmx int G *m adjmx int G
    = k%:R%:M + lam%:R *: adjmx int G
      + mu%:R *: (const_mx 1 - 1%:M - adjmx int G).

Lemma natr_int_inj (a b : nat) : (a%:R = b%:R :> int) -> a = b.
Proof. by move=> /eqP; rewrite eqr_nat => /eqP. Qed.

Lemma sr_rhs_diag (G:sgraph) (k lam mu:nat) (i:'I_#|G|) :
  (k%:R%:M + lam%:R *: adjmx int G + mu%:R *: (const_mx 1 - 1%:M - adjmx int G)) i i = k%:R.
Proof.
by rewrite !mxE eqxx sg_irrefl mulr0 mulr1n subr0 addr0 mulr0 addr0.
Qed.

Lemma sr_rhs_off (G:sgraph) (k lam mu:nat) (i j:'I_#|G|) : i != j ->
  (k%:R%:M + lam%:R *: adjmx int G + mu%:R *: (const_mx 1 - 1%:M - adjmx int G)) i j
  = lam%:R * (if enum_val i -- enum_val j then 1 else 0)
    + mu%:R * (if enum_val i -- enum_val j then 0 else 1).
Proof.
move=> nij; rewrite !mxE (negbTE nij) mulr0n add0r subr0.
by case: (enum_val i -- enum_val j); rewrite ?subrr ?subr0.
Qed.

Lemma sr_mateqE (G:sgraph) (k lam mu : nat) :
  sr_mateq G k lam mu <-> sr_clauses G k lam mu.
Proof.
rewrite /sr_mateq /sr_clauses; split.
- move=> Heq; split.
  + move=> v; move: Heq => /matrixP/(_ (enum_rank v) (enum_rank v)).
    rewrite adjmx2_common sr_rhs_diag => /natr_int_inj.
    by rewrite enum_rankK /common_nbr setIid.
  + move=> u v uv; have nij : enum_rank u != enum_rank v.
      by rewrite (inj_eq enum_rank_inj) (sg_edgeNeq uv).
    move: Heq => /matrixP/(_ (enum_rank u) (enum_rank v)).
    rewrite adjmx2_common (sr_rhs_off _ _ _ nij) !enum_rankK uv.
    by rewrite mulr1 mulr0 addr0 => /natr_int_inj.
  + move=> u v ne nadj; have nij : enum_rank u != enum_rank v.
      by rewrite (inj_eq enum_rank_inj) (negbTE ne).
    move: Heq => /matrixP/(_ (enum_rank u) (enum_rank v)).
    rewrite adjmx2_common (sr_rhs_off _ _ _ nij) !enum_rankK (negbTE nadj).
    by rewrite mulr0 mulr1 add0r => /natr_int_inj.
- move=> [rk hlam hmu]; apply/matrixP => i j.
  rewrite adjmx2_common.
  case: (eqVneq i j) => [->|nij].
  + by rewrite sr_rhs_diag /common_nbr setIid (rk (enum_val j)).
  + rewrite (sr_rhs_off _ _ _ nij).
    case: (boolP (enum_val i -- enum_val j)) => [adj|nadj].
    * by rewrite mulr1 mulr0 addr0 (hlam _ _ adj).
    * rewrite mulr0 mulr1 add0r hmu //.
      by apply: contra_neq nij => /enum_val_inj ->.
Qed.

Definition strongly_regular_alg (G : sgraph) : Prop :=
  exists k lam mu : nat,
    [/\ connected [set: G], (0 < k)%N /\ (k < (#|G|).-1)%N & sr_mateq G k lam mu].

Lemma strongly_regularE (G : sgraph) :
  strongly_regular G <-> strongly_regular_alg G.
Proof.
split.
- case=> k [lam] [mu] [conn kk rk hlam hmu].
  exists k, lam, mu; split=> //.
  by apply/sr_mateqE; split.
- case=> k [lam] [mu] [conn kk /sr_mateqE [rk hlam hmu]].
  by exists k, lam, mu; split.
Qed.
