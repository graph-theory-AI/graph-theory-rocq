(** * Digraph.conjectures.grounding_X221 — faithfulness grounding for wave X221

    GROUNDING (not new mathematics): satisfiability witnesses, structural laws
    and guard-has-teeth facts for the seven statements of [X221.v].

    Coverage, statement by statement:
      - [delta122_hero_k1_plus_dipath2_free_statement] : NON-VACUITY — every
        transitive tournament [TT n] lies in the guarded class, so the class is
        infinite ([x221_TT_in_class]); TEETH — dropping the [oriented_dg] guard
        puts a single vertex with a loop in the class, and that digraph is not
        dicolourable for ANY number of colours ([x221_loop_not_dicolorable]),
        which would refute the statement for a reason unrelated to the question.
      - [delta122_hero_oriented_complete_multipartite_statement] : NON-VACUITY —
        every [TT n] is oriented complete multipartite and Delta(1,2,2)-free
        ([x221_TT_multipartite]); the same loop witness gives the teeth.
      - the two Theta statements : the extremal relations are FUNCTIONAL
        ([x221_abar_functional], [x221_tbar_functional]) and INHABITED
        ([x221_abar_0], [x221_tbar_0]); TEETH — the degenerate zero function is
        NOT Theta of the intended growth ([x221_theta_nlogn_not_zero],
        [x221_theta_ndivlogn_not_zero]), so the conclusion is not free.
      - [ordered_twinwidth_clique_and_tww_bound_statement] : the twin-width
        value relation is FUNCTIONAL ([x221_tww_eq_functional]) and INHABITED on
        a nonempty tournament ([x221_tww_eq_TT1]).
      - [kextension_linear_unavoidability_statement] : NON-VACUITY — the family
        of empty digraphs is linearly unavoidable ([x221_void_lin_unavoidable]);
        TEETH — the acyclicity guard of [x221_kextension] really excludes
        digraphs that would otherwise qualify
        ([x221_kextension_acyclic_guard_has_teeth]).
      - [orientation_C4_eulerian_avoidable_statement] : the underlying graph of
        [x221_c4or b] is the 4-cycle whatever [b] is ([x221_c4or_uadjE],
        [x221_c4or_card]); the Eulerian hypothesis is satisfiable
        ([x221_C3_eulerian]) and is a REAL restriction
        ([x221_TT2_not_eulerian]).

    Every lemma is closed by [Qed]; the [Print Assumptions] audit at the end
    shows the representative ones are axiom-free. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_order all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph oriented tournament.
From Digraph Require Import dipath order strong classic_core dichromatic omegabar.
From Digraph Require Import heroes heroes_dichotomy unvd twinwidth twinwidth_ordered.
From Digraph Require Import grounding_twinwidth.
From GTBase Require Import asymptotics.
From Digraph Require Import X221.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

(** ** Transitive tournaments populate both hero classes *)

Lemma x221_TT_oriented (n : nat) : oriented_dg (TT n : diGraphType).
Proof. by move=> u v; rewrite !arcTTE -leqNgt => /ltnW. Qed.

Lemma x221_TT_nonadj (n : nat) (u v : (TT n : diGraphType)) :
  x221_nonadj u v -> u = v.
Proof.
case/andP => h1 h2; case: (eqVneq u v) => [//|nuv].
by have := arc_or nuv; rewrite (negbTE h1) (negbTE h2).
Qed.

Lemma x221_TT_arrow_free (n : nat) :
  no_induced_arrowK2_K1 (TT n : diGraphType).
Proof.
move=> [a [b [c [_ [nac [_ [_ [_ [nacx [ncax _]]]]]]]]]].
by have := arc_or nac; rewrite (negbTE nacx) (negbTE ncax).
Qed.

Lemma x221_TT_Delta122_free (n : nat) :
  ind_free x221_Delta122 (TT n : diGraphType).
Proof.
move=> [f [_ hf]].
have ab : f (inl (inl (ord0 : TT 1))) --> f (inl (inr (ord0 : TT 2))).
  by rewrite hf.
have bc : f (inl (inr (ord0 : TT 2))) --> f (inr (ord0 : TT 2)).
  by rewrite hf.
have ca : f (inr (ord0 : TT 2)) --> f (inl (inl (ord0 : TT 1))).
  by rewrite hf.
move: ab bc ca; rewrite !arcTTE => h1 h2 h3.
by have := ltn_trans (ltn_trans h1 h2) h3; rewrite ltnn.
Qed.

(** NON-VACUITY for [delta122_hero_k1_plus_dipath2_free_statement]: the guarded
    class contains every transitive tournament, hence digraphs of every order. *)
Lemma x221_TT_in_class (n : nat) :
  [/\ oriented_dg (TT n : diGraphType),
      no_induced_arrowK2_K1 (TT n : diGraphType)
    & ind_free x221_Delta122 (TT n : diGraphType)].
Proof.
by split; [exact: x221_TT_oriented | exact: x221_TT_arrow_free
          | exact: x221_TT_Delta122_free].
Qed.

(** NON-VACUITY for
    [delta122_hero_oriented_complete_multipartite_statement]. *)
Lemma x221_TT_multipartite (n : nat) :
  x221_oriented_complete_multipartite (TT n : diGraphType)
  /\ ind_free x221_Delta122 (TT n : diGraphType).
Proof.
split; last exact: x221_TT_Delta122_free.
split; first exact: x221_TT_oriented.
by move=> u v w /x221_TT_nonadj -> hvw.
Qed.

(** ** The [oriented_dg] guard has teeth: a loop kills dicolourability *)

Definition x221_loop1 : Type := unit.
HB.instance Definition _ := Finite.on x221_loop1.
HB.instance Definition _ :=
  HasArc.Build x221_loop1 (fun _ _ : unit => true).

Lemma x221_loop_not_dicolorable (k : nat) :
  ~~ dicolorableb (x221_loop1 : diGraphType) k.
Proof.
apply/existsPn => col; apply/forallPn; exists (col tt).
set S := [set v : x221_loop1 | col v == col tt].
have tin : tt \in S by rewrite /S inE.
have v0 : induced_digraph S := exist _ tt tin.
by apply: (loop_not_acyclicb (v := v0)); rewrite sub_arcE.
Qed.

(** The loop digraph is [no_induced_arrowK2_K1]- and Delta(1,2,2)-free (both
    patterns need at least three vertices), so ONLY the [oriented_dg] guard
    keeps it out of the class of
    [delta122_hero_k1_plus_dipath2_free_statement]. *)
Lemma x221_loop_arrow_free : no_induced_arrowK2_K1 (x221_loop1 : diGraphType).
Proof. by move=> [a [b [c [nab _]]]]; move: nab; case: a; case: b. Qed.

Lemma x221_loop_Delta122_free :
  ind_free x221_Delta122 (x221_loop1 : diGraphType).
Proof.
move=> [f [finj hf]].
have e : f (inl (inl (ord0 : TT 1))) = f (inr (ord0 : TT 2)).
  by case: (f _); case: (f _).
by have := finj _ _ e.
Qed.

Lemma x221_oriented_guard_has_teeth :
  [/\ no_induced_arrowK2_K1 (x221_loop1 : diGraphType),
      ind_free x221_Delta122 (x221_loop1 : diGraphType)
    & forall k : nat, ~~ dicolorableb (x221_loop1 : diGraphType) k].
Proof.
split; [exact: x221_loop_arrow_free | exact: x221_loop_Delta122_free
       | exact: x221_loop_not_dicolorable].
Qed.

(** ** The extremal relations are functional and inhabited *)

Lemma x221_abar_functional (n a a' : nat) :
  x221_abar n a -> x221_abar n a' -> a = a'.
Proof.
move=> [la [D [oD cD aD]]] [la' [D' [oD' cD' aD']]].
apply/eqP; rewrite eqn_leq; apply/andP; split.
  by rewrite -aD'; exact: (la _ oD' cD').
by rewrite -aD; exact: (la' _ oD cD).
Qed.

Lemma x221_tbar_functional (n t t' : nat) :
  x221_tbar n t -> x221_tbar n t' -> t = t'.
Proof.
move=> [ua [D [oD cD aD]]] [ua' [D' [oD' cD' aD']]].
apply/eqP; rewrite eqn_leq; apply/andP; split.
  by rewrite -aD; exact: (ua' _ oD cD).
by rewrite -aD'; exact: (ua _ oD' cD').
Qed.

Lemma x221_TT0_otf : x221_oriented_triangle_free (TT 0 : diGraphType).
Proof.
split; first exact: x221_TT_oriented.
by move=> [u _]; have := ltn_ord u; rewrite ltn0.
Qed.

Lemma x221_alphavec0 (D : diGraphType) : #|D| = 0 -> x221_alphavec D = 0.
Proof.
move=> c0; apply/eqP; rewrite -leqn0.
by apply/bigmax_leqP => S _; rewrite -c0 max_card.
Qed.

(** The min-bigop defining the dichromatic number never exceeds its neutral
    element, so [x221_dichro D <= #|D|] always. *)
Lemma x221_bigmin_le (I : Type) (r : seq I) (P : pred I) (F : I -> nat)
    (m : nat) :
  (\big[minn/m]_(i <- r | P i) F i <= m)%N.
Proof.
elim: r => [|i r ih]; first by rewrite big_nil.
rewrite big_cons; case: (P i) => //.
exact: leq_trans (geq_minr _ _) ih.
Qed.

Lemma x221_dichro_le (D : diGraphType) : (x221_dichro D <= #|D|)%N.
Proof. exact: x221_bigmin_le. Qed.

Lemma x221_dichro0 (D : diGraphType) : #|D| = 0 -> x221_dichro D = 0.
Proof. by move=> c0; apply/eqP; rewrite -leqn0 -c0; exact: x221_dichro_le. Qed.

Lemma x221_abar_0 : x221_abar 0 0.
Proof.
split=> [//|]; exists (TT 0 : diGraphType); split.
- exact: x221_TT0_otf.
- exact: card_TT.
- by apply: x221_alphavec0; exact: card_TT.
Qed.

Lemma x221_tbar_0 : x221_tbar 0 0.
Proof.
split=> [D _ c0|]; first by rewrite (x221_dichro0 c0).
exists (TT 0 : diGraphType); split.
- exact: x221_TT0_otf.
- exact: card_TT.
- by apply: x221_dichro0; exact: card_TT.
Qed.

(** ** The Theta guards have teeth: the zero function is not a solution *)

Lemma x221_sqrt_ceil_gt0 (m : nat) : (0 < m)%N -> (0 < sqrt_ceil m)%N.
Proof.
move=> m0; rewrite lt0n; apply/eqP => e.
by move: (sqrt_ceil_spec m); rewrite e (@exp0n 2 isT) leqn0 => /eqP em;
   rewrite em in m0.
Qed.

Lemma x221_trunc_log2_gt0 (n : nat) : (2 <= n)%N -> (0 < trunc_log 2 n)%N.
Proof. by move=> n2; rewrite trunc_log_gt0 n2. Qed.

Lemma x221_trunc_log2_le (n : nat) : (0 < n)%N -> (trunc_log 2 n <= n)%N.
Proof.
move=> n0; apply: (leq_trans _ (@trunc_logP 2 n isT n0)).
exact: ltnW (@ltn_expl 2 (trunc_log 2 n) isT).
Qed.

Lemma x221_theta_nlogn_not_zero :
  ~ big_Theta_nat (fun _ => 0%N) (fun n => sqrt_ceil (n * trunc_log 2 n)).
Proof.
move=> [_ [C [_ [N hN]]]].
have := hN (maxn N 2) (leq_maxl N 2); rewrite muln0 leqn0 => /eqP e0.
have h2 : (2 <= maxn N 2)%N by exact: leq_maxr.
have : (0 < sqrt_ceil (maxn N 2 * trunc_log 2 (maxn N 2)))%N.
  by apply: x221_sqrt_ceil_gt0; rewrite muln_gt0 (leq_trans _ h2) //
     x221_trunc_log2_gt0.
by rewrite e0.
Qed.

Lemma x221_theta_ndivlogn_not_zero :
  ~ big_Theta_nat (fun _ => 0%N) (fun n => sqrt_ceil (n %/ trunc_log 2 n)).
Proof.
move=> [_ [C [_ [N hN]]]].
have := hN (maxn N 2) (leq_maxl N 2); rewrite muln0 leqn0 => /eqP e0.
have h2 : (2 <= maxn N 2)%N by exact: leq_maxr.
have hl : (0 < trunc_log 2 (maxn N 2))%N by exact: x221_trunc_log2_gt0.
have : (0 < sqrt_ceil (maxn N 2 %/ trunc_log 2 (maxn N 2)))%N.
  apply: x221_sqrt_ceil_gt0; rewrite divn_gt0 //.
  by apply: x221_trunc_log2_le; exact: leq_trans h2.
by rewrite e0.
Qed.

(** ** The twin-width value relation is functional and inhabited *)

Lemma x221_tww_eq_functional (T : tournament) (t t' : nat) :
  x221_tww_eq T t -> x221_tww_eq T t' -> t = t'.
Proof.
move=> [ht mt] [ht' mt']; case: (ltngtP t t') => // lt.
- by case: (mt' _ lt ht).
- by case: (mt _ lt ht').
Qed.

Lemma x221_tww_eq_TT1 : x221_tww_eq (TT 1 : tournament) 0.
Proof. by split; [exact: tww_le_TT1 | move=> m; rewrite ltn0]. Qed.

Lemma x221_TT1_nonempty : (0 < #|(TT 1 : tournament)|)%N.
Proof. by rewrite card_TT. Qed.

(** ** Linear unavoidability: an inhabited family, and the acyclicity teeth *)

Definition x221_void (D : diGraphType) : Prop := forall x : D, False.

Lemma x221_unavoidable_void (D : diGraphType) :
  x221_void D -> unavoidable D 0.
Proof.
move=> dF T _ _; exists (fun x : D => match dF x with end); split.
  by move=> x; case: (dF x).
by move=> u v; case: (dF u).
Qed.

Lemma x221_void_lin_unavoidable : x221_linearly_unavoidable x221_void.
Proof.
exists 0 => D N dF [uN mN]; rewrite mul0n leqn0; apply/eqP.
case: N uN mN => [//|N _ mN].
by case: (mN 0 (ltn0Sn N) (x221_unavoidable_void dF)).
Qed.

Lemma x221_dgiso_void (D1 D2 : diGraphType) :
  x221_void D1 -> x221_void D2 -> dgiso D1 D2.
Proof.
move=> e1 e2; exists (fun x : D1 => match e1 x with end); split.
  by apply: (@Bijective _ _ _ (fun y : D2 => match e2 y with end)) =>
     [x|y]; [case: (e1 x) | case: (e2 y)].
by move=> u v; case: (e1 u).
Qed.

Local Open Scope ring_scope.

Lemma x221_C3_dicycle :
  dicycle ([:: 0; 1; 1 + 1] : seq (tournament.C3 : diGraphType)).
Proof. by []. Qed.

Lemma x221_C3_not_acyclic : ~~ acyclicb (tournament.C3 : diGraphType).
Proof. exact: dicycle_not_acyclicb x221_C3_dicycle. Qed.

Lemma x221_kextension_acyclic_guard_has_teeth :
  exists (F : diGraphType -> Prop) (k : nat) (D : diGraphType),
    [/\ (exists S : {set D},
           #|S| = k /\
           exists A : diGraphType, F A /\ dgiso (induced_digraph (~: S)) A),
        ~~ acyclicb D
      & ~ x221_kextension k F D].
Proof.
exists x221_void, 3, (tournament.C3 : diGraphType); split.
- exists [set: (tournament.C3 : diGraphType)]; split.
    by rewrite cardsT card_C3.
  exists (TT 0 : diGraphType); split; first by move=> x; have := ltn_ord x;
    rewrite ltn0.
  apply: x221_dgiso_void; last by move=> x; have := ltn_ord x; rewrite ltn0.
  by rewrite setCT => -[v pv]; move: pv; rewrite in_set0.
- exact: x221_C3_not_acyclic.
by move=> [ac _]; move: x221_C3_not_acyclic; rewrite ac.
Qed.

(** ** The orientations of C_4, Eulerian digraphs *)

Lemma x221_c4or_card (b : 'Z_4 -> bool) : #|{: x221_c4or b}| = 4.
Proof. by rewrite card_ord. Qed.

(** Whatever the orientation [b], the underlying graph of [x221_c4or b] is the
    4-cycle: [u] and [v] are adjacent exactly when they are consecutive. *)
Lemma x221_c4or_uadjE (b : 'Z_4 -> bool) (u v : x221_c4or b) :
  x221_uadj u v = (v == u + 1) || (u == v + 1).
Proof.
rewrite /x221_uadj /arc /=.
by case: (b u); case: (b v); case: (v == u + 1); case: (u == v + 1).
Qed.

Lemma x221_C3_Nout (v : (tournament.C3 : diGraphType)) :
  [set w | v --> w] = [set v + 1].
Proof. by apply/setP => w; rewrite !inE arcC3E. Qed.

Lemma x221_C3_Nin (v : (tournament.C3 : diGraphType)) :
  [set u | u --> v] = [set v - 1].
Proof.
apply/setP => u; rewrite !inE arcC3E.
apply/idP/idP => /eqP h; apply/eqP.
  by rewrite h addrK.
by rewrite h subrK.
Qed.

(** NON-VACUITY for [orientation_C4_eulerian_avoidable_statement]: the Eulerian
    hypothesis is satisfiable with positive minimum out-degree. *)
Lemma x221_C3_eulerian : x221_eulerian (tournament.C3 : diGraphType).
Proof.
move=> v; rewrite /outdeg /indeg /Nin x221_C3_Nout x221_C3_Nin.
by rewrite !cards1.
Qed.

(** TEETH: being Eulerian is a real restriction — transitive tournaments are
    not Eulerian. *)
Lemma x221_TT2_not_eulerian : ~ x221_eulerian (TT 2 : diGraphType).
Proof.
move=> h.
have i0 : indeg (ord0 : (TT 2 : diGraphType)) = 0%N.
  apply/eqP; rewrite /indeg /Nin cards_eq0; apply/eqP/setP => u.
  by rewrite !inE arcTTE ltn0.
have o0 : (0 < outdeg (ord0 : (TT 2 : diGraphType)))%N.
  rewrite /outdeg; apply/card_gt0P; exists (Ordinal (isT : (1 < 2)%N)).
  by rewrite inE arcTTE.
by move: o0; rewrite (h ord0) i0.
Qed.

(** ** Print Assumptions audit *)

Print Assumptions x221_TT_in_class.
Print Assumptions x221_oriented_guard_has_teeth.
Print Assumptions x221_abar_functional.
Print Assumptions x221_tbar_functional.
Print Assumptions x221_theta_nlogn_not_zero.
Print Assumptions x221_theta_ndivlogn_not_zero.
Print Assumptions x221_tww_eq_functional.
Print Assumptions x221_void_lin_unavoidable.
Print Assumptions x221_kextension_acyclic_guard_has_teeth.
Print Assumptions x221_c4or_uadjE.
Print Assumptions x221_C3_eulerian.
Print Assumptions x221_TT2_not_eulerian.
