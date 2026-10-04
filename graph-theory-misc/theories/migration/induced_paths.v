(** * GTMisc.migration.induced_paths — B22 certificates: the X91, X114 and X208 induced paths and rows

    Frozen verbatim at the private baseline (byte-identical at B21 66279eb and C20 97605dd): the
    nonempty induced path [x91_induced_path] with its chains [x91_Pk_free] / [x91_avoidable_path] and
    the complete row [avoidable_path_or_pk_free_statement] (studies slug); the full-endpoint induced
    path [x114_induced_path_between], the C20 wrapper chain [x114_induced_subdivision] over the frozen
    public wrapper of GTBase.migration.induced_paths, the decision problem [x114_hisc_problem] and
    the complete row [subcubic_induced_subdivision_np_complete_statement] (studies slug); and the
    index-encoded exact-order existence [x208_induced_path_order] with its chain [x208_Pt_free] and
    the complete row [Pt_free_maximum_independent_set_polytime_statement] (arxiv:1803.05396#01,
    partial).  Since B22: [x91_induced_path] aliases [GTBase.induced_paths.nonempty_induced_path]
    and [x114_induced_path_between] aliases [induced_path_between], both by conversion (their
    consecutive-pair tests were already B3's aliases of [seq_consecutive]);
    [x208_induced_path_order] aliases [has_induced_path_of_order], an explicit iff through the index
    bridge [chordless_nthP] on the duplicate-free list ([x208]'s in-range indices add no hidden
    default-vertex premise: the existential first vertex is the list's head).  The copies keep the
    other families' live aliases ([x91_consecutive_in_path], [x91_induced_cycle],
    [x91_sequence_contained], [x114_subcubic], the D7 complexity layer, [x208_polytime_mis_on]).
    The complete pre-B3/B4/B22 and pre-B3/A14/C19/C20/B22 rows are B4's
    [X91Original.avoidable_path_or_pk_free_statement] and C19's
    [X114Original.subcubic_induced_subdivision_np_complete_statement], reused with their own
    certificates; X208 has no earlier frozen row.  The local constructor [X114Model] and its seven
    projections stay live with unchanged types and Arguments; the full in-NP verifier/cost witnesses
    and NP-hardness reductions transfer through the problem iff as in C20. *)

From GTBase Require Import base model_support induced_paths induced_subdivisions complexity.
From GTBase.migration Require induced_paths.
From GTMisc.conjectures Require Import D7 X91 X114 X208.
From GTMisc.migration Require consecutive_in_cycle model_support.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module B22 := GTBase.migration.induced_paths.
Module B4 := GTMisc.migration.consecutive_in_cycle.
Module C19 := GTMisc.migration.model_support.

Module Legacy.

Definition x91_induced_path (G : sgraph) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q =>
      uniq p /\
      path (--) x q /\
      forall u v : G,
        u \in p -> v \in p -> u -- v -> u != v ->
        x91_consecutive_in_path p u v
  end.

Definition x114_induced_path_between (G : sgraph) (a b : G) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q =>
      x = a /\
      last x q = b /\
      uniq p /\
      path (--) x q /\
      forall u v : G,
        u \in p -> v \in p -> u -- v -> u != v ->
        x114_consecutive_in_path p u v
  end.

Definition x208_induced_path_order (G : sgraph) (t : nat) : Prop :=
  exists (x : G) (p : seq G),
    [/\ size (x :: p) = t,
        path (--) x p,
        uniq (x :: p) &
        forall i j : nat,
          i.+1 < j -> j < size (x :: p) ->
          ~~ (nth x (x :: p) i -- nth x (x :: p) j)].

End Legacy.

Module X91Legacy.

Definition x91_avoidable_path (G : sgraph) (p : seq G) : Prop :=
  Legacy.x91_induced_path p /\
  forall u v : G,
    Legacy.x91_induced_path (u :: rcons p v) ->
    exists c : seq G,
      x91_induced_cycle c /\ x91_sequence_contained (u :: rcons p v) c.

Definition x91_Pk_free (G : sgraph) (k : nat) : Prop :=
  forall p : seq G, size p = k -> ~ Legacy.x91_induced_path p.

Definition avoidable_path_or_pk_free_statement : Prop :=
  forall k : nat,
    0 < k ->
    forall G : sgraph,
      X91Legacy.x91_Pk_free G k \/
      exists p : seq G, size p = k /\ X91Legacy.x91_avoidable_path p.

End X91Legacy.

Module X114Legacy.

Definition x114_induced_subdivision (H G : sgraph) : Prop := B22.Legacy.induced_subdivision H G.

Definition x114_hisc_problem (H : sgraph) : problem :=
  {| pinput := sgraph;
     psize  := fun G : sgraph => #|G|;
     pmem   := fun G : sgraph => X114Legacy.x114_induced_subdivision H G |}.

Definition subcubic_induced_subdivision_np_complete_statement : Prop :=
  exists H : sgraph,
    x114_subcubic H /\ x114_np_complete (X114Legacy.x114_hisc_problem H).

End X114Legacy.

Module X208Legacy.

Definition x208_Pt_free (G : sgraph) (t : nat) : Prop :=
  ~ Legacy.x208_induced_path_order G t.

Definition Pt_free_maximum_independent_set_polytime_statement : Prop :=
  forall t : nat, 7 <= t -> x208_polytime_mis_on (fun G => X208Legacy.x208_Pt_free G t).

End X208Legacy.

(** ** X91 (conversions) *)

Lemma x91_induced_path_compat (G : sgraph) (p : seq G) :
  Legacy.x91_induced_path p <-> x91_induced_path p.
Proof. by []. Qed.

Lemma x91_Pk_free_compat (G : sgraph) (k : nat) : X91Legacy.x91_Pk_free G k <-> x91_Pk_free G k.
Proof. by []. Qed.

Lemma x91_avoidable_path_compat (G : sgraph) (p : seq G) :
  X91Legacy.x91_avoidable_path p <-> x91_avoidable_path p.
Proof. by []. Qed.

Lemma avoidable_path_or_pk_free_statement_compat :
  X91Legacy.avoidable_path_or_pk_free_statement <-> avoidable_path_or_pk_free_statement.
Proof. by []. Qed.

(** ** X114 *)

Lemma x114_induced_path_between_compat (G : sgraph) (a b : G) (p : seq G) :
  Legacy.x114_induced_path_between a b p <-> x114_induced_path_between a b p.
Proof. by []. Qed.

Lemma x114_induced_subdivision_compat (H G : sgraph) :
  X114Legacy.x114_induced_subdivision H G <-> x114_induced_subdivision H G.
Proof. exact: B22.induced_subdivision_compat. Qed.

Lemma x114_hisc_problem_compat (H : sgraph) :
  [/\ forall G : sgraph,
        @pmem (X114Legacy.x114_hisc_problem H) G <-> @pmem (x114_hisc_problem H) G,
      in_NP (X114Legacy.x114_hisc_problem H) <-> in_NP (x114_hisc_problem H) &
      NP_hard (X114Legacy.x114_hisc_problem H) <-> NP_hard (x114_hisc_problem H)].
Proof.
have mem G : @pmem (X114Legacy.x114_hisc_problem H) G <-> @pmem (x114_hisc_problem H) G.
  exact: x114_induced_subdivision_compat.
split=> //.
- split=> -[verify [vcost [a [d [b [vmem vbound]]]]]];
    exists verify, vcost, a, d, b; split=> // G.
  + exact: iff_trans (iff_sym (mem G)) (vmem G).
  + exact: iff_trans (mem G) (vmem G).
- split=> hard A /hard[f [cost [a [d [b [fmem fcost fsize]]]]]];
    exists f, cost, a, d, b; split=> // x.
  + exact: iff_trans (fmem x) (mem (f x)).
  + exact: iff_trans (fmem x) (iff_sym (mem (f x))).
Qed.

Lemma subcubic_induced_subdivision_np_complete_statement_compat :
  X114Legacy.subcubic_induced_subdivision_np_complete_statement <->
  subcubic_induced_subdivision_np_complete_statement.
Proof.
have np H : x114_np_complete (X114Legacy.x114_hisc_problem H) <->
            x114_np_complete (x114_hisc_problem H).
  have [_ inNP hard] := x114_hisc_problem_compat H.
  by split=> -[a b]; split; [exact/inNP | exact/hard | exact/inNP | exact/hard].
by split=> -[H [sub hnp]]; exists H; split=> //; apply/np.
Qed.

(** ** X208: the index encoding and the canonical exact-order view *)

Lemma x208_induced_path_order_compat (G : sgraph) (t : nat) :
  Legacy.x208_induced_path_order G t <-> x208_induced_path_order G t.
Proof.
rewrite /x208_induced_path_order; split.
- move=> [x [q [sz pth up idx]]]; exists (x :: q); split=> //.
  split=> //; split=> //.
  by apply/(chordless_nthP up).
- move=> [p [sz np]]; case: p sz np => [|x q] sz // [up [pth c]]; exists x, q; split=> //.
  by apply/(chordless_nthP up).
Qed.

Lemma x208_Pt_free_compat (G : sgraph) (t : nat) : X208Legacy.x208_Pt_free G t <-> x208_Pt_free G t.
Proof. by split=> h /x208_induced_path_order_compat. Qed.

Lemma Pt_free_maximum_independent_set_polytime_statement_compat :
  X208Legacy.Pt_free_maximum_independent_set_polytime_statement <->
  Pt_free_maximum_independent_set_polytime_statement.
Proof.
split=> h t t7; move: (h t t7);
  rewrite /x208_polytime_mis_on /polytime_outputs_graph_on /polytime_outputs_on_class;
  by move=> [p [cost spec]]; exists p; split=> // G /x208_Pt_free_compat; exact: spec.
Qed.

(** ** The complete Originals, reused from B4 (X91) and C19 (X114) *)

Lemma avoidable_path_or_pk_free_statement_original_compat :
  GTMisc.migration.consecutive_in_cycle.X91Original.avoidable_path_or_pk_free_statement <-> avoidable_path_or_pk_free_statement.
Proof. exact: B4.avoidable_path_or_pk_free_statement_original_compat. Qed.

Lemma subcubic_induced_subdivision_np_complete_statement_original_compat :
  GTMisc.migration.model_support.X114Original.subcubic_induced_subdivision_np_complete_statement <->
  subcubic_induced_subdivision_np_complete_statement.
Proof. exact: C19.subcubic_induced_subdivision_np_complete_statement_original_compat. Qed.

Print Assumptions x91_induced_path_compat.
Print Assumptions x91_Pk_free_compat.
Print Assumptions x91_avoidable_path_compat.
Print Assumptions avoidable_path_or_pk_free_statement_compat.
Print Assumptions x114_induced_path_between_compat.
Print Assumptions x114_induced_subdivision_compat.
Print Assumptions x114_hisc_problem_compat.
Print Assumptions subcubic_induced_subdivision_np_complete_statement_compat.
Print Assumptions x208_induced_path_order_compat.
Print Assumptions x208_Pt_free_compat.
Print Assumptions Pt_free_maximum_independent_set_polytime_statement_compat.
Print Assumptions avoidable_path_or_pk_free_statement_original_compat.
Print Assumptions subcubic_induced_subdivision_np_complete_statement_original_compat.
