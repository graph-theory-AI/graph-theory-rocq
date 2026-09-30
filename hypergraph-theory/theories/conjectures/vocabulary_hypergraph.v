(** * Hypergraph.conjectures.vocabulary_hypergraph -- wave-V vocabulary equivalences

    The hypergraph package had no [foundations/] directory when its conjecture
    files were written, so the same finite-hypergraph notions were re-declared
    once per file; meta/STATEMENT_IMPROVEMENTS.md (section "## hypergraph-theory",
    subsection "### Duplicated vocabulary") lists the copies.  This file records,
    for each group of copies, ONE lemma tying the per-file spelling to the
    canonical notion, so that the duplicates can later be retired by rewriting
    with these lemmas instead of by editing statement bodies.

    No statement body is changed here.  The canonical notions are

      - [Hypergraph.foundations.hypergraph]: [hg_uniform], [hg_degree];
      - [Hypergraph.conjectures.U12]: [hg_cover] (the U12 spelling of a vertex
        cover, which the Ryser edge of implications_U12.v already uses);
      - [GTBase.asymptotics]: [sqrt_ceil];
      - [Hypergraph.conjectures.X119]: the q-colour Ramsey host machinery, of
        which the X108 / X117 two-colour copies are the [q = 2] instance.

    PLACEMENT.  Every lemma below mentions at least one notion defined in a
    [theories/conjectures/X*.v] file, so none of them may live in
    [theories/foundations/] (a foundations file must not import a conjectures
    file).  The phases concerned (X6, X72, X73, X104, X108, X117, X119, X137,
    X209) have no [implications_<phase>.v] / [grounding_<phase>.v] file, so the
    bridges are collected here rather than in twenty new per-phase files.  The
    three bridges the Ryser edge needs ([x6_matching_equiv_hg_matching],
    [x6_matching_number_equiv_is_matching_number],
    [x6_r_partite_uniform_equiv_r_partite_uniform]) already live in
    [implications_U12.v] and are NOT duplicated here.

    The file is axiom-free: no Axiom/Parameter/Admitted. *)

From GTBase Require Import base asymptotics.
From Hypergraph.foundations Require Import hypergraph.
From Hypergraph.conjectures Require Import U12 X6 X72 X73 X104 X108 X117 X119
  X137 X209.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** k-uniformity: seven copies of one notion ***************************

    [hg_uniform E k] is "every hyperedge of [E] has exactly [k] vertices".  The
    seven per-file copies have literally that body, so the bridges hold by
    conversion; they are recorded as lemmas so that any future drift breaks this
    file rather than silently changing a statement. *)

Lemma k_uniform_equiv_hg_uniform (T : finType) (E : {set {set T}}) (k : nat) :
  k_uniform E k <-> hg_uniform E k.
Proof. by split=> H; exact: H. Qed.

Lemma x6_uniform_equiv_hg_uniform (T : finType) (E : {set {set T}}) (r : nat) :
  x6_uniform E r <-> hg_uniform E r.
Proof. by split=> H; exact: H. Qed.

Lemma x104_uniform_equiv_hg_uniform (T : finType) (E : {set {set T}}) (r : nat) :
  x104_uniform E r <-> hg_uniform E r.
Proof. by split=> H; exact: H. Qed.

Lemma x108_uniform_equiv_hg_uniform (T : finType) (E : {set {set T}}) (r : nat) :
  x108_uniform E r <-> hg_uniform E r.
Proof. by split=> H; exact: H. Qed.

Lemma x119_uniform_equiv_hg_uniform (T : finType) (E : {set {set T}}) (r : nat) :
  x119_uniform E r <-> hg_uniform E r.
Proof. by split=> H; exact: H. Qed.

Lemma x137_uniform_equiv_hg_uniform (T : finType) (F : {set {set T}}) (r : nat) :
  x137_uniform F r <-> hg_uniform F r.
Proof. by split=> H; exact: H. Qed.

Lemma x209_uniform_equiv_hg_uniform (T : finType) (E : {set {set T}}) (k : nat) :
  x209_uniform E k <-> hg_uniform E k.
Proof. by split=> H; exact: H. Qed.

(** ** Vertex cover: two spellings of "meets every hyperedge" *************

    [hg_cover X E] (U12) spells the meeting condition [X :&: e != set0];
    [x72_vertex_cover E X] (X72) spells it [~~ [disjoint X & e]].  The two are
    equivalent by [setI_eq0], not by conversion. *)

Lemma x72_vertex_cover_equiv_hg_cover
    (T : finType) (E : {set {set T}}) (X : {set T}) :
  x72_vertex_cover E X <-> hg_cover X E.
Proof.
by split=> H e eE; move: (H e eE); rewrite -setI_eq0 ?negbK //; apply: contraNN.
Qed.

(** The two cover-number wrappers agree as a consequence. *)
Lemma x72_transversal_number_equiv_is_cover_number
    (T : finType) (E : {set {set T}}) (tau : nat) :
  x72_transversal_number E tau <-> is_cover_number E tau.
Proof.
split=> [[[X [cX cardX]] min]|[[X [cX cardX]] min]]; split.
- by exists X; split=> //; apply/x72_vertex_cover_equiv_hg_cover.
- by move=> Y cY; apply: min; apply/x72_vertex_cover_equiv_hg_cover.
- by exists X; split=> //; apply/x72_vertex_cover_equiv_hg_cover.
- by move=> Y cY; apply: min; apply/x72_vertex_cover_equiv_hg_cover.
Qed.

(** ** Hyperedge degree: two copies **************************************

    [hg_degree E v] counts the hyperedges of [E] through [v]; [x6_hg_degree]
    (X6) and [x73_hyperdegree] (X73) have the same body. *)

Lemma x6_hg_degreeE (T : finType) (E : {set {set T}}) (v : T) :
  x6_hg_degree E v = hg_degree E v.
Proof. by []. Qed.

Lemma x73_hyperdegreeE (T : finType) (E : {set {set T}}) (v : T) :
  x73_hyperdegree E v = hg_degree E v.
Proof. by []. Qed.

Lemma x73_hyperdegree_equiv_x6_hg_degree
    (T : finType) (E : {set {set T}}) (v : T) :
  x73_hyperdegree E v = x6_hg_degree E v.
Proof. by []. Qed.

(** ** Integer ceiling square root ***************************************

    [x119_sqrt] (X119) is a verbatim copy of [GTBase.asymptotics.sqrt_ceil],
    lemma included.  Both are [ex_minn] of the same predicate, so they agree by
    [eq_ex_minn]. *)

Lemma x119_sqrtE (m : nat) : x119_sqrt m = sqrt_ceil m.
Proof. by apply: eq_ex_minn. Qed.

(** ** The Ramsey host machinery: X108 / X117 are the q = 2 instance of X119

    The three files declare the same "image of a hyperedge under an injection",
    "monochromatic copy in the complete host on [N] vertices" and "[N] vertices
    force a monochromatic copy".  X108 and X117 fix TWO colours ([bool]); X119
    is the [q]-colour generalisation ([['I_q]]).  [x108_image_edge] is already
    stated for an arbitrary target [finType], so the image bridges are
    conversions; the monochromatic-copy bridge at [q = 2] needs the bijection
    [bool <-> 'I_2]. *)

Lemma x117_image_edgeE (T : finType) (N : nat) (f : T -> 'I_N) (e : {set T}) :
  x117_image_edge f e = x108_image_edge f e.
Proof. by []. Qed.

Lemma x119_image_edgeE (T : finType) (N : nat) (f : T -> 'I_N) (e : {set T}) :
  x119_image_edge f e = x108_image_edge f e.
Proof. by []. Qed.

Lemma x117_monochromatic_copyE
    (T : finType) (E : {set {set T}}) (N : nat) (col : {set 'I_N} -> bool) :
  x117_monochromatic_copy E col = x108_monochromatic_copy E col.
Proof. by []. Qed.

Lemma x117_forces_mono_equiv_x108
    (T : finType) (E : {set {set T}}) (N : nat) :
  x117_forces_mono E N <-> x108_two_colour_ramsey_at_most E N.
Proof. by split=> H; exact: H. Qed.

(** The two-element colour type as [['I_2]] and back. *)
Definition b2i2 (b : bool) : 'I_2 := @Ordinal 2 b (leq_b1 b).
Definition i22b (i : 'I_2) : bool := (i : nat) == 1.

Lemma b2i2K : cancel b2i2 i22b.
Proof. by case. Qed.

Lemma i22bK : cancel i22b b2i2.
Proof. by move=> i; apply/val_inj; case: i => -[|[|m]]. Qed.

(** The [q = 2] instance of the X119 machinery is the X108 / X117 notion. *)
Lemma x108_two_colour_ramsey_at_most_equiv_x119_forces_mono
    (T : finType) (E : {set {set T}}) (N : nat) :
  x108_two_colour_ramsey_at_most E N <-> x119_forces_mono E 2 N.
Proof.
split=> H col.
- have [c [f [finj fcol]]] := H (fun s => i22b (col s)).
  exists (b2i2 c), f; split=> // e eE.
  by rewrite -[col _]i22bK (fcol e eE).
- have [c [f [finj fcol]]] := H (fun s => b2i2 (col s)).
  exists (i22b c), f; split=> // e eE.
  by rewrite -[col _]b2i2K (fcol e eE).
Qed.

Lemma x117_forces_mono_equiv_x119_forces_mono
    (T : finType) (E : {set {set T}}) (N : nat) :
  x117_forces_mono E N <-> x119_forces_mono E 2 N.
Proof.
by rewrite x117_forces_mono_equiv_x108;
   exact: x108_two_colour_ramsey_at_most_equiv_x119_forces_mono.
Qed.

Print Assumptions k_uniform_equiv_hg_uniform.
Print Assumptions x72_vertex_cover_equiv_hg_cover.
Print Assumptions x72_transversal_number_equiv_is_cover_number.
Print Assumptions x119_sqrtE.
Print Assumptions x108_two_colour_ramsey_at_most_equiv_x119_forces_mono.
Print Assumptions x117_forces_mono_equiv_x119_forces_mono.
