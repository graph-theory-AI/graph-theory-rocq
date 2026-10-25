(** * Chromatic.applications.melnikov_valency_variety -- a counterexample to Melnikov's
    valency-variety problem as stated (opg:melnikovs_valency_variety_problem).

    The row [melnikovs_valency_variety_statement] (U1.v) asserts, for every graph G with at least
    two vertices, ceil(floor(w(G)/2) / (|V(G)| - w(G))) < chi(G), where w(G) is the number of
    distinct vertex degrees. The 37-vertex graph below, from the resolution write-up in
    coordination/sources/melnikovs_valency_variety_problem/ (output.md, section 1), has the
    degrees 0, 1, ..., 29, so w = 30 and the bound is ceil(15 / 7) = 3, and it has a proper
    3-colouring, so chi <= 3 (its triangle a1 b0 c0 gives chi = 3). CAVEAT: the graph has an
    isolated vertex z (degree 0, which counts toward w); the source's wording "any graph G with at
    least two vertices" admits it, and the row's body does too.

    Vertices are 'I_37: a1..a5 = 0..4, b0..b5 = 5..10, c0..c6 = 11..17, t1..t6 = 18..23,
    u1..u12 = 24..35, z = 36 ([mel_part] gives the class, [mel_idx] the index in it). The finite
    facts are checked by [vm_compute] after [enum 'I_37] is rewritten to an explicit list. *)
From GTBase Require Import base colourings.
From Chromatic.conjectures Require Import U1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The edges, from section 1 of the write-up: the complete tripartite graph on A, B, C; T joined
    to B and C; u7..u12 joined to B; u7, u8, u9 joined to a5, a4..a5, a3..a5; u_i (i >= 10)
    joined to c_j for i + j >= 13; u_i (i <= 6) joined to b_j for i + j >= 7, plus u1 c4, u2 c5,
    u3 c5, u4 c6, u5 c6, u6 c6. [mel_e v w] lists them with v in the earlier class. *)
Definition mel_part (v : nat) : nat :=
  if v < 5 then 0 else if v < 11 then 1 else if v < 18 then 2
  else if v < 24 then 3 else if v < 36 then 4 else 5.

Definition mel_idx (v : nat) : nat :=
  if v < 5 then v.+1 else if v < 11 then v - 5 else if v < 18 then v - 11
  else if v < 24 then v - 17 else if v < 36 then v - 23 else 0.

Definition mel_e (v w : nat) : bool :=
  let pv := mel_part v in let pw := mel_part w in
  let iv := mel_idx v in let iw := mel_idx w in
  [|| (pv == 0) && (pw == 1), (pv == 0) && (pw == 2), (pv == 1) && (pw == 2),
      (pv == 1) && (pw == 3), (pv == 2) && (pw == 3),
      (pv == 1) && (pw == 4) && (7 <= iw),
      (pv == 0) && (pw == 4) && (7 <= iw <= 9) && (12 <= iv + iw),
      (pv == 2) && (pw == 4) && (10 <= iw) && (13 <= iv + iw),
      (pv == 1) && (pw == 4) && (iw <= 6) && (7 <= iv + iw)
    | (pv == 2) && (pw == 4) && (iw <= 6) && (iv == nth 0 [:: 0; 4; 5; 5; 6; 6; 6] iw)].

Definition mel_rel (v w : 'I_37) : bool := (v != w) && (mel_e v w || mel_e w v).

Lemma mel_sym : symmetric mel_rel.
Proof. by move=> v w; rewrite /mel_rel eq_sym orbC. Qed.

Lemma mel_irrefl : irreflexive mel_rel.
Proof. by move=> v; rewrite /mel_rel eqxx. Qed.

Definition mel_graph : sgraph := SGraph mel_sym mel_irrefl.

Definition mel_I37 : seq 'I_37 :=
  [:: @Ordinal 37 0 isT; @Ordinal 37 1 isT; @Ordinal 37 2 isT; @Ordinal 37 3 isT;
      @Ordinal 37 4 isT; @Ordinal 37 5 isT; @Ordinal 37 6 isT; @Ordinal 37 7 isT;
      @Ordinal 37 8 isT; @Ordinal 37 9 isT; @Ordinal 37 10 isT; @Ordinal 37 11 isT;
      @Ordinal 37 12 isT; @Ordinal 37 13 isT; @Ordinal 37 14 isT; @Ordinal 37 15 isT;
      @Ordinal 37 16 isT; @Ordinal 37 17 isT; @Ordinal 37 18 isT; @Ordinal 37 19 isT;
      @Ordinal 37 20 isT; @Ordinal 37 21 isT; @Ordinal 37 22 isT; @Ordinal 37 23 isT;
      @Ordinal 37 24 isT; @Ordinal 37 25 isT; @Ordinal 37 26 isT; @Ordinal 37 27 isT;
      @Ordinal 37 28 isT; @Ordinal 37 29 isT; @Ordinal 37 30 isT; @Ordinal 37 31 isT;
      @Ordinal 37 32 isT; @Ordinal 37 33 isT; @Ordinal 37 34 isT; @Ordinal 37 35 isT;
      @Ordinal 37 36 isT].

Lemma mel_enum : enum 'I_37 = mel_I37.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

Lemma mel_all (P : pred 'I_37) : all P mel_I37 -> forall x, P x.
Proof. by move=> /allP h x; apply: h; rewrite -mel_enum mem_enum. Qed.

Lemma mel_all2 (P : 'I_37 -> 'I_37 -> bool) :
  all (fun x => all (P x) mel_I37) mel_I37 -> forall x y, P x y.
Proof.
move=> h x; apply: mel_all; move: x.
exact: (mel_all (P := fun x => all (P x) mel_I37)).
Qed.

Lemma mel_card (P : pred 'I_37) : #|P| = count P mel_I37.
Proof. by rewrite cardE /enum_mem -enumT mel_enum size_filter. Qed.

Lemma mel_deg (x : mel_graph) : #|N(x)| = count (fun y => mel_rel x y) mel_I37.
Proof. by rewrite cardsE mel_card. Qed.

(** The degree table of the write-up (section 2): z has 0, u_i has i, a1, a2 and the t's have 13,
    a3, a4, a5 have 14, 15, 16, c_j has 17 + j and b_j has 24 + j, in vertex order. *)
Lemma mel_degree_table :
  [seq count (fun y => mel_rel x y) mel_I37 | x <- mel_I37] =
  [:: 13; 13; 14; 15; 16; 24; 25; 26; 27; 28; 29; 17; 18; 19; 20; 21; 22; 23;
      13; 13; 13; 13; 13; 13; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 0].
Proof. by vm_compute. Qed.

Lemma mel_valency_variety : valency_variety mel_graph = 30.
Proof.
rewrite /valency_variety enum_setT -enumT mel_enum.
rewrite (eq_map (fun x => mel_deg x)).
by vm_compute.
Qed.

Definition mel_col (v : mel_graph) : 'I_3 :=
  if mel_part v == 1 then @Ordinal 3 1 isT
  else if (mel_part v == 2) || ((mel_part v == 4) && (7 <= mel_idx v <= 9)) then @Ordinal 3 2 isT
  else @Ordinal 3 0 isT.

Lemma mel_col_proper : proper_colouring mel_col.
Proof.
rewrite proper_colouringE; apply/forallP => x; apply/forallP => y; move: x y.
apply: (mel_all2 (P := fun x y : 'I_37 => (@edge_rel mel_graph x y) ==> (mel_col x != mel_col y))).
by vm_compute.
Qed.

Lemma mel_chi : χ([set: mel_graph]) <= 3.
Proof. by have := proper_colouring_chi mel_col_proper; rewrite card_ord. Qed.

Theorem melnikovs_valency_variety_disproved : ~ melnikovs_valency_variety_statement.
Proof.
move=> /(_ mel_graph); rewrite card_ord mel_valency_variety => /(_ isT) h.
by have := leq_trans h mel_chi.
Qed.


Print Assumptions melnikovs_valency_variety_disproved.
