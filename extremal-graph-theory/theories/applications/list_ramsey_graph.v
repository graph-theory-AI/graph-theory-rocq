(** Graph-theoretic readback of the finite-palette Ramsey theorem. *)
From GTBase Require Import base.
From GraphTheory Require Import dom partition.
From Extremal.foundations Require Import list_ramsey.
From Extremal.applications Require Import list_ramsey_nat.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition lr_proper (G : sgraph) (C : finType) (f : G -> C) : Prop :=
  forall x y, x -- y -> f x != f y.

Lemma lr_proper_chi_bound (G : sgraph) (C : finType) (f : G -> C) :
  lr_proper f -> χ([set: G]) <= #|C|.
Proof.
move=> hf.
pose P := preim_partition f [set: G].
have hp : coloring P [set: G].
  apply/andP; split; first exact: preim_partitionP.
  apply/forall_inP=> A /imsetP[x _ ->]; apply/stableP.
  move=> y z; rewrite !inE /= => /eqP hy /eqP hz.
  apply/negP=> hyz; by have := hf y z hyz; rewrite -hy -hz eqxx.
apply: leq_trans (color_bound hp) _.
pose fiber c := [set x : G | c == f x].
have hsub : P \subset [set fiber c | c in [set: C]].
  apply/subsetP=> A /imsetP[x _ ->]; apply/imsetP.
  exists (f x); first by rewrite inE.
  by apply/setP=> y; rewrite /fiber !inE.
apply: leq_trans (subset_leq_card hsub) _.
by have := leq_imset_card fiber [set: C]; rewrite cardsT.
Qed.

Lemma lr_chi_coloring (G : sgraph) (s : nat) :
  χ([set: G]) <= s -> exists f : G -> 'I_s, lr_proper f.
Proof.
case: chiP => P /andP[hp /forall_inP hs] _ hchi.
have hb x : pblock P x \in P.
  apply: pblock_mem; by rewrite (cover_partition hp) inE.
pose C := {A : {set G} | A \in P}.
pose b (x : G) : C := Sub (pblock P x) (hb x).
have Cbound : #|{: C}| <= s by rewrite /C card_sig.
pose f x := widen_ord Cbound (enum_rank (b x)).
exists f => x y hxy; apply/negP=> /eqP he.
have hsame : pblock P x = pblock P y.
  have er : enum_rank (b x) = enum_rank (b y).
    apply: ord_inj; exact: (congr1 (@nat_of_ord s) he).
  have eb : b x = b y := enum_rank_inj er.
  exact: (congr1 (fun z : C => val z) eb).
have hx : x \in pblock P x by rewrite mem_pblock (cover_partition hp) inE.
have hy : y \in pblock P x by rewrite hsame mem_pblock (cover_partition hp) inE.
by have /stableP/(_ x y hx hy) := hs _ (hb x); rewrite hxy.
Qed.

Definition lr_color_graph (V : finType) (C : eqType) (phi : V -> V -> C) (c : C) : sgraph :=
  fg_mk_sgraph (fun x y => phi x y == c).

Lemma lr_color_graph_edge (V : finType) (C : eqType) (phi : V -> V -> C) (c : C) :
  (forall x y, phi x y = phi y x) ->
  forall x y : lr_color_graph phi c,
    (x -- y) = ((x != y) && (phi x y == c)).
Proof. by move=> sym x y; rewrite /edge_rel /= /fg_srel (sym y x) orbb. Qed.

Theorem lr_avoids_chromatic (V C : finType) (s : nat) (phi : V -> V -> C) :
  (forall x y, phi x y = phi y x) ->
  lr_avoids s phi <-> forall c, χ([set: lr_color_graph phi c]) <= s.
Proof.
move=> sym; split.
- move=> [f hf] c.
  have proper : lr_proper (fun x : lr_color_graph phi c => f x c).
    move=> x y; rewrite lr_color_graph_edge // => /andP[xy /eqP pc].
    by have := hf x y xy; rewrite pc.
  by have := lr_proper_chi_bound proper; rewrite card_ord.
- move=> hchi.
  have exg c : exists g : {ffun V -> 'I_s},
      [forall x, forall y, ((x != y) && (phi x y == c)) ==> (g x != g y)].
    have [f hf] := lr_chi_coloring (hchi c).
    exists [ffun x => f x]; apply/forallP=> x; apply/forallP=> y.
    apply/implyP=> edge; rewrite !ffunE; apply: hf.
    by rewrite lr_color_graph_edge.
  pose g c := xchoose (exg c).
  exists (fun x => [ffun c => g c x]) => x y xy.
  rewrite !ffunE.
  have /forallP/(_ x)/forallP/(_ y)/implyP H := xchooseP (exg (phi x y)).
  apply: H; by rewrite xy eqxx.
Qed.

Lemma lr_not_avoids_chromatic (V C : finType) (s : nat) (phi : V -> V -> C) :
  (forall x y, phi x y = phi y x) ->
  (~ lr_avoids s phi) <-> exists c, s < χ([set: lr_color_graph phi c]).
Proof.
move=> sym; split.
- move=> noavoid.
  case: (boolP [exists c, s < χ([set: lr_color_graph phi c])]).
    by move/existsP=> [c hc]; exists c.
  move/negP=> none; exfalso; apply: noavoid.
  apply: (proj2 (lr_avoids_chromatic s sym)) => c.
  rewrite leqNgt; apply/negP=> hc; apply: none.
  by apply/existsP; exists c.
- move=> [c hc] avoid.
  have bound := proj1 (lr_avoids_chromatic s sym) avoid c.
  by have := leq_ltn_trans bound hc; rewrite ltnn.
Qed.

(** Forcing a monochromatic member of H_s is equivalent to forcing a color
    class whose chromatic number exceeds s: that class itself is a member,
    while a proper s-coloring restricts to every subgraph. *)
Definition lr_graph_forces (s k n : nat) : Prop :=
  exists q : nat, 0 < q /\
    exists L : 'I_n -> 'I_n -> {set 'I_q},
      lr_valid_lists k L /\
      forall phi, lr_admissible L phi ->
        exists c, s < χ([set: lr_color_graph phi c]).

Lemma lr_forces_graph (s k n : nat) : lr_forces s k n <-> lr_graph_forces s k n.
Proof.
split=> -[q [qpos [L [valid force]]]]; exists q; split=> //; exists L; split=> //.
- move=> phi legal; apply: (proj1 (lr_not_avoids_chromatic s (proj1 legal))).
  exact: force phi legal.
- move=> phi legal; apply: (proj2 (lr_not_avoids_chromatic s (proj1 legal))).
  exact: force phi legal.
Qed.

Definition list_ramsey_chromatic_graph_statement : Prop :=
  forall s k : nat, 2 <= s -> 0 < k ->
    lr_graph_forces s k (s ^ k).+1 /\
    forall n, lr_graph_forces s k n -> (s ^ k).+1 <= n.

Theorem list_ramsey_chromatic_graph : list_ramsey_chromatic_graph_statement.
Proof.
move=> s k s2 kpos; have [upper lower] := list_ramsey_chromatic s2 kpos.
split; first exact: (proj1 (lr_forces_graph s k (s ^ k).+1)).
move=> n Hn; apply: lower; exact: (proj2 (lr_forces_graph s k n)).
Qed.

Theorem lr_nat_avoids_chromatic (V : finType) (s : nat) (phi : V -> V -> nat) :
  (forall x y, phi x y = phi y x) ->
  lr_nat_avoids s phi <-> forall c, χ([set: lr_color_graph phi c]) <= s.
Proof.
move=> sym; split.
- move=> [f hf] c.
  have proper : lr_proper (fun x : lr_color_graph phi c => f x c).
    move=> x y; rewrite lr_color_graph_edge // => /andP[xy /eqP pc].
    by have := hf x y xy; rewrite pc.
  by have := lr_proper_chi_bound proper; rewrite card_ord.
- move=> hchi.
  have exg c : exists g : {ffun V -> 'I_s},
      [forall x, forall y, ((x != y) && (phi x y == c)) ==> (g x != g y)].
    have [f hf] := lr_chi_coloring (hchi c).
    exists [ffun x => f x]; apply/forallP=> x; apply/forallP=> y.
    apply/implyP=> edge; rewrite !ffunE; apply: hf.
    by rewrite lr_color_graph_edge.
  pose g c := xchoose (exg c).
  exists (fun x c => g c x) => x y xy.
  have /forallP/(_ x)/forallP/(_ y)/implyP H := xchooseP (exg (phi x y)).
  apply: H; by rewrite xy eqxx.
Qed.

Lemma lr_nat_not_avoids_chromatic (V : finType) (s : nat) (phi : V -> V -> nat) :
  0 < s -> (forall x y, phi x y = phi y x) ->
  (~ lr_nat_avoids s phi) <-> exists c, s < χ([set: lr_color_graph phi c]).
Proof.
move=> spos sym; split.
- move=> noavoid.
  case: (boolP [exists e : V * V, s < χ([set: lr_color_graph phi (phi e.1 e.2)])]).
    by move/existsP=> [e he]; exists (phi e.1 e.2).
  move/negP=> none; exfalso; apply: noavoid.
  apply: (proj2 (lr_nat_avoids_chromatic s sym)) => c.
  case: (boolP [exists e : V * V, phi e.1 e.2 == c]).
    move/existsP=> [e /eqP ec]; rewrite leqNgt; apply/negP=> hc; apply: none.
    by apply/existsP; exists e; rewrite ec.
  move/negP=> absent.
  have missing x y : phi x y != c.
    apply/negP=> xc; apply: absent; apply/existsP; by exists (x,y).
  have proper : lr_proper (fun _ : lr_color_graph phi c => Ordinal spos).
    move=> x y; by rewrite lr_color_graph_edge // (negbTE (missing x y)) andbF.
  by have := lr_proper_chi_bound proper; rewrite card_ord.
- move=> [c hc] avoid.
  have bound := proj1 (lr_nat_avoids_chromatic s sym) avoid c.
  by have := leq_ltn_trans bound hc; rewrite ltnn.
Qed.

Definition lr_nat_graph_forces (s k n : nat) : Prop :=
  exists L : 'I_n -> 'I_n -> seq nat,
    lr_nat_valid_lists k L /\
    forall phi, lr_nat_admissible L phi ->
      exists c, s < χ([set: lr_color_graph phi c]).

Lemma lr_nat_forces_graph (s k n : nat) :
  0 < s -> (lr_nat_forces s k n <-> lr_nat_graph_forces s k n).
Proof.
move=> spos; split=> -[L [valid force]]; exists L; split=> //.
- move=> phi legal; apply: (proj1 (lr_nat_not_avoids_chromatic spos (proj1 legal))).
  exact: force phi legal.
- move=> phi legal; apply: (proj2 (lr_nat_not_avoids_chromatic spos (proj1 legal))).
  exact: force phi legal.
Qed.

(** Exact source-facing statement: colors are arbitrary natural numbers,
    monochromatic graphs use the library's chromatic number, and the Ramsey
    number is expressed by its least-forcing-order characterization. *)
Definition list_ramsey_chromatic_resolution_statement : Prop :=
  forall s k : nat, 2 <= s -> 0 < k ->
    lr_nat_graph_forces s k (s ^ k).+1 /\
    forall n, lr_nat_graph_forces s k n -> (s ^ k).+1 <= n.

Theorem list_ramsey_chromatic_resolution : list_ramsey_chromatic_resolution_statement.
Proof.
move=> s k s2 kpos; have [upper lower] := list_ramsey_natural s2 kpos.
have spos : 0 < s := ltn_trans (ltnSn 0) s2.
split; first exact: (proj1 (lr_nat_forces_graph k (s ^ k).+1 spos)).
move=> n Hn; apply: lower; exact: (proj2 (lr_nat_forces_graph k n spos)).
Qed.
