(** * Minor.conjectures.implications_X298 -- the two edges out of Holroyd's Strong Hadwiger row.

    Wave X298 encodes Holroyd's Strong Hadwiger conjecture as the studies row
    studies:std_strong_hadwiger_s_conjecture_holroyd ([holroyd_strong_hadwiger_statement]: a colorful set S of G
    roots a K_(chi(G)) minor) and Dvorak and Swart's Conjecture 4 as arxiv:2504.07764#00
    ([rooted_minor_free_unrealizable_colourings_statement]).  The theorems below record two Rocq-only implication
    edges (meta/corpus_relations.json names neither X298 row):
    - Holroyd => Hadwiger (X214's bm:bm-041, [hadwiger_chromatic_clique_minor_statement]), at S = V(G): Holroyd's
      conjecture strengthens Hadwiger's (arXiv:2209.00594v1, l.112);
    - Holroyd => Conjecture 4, the implication arXiv:2504.07764v1 states at l.99-101.
    Shared facts: an optimal colouring as a map into 'I_(chi(G)) ([x298_chi_colouring], the atlas' chi_colouring
    restated, since minor-theory cannot import the atlas), and a proper colouring that misses a colour bounds the
    chromatic number below its palette ([x298_chi_lt_missing]).  Axiom-free: only [Qed]-closed results. *)

From GTBase Require Import base colourings.
From GraphTheory Require Import minor coloring.
From Minor.conjectures Require Import X214 X298.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Colourings and the chromatic number *)

(** An optimal colouring as a map into ['I_(χ(G))] (Atlas.foundations.fractional's [chi_colouring]). *)
Lemma x298_chi_colouring (G : sgraph) :
  exists col : G -> 'I_(χ([set: G])), proper_colouring col.
Proof.
case: chiP => P hcol _.
have [hpart hstab] := andP hcol.
have hcov : cover P = [set: G] by rewrite (cover_partition hpart); apply/setP => x; rewrite !inE.
have inP (x : G) : pblock P x \in P.
  by rewrite pblock_mem // hcov inE.
have lt (x : G) : (index (pblock P x) (enum P) < #|P|)%N.
  by rewrite cardE index_mem mem_enum.
exists (fun x => Ordinal (lt x)); apply/proper_colouringP => x y xy; apply/negP => /eqP [] e.
have eb : pblock P x = pblock P y.
  by rewrite -(nth_index set0 (s := enum P) (x := pblock P x)) ?mem_enum // e nth_index ?mem_enum.
have /stableP st : stable (pblock P x) by move/forallP: hstab => /(_ (pblock P x)); rewrite inP.
have hx : x \in pblock P x by rewrite mem_pblock hcov inE.
have hy : y \in pblock P x by rewrite eb mem_pblock hcov inE.
by move: (st x y hx hy); rewrite xy.
Qed.

(** A proper colouring into ['I_m] that misses the colour [i] is a proper colouring into the other [m - 1]
    colours. *)
Lemma x298_chi_lt_missing (G : sgraph) (m : nat) (col : G -> 'I_m) (i : 'I_m) :
  proper_colouring col -> (forall v, col v != i) -> χ([set: G]) < m.
Proof.
move=> pc miss.
pose col' (v : G) : {c : 'I_m | c != i} := exist _ (col v) (miss v).
have pc' : proper_colouring col'.
  rewrite -(@proper_colouring_relabel _ _ _ col' val val_inj).
  by rewrite (@proper_colouring_ext _ _ _ col).
have := proper_colouring_chi pc'.
rewrite card_sig cardC1 card_ord => h; apply: leq_ltn_trans h _.
have m0 : 0 < m by apply: leq_ltn_trans (ltn_ord i).
by rewrite prednK.
Qed.

(** ** Holroyd (X298) ==> Hadwiger (X214, bm:bm-041) *)

(** V(G) is colorful: every proper chi(G)-colouring uses every colour. *)
Lemma x298_setT_colourful (G : sgraph) (col : G -> 'I_(χ([set: G]))) :
  proper_colouring col -> forall i, exists2 s, s \in [set: G] & col s = i.
Proof.
move=> pc i; case: (boolP [exists v, col v == i]) => [/existsP [v /eqP e]|].
  by exists v; rewrite ?inE.
rewrite negb_exists => /forallP miss.
by have := x298_chi_lt_missing pc miss; rewrite ltnn.
Qed.

(*@EDGE from=holroyd_strong_hadwiger_statement to=hadwiger_chromatic_clique_minor_statement kind=implies status=verified proved=true proof=holroyd_strong_hadwiger_implies_hadwiger_chromatic_clique_minor note="Rocq-only edge (no corpus relation), routed as a separate edge item after wave X298 (Lancelot's (629)): Holroyd's Strong Hadwiger conjecture strengthens Hadwiger's (arXiv:2209.00594v1, l.112), which is its case S = V(G). V(G) is colorful: a proper chi(G)-colouring that misses a colour maps into the other chi(G) - 1 colours, below the chromatic number (x298_chi_lt_missing); the V(G)-rooted model of K_(chi(G)) is a K_(chi(G)) minor (minor_of_rmap)." *)
Theorem holroyd_strong_hadwiger_implies_hadwiger_chromatic_clique_minor :
  holroyd_strong_hadwiger_statement -> hadwiger_chromatic_clique_minor_statement.
Proof.
move=> H k G <-.
have [phi [rm _]] := H G [set: G] (@x298_setT_colourful G).
exact: minor_of_rmap rm.
Qed.

(** ** Holroyd (X298) ==> Dvorak and Swart's Conjecture 4 (X298, arxiv:2504.07764#00) *)

(** An injective map of ['I_k] into itself is onto. *)
Lemma x298_inj_onto (k : nat) (f : 'I_k -> 'I_k) : injective f -> forall t, exists j, f j = t.
Proof. by move=> /injF_bij [g _ fg] t; exists (g t); rewrite fg. Qed.

(*@EDGE from=holroyd_strong_hadwiger_statement to=rooted_minor_free_unrealizable_colourings_statement kind=implies status=verified proved=true proof=holroyd_strong_hadwiger_implies_rooted_minor_free_unrealizable_colourings note="Rocq-only edge (no corpus relation), routed as a separate edge item after wave X298 (Lancelot's (629)): the implication arXiv:2504.07764v1 states at l.99-101 (its Conjecture 4 is a weakening of Holroyd's). For each k take X = 'I_k and C = the injective colourings of X, closed under colour permutations. A graph G realizing C has a proper k-colouring, so chi(G) <= k; and chi(G) = k, since an optimal colouring widened to k colours would restrict to a colouring of X in C, injective, hence onto, but missing the colour chi(G). So every proper chi(G)-colouring is onto on X, X is colorful, and Holroyd gives an X-rooted K_k model: G is not X-rooted-K_k-minor-free." *)
Theorem holroyd_strong_hadwiger_implies_rooted_minor_free_unrealizable_colourings :
  holroyd_strong_hadwiger_statement -> rooted_minor_free_unrealizable_colourings_statement.
Proof.
move=> H k _.
pose C := [set f : {ffun 'I_k -> 'I_k} | injectiveb f].
exists k, C; split.
  move=> pi f [pinv piK _]; rewrite !inE => /injectiveP finj.
  by apply/injectiveP => a b; rewrite !ffunE => /(can_inj piK)/finj.
move=> G x xinj norooted real.
have inC (col : G -> 'I_k) : proper_colouring col -> injective (fun j => col (x j)).
  move=> pc; have : [ffun j => col (x j)] \in C by apply/real; exists col => // j; rewrite ffunE.
  by rewrite inE => /injectiveP fi a b e; apply: fi; rewrite !ffunE.
have [col0 pc0 _] : exists2 col : G -> 'I_k, proper_colouring col & forall j, col (x j) = [ffun j => j] j.
  by apply/real; rewrite inE; apply/injectiveP => a b; rewrite !ffunE.
have chik : χ([set: G]) <= k by have := proper_colouring_chi pc0; rewrite card_ord.
have chieq : χ([set: G]) = k.
  apply/eqP; rewrite eqn_leq chik /= leqNgt; apply/negP => lt.
  have [col1 pc1] := x298_chi_colouring G.
  have pc2 : proper_colouring (widen_ord chik \o col1).
    by rewrite proper_colouring_relabel // => a b /(congr1 val) /= /val_inj.
  have [j /(congr1 val) /= e] := x298_inj_onto (inC _ pc2) (Ordinal lt).
  by have := ltn_ord (col1 (x j)); rewrite e ltnn.
pose S := [set x j | j in 'I_k].
move: (H G S); rewrite chieq => HS; apply: norooted; apply: HS => col pc i.
have [j <-] := x298_inj_onto (inC _ pc) i.
exists (x j) => //.
by apply/imsetP; exists j.
Qed.
