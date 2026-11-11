(** * Minor.conjectures.grounding_X298 -- grounding lemmas for wave X298.

    Qed-closed, axiom-free certificates for the two rows of [X298.v] (hyp_inhabited, not_trivially_true; X298
    declares no helper, so no helper_sanity).
    - Holroyd's row: hyp at K_1 with S = V(K_1) (one colour, met on S; the one vertex is the model); ntt drops
      colourfulness, and the variant fails at K_1 with S empty (no branch set meets the empty set).
    - Dvorak and Swart's row: hyp at k = 3 with the set of all colourings of one root, placed in K_1, which has no
      model of K_3 at all; ntt: the variant whose witness C must be empty or the set of all colourings implies
      the row and fails, because the set of all colourings is realized by the edgeless graph on X and the empty
      set by X beside a disjoint K_4.
    They validate the statements; they do not prove them. *)

From GTBase Require Import base colourings.
From GraphTheory Require Import minor.
From Minor.conjectures Require Import X298.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ** Shared facts *)

(* The whole vertex set of K_n is a clique, so chi(K_n) = n. *)
Lemma g298_chi_K (n : nat) : χ([set: 'K_n]) = n.
Proof.
by rewrite (chi_clique (@Kn_clique n)) cardsT card_ord.
Qed.

(* Two ordinals below 1 are equal. *)
Lemma g298_ord1 (m : nat) (i j : 'I_m) : m = 1 -> i = j.
Proof.
move=> m1; subst m; apply: val_inj; case: i => [[|i] //]; case: j => [[|j] //].
Qed.

(* ** Holroyd's row *)

Definition g298_colourful (G : sgraph) (S : {set G}) : Prop :=
  forall col : G -> 'I_(χ([set: G])), proper_colouring col ->
    forall i : 'I_(χ([set: G])), exists2 s, s \in S & col s = i.

Definition g298_rooted_chi_model (G : sgraph) (S : {set G}) : Prop :=
  exists phi : ('K_(χ([set: G]))) -> {set G},
    minor_rmap phi /\ (forall i, phi i :&: S != set0).

(* hyp: at K_1, the whole vertex set is colourful and roots a K_1 model; the statement gives that model too. *)
Definition g298_holroyd_hyp_claim : Prop :=
  [/\ g298_colourful [set: 'K_1], g298_rooted_chi_model [set: 'K_1]
    & (holroyd_strong_hadwiger_statement -> g298_rooted_chi_model [set: 'K_1])].

Lemma g298_K1_colourful : g298_colourful [set: 'K_1].
Proof.
move=> col _ i; exists ord0; first by rewrite inE.
exact: g298_ord1 (g298_chi_K 1).
Qed.

Lemma g298_K1_model : g298_rooted_chi_model [set: 'K_1].
Proof.
exists (fun _ => [set ord0]); split; last by move=> i; rewrite setIT; apply/set0Pn; exists ord0; rewrite inE.
split.
- by move=> i; apply/set0Pn; exists ord0; rewrite inE.
- by move=> i; exact: connected1.
- by move=> i j ij; rewrite (g298_ord1 i j (g298_chi_K 1)) eqxx in ij.
- by move=> i j ij; rewrite /edge_rel /= (g298_ord1 i j (g298_chi_K 1)) eqxx in ij.
Qed.

Theorem g298_holroyd_hyp_inhabited : g298_holroyd_hyp_claim.
Proof.
split; [exact: g298_K1_colourful | exact: g298_K1_model |].
by move=> S; apply: S; exact: g298_K1_colourful.
Qed.

(* ntt: every vertex set roots a K_chi model (colourfulness dropped); it fails at K_1 with the empty set. *)
Definition g298_holroyd_any_root : Prop := forall (G : sgraph) (S : {set G}), g298_rooted_chi_model S.

Definition g298_holroyd_ntt_claim : Prop :=
  ~ g298_holroyd_any_root /\ (g298_holroyd_any_root -> holroyd_strong_hadwiger_statement).

Theorem g298_holroyd_not_trivially_true : g298_holroyd_ntt_claim.
Proof.
split; last by move=> V G S _; exact: V.
move=> V; have [phi [_ hS]] := V 'K_1 set0.
have i : 'I_(χ([set: 'K_1])) by rewrite g298_chi_K; exact: ord0.
by have := hS i; rewrite setI0 eqxx.
Qed.

(* ** Dvorak and Swart's row *)

Definition g298_perm_closed (n k : nat) (C : {set {ffun 'I_n -> 'I_k}}) : Prop :=
  forall (pi : 'I_k -> 'I_k) (f : {ffun 'I_n -> 'I_k}), bijective pi -> f \in C -> [ffun j => pi (f j)] \in C.

Definition g298_rooted_free (n k : nat) (G : sgraph) (x : 'I_n -> G) : Prop :=
  ~ (exists phi : ('K_k) -> {set G}, minor_rmap phi /\ (forall i, phi i :&: [set x j | j in 'I_n] != set0)).

Definition g298_realizes (n k : nat) (G : sgraph) (x : 'I_n -> G) (C : {set {ffun 'I_n -> 'I_k}}) : Prop :=
  forall f : {ffun 'I_n -> 'I_k},
    f \in C <-> exists2 col : G -> 'I_k, proper_colouring col & forall j, col (x j) = f j.

Lemma g298_setT_perm_closed (n k : nat) : g298_perm_closed [set: {ffun 'I_n -> 'I_k}].
Proof. by move=> pi f _ _; rewrite inE. Qed.

(* K_1 has no model of K_3: two branch sets would be disjoint non-empty sets of one vertex. *)
Lemma g298_K1_no_K3 (phi : ('K_3) -> {set 'K_1}) : ~ minor_rmap phi.
Proof.
case=> ne _ dis _.
have [a a0] := set0Pn _ (ne ord0); have [b b1] := set0Pn _ (ne (@Ordinal 3 1 isT)).
have ab : a = b by apply: g298_ord1.
by move: (dis ord0 (@Ordinal 3 1 isT) isT) => /disjointFr /(_ a0); rewrite ab b1.
Qed.

(* hyp: k = 3, the set of all colourings of one root (closed under permutations), placed in K_1 by the identity
   (injective), which is rooted-K_3-minor-free; the statement gives a witness at k = 3. *)
Definition g298_ds_hyp_claim : Prop :=
  [/\ g298_perm_closed [set: {ffun 'I_1 -> 'I_3}], injective (fun j : 'I_1 => j : ('K_1)),
      g298_rooted_free 3 (fun j : 'I_1 => j : ('K_1))
    & (rooted_minor_free_unrealizable_colourings_statement ->
       exists (n : nat) (C : {set {ffun 'I_n -> 'I_3}}), g298_perm_closed C)].

Theorem g298_ds_hyp_inhabited : g298_ds_hyp_claim.
Proof.
split; [exact: g298_setT_perm_closed | by [] | |].
- by move=> [phi [mp _]]; exact: g298_K1_no_K3 mp.
- move=> S; have [n [C [cl _]]] := S 3 isT; by exists n, C.
Qed.

(* The set of all colourings is realized by the edgeless graph on X, which has no model of K_k for k >= 2. *)
Lemma g298_edgeless_realizes_all (n k : nat) :
  g298_realizes (fun j : 'I_n => j : compl 'K_n) [set: {ffun 'I_n -> 'I_k}].
Proof.
move=> f; rewrite inE; split => // _.
exists (fun v : compl 'K_n => f v) => //.
by apply/proper_colouringP => u v uv; move: (compl_Kn_edgeless u v); rewrite uv.
Qed.

Lemma g298_edgeless_rooted_free (n k : nat) : 2 <= k -> g298_rooted_free k (fun j : 'I_n => j : compl 'K_n).
Proof.
move=> k2 [phi [[_ _ _ adj] _]].
have k0 : 0 < k by exact: ltnW k2.
have /adj : (Ordinal k0 : 'K_k) -- (Ordinal k2 : 'K_k) by [].
by move=> /existsP [u /andP [_ /existsP [v /andP [_ uv]]]]; move: (compl_Kn_edgeless u v); rewrite uv.
Qed.

(* Beside any graph H, the edgeless graph on X is still X-rooted-K_k-minor-free for k >= 2: a branch set holds a
   root, on the edgeless side, and is connected, so it stays on that side, where no two sets are adjacent. *)
Lemma g298_join_rooted_free (n k : nat) (H : sgraph) :
  2 <= k -> g298_rooted_free k (fun j : 'I_n => inl j : sjoin (compl 'K_n) H).
Proof.
move=> k2 [phi [[_ conn _ adj] root]].
have k0 : 0 < k by exact: ltnW k2.
have [r /setIP [r0 /imsetP [j _ rj]]] := set0Pn _ (root (Ordinal k0)).
have /adj /existsP [u /andP [u0 /existsP [v /andP [v1 uv]]]] :
  (Ordinal k0 : 'K_k) -- (Ordinal k2 : 'K_k) by [].
case: u uv u0 => [a|a]; case: v v1 => [b|b] v1 //= uv u0.
- by have /negP := compl_Kn_edgeless a b; apply.
- have /preliminaries.sub_restrict_connect := conn _ r (inr a) r0 u0.
  by rewrite rj; apply/negP; exact: sjoin_disconnected.
Qed.

(* The empty set of colourings is realized by X beside a disjoint K_(k+1): no proper k-colouring exists, since its
   restriction to K_(k+1) would be one (chi(K_(k+1)) = k + 1). *)
Lemma g298_join_realizes_none (n k : nat) :
  g298_realizes (fun j : 'I_n => inl j : sjoin (compl 'K_n) 'K_k.+1) (set0 : {set {ffun 'I_n -> 'I_k}}).
Proof.
move=> f; rewrite inE; split => // [[col pc _]].
have pK : proper_colouring (fun v : 'K_k.+1 => col (inr v)).
  apply/proper_colouringP => u v uv.
  by move/proper_colouringP: pc => pc; exact: pc (inr u) (inr v) uv.
by have := proper_colouring_chi pK; rewrite g298_chi_K card_ord ltnn.
Qed.

(* ntt: the variant whose witness C must be empty or full. *)
Definition g298_ds_trivial_witness : Prop :=
  forall k : nat, 3 <= k ->
  exists (n : nat) (C : {set {ffun 'I_n -> 'I_k}}),
    (C = set0 \/ C = setT) /\ g298_perm_closed C /\
    (forall (G : sgraph) (x : 'I_n -> G), injective x -> g298_rooted_free k x -> ~ g298_realizes x C).

Definition g298_ds_ntt_claim : Prop :=
  ~ g298_ds_trivial_witness /\
  (g298_ds_trivial_witness -> rooted_minor_free_unrealizable_colourings_statement).

Theorem g298_ds_not_trivially_true : g298_ds_ntt_claim.
Proof.
split; last first.
  move=> V k k3; have [n [C [_ [cl h]]]] := V k k3; exists n, C; split; first exact: cl.
  move=> G x xi; exact: h G x xi.
move=> V; have [n [C [[->|->] [_ h]]]] := V 3 isT.
- apply: (h _ (fun j : 'I_n => inl j : sjoin (compl 'K_n) 'K_4)).
  + by move=> a b [].
  + exact: g298_join_rooted_free.
  + exact: g298_join_realizes_none.
- apply: (h _ (fun j : 'I_n => j : compl 'K_n)) => //.
  + exact: g298_edgeless_rooted_free.
  + exact: g298_edgeless_realizes_all.
Qed.
