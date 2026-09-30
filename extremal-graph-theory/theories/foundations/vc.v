(** * Extremal.foundations.vc — VC dimension of the neighbourhood set system

    Two reusable ingredients of the "Erdős–Hajnal implies its VC-dimension
    specialisation" reduction (corpus edge e116, X223 row arxiv:1912.02342#00):

    (1) VC-DIMENSION IS MONOTONE UNDER INDUCED SUBGRAPHS.  If [i : F ⇀ G] is an
        induced-subgraph embedding (injective and adjacency-mono in BOTH
        directions, coq-graph-theory's [isubgraph]), then a set shattered in [F]
        has a shattered image in [G] — neighbourhoods of [F] are exactly the
        traces of neighbourhoods of [G] on the image.  Hence bounding the
        VC dimension of the host bounds the VC dimension of every induced
        subgraph ([vc_dim_leq_isubgraph]).

    (2) THE SHATTERING GADGET [shatter_graph n].  The bipartite graph with parts
        ['I_n] and [{set 'I_n}], where [inr A] is adjacent exactly to the [inl i]
        with [i \in A].  Its ['I_n]-side ([shatter_side n], of size [n]) is
        shattered, so [shatter_graph d.+1] has VC dimension > d
        ([not_vc_dim_leq_shatter_graph]) and is therefore NOT an induced subgraph
        of any graph of VC dimension at most [d].

    The predicates [shattered] and [vc_dim_leq] below are the BODIES of X223's
    [x223_shattered] and [x223_vc_dim_leq] verbatim (a foundations file must not
    depend on a conjecture file), so they are convertible with them and the
    lemmas apply to the conjecture statement as-is. *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** [S] is shattered by the open neighbourhoods: every subset of [S] is cut out
    of [S] by the neighbourhood of some vertex. *)
Definition shattered (G : sgraph) (S : {set G}) : Prop :=
  forall T : {set G}, T \subset S -> exists v : G, N(v) :&: S = T.

(** The VC dimension of [G] is at most [d]: no shattered set exceeds [d]. *)
Definition vc_dim_leq (G : sgraph) (d : nat) : Prop :=
  forall S : {set G}, shattered S -> #|S| <= d.

(** ** Monotonicity under induced subgraphs *)

(** Neighbourhoods of an induced subgraph are the traces of the host's
    neighbourhoods on the image. *)
Lemma opn_cap_imset (F G : sgraph) (i : F ⇀ G) (v : F) (S : {set F}) :
  N(i v) :&: (i @: S) = i @: (N(v) :&: S).
Proof.
apply/setP => x; rewrite inE; apply/idP/idP.
  case/andP => xN /imsetP[u uS Ex].
  rewrite Ex in xN; rewrite Ex.
  apply: imset_f; move: xN; rewrite !inE => xN.
  by rewrite -(isubgraph_mono i) xN uS.
case/imsetP => u; rewrite !inE => /andP[vu uS] ->.
by rewrite (isubgraph_mono i) vu /=; apply: imset_f.
Qed.

Lemma shattered_isubgraph (F G : sgraph) (i : F ⇀ G) (S : {set F}) :
  shattered S -> shattered (i @: S).
Proof.
move=> shS T subT.
have subS : [set x in S | i x \in T] \subset S.
  by apply/subsetP => x; rewrite inE => /andP[].
have [v Hv] := shS _ subS.
exists (i v); rewrite opn_cap_imset Hv.
apply/setP => x; apply/idP/idP.
  by case/imsetP => u; rewrite inE => /andP[_ iuT] ->.
move=> xT; have /imsetP[u uS Ex] := subsetP subT _ xT.
by rewrite Ex; apply: imset_f; rewrite inE uS -Ex xT.
Qed.

Lemma vc_dim_leq_isubgraph (F G : sgraph) (i : F ⇀ G) (d : nat) :
  vc_dim_leq G d -> vc_dim_leq F d.
Proof.
move=> HG S shS.
have H1 : shattered (i @: S) by exact: shattered_isubgraph.
rewrite -(card_imset _ (isubgraph_inj i)); exact: HG H1.
Qed.

(** ** The shattering gadget *)

Section Shattering.
Variable n : nat.

Definition shat_rel : rel ('I_n + {set 'I_n})%type := fun x y =>
  match x, y with
  | inl i, inr A => i \in A
  | inr A, inl i => i \in A
  | _, _ => false
  end.

Lemma shat_rel_sym : symmetric shat_rel. Proof. by case=> ? []. Qed.
Lemma shat_rel_irrefl : irreflexive shat_rel. Proof. by case. Qed.

Definition shatter_graph : sgraph := SGraph shat_rel_sym shat_rel_irrefl.

(** The ['I_n] side of the gadget. *)
Definition shatter_side : {set shatter_graph} := [set inl i | i in [set: 'I_n]].

Lemma in_shatter_side (x : shatter_graph) :
  (x \in shatter_side) = if x is inl _ then true else false.
Proof.
rewrite /shatter_side; case: x => [i|A].
  exact: (imset_f _ (in_setT i)).
by apply/negbTE/negP => /imsetP[j _ E]; discriminate E.
Qed.

Lemma card_shatter_side : #|shatter_side| = n.
Proof.
by rewrite /shatter_side (card_imset _ (@inl_inj 'I_n {set 'I_n})) cardsT card_ord.
Qed.

Lemma shatter_adj (A : {set 'I_n}) (i : 'I_n) :
  ((inr A : shatter_graph) -- inl i) = (i \in A).
Proof. by []. Qed.

Lemma shattered_shatter_side : shattered shatter_side.
Proof.
move=> T /subsetP subT; exists (inr [set i : 'I_n | inl i \in T]).
apply/setP => x; case: x => [i|A].
  by rewrite !inE shatter_adj inE in_shatter_side andbT.
rewrite inE in_shatter_side andbF; apply/esym/negbTE/negP => HA.
by move/subT: HA; rewrite in_shatter_side.
Qed.

End Shattering.

Lemma not_vc_dim_leq_shatter_graph (d : nat) :
  ~ vc_dim_leq (shatter_graph d.+1) d.
Proof.
move/(_ (shatter_side d.+1) (@shattered_shatter_side d.+1)).
by rewrite card_shatter_side ltnn.
Qed.
