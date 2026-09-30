(** * Atlas.foundations.complete_minors -- clique minors of complete bipartite graphs

    [K_{n+1,n+1}] has a [K_{n+2}] minor (contract [n] edges of a perfect
    matching), and every graph has a [K_0] minor. *)

From GTBase Require Import base.
From GraphTheory Require Import minor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** K_{n+1,n+1} has a K_{n+2} minor: contract n matching edges. *)
Lemma KB_diag_minor_K (n : nat) : minor (KB n.+1 n.+1) 'K_n.+2.
Proof.
pose a (i : nat) : KB n.+1 n.+1 := inl (inord i).
pose b (i : nat) : KB n.+1 n.+1 := inr (inord i).
have ab i j : a i -- b j by [].
have ba i j : b j -- a i by [].
pose phi (i : 'K_n.+2) : {set KB n.+1 n.+1} :=
  if (i < n)%N then [set a i; b i] else if i == n :> nat then [set a n] else [set b n].
have hi (i : 'K_n.+2) : (i < n)%N \/ (i : nat) = n \/ (i : nat) = n.+1.
  case: (ltngtP i n) => h; [by left | | by right; left].
  by right; right; apply/eqP; rewrite eqn_leq h -ltnS ltn_ord.
have ainj i j : (i <= n)%N -> (j <= n)%N -> (a i == a j) = (i == j).
  move=> ih jh; apply/eqP/eqP => [e|->//].
  by move: e => [] /(congr1 val); rewrite /= !inordK.
have binj i j : (i <= n)%N -> (j <= n)%N -> (b i == b j) = (i == j).
  move=> ih jh; apply/eqP/eqP => [e|->//].
  by move: e => [] /(congr1 val); rewrite /= !inordK.
have abn i j : (a i == b j) = false by [].
apply: (@minor_of_rmap _ _ phi); split.
- move=> i; rewrite /phi; case: ifP => _; last case: ifP => _.
  + by apply/set0Pn; exists (a i); rewrite !inE eqxx.
  + by apply/set0Pn; exists (a n); rewrite !inE.
  + by apply/set0Pn; exists (b n); rewrite !inE.
- move=> i; rewrite /phi; case: ifP => _; last case: ifP => _.
  + exact: connected2.
  + exact: connected1.
  + exact: connected1.
- pose g (x : KB n.+1 n.+1) : nat :=
    match x with inl k => if (k < n)%N then (k : nat) else n | inr k => if (k < n)%N then (k : nat) else n.+1 end.
  have gphi (x : KB n.+1 n.+1) (i : 'K_n.+2) : x \in phi i -> g x = i.
    rewrite /phi; case: ifP => h; last case: ifP => h2.
    + have il : (i <= n)%N by exact: ltnW.
      by rewrite !inE => /orP[] /eqP ->; rewrite /g /= inordK ?h.
    + by rewrite inE => /eqP ->; rewrite /g /= inordK ?ltnn // (eqP h2).
    + rewrite inE => /eqP ->; rewrite /g /= inordK ?ltnn //.
      by have [|[]] := hi i; [rewrite h | move/eqP; rewrite h2 | ].
  move=> i j ij; rewrite -setI_eq0; apply/eqP/setP => x; rewrite in_setI in_set0.
  apply/negbTE/negP => /andP[/gphi xi /gphi xj].
  by move: ij; rewrite -val_eqE /= -xi -xj eqxx.
- move=> i j ij; have {}ij : (i : nat) != j by exact: ij.
  rewrite /phi.
  have [ilt|[ie|ie]] := hi i; have [jlt|[je|je]] := hi j;
    rewrite ?ilt ?jlt ?ie ?je ?ltnn ?eqxx ?ltnSn ?(gtn_eqF (ltnSn n)) /=;
    rewrite ?(ltnNge n.+1 n) ?leqnSn ?(ltn_eqF ilt) ?(ltn_eqF jlt) /=;
    try (by move: ij; rewrite ?ie ?je eqxx);
    apply/neighborP;
    first [ by exists (a i), (b j); rewrite !inE ?eqxx ?orbT
          | by exists (b i), (a j); rewrite !inE ?eqxx ?orbT
          | by exists (a i), (b n); rewrite !inE ?eqxx ?orbT
          | by exists (b i), (a n); rewrite !inE ?eqxx ?orbT
          | by exists (a n), (b j); rewrite !inE ?eqxx ?orbT
          | by exists (b n), (a j); rewrite !inE ?eqxx ?orbT
          | by exists (a n), (b n); rewrite !inE ?eqxx ?orbT
          | by exists (b n), (a n); rewrite !inE ?eqxx ?orbT ].
Qed.

(** Every graph has the empty clique as a minor. *)
Lemma minor_K0 (G : sgraph) : minor G 'K_0.
Proof. by apply: (@minor_of_rmap G 'K_0 (fun _ => set0)); split => -[]. Qed.
