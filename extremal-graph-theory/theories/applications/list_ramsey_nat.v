(** Natural-number edge lists reduce to a finite ordinal palette. *)
From mathcomp Require Import all_boot.
From Extremal.foundations Require Import list_ramsey.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma lr_mem_max (xs : seq nat) (c : nat) :
  c \in xs -> c <= foldr maxn 0 xs.
Proof.
elim: xs => [|a xs IH] //=.
rewrite inE => /orP [/eqP ->|cx].
- exact: leq_maxl.
- exact: leq_trans (IH cx) (leq_maxr a _).
Qed.

Definition lr_nat_valid_lists (V : finType) (k : nat)
    (L : V -> V -> seq nat) : Prop :=
  (forall x y c, (c \in L x y) = (c \in L y x)) /\
  forall x y, x != y -> uniq (L x y) /\ size (L x y) = k.

Definition lr_nat_admissible (V : finType) (L : V -> V -> seq nat)
    (phi : V -> V -> nat) : Prop :=
  (forall x y, phi x y = phi y x) /\
  forall x y, x != y -> phi x y \in L x y.

Definition lr_nat_avoids (V : finType) (s : nat)
    (phi : V -> V -> nat) : Prop :=
  exists f : V -> nat -> 'I_s,
    forall x y, x != y -> f x (phi x y) != f y (phi x y).

Theorem lr_nat_avoiding_coloring (V : finType) (L : V -> V -> seq nat) (s k : nat) :
  0 < s -> lr_nat_valid_lists k L -> #|V| <= s ^ k ->
  exists phi, lr_nat_admissible L phi /\ lr_nat_avoids s phi.
Proof.
move=> spos [Lsym Lcard] bound.
pose colors := flatten [seq L e.1 e.2 | e <- enum [set: V * V]].
pose m := foldr maxn 0 colors.
have bounded x y c : c \in L x y -> c < m.+1.
  move=> cL; rewrite ltnS; apply: lr_mem_max.
  apply/flatten_mapP; exists (x,y) => //; by rewrite mem_enum inE.
pose LL x y := [set i : 'I_m.+1 | (i : nat) \in L x y].
have LLsym x y : LL x y = LL y x.
  by apply/setP=> i; rewrite /LL !inE Lsym.
have LLcard x y : x != y -> #|LL x y| = k.
  move=> xy; have [LU Lsize] := Lcard x y xy.
  have injord : {in L x y &, injective (@inord m)}.
    move=> a b aL bL E.
    have := congr1 (@nat_of_ord m.+1) E.
    by rewrite !inordK ?(bounded _ _ _ aL) ?(bounded _ _ _ bL).
  have mappedU : uniq [seq inord c : 'I_m.+1 | c <- L x y].
    by rewrite map_inj_in_uniq.
  have E : LL x y = [set i : 'I_m.+1 | i \in [seq inord c | c <- L x y]].
    apply/setP=> i; rewrite /LL !inE.
    apply/idP/idP=> H.
    - apply/mapP; exists (i : nat) => //; by rewrite inord_val.
    - move/mapP: H=> [c cL ->]; by rewrite inordK ?(bounded _ _ _ cL).
  rewrite E cardsE.
  have C : #|[seq inord c : 'I_m.+1 | c <- L x y]| = size (L x y).
    by rewrite (card_uniqP mappedU) size_map.
  by rewrite C Lsize.
have valid : lr_valid_lists k LL by split.
have [phi [admissible [f hf]]] := lr_avoiding_coloring (@ord0 m) spos valid bound.
have [phisym philegal] := admissible.
exists (fun x y => (phi x y : nat)); split.
- split=> [x y|x y xy]; first by rewrite phisym.
  by have := philegal x y xy; rewrite /LL inE.
- exists (fun x c => f x (inord c)) => x y xy.
  by rewrite !inord_val; exact: hf x y xy.
Qed.

Lemma lr_nat_product_bound (V : finType) (s k : nat) (phi : V -> V -> nat) :
  (forall x y, x != y -> phi x y < k) ->
  lr_nat_avoids s phi -> #|V| <= s ^ k.
Proof.
move=> phi_bound [f hf].
pose F x := [ffun c : 'I_k => f x c].
have injF : injective F.
  move=> x y E; apply/eqP; apply/negPn/negP=> xy.
  pose c : 'I_k := Ordinal (phi_bound x y xy).
  have labels := congr1 (fun h : {ffun 'I_k -> 'I_s} => h c) E.
  rewrite /F !ffunE /= in labels.
  by have := hf x y xy; rewrite labels eqxx.
by have := leq_card F injF; rewrite card_ffun !card_ord.
Qed.

Definition lr_nat_forces (s k n : nat) : Prop :=
  exists L : 'I_n -> 'I_n -> seq nat,
    lr_nat_valid_lists k L /\
    forall phi, lr_nat_admissible L phi -> ~ lr_nat_avoids s phi.

Definition lr_nat_is_number (s k r : nat) : Prop :=
  lr_nat_forces s k r /\ forall n, lr_nat_forces s k n -> r <= n.

(** No corpus row: natural-number-colour variant of the list Ramsey equality R_l(H_s, k) = s^k + 1,
    PROVED below as [list_ramsey_natural]: edge lists are ordinary finite [seq nat] and the
    Ramsey number is the least n forcing a non-avoiding colouring. Same underlying result
    as arXiv:2103.15175 Section 3.1, whose corpus row arxiv:2103.15175#00 carries no
    formal_name and so cannot be cited; see
    https://graph-theory-ai.github.io/graph-conjectures/arxiv/2103.15175__00/ *)
Definition list_ramsey_natural_statement : Prop :=
  forall s k : nat, 2 <= s -> 0 < k -> lr_nat_is_number s k (s ^ k).+1.

(** Exact least-number theorem with arbitrary natural-number colors and
    ordinary finite edge lists. The upper forcing assignment uses 0,...,k-1;
    the lower bound places no global restriction on the colors appearing. *)
Theorem list_ramsey_natural : list_ramsey_natural_statement.
Proof.
move=> s k s2 kpos.
have spos : 0 < s := ltn_trans (ltnSn 0) s2.
split.
- exists (fun _ _ => iota 0 k); split.
  + split=> // x y _; split; [exact: iota_uniq | exact: size_iota].
  + move=> phi [_ legal] avoiding.
    have pb x y : x != y -> phi x y < k.
      move=> xy; have := legal x y xy.
      by rewrite mem_iota add0n leq0n.
    have small := lr_nat_product_bound pb avoiding.
    by rewrite card_ord ltnn in small.
- move=> n [L [valid forcing]].
  case: (leqP (s ^ k).+1 n) => // bound.
  have small : #|'I_n| <= s ^ k by rewrite card_ord.
  have [phi [legal avoiding]] := lr_nat_avoiding_coloring spos valid small.
  exfalso; exact: forcing phi legal avoiding.
Qed.
