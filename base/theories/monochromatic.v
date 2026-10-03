(** * Monochromatic subsets for a supplied colour map

    A subset is monochromatic when all its vertices have the same colour.
    This is MathComp's [constant] applied to the enumerated colour sequence;
    the map and its labels remain supplied data. The domain is any finite type
    and the palette any equality type. Graph adjacency is irrelevant.

    Empty and singleton subsets are monochromatic, including an empty domain
    with an empty palette. No colour witness or palette inhabitant is required.
    Values outside the subset do not matter. See [monochromatic_onP] for the
    exact pairwise Prop and [monochromatic_onE] for the bounded Boolean forall.
    Registry: meta/library_primitives/monochromatic.json (C8). *)
From mathcomp Require Import all_boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Unlike [constantP], this view requires no default palette element. *)
Lemma constant_pairwiseP (C : eqType) (s : seq C) :
  reflect {in s &, forall x y : C, x = y} (constant s).
Proof.
case: s => [|a s] /=.
- by constructor=> x y; rewrite in_nil.
apply: (iffP allP).
- move=> h.
  have eq_a z : z \in a :: s -> z = a.
    rewrite inE => /orP[/eqP //|zs].
    apply/eqP; exact: h z zs.
  by move=> x y /eq_a -> /eq_a ->.
- move=> h z zs; apply/eqP; apply: h.
  + by rewrite inE zs orbT.
  + by rewrite inE eqxx.
Qed.

Definition monochromatic_on (T : finType) (C : eqType)
    (col : T -> C) (S : {set T}) : bool :=
  constant [seq col x | x <- enum S].

Lemma monochromatic_onP (T : finType) (C : eqType)
    (col : T -> C) (S : {set T}) :
  reflect {in S &, forall x y : T, col x = col y} (monochromatic_on col S).
Proof.
apply: (iffP (constant_pairwiseP _)).
- move=> h x y xS yS; apply: h.
  + by apply/mapP; exists x; rewrite ?mem_enum.
  + by apply/mapP; exists y; rewrite ?mem_enum.
- move=> h x y /mapP[u]; rewrite mem_enum => uS ->.
  move=> /mapP[v]; rewrite mem_enum => vS ->.
  exact: h u v uS vS.
Qed.

Lemma monochromatic_onE (T : finType) (C : eqType)
    (col : T -> C) (S : {set T}) :
  monochromatic_on col S = [forall x in S, [forall y in S, col x == col y]].
Proof.
apply/idP/idP.
- move/monochromatic_onP=> h; apply/forall_inP=> x xS.
  by apply/forall_inP=> y yS; apply/eqP; exact: h x y xS yS.
- move/forall_inP=> h; apply/monochromatic_onP=> x y xS yS.
  move/forall_inP: (h x xS) => hx; apply/eqP; exact: hx y yS.
Qed.

Lemma monochromatic_on_set0 (T : finType) (C : eqType) (col : T -> C) :
  monochromatic_on col set0.
Proof. by apply/monochromatic_onP=> x y; rewrite in_set0. Qed.

Lemma monochromatic_on_set1 (T : finType) (C : eqType) (col : T -> C) x :
  monochromatic_on col [set x].
Proof. by apply/monochromatic_onP=> u v /set1P -> /set1P ->. Qed.

Lemma monochromatic_on_const (T : finType) (C : eqType) (c : C) (S : {set T}) :
  monochromatic_on (fun _ : T => c) S.
Proof. by apply/monochromatic_onP=> x y. Qed.

Lemma monochromatic_on_pair (T : finType) (C : eqType) (col : T -> C) x y :
  monochromatic_on col [set x; y] = (col x == col y).
Proof.
apply/monochromatic_onP/eqP=> [h|xy].
- by apply: h; rewrite !inE eqxx ?orbT.
- move=> u v; rewrite !inE => /orP[/eqP ->|/eqP ->] /orP[/eqP ->|/eqP ->] //.
Qed.

Lemma monochromatic_on_sub (T : finType) (C : eqType)
    (col : T -> C) (S A : {set T}) :
  S \subset A -> monochromatic_on col A -> monochromatic_on col S.
Proof.
move/subsetP=> sub /monochromatic_onP h; apply/monochromatic_onP=> x y /sub xA /sub yA.
exact: h x y xA yA.
Qed.

Lemma monochromatic_on_ext (T : finType) (C : eqType)
    (c d : T -> C) (S : {set T}) :
  {in S, c =1 d} -> monochromatic_on c S = monochromatic_on d S.
Proof.
move=> cd; apply/monochromatic_onP/monochromatic_onP=> h x y xS yS.
- by rewrite -(cd x xS) -(cd y yS); exact: h x y xS yS.
- by rewrite (cd x xS) (cd y yS); exact: h x y xS yS.
Qed.

Lemma monochromatic_on_relabel (T : finType) (C D : eqType)
    (col : T -> C) (f : C -> D) (S : {set T}) :
  injective f -> monochromatic_on (f \o col) S = monochromatic_on col S.
Proof.
move=> inj; apply/monochromatic_onP/monochromatic_onP=> h x y xS yS.
- exact: inj (h x y xS yS).
- by rewrite /comp (h x y xS yS).
Qed.

(** A finite subset fails constancy exactly when two of its members differ.
    This view also requires no inhabited palette or nonempty-set assumption. *)
Lemma non_monochromatic_onP (T : finType) (C : eqType)
    (col : T -> C) (S : {set T}) :
  reflect (exists x y : T, [/\ x \in S, y \in S & col x != col y])
    (~~ monochromatic_on col S).
Proof.
rewrite monochromatic_onE negb_forall.
apply: (iffP existsP).
- move=> [x]; rewrite negb_imply => /andP[xS].
  rewrite negb_forall => /existsP[y]; rewrite negb_imply => /andP[yS xy].
  by exists x, y.
- move=> [x [y [xS yS xy]]]; exists x.
  rewrite negb_imply xS /= negb_forall; apply/existsP; exists y.
  by rewrite negb_imply yS /=.
Qed.
