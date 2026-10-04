(** Public client of [Digraph.foundations.tournament_unavoidability]: it uses only
    the core digraph/tournament layer and the foundation, never a conjecture file.
    - the empty digraph [TT 0] is unavoidable for every order and has value 0;
    - one vertex [TT 1] has value 1, and then every larger order is unavoidable;
    - one directed arc [TT 2] has value 2, and 2 is its only value;
    - two isolated vertices also have value 2: non-arcs may land on arcs, so the
      containment is not induced;
    - a loop or a digon embeds in no tournament, so such digraphs have no value. *)
From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory digraph oriented tournament.
From Digraph.foundations Require Import tournament_unavoidability.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Every value is at least the order; a smaller order is never unavoidable. *)
Lemma below_order_not_unavoidable (D : diGraphType) (M : nat) :
  (M < #|D|)%N -> ~ tournament_unavoidable D M.
Proof. by move=> lt /tournament_unavoidable_card; rewrite leqNgt lt. Qed.

Lemma order_value (D : diGraphType) (N : nat) :
  #|D| = N -> tournament_unavoidable D N -> unavoidability_number D N.
Proof. by move=> <- un; split=> // M lt; exact: below_order_not_unavoidable. Qed.

(** ** The empty digraph *)

Lemma TT0_unavoidable (N : nat) : tournament_unavoidable (TT 0) N.
Proof. by apply: tournament_unavoidable_empty; rewrite card_TT. Qed.

Lemma TT0_value : unavoidability_number (TT 0) 0.
Proof. by apply: unavoidability_number_empty; rewrite card_TT. Qed.

(** ** One vertex *)

Lemma TT1_unavoidable : tournament_unavoidable (TT 1) 1.
Proof.
move=> T cardT.
have [t _] : {t : T | t \in T} by apply/sigW/card_gt0P; rewrite cardT.
exists (fun _ => t); split=> [a b _|a b].
  by rewrite [a]ord1 [b]ord1.
move=> ab; have : (a : TT 1) --> b := ab.
by rewrite arcTTE [a]ord1 [b]ord1 ltnn.
Qed.

Lemma TT1_value : unavoidability_number (TT 1) 1.
Proof. exact: order_value (card_TT 1) TT1_unavoidable. Qed.

Lemma TT1_unavoidable_large (N : nat) : (0 < N)%N -> tournament_unavoidable (TT 1) N.
Proof. by move=> pos; apply: tournament_unavoidable_monotone pos TT1_unavoidable. Qed.

(** ** One directed arc *)

Lemma TT2_unavoidable : tournament_unavoidable (TT 2) 2.
Proof.
move=> T cardT.
have /card_gt1P[x [y [_ _ xy]]] : (1 < #|T|)%N by rewrite cardT.
wlog a : x y xy / x --> y.
  move=> h; case/orP: (arc_or xy) => a; first exact: h a.
  by apply: (h y x) => //; rewrite eq_sym.
exists (fun i : 'I_2 => if val i == 0 then x else y); split=> [i j|i j].
  case: i j => -[|[|//]] ip [[|[|//]] jp] //= e; try exact: val_inj.
  - by move: xy; rewrite e eqxx.
  - by move: xy; rewrite e eqxx.
have : (i : TT 2) --> j -> (val i == 0) && (val j == 1).
  by rewrite arcTTE; case: i j => -[|[|//]] ? [[|[|//]] ?].
by move=> /= h /h /andP[/eqP-> /eqP->].
Qed.

Lemma TT2_value : unavoidability_number (TT 2) 2.
Proof. exact: order_value (card_TT 2) TT2_unavoidable. Qed.

Lemma TT2_value_unique (N : nat) : unavoidability_number (TT 2) N -> N = 2.
Proof. by move=> v; exact: unavoidability_number_unique v TT2_value. Qed.

Lemma TT2_not_1_unavoidable : ~ tournament_unavoidable (TT 2) 1.
Proof. by apply: below_order_not_unavoidable; rewrite card_TT. Qed.

(** ** Two isolated vertices: the containment is not induced *)

Definition coarc2 : Type := 'I_2.
HB.instance Definition _ := Finite.on coarc2.
HB.instance Definition _ := HasArc.Build coarc2 [rel _ _ : 'I_2 | false].

Lemma coarc2_unavoidable : tournament_unavoidable coarc2 2.
Proof.
move=> T cardT.
have /card_gt1P[x [y [_ _ xy]]] : (1 < #|T|)%N by rewrite cardT.
exists (fun i : 'I_2 => if val i == 0 then x else y); split=> [i j|//].
case: i j => -[|[|//]] ip [[|[|//]] jp] //= e; try exact: val_inj.
- by move: xy; rewrite e eqxx.
- by move: xy; rewrite e eqxx.
Qed.

Lemma coarc2_value : unavoidability_number coarc2 2.
Proof. exact: (@order_value coarc2 2 (card_ord 2) coarc2_unavoidable). Qed.

(** ** Loops and digons have no value *)

Definition loop1 : Type := unit.
HB.instance Definition _ := Finite.on loop1.
HB.instance Definition _ := HasArc.Build loop1 [rel _ _ : unit | true].

Lemma loop1_no_value (N : nat) : ~ unavoidability_number loop1 N.
Proof. by case=> un _; exact: (@not_tournament_unavoidable_loop loop1 tt N isT un). Qed.

Definition digon : Type := bool.
HB.instance Definition _ := Finite.on digon.
HB.instance Definition _ := HasArc.Build digon [rel u v : bool | u != v].

Lemma digon_no_value (N : nat) : ~ unavoidability_number digon N.
Proof. by case=> un _; exact: (@not_tournament_unavoidable_digon digon true false N isT isT un). Qed.
