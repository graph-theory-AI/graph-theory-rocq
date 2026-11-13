(** * Cycle.conjectures.grounding_X306 -- grounding lemmas for wave X306

    [Qed]-closed, axiom-free certificates for the row of [Cycle.conjectures.X306] and its helper
    [x306_z3_connected]:
      - hyp_inhabited: the two-vertex multigraph with five parallel edges ([g306_banana5]) is 5-edge-connected,
        and the statement's conclusion is then claimed for it;
      - not_trivially_true: Z_3-connectivity fails on the one-edge graph, so the variant without the
        5-edge-connectivity hypothesis is false, and that variant would imply the row;
      - helper_sanity: the five-edge witness IS Z_3-connected (five nonzero elements of Z_3 reach every value),
        the one-edge graph is not, and every graph with at most one vertex is (the small cases of the Notes). *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import mgraph.
From GTBase Require Import base.
From Cycle.foundations Require Import connectivity.
From Cycle.conjectures Require Import X306.
From mathcomp Require Import all_algebra.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The witness: two vertices joined by five parallel edges *)

(** Vertices [false] and [true]; the five edges ['I_5] all go from [false] to [true]. *)
Definition g306_banana5 : mgraph := @Graph unit unit bool 'I_5 (fun b _ => b) (fun _ => tt) (fun _ => tt).

Lemma g306_banana5_ec : edge_connected g306_banana5 5.
Proof.
move=> E ltE x y.
have [i iE] : exists i : 'I_5, i \notin E.
  case: (pickP (fun i : 'I_5 => i \notin E)) => [i iE|allE]; first by exists i.
  move: ltE; rewrite (_ : E = setT) ?cardsT ?card_ord //.
  by apply/setP => j; rewrite inE; move: (allE j) => /negbFE.
case: x; case: y.
- by exists [::].
- by exists [:: i]; rewrite /= iE.
- by exists [:: i]; rewrite /= iE.
- by exists [::].
Qed.

(** ** Small graphs and the one-edge graph *)

(** A graph with at most one vertex is Z_3-connected: the boundary must be 0 and every edge is a loop. *)
Lemma g306_small_z3 (G : mgraph) : (#|G| <= 1)%N -> x306_z3_connected G.
Proof.
move=> G1 beta sum0; exists (fun _ => 1%R); split=> [e|v]; first exact: oner_neq0.
have allv : forall u : G, u = v by move=> u; apply: (card_le1_eqP G1).
rewrite (eq_bigl xpredT); first by move=> e; rewrite (allv (source e)) eqxx.
rewrite [X in (_ - X)%R](eq_bigl xpredT); first by move=> e; rewrite (allv (target e)) eqxx.
rewrite subrr.
move: sum0; rewrite (big_pred1 v) //.
by move=> u; rewrite /= (allv u) eqxx.
Qed.

(** The one-edge graph is not Z_3-connected: with the zero boundary its edge would carry 0. *)
Lemma g306_edge_not_z3 : ~ x306_z3_connected (edge_graph tt tt tt).
Proof.
move=> /(_ (fun _ => 0%R)); rewrite big1 // => /(_ erefl) [f [nz /(_ (inl tt))]] f0.
rewrite (big_pred1 None) in f0; first by case=> [[]|].
rewrite big_pred0 in f0; first by case=> [[]|].
by rewrite subr0 in f0; move: (nz None); rewrite f0 eqxx.
Qed.

(** ** hyp_inhabited *)
Definition g306_hyp_claim : Prop :=
  edge_connected g306_banana5 5 /\ (jlpt_z3_connectivity_statement -> x306_z3_connected g306_banana5).

Theorem g306_hyp_inhabited : g306_hyp_claim.
Proof. by split=> [|S]; [exact: g306_banana5_ec | exact: S _ g306_banana5_ec]. Qed.

(** ** not_trivially_true: without 5-edge-connectivity the conclusion fails *)
Definition g306_all_z3 : Prop := forall G : mgraph, x306_z3_connected G.

Definition g306_ntt_claim : Prop :=
  ~ g306_all_z3 /\ (g306_all_z3 -> jlpt_z3_connectivity_statement).

Theorem g306_not_trivially_true : g306_ntt_claim.
Proof. by split=> [/(_ (edge_graph tt tt tt))|V G _]; [exact: g306_edge_not_z3 | exact: V]. Qed.

(** ** helper_sanity *)

(** Five nonzero elements of Z_3 reach every value. *)
Lemma g306_five_nonzero (b : 'Z_3) :
  exists f : 'I_5 -> 'Z_3, (forall i, f i != 0%R) /\ (\sum_(i < 5) f i)%R = b.
Proof.
case: b => [[|[|[|//]]] /= ?].
- exists (fun i : 'I_5 => if i == ord0 then (1 + 1)%R else 1%R); split; first by move=> i; case: (i == ord0).
  by rewrite !big_ord_recl big_ord0; apply/val_inj.
- exists (fun _ : 'I_5 => (1 + 1)%R); split => //.
  by rewrite !big_ord_recl big_ord0; apply/val_inj.
- exists (fun _ : 'I_5 => 1%R); split => //.
  by rewrite !big_ord_recl big_ord0; apply/val_inj.
Qed.

(** The five-edge witness is Z_3-connected: put the values on the five edges, all from [false] to [true]. *)
Lemma g306_banana5_z3 : x306_z3_connected g306_banana5.
Proof.
move=> beta sum0; have [f [nz sf]] := g306_five_nonzero (beta false).
exists f; split => // v.
have src : forall e : edge g306_banana5, source e = false by [].
have tgt : forall e : edge g306_banana5, target e = true by [].
have bt : beta true = (- beta false)%R.
  by move: sum0; rewrite big_bool /= => /eqP; rewrite addr_eq0 => /eqP.
case: v.
- rewrite big_pred0; first by move=> e; rewrite src.
  rewrite (eq_bigl xpredT); first by move=> e; rewrite tgt.
  by rewrite sub0r bt -sf.
- rewrite [X in (_ - X)%R]big_pred0; first by move=> e; rewrite tgt.
  rewrite (eq_bigl xpredT); first by move=> e; rewrite src.
  by rewrite subr0 -sf.
Qed.

Definition g306_helper_claim : Prop :=
  [/\ x306_z3_connected g306_banana5, ~ x306_z3_connected (edge_graph tt tt tt)
    & forall G : mgraph, (#|G| <= 1)%N -> x306_z3_connected G].

Theorem g306_helper_sanity : g306_helper_claim.
Proof. by split; [exact: g306_banana5_z3 | exact: g306_edge_not_z3 | exact: g306_small_z3]. Qed.
