(** * Chromatic.foundations.strong_pair_palettes — strong edge colouring by a total symmetric pair palette

    Library migration D13 stage 1, family [strong-edge-colouring] (meta/library_primitives/strong-edge-colouring.json),
    class "total symmetric pair palette".  For a simple graph [G] and vertices [x y u v]:

    - [distinct_edge_pairs x y u v]: the unordered pairs [{x, y}] and [{u, v}] differ, i.e. neither [x = u, y = v] nor
      [x = v, y = u].
    - [near_edge_pairs x y u v]: one of the eight disjuncts [x = u], [x = v], [y = u], [y = v], [x -- u], [x -- v],
      [y -- u], [y -- v] holds: the pairs share a vertex or an endpoint of one is adjacent to an endpoint of the other.
    - [strong_pair_colourable G k]: some map [col : G -> G -> 'I_k] on ALL ordered vertex pairs is symmetric, and gives
      different colours to any two host edges [x -- y], [u -- v] whose pairs are distinct and near (the guards in this
      order).  Its values off the edges are unconstrained.

    No nonemptiness, edge or palette guard is added: the map is total, so a nonempty host needs a nonempty palette
    ([strong_pair_colourable0]: at [k = 0] it holds exactly on the empty host), an edgeless nonempty host needs
    [0 < k] and nothing more, and two near distinct edges need two colours.  The palette bound is monotone.  Chromatic
    U5's [diff_edge], [near_edge] and [strong_edge_colourable] are these three definitions by conversion.  X43's
    chromatic number of the square of a line graph and XE1's exact edge-set palette are separate classes of this family
    (later stages); no line-graph equivalence is asserted here.  No conjecture module is imported. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PairPalettes.
Variable G : sgraph.
Implicit Types (x y u v : G) (k : nat).

(** The unordered pairs [{x, y}] and [{u, v}] differ. *)
Definition distinct_edge_pairs x y u v : bool :=
  ~~ (((x == u) && (y == v)) || ((x == v) && (y == u))).

(** The pairs share a vertex, or an endpoint of one is adjacent to an endpoint of the other. *)
Definition near_edge_pairs x y u v : bool :=
  [|| x == u, x == v, y == u, y == v, x -- u, x -- v, y -- u | y -- v].

Lemma distinct_edge_pairs_refl x y : distinct_edge_pairs x y x y = false.
Proof. by rewrite /distinct_edge_pairs !eqxx. Qed.

Lemma distinct_edge_pairs_flip x y : distinct_edge_pairs x y y x = false.
Proof. by rewrite /distinct_edge_pairs !eqxx orbT. Qed.

Lemma distinct_edge_pairsC x y u v : distinct_edge_pairs x y u v = distinct_edge_pairs u v x y.
Proof.
rewrite /distinct_edge_pairs; congr (~~ _).
by rewrite (eq_sym x u) (eq_sym y v) (eq_sym x v) (eq_sym y u) [(v == x) && _]andbC.
Qed.

Lemma near_edge_pairs_refl x y : near_edge_pairs x y x y.
Proof. by rewrite /near_edge_pairs eqxx. Qed.

Lemma near_edge_pairsC x y u v : near_edge_pairs x y u v = near_edge_pairs u v x y.
Proof.
rewrite /near_edge_pairs (eq_sym x u) (eq_sym x v) (eq_sym y u) (eq_sym y v) (sg_sym x u) (sg_sym x v) (sg_sym y u)
  (sg_sym y v).
by case: (u == x); case: (v == x); case: (u == y); case: (v == y); case: (u -- x); case: (v -- x); case: (u -- y);
  case: (v -- y).
Qed.

(** Two host edges with distinct near pairs: a shared vertex is near. *)
Lemma near_edge_pairs_share x y v : near_edge_pairs x y y v.
Proof. by rewrite /near_edge_pairs eqxx !orbT. Qed.

End PairPalettes.

(** Some total symmetric map on ordered vertex pairs separates every two host edges with distinct near pairs. *)
Definition strong_pair_colourable (G : sgraph) (k : nat) : Prop :=
  exists col : G -> G -> 'I_k,
    (forall x y : G, col x y = col y x) /\
    (forall x y u v : G, x -- y -> u -- v ->
        distinct_edge_pairs x y u v -> near_edge_pairs x y u v -> col x y != col u v).

Section Palettes.
Variable G : sgraph.

(** A larger palette keeps the same colours. *)
Lemma strong_pair_colourable_mono k k' : k <= k' -> strong_pair_colourable G k -> strong_pair_colourable G k'.
Proof.
move=> kk' [col [sym sep]]; exists (fun x y => widen_ord kk' (col x y)); split=> [x y | x y u v xy uv d n].
  by rewrite sym.
apply: contra (sep x y u v xy uv d n) => /eqP E; apply/eqP/val_inj.
exact: (congr1 val E).
Qed.

(** Zero palette: only the empty host, since the map is total. *)
Lemma strong_pair_colourable0 : strong_pair_colourable G 0 <-> #|G| = 0.
Proof.
split=> [[col _] | G0].
  apply/eqP; rewrite eqn0Ngt; apply/negP => /card_gt0P [x _].
  by case: (col x x) => m; rewrite ltn0.
have nG (x : G) : False by move: (card0_eq G0 x); rewrite !inE.
by exists (fun x _ => False_rect _ (nG x)); split=> x; case: (nG x).
Qed.

(** The empty host has every palette. *)
Lemma strong_pair_colourable_card0 k : #|G| = 0 -> strong_pair_colourable G k.
Proof. by move=> G0; apply: strong_pair_colourable_mono (leq0n k) _; apply/strong_pair_colourable0. Qed.

(** A nonempty host needs a nonempty palette. *)
Lemma strong_pair_colourable_gt0 k (x : G) : strong_pair_colourable G k -> 0 < k.
Proof. by case=> col _; case: (col x x) => i ilt; apply: leq_ltn_trans (leq0n i) ilt. Qed.

(** An edgeless host needs nothing more than one colour. *)
Lemma strong_pair_colourable_edgeless k : 0 < k -> (forall x y : G, ~~ x -- y) -> strong_pair_colourable G k.
Proof.
move=> k0 nE; exists (fun _ _ => Ordinal k0); split=> // x y u v xy.
by move: (nE x y); rewrite xy.
Qed.

(** Two host edges with distinct near pairs need two colours. *)
Lemma strong_pair_colourable_two k (x y u v : G) :
  strong_pair_colourable G k -> x -- y -> u -- v -> distinct_edge_pairs x y u v -> near_edge_pairs x y u v -> 1 < k.
Proof.
case=> col [_ sep] xy uv d n; rewrite ltnNge; apply/negP => k1.
move/negP: (sep x y u v xy uv d n); apply; apply/eqP/val_inj.
have a0 : val (col x y) = 0 by apply/eqP; rewrite -leqn0 -ltnS (leq_trans (ltn_ord _) k1).
have b0 : val (col u v) = 0 by apply/eqP; rewrite -leqn0 -ltnS (leq_trans (ltn_ord _) k1).
by rewrite a0 b0.
Qed.

End Palettes.
