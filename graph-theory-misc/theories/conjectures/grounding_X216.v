(** * GTMisc.conjectures.grounding_X216 -- grounding lemmas for wave X216

    Both X216 rows are BLOCKED placeholders (see the Notes of
    [GTMisc.conjectures.X216]); these Qed-closed lemmas validate the GRAPH-THEORETIC
    vocabulary they are built from -- the part that is not in dispute -- and record
    where the guards bite:

    - NON-VACUITY: the instance class of the second-Hamilton-cycle row is inhabited
      (['K_4] is cubic and has a Hamilton cycle), and the odd-path family of the
      co-NP row is inhabited (['K_2] has one internally disjoint odd (X,Y)-path).
    - THE GUARDS HAVE TEETH: ['K_3] is Hamiltonian but not cubic, so the class is a
      real restriction; an output that is not a list never satisfies the output
      specification; the empty sequence and an even-length walk are not odd
      (X,Y)-paths; ['K_1] has no odd (X,Y)-path at all; and with k = 0 the path
      predicate degenerates to True, so the parameter k is load-bearing. *)

From GTBase Require Import base.
From GTMisc.conjectures Require Import X216.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Degrees in complete graphs *)

Lemma neigh_Kn (n : nat) (x : 'K_n.+1) : N(x) = [set~ x].
Proof. by apply/setP => y; rewrite !inE /edge_rel /= eq_sym. Qed.

Lemma deg_Kn_eq (n : nat) (x : 'K_n.+1) : #|N(x)| = n.
Proof. by rewrite neigh_Kn cardsC1 card_ord. Qed.

(** ** The second-Hamilton-cycle instance class is inhabited, and restrictive *)

Definition x216_K4_cycle : seq 'K_4 :=
  [:: (@Ordinal 4 0 isT : 'K_4); (@Ordinal 4 1 isT : 'K_4);
      (@Ordinal 4 2 isT : 'K_4); (@Ordinal 4 3 isT : 'K_4)].

Lemma hamiltonian_cycle_K4 : hamiltonian_cycle 'K_4 x216_K4_cycle.
Proof. by rewrite /hamiltonian_cycle /ucycleb /= card_ord. Qed.

Lemma cubic_K4 : regular 'K_4 3.
Proof. by move=> v; exact: (@deg_Kn_eq 3). Qed.

Lemma x216_class_inhabited :
  x216_cubic_hamiltonian_instance (existT (fun G : sgraph => seq G) 'K_4 x216_K4_cycle).
Proof. by split; [exact: cubic_K4|exact: hamiltonian_cycle_K4]. Qed.

(** ['K_3] is Hamiltonian but NOT cubic: the class guard is a real restriction. *)
Lemma not_cubic_K3 : ~ regular 'K_3 3.
Proof. by move=> /(_ (@Ordinal 3 0 isT : 'K_3)); rewrite (@deg_Kn_eq 2). Qed.

(** ** The output specification has teeth *)

(** A numeral is never a correct output: the specification really asks for a cycle. *)
Lemma x216_output_not_nat (x : x216_cycle_instance) (n : nat) :
  ~ x216_second_hamilton_output x (Dnat n).
Proof. by case=> c' [_ _]; rewrite /x216_enc_seq; case: c'. Qed.

(** ** The odd-path vocabulary *)

(** The empty sequence is never an (X,Y)-path. *)
Lemma x216_odd_xy_path_nil (G : sgraph) (X Y : {set G}) :
  x216_odd_xy_path X Y [::] = false.
Proof. by []. Qed.

(** One internally disjoint odd (X,Y)-path in ['K_2]: the vocabulary is inhabited. *)
Lemma x216_odd_paths_K2 :
  x216_odd_disjoint_paths [set (@Ordinal 2 0 isT : 'K_2)]
                          [set (@Ordinal 2 1 isT : 'K_2)] 1.
Proof.
exists (fun _ => [:: (@Ordinal 2 0 isT : 'K_2); (@Ordinal 2 1 isT : 'K_2)]).
split=> [i|i j Hij].
- by rewrite /x216_odd_xy_path /= !inE !eqxx.
- by move: Hij; rewrite (ord1 i) (ord1 j) eqxx.
Qed.

(** An even-length walk is NOT an odd (X,Y)-path, even when everything else fits. *)
Lemma x216_even_walk_rejected :
  x216_odd_xy_path [set (@Ordinal 3 0 isT : 'K_3)] [set (@Ordinal 3 2 isT : 'K_3)]
    [:: (@Ordinal 3 0 isT : 'K_3); (@Ordinal 3 1 isT : 'K_3);
        (@Ordinal 3 2 isT : 'K_3)] = false.
Proof. by rewrite /x216_odd_xy_path /= !andbF. Qed.

(** ['K_1] carries no odd (X,Y)-path: an odd number of edges needs two distinct
    vertices. *)
Lemma x216_no_odd_path_K1 (X Y : {set 'K_1}) (p : seq 'K_1) :
  x216_odd_xy_path X Y p = false.
Proof.
case: p => [|x [|y q]] //=; first by rewrite !andbF.
by rewrite (ord1 x) (ord1 y) /=.
Qed.

Lemma x216_no_odd_paths_K1 (X Y : {set 'K_1}) :
  ~ x216_odd_disjoint_paths X Y 1.
Proof.
by case=> f [Hf _]; move: (Hf ord0); rewrite x216_no_odd_path_K1.
Qed.

(** With k = 0 the predicate degenerates to True: the parameter k is load-bearing. *)
Lemma x216_odd_paths_0 (G : sgraph) (X Y : {set G}) : x216_odd_disjoint_paths X Y 0.
Proof.
by exists (fun i : 'I_0 => [::]); split=> i; move: (ltn_ord i); rewrite ltn0.
Qed.

Print Assumptions x216_class_inhabited.
Print Assumptions not_cubic_K3.
Print Assumptions x216_output_not_nat.
Print Assumptions x216_odd_paths_K2.
Print Assumptions x216_even_walk_rejected.
Print Assumptions x216_no_odd_paths_K1.
Print Assumptions x216_odd_paths_0.
