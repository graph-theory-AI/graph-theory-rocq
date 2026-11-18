(** * GTMisc.conjectures.X141 -- v2 row: the zombie number is subadditive on the Cartesian product (Fitzpatrick,
      Howell, Messinger and Pike, Question 10) *)

From GTBase Require Export base.
From GTMisc.foundations Require Import zombies.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X141 sanity *)

(** The hypotheses are inhabited: on K_1 box K_1 one zombie wins and zero do not. *)
Lemma x141_K1_box_K1_zombie_number : zombie_number (cartesian_product 'K_1 'K_1) 1.
Proof.
split.
  by apply: (@zombies_win_dominating (cartesian_product 'K_1 'K_1) (ord0, ord0)) => -[a b];
    rewrite (ord1 a) (ord1 b) eqxx.
by move=> j; rewrite ltnS leqn0 => /eqP ->; apply: not_zombies_win_0; rewrite card_prod card_ord.
Qed.

(** ** X141 statement ********************************************************* *)

(** Corpus row: studies:std_fitzpatrick_howell_messinger_pike_subadditivity
    Site: none
    Review: none
    English statement: (Fitzpatrick, Howell, Messinger and Pike, "A deterministic version of the game of zombies
      and survivors on graphs", Discrete Applied Mathematics 213 (2016) 1-12, Question 10; studies slice of the
      corpus, record arXiv:2008.03587, Question 1.1) Is z(G box H) <= z(G) + z(H) for all graphs G and H?  Here
      z(G) is the zombie number of the deterministic game of Zombies and Survivors (the minimum number of zombies
      that capture the survivor, the zombies choosing their vertices first and then, every round, each moving along
      a geodesic towards the survivor) and G box H the Cartesian product.
    Definitions: [connected [set: G]] - G is connected (coq-graph-theory); [zombie_number G k] - z(G) = k: k zombies
      win the game and fewer do not (graph-theory-misc foundations/zombies.v, where each rule is encoded and cited);
      [cartesian_product G H] - G box H, (a, b) adjacent to (a', b') when a = a' and b -- b' or b = b' and a -- a'
      (GTBase base.v).
    Notes: RE-ENCODED 2026-11-17 (coordination/PROGRAMME.md A1; meta/STATEMENT_IMPROVEMENTS.md).  The earlier body
      encoded the ZERO FORCING number, another parameter (a wrong object, the corpus topic label "zero-forcing"
      having been followed); the parameter of the source is the zombie number, now from foundations/zombies.v.  The
      formal name is kept (the precedent of X197's re-encoding); its "zero_forcing" is historical.  The conclusion
      names z(G box H) as the record's Theorem 1.3 does (main.tex l.208-210).  Both sources play on connected graphs
      (the record, l.182-184: "assume all graphs throughout the paper to be connected"; FHMP16 l.94), hence the
      hypotheses that G and H are connected and nonempty; G box H is then connected and nonempty.  Status: solved
      in its own record (Theorem 1.3, l.208-210, "we answer Question 1.1 in the affirmative", l.201; an independent
      proof is reported at l.438-441), recorded solved through the literature item lit39 (statement read, proof not
      verified).  Line numbers are those of the deposited 2008.03587v3 main.tex and of FHMP16's deposited
      paper.txt. *)
Definition zero_forcing_cartesian_product_subadditivity_statement : Prop :=
  forall G H : sgraph,
    connected [set: G] -> 0 < #|G| -> connected [set: H] -> 0 < #|H| ->
    forall zG zH zGH : nat,
      zombie_number G zG -> zombie_number H zH ->
      zombie_number (cartesian_product G H) zGH -> zGH <= zG + zH.

(** The statement's instance at G = H = K_1 has inhabited hypotheses: z(K_1) = 1 and z(K_1 box K_1) = 1 <= 1 + 1. *)
Lemma x141_K1_instance :
  [/\ connected [set: 'K_1] /\ 0 < #|'K_1|, zombie_number 'K_1 1,
      zombie_number (cartesian_product 'K_1 'K_1) 1 & 1 <= 1 + 1].
Proof.
split => //; last exact: x141_K1_box_K1_zombie_number; last exact: zombie_number_K1.
split; last by rewrite card_ord.
have -> : [set: 'K_1] = [set ord0] by apply/setP => x; rewrite !inE (ord1 x) eqxx.
exact: connected1.
Qed.
