(** Downstream use of complete and anticomplete vertex-set pairs without corpus imports: empty parts and the empty
    carrier, a shared singleton in [K_1], singleton parts in [K_2] and in an edgeless graph, swapping and restricting
    parts, completeness with a nonclique part, and the complement duality that needs disjoint parts. *)
From GTBase Require Import base set_pairs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Empty parts: all three contracts hold, on every graph, the empty carrier included. *)
Example empty_parts (G : sgraph) (A : {set G}) :
  [/\ complete_between set0 A, complete_between A set0, ~~ neighbor set0 A, anticomplete set0 A
    & anticomplete A set0].
Proof.
have nA : ~~ neighbor set0 A by apply/neighborNP => a b; rewrite inE.
have An : ~~ neighbor A set0 by apply/neighborNP => a b _; rewrite inE.
split=> //; first (by apply/complete_betweenP => a b; rewrite inE).
  by apply/complete_betweenP => a b _; rewrite inE.
- by rewrite /anticomplete nA andbT; apply/pred0P => x; rewrite /= inE.
- by rewrite /anticomplete An andbT; apply/pred0P => x; rewrite /= inE andbF.
Qed.

Example empty_carrier : complete_between [set: 'K_0] [set: 'K_0] /\ anticomplete [set: 'K_0] [set: 'K_0].
Proof.
by split; [apply/complete_betweenP => -[] | apply/anticompleteP; split; [apply/pred0P => -[] | move=> -[]]].
Qed.

(** A shared singleton in [K_1]: raw anticomplete with itself, but neither disjoint-anticomplete nor complete. *)
Example K1_shared_singleton :
  [/\ ~~ neighbor [set: 'K_1] [set: 'K_1], ~~ anticomplete [set: 'K_1] [set: 'K_1]
    & ~~ complete_between [set: 'K_1] [set: 'K_1]].
Proof.
split.
- by apply/neighborNP => a b _ _; rewrite /edge_rel /= negbK; apply/eqP/ord_inj; case: a b => [[|a] ?] [[|b] ?].
- apply/negP => /anticompleteP [/pred0P /(_ ord0)]; by rewrite /= inE.
- by apply/negP => /complete_between_disjoint /pred0P /(_ ord0); rewrite /= inE.
Qed.

(** Distinct singleton parts in [K_2] are complete, not anticomplete. *)
Example K2_singletons :
  complete_between [set (ord0 : 'K_2)] [set ord_max] /\ ~~ anticomplete [set (ord0 : 'K_2)] [set ord_max].
Proof.
split; first by apply/complete_betweenP => a b /set1P -> /set1P ->.
by apply/negP => /anticompleteP [_ h]; apply: (h ord0 ord_max); rewrite ?inE.
Qed.

(** In an edgeless graph the same parts are anticomplete, not complete. *)
Definition edgeless (n : nat) : sgraph :=
  @SGraph 'I_n (fun _ _ => false) (fun _ _ => erefl) (fun _ => erefl).

Example edgeless_singletons :
  anticomplete [set (ord0 : edgeless 2)] [set ord_max] /\ ~~ complete_between [set (ord0 : edgeless 2)] [set ord_max].
Proof.
split; first by apply/anticompleteP; split=> [|//]; rewrite disjoint_sym disjoints1 inE.
by apply/negP => /complete_betweenP /(_ ord0 ord_max); rewrite !inE eqxx => /(_ isT isT).
Qed.

(** Swapping and restricting parts. *)
Example swap_restrict (G : sgraph) (A B C : {set G}) :
  C \subset A -> anticomplete A B -> complete_between A B ->
  [/\ anticomplete B A, anticomplete C B, complete_between B A & complete_between C B].
Proof.
move=> CA ab cab; split; first by rewrite anticompleteC.
- exact: anticompleteW CA (subxx B) ab.
- by rewrite complete_betweenC.
- exact: complete_betweenW CA (subxx B) cab.
Qed.

(** Cross completeness without a clique: in [K_{1,2}] the centre is complete to both leaves, which are not adjacent. *)
Example star_complete_nonclique :
  complete_between [set x : 'K_1,2 | is_inl x] [set x : 'K_1,2 | ~~ is_inl x] /\
  ~~ cliqueb [set x : 'K_1,2 | ~~ is_inl x].
Proof.
split; first by apply/complete_betweenP => -[a|a] [b|b]; rewrite !inE.
apply/negP => /cliqueP /(_ (inr ord0) (inr ord_max)); rewrite !inE /=.
by move/(_ isT isT isT).
Qed.

(** Complement duality needs disjoint parts: the shared [K_1] singleton is raw anticomplete in [K_1] but not complete
    in its complement, while for disjoint parts the two coincide. *)
Example complement_duality (G : sgraph) (A B : {set G}) :
  [disjoint A & B] -> @complete_between (compl G) A B = ~~ neighbor A B.
Proof. exact: complete_between_compl. Qed.

Example complement_needs_disjointness :
  ~~ neighbor [set: 'K_1] [set: 'K_1] /\ ~~ @complete_between (compl 'K_1) [set: 'K_1] [set: 'K_1].
Proof.
split; first by case: K1_shared_singleton.
by apply/negP => /complete_between_disjoint /pred0P /(_ ord0); rewrite /= inE.
Qed.

Print Assumptions empty_parts.
Print Assumptions K1_shared_singleton.
Print Assumptions K2_singletons.
Print Assumptions edgeless_singletons.
Print Assumptions star_complete_nonclique.
Print Assumptions complement_needs_disjointness.
