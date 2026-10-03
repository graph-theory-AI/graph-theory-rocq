(** * Incidence degree in a supplied finite family

    [incidence_degree F v] is the number of members of the finite family
    [F : {set {set T}}] that contain [v].  The carrier [T] is any finite type
    and [F] is supplied data: it need not be the edge set of a graph, nor
    uniform, nor nonempty, and its members may be empty or singletons (an
    empty member contains no vertex; a singleton member [[set v]] counts once
    at [v]).  It is the degree of [v] in the set system (hypergraph) [F]; at
    the edge set [E(G)] of a simple graph it is the graph degree [#|N(v)|]
    ([GTBase.common.incidence_degree_edges]).

    The members inside a vertex set [W] are written explicitly,
    [incidence_degree [set e in F | e \subset W] v]: that count is zero for
    [v] outside [W] ([incidence_degree_inside_out]) and the full degree for
    [W = setT] ([incidence_degree_insideT]).
    Registry: meta/library_primitives/incidence-degree.json (A10). *)
From mathcomp Require Import all_boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section IncidenceDegree.
Variable T : finType.
Implicit Types (F M : {set {set T}}) (e W : {set T}) (v : T).

Definition incidence_degree F v : nat := #|[set e in F | v \in e]|.

(** At most the size of the family. *)
Lemma incidence_degree_le F v : incidence_degree F v <= #|F|.
Proof. by apply: subset_leq_card; apply/subsetP => e; rewrite inE => /andP[]. Qed.

(** The empty family counts nothing. *)
Lemma incidence_degree_set0 v : incidence_degree set0 v = 0.
Proof. by apply/eqP; rewrite cards_eq0; apply/eqP/setP => e; rewrite !inE. Qed.

(** A one-member family counts its member exactly when it contains [v]: an
    empty member counts nothing, a singleton member [[set v]] counts once. *)
Lemma incidence_degree_set1 e v : incidence_degree [set e] v = (v \in e).
Proof.
rewrite /incidence_degree; case: (boolP (v \in e)) => ve.
  by rewrite (_ : [set f in [set e] | v \in f] = [set e]) ?cards1 //; apply/setP => f;
     rewrite !inE; case: (f =P e) => // ->.
apply/eqP; rewrite cards_eq0; apply/eqP/setP => f; rewrite !inE.
by case: (f =P e) => //= ->; apply/negbTE.
Qed.

(** The degree is positive exactly when some member contains [v]. *)
Lemma incidence_degree_gt0 F v : (0 < incidence_degree F v) = [exists e in F, v \in e].
Proof.
apply/card_gt0P/existsP => [[e]|[e /andP[eF ve]]]; last by exists e; rewrite inE eF ve.
by rewrite inE => /andP[eF ve]; exists e; rewrite eF ve.
Qed.

(** Monotone in the family. *)
Lemma incidence_degree_subset F M v :
  M \subset F -> incidence_degree M v <= incidence_degree F v.
Proof.
move=> MF; apply: subset_leq_card; apply/subsetP => e; rewrite !inE => /andP[eM ->].
by rewrite (subsetP MF).
Qed.

(** Removing a subfamily removes its incidences. *)
Lemma incidence_degree_setD F M v :
  M \subset F -> incidence_degree (F :\: M) v = incidence_degree F v - incidence_degree M v.
Proof.
move=> MF; rewrite /incidence_degree.
have -> : [set e in F :\: M | v \in e] = [set e in F | v \in e] :\: [set e in M | v \in e].
  by apply/setP => e; rewrite !inE; case: (e \in M); case: (e \in F); case: (v \in e).
rewrite cardsD; congr (_ - _).
suff -> : [set e in F | v \in e] :&: [set e in M | v \in e] = [set e in M | v \in e] by [].
apply/setIidPr/subsetP => e.
by rewrite !inE => /andP[eM ->]; rewrite (subsetP MF).
Qed.

(** The members inside [W] never contain a vertex outside [W]. *)
Lemma incidence_degree_inside_out F W v :
  v \notin W -> incidence_degree [set e in F | e \subset W] v = 0.
Proof.
move=> vW; apply/eqP; rewrite cards_eq0; apply/eqP/setP => e; rewrite !inE.
apply/negbTE; apply: contra vW => /andP[/andP[_ eW] ve].
exact: (subsetP eW).
Qed.

(** Inside the whole carrier, the restriction is the full degree. *)
Lemma incidence_degree_insideT F v :
  incidence_degree [set e in F | e \subset [set: T]] v = incidence_degree F v.
Proof. by apply: eq_card => e; rewrite !inE subsetT andbT. Qed.

End IncidenceDegree.
