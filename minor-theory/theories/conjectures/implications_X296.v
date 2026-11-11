(** * Minor.conjectures.implications_X296 -- the equivalence edge between U7's and X296's weak-immersion rows.

    U7 encodes the Open Problem Garden row opg:coloring_and_immersion ([coloring_and_immersion_statement]:
    0 < t -> t <= chi(G) -> G immerses K_t).  Wave X296 encodes the studies row studies:std_lescure_meyniel_conjecture
    ([lescure_meyniel_weak_immersion_statement]: every graph G immerses K_(chi(G)); the Lescure-Meyniel conjecture,
    arXiv:2510.05893v1 Conjecture 1.1).  Both use U7's [immersion], the weak immersion.  The two rows state the same
    conjecture (CORPUS_FEEDBACK item 94).  grounding_X296.v proves the equivalence ([g296_equiv_U7]: an immersion of
    K_(chi(G)) restricts to K_t for t <= chi(G); conversely U7 at t = chi(G) when chi(G) > 0, and K_0 when
    chi(G) = 0); the theorem below records it as a registry edge, oriented from the older row.  Rocq-only edge:
    meta/corpus_relations.json has no relation between the two rows.  Axiom-free: only [Qed]-closed results. *)

From Minor.conjectures Require Import U7 X296 grounding_X296.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Coloring and immersion (U7, opg:coloring_and_immersion) <==> Lescure-Meyniel (X296) *)

(*@EDGE from=coloring_and_immersion_statement to=lescure_meyniel_weak_immersion_statement kind=equiv status=verified proved=true proof=coloring_and_immersion_equiv_lescure_meyniel_weak_immersion note="Rocq-only edge (no corpus relation), routed as a separate edge item after wave X296 (Lancelot's (624)): the two rows are the same conjecture (CORPUS_FEEDBACK item 94), and grounding_X296.v proves the equivalence (g296_equiv_U7). U7 => X296: U7 at t = chi(G) gives the K_(chi(G)) immersion when chi(G) > 0, and every graph immerses K_0. X296 => U7: an immersion of K_(chi(G)) restricts to one of K_t for t <= chi(G) (g296_immersion_K_le)." *)
Theorem coloring_and_immersion_equiv_lescure_meyniel_weak_immersion :
  coloring_and_immersion_statement <-> lescure_meyniel_weak_immersion_statement.
Proof. exact: (iff_sym g296_equiv_U7). Qed.
