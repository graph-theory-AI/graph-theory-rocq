(** * Minor.conjectures.implications_X293 -- the equivalence edge between X214's and X293's Hadwiger rows.

    X214 encodes Hadwiger's conjecture as bm:bm-041 ([hadwiger_chromatic_clique_minor_statement]: chi(G) = k
    -> K_k is a minor of G).  Wave X293 encodes it as the studies row studies:std_hadwiger_s_conjecture
    ([hadwiger_minor_closed_class_statement], arXiv:1710.02727v1 Conjecture 1 over minor-closed classes).
    The two rows state the same conjecture.  grounding_X293.v proves the equivalence ([g293_equiv_X214]:
    forward through the class of K_(t+1)-minor-free graphs, backward through minor-closure); the theorem below
    records it as a registry edge.  Rocq-only edge: meta/corpus_relations.json has no relation between the two
    rows.  Axiom-free: only [Qed]-closed results. *)

From Minor.conjectures Require Import X214 X293 grounding_X293.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Hadwiger (X214, bm:bm-041) <==> Hadwiger over minor-closed classes (X293) *)

(*@EDGE from=hadwiger_chromatic_clique_minor_statement to=hadwiger_minor_closed_class_statement kind=equiv status=verified proved=true proof=hadwiger_chromatic_clique_minor_equiv_hadwiger_minor_closed_class note="Rocq-only edge (no corpus relation), left out of wave X293 for a separate edge item (Lancelot's (574)): the two rows are the same conjecture, and grounding_X293.v proves the equivalence (g293_equiv_X214). X214 => X293: K_(t+1) has chromatic number t+1, and in a minor-closed class without K_(t+1) a graph of chromatic number above t would have K_(t+1) as a minor (of its K_chi minor), hence in the class. X293 => X214: the graphs with no K_k minor form a minor-closed class without K_k, so their chromatic number is below k (k = 0 and 1 directly)." *)
Theorem hadwiger_chromatic_clique_minor_equiv_hadwiger_minor_closed_class :
  hadwiger_chromatic_clique_minor_statement <-> hadwiger_minor_closed_class_statement.
Proof. exact: (iff_sym g293_equiv_X214). Qed.
