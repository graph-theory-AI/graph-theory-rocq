(** * Extremal.conjectures.X143 -- v2 forcing graph row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X143 vocabulary ***********************************************)

Definition x143_contains_cycle (G : sgraph) : Prop :=
  exists c : seq G, ucycle (--) c /\ 2 < size c.

Definition x143_hom_count (A G : sgraph) : nat :=
  #|[set f : {ffun A -> G} |
      [forall x : A, [forall y : A, (x -- y) ==> (f x -- f y)]]]|.

Definition x143_edge_density_num (G : sgraph) : nat := 2 * fg_edge_count G.
Definition x143_edge_density_den (G : sgraph) : nat := #|G| * #|G|.

Definition x143_density_converges
    (num den : sgraph -> nat) (target_num target_den : nat)
    (Gs : nat -> sgraph) : Prop :=
  forall a b : nat, 0 < a -> a <= b ->
    eventually (fun n =>
      b * (target_den * num (Gs n)) <=
        (b * target_num + a * target_num) * den (Gs n)).

Definition x143_quasirandom_sequence (Gs : nat -> sgraph) : Prop :=
  forall H : sgraph,
    exists p q : nat, 0 < q /\
      x143_density_converges
        (fun G => x143_hom_count H G)
        (fun G => #|G| ^ #|H|)
        p q Gs.

Definition x143_forcing_graph (G : sgraph) : Prop :=
  forall (Gs : nat -> sgraph) (p q : nat),
    0 < q ->
    x143_density_converges x143_edge_density_num x143_edge_density_den p q Gs ->
    x143_density_converges
      (fun H => x143_hom_count G H)
      (fun H => #|H| ^ #|G|)
      (p ^ fg_edge_count G) (q ^ fg_edge_count G) Gs ->
    x143_quasirandom_sequence Gs.

(** Corpus row: studies:std_forcing_conjecture_skokan_thoma
    Site: none
    Review: none
    English statement: (Skokan and Thoma, "Forcing Conjecture (Skokan-Thoma)")
      A graph A is forcing if and only if it is bipartite and contains a cycle, where A is
      forcing when every graph sequence whose edge density converges to some rational p/q and
      whose homomorphism density of A converges to (p/q)^|E(A)| is quasirandom, i.e. the
      homomorphism density of every graph H converges along the sequence.
    Definitions: [x143_contains_cycle G] - some uniform cycle of length more than 2 exists (X143.v);
      [x143_hom_count A G] - the number of adjacency-preserving maps A -> G (X143.v);
      [x143_edge_density_num], [x143_edge_density_den] - 2|E(G)| and |V(G)|^2, the edge density
      as a fraction (X143.v); [x143_density_converges num den p q Gs] - an eventual relative
      bound of num(Gs n)/den(Gs n) against p/q (X143.v); [x143_quasirandom_sequence Gs] - every
      graph H has a convergent homomorphism density along Gs (X143.v); [x143_forcing_graph G]
      (X143.v); [fg_edge_count], [eventually] - GTBase; [bipartite] - GTBase.
    Notes: this row is recorded as BLOCKED. The 2026-07-17 faithfulness audit
      (meta/BLOCKED_RETARGETING_AUDIT.md) found that [x143_density_converges] states only the
      UPPER relative bound b * target_den * num <= (b + a) * target_num * den, whereas the
      source's t(F,G_n) -> p^{e(F)} is a TWO-SIDED convergence; there is no matching lower
      bound, so a sequence whose densities collapse to 0 satisfies the predicate. The hypothesis
      side of the iff is therefore too weak and the conclusion side too weak as well, which
      makes the encoded biconditional a proxy rather than the conjecture (ledger). The row also
      comes from the studies slice, which has no site or review page. *)
Definition skokan_thoma_forcing_graph_characterisation_statement : Prop :=
  forall A : sgraph,
    x143_forcing_graph A <-> bipartite A /\ x143_contains_cycle A.
