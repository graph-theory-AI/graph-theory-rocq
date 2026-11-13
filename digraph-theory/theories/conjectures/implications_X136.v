(** * Digraph.conjectures.implications_X136 -- a Rocq-only EDGE between X79 and X136 (Erdos-Hajnal for tournaments).

    X79 (studies:std_alon_pach_solymosi_conjecture, [alon_pach_solymosi_tournament_erdos_hajnal_statement]) states
    the Erdos-Hajnal conjecture for tournaments with a size witness: every H-free tournament T has a transitive
    subtournament on at least a vertices, with |T| ^ en <= a ^ ed.  X136
    (studies:std_erd_s_hajnal_conjecture_for_tournaments,
    [erdos_hajnal_tournament_transitive_subtournament_statement]) states it with the vertex set itself: every H-free
    tournament G has a set S inducing a transitive subtournament, with |G| ^ a <= |S| ^ b.  X79's Notes say that
    they are the same conjecture.  The theorem below records the Rocq-only equivalence (no corpus relation).
    Forward: X79's exponents serve X136, with the same S, since a <= |S| gives a ^ ed <= |S| ^ ed ([leq_exp2r],
    0 < ed).  Backward: X136's exponents serve X79, with a = |S|.
    Axiom-free: only [Qed]-closed results, and no helper of its own. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented tournament.
From Digraph.conjectures Require Import heroes X79 X136.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Erdos-Hajnal for tournaments: the size-witness form (X79) <=> the vertex-set form (X136) *)

(*@EDGE from=alon_pach_solymosi_tournament_erdos_hajnal_statement to=erdos_hajnal_tournament_transitive_subtournament_statement kind=equiv status=verified proof=alon_pach_solymosi_tournament_erdos_hajnal_equiv_erdos_hajnal_tournament_transitive_subtournament note="Rocq-only edge (no corpus relation), routed after edge-x116 (Lancelot's (724), (725)): the two encodings of the Erdos-Hajnal conjecture for tournaments, studies:std_alon_pach_solymosi_conjecture (X79: a transitive subtournament on at least a vertices with |T|^en <= a^ed) and studies:std_erd_s_hajnal_conjecture_for_tournaments (X136: a vertex set S inducing a transitive subtournament with |G|^a <= |S|^b); X79's Notes say that they are one conjecture. Forward: the same exponents and the same S, since a <= |S| gives a^ed <= |S|^ed (leq_exp2r, 0 < ed). Backward: the same exponents, with a = |S|. Both rows are open." *)
Theorem alon_pach_solymosi_tournament_erdos_hajnal_equiv_erdos_hajnal_tournament_transitive_subtournament :
  alon_pach_solymosi_tournament_erdos_hajnal_statement <->
  erdos_hajnal_tournament_transitive_subtournament_statement.
Proof.
split=> [s79 H | s136 H].
- have [en [ed [en0 ed0 h]]] := s79 H.
  exists en, ed; split=> // G HG.
  have [a [[S [aS tS]] pb]] := h G HG.
  exists S; split=> //.
  apply: (leq_trans pb); by rewrite leq_exp2r.
- have [a [b [a0 b0 h]]] := s136 H.
  exists a, b; split=> // T HT.
  have [S [pS tS]] := h T HT.
  exists #|S|; split=> //; by exists S.
Qed.
