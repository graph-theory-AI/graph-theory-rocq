(** * GTMisc.conjectures.X141 -- v2 zero-forcing Cartesian product row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X141 vocabulary ***********************************************)

(** Zero-forcing closure: from a blue set [S], a blue vertex [u] may force the
    unique uncoloured neighbour [v] when [N(u) \ S] is exactly [{v}]. *)
Inductive x141_zf_closure (G : sgraph) : {set G} -> {set G} -> Prop :=
| x141_zf_done (S : {set G}) : @x141_zf_closure G S S
| x141_zf_step (S T : {set G}) (u v : G) :
    u \in S ->
    v \notin S ->
    N(u) :\: S = [set v] ->
    @x141_zf_closure G (S :|: [set v]) T ->
    @x141_zf_closure G S T.

Definition x141_zero_forcing_set (G : sgraph) (S : {set G}) : Prop :=
  @x141_zf_closure G S [set: G].

Definition x141_zero_forcing_number_le (G : sgraph) (k : nat) : Prop :=
  exists S : {set G}, #|S| <= k /\ x141_zero_forcing_set S.

Definition x141_zero_forcing_number (G : sgraph) (z : nat) : Prop :=
  x141_zero_forcing_number_le G z /\
  forall k : nat, x141_zero_forcing_number_le G k -> z <= k.

(** ** X141 statements *****************************************************)

(** Corpus row: studies:std_fitzpatrick_howell_messinger_pike_subadditivity
    Site: none
    Review: none
    English statement: (Fitzpatrick, Howell, Messinger and Pike, subadditivity conjecture for
      the Cartesian product)
      For all finite simple graphs G and H, if zG is the zero forcing number of G and zH that
      of H, then the Cartesian product of G and H has a zero forcing set of size at most
      zG + zH.
    Definitions: [x141_zf_closure S T] - T is reachable from the blue set S by zero-forcing
      steps, a step letting a blue vertex u colour the unique uncoloured vertex of its
      neighbourhood (this file); [x141_zero_forcing_set S] - the closure of S is the whole
      vertex set (this file); [x141_zero_forcing_number_le G k] - some zero forcing set has size
      at most k (this file); [x141_zero_forcing_number G z] - z is the least such size (this
      file); [cartesian_product] - the Cartesian graph product (GTBase).
    Notes: KNOWN UNFAITHFUL, row leg is blocked (independent adversarial audit wf_bdaea8ab,
      2026-07-18).  WRONG OBJECT: in the source (arXiv:2008.03587, "A note on deterministic
      zombies", and Fitzpatrick-Howell-Messinger-Pike 2016) the parameter z is the
      deterministic ZOMBIE number, a pursuit-game parameter in which the pursuers must move
      closer to the survivor; this file encodes z as the ZERO FORCING number, a propagation
      parameter.  The two are different graph parameters, so the Rocq body states a different
      conjecture than the corpus row, which the "zero-forcing" topic label of the corpus
      propagated into the formalization.  Recorded in meta/STATEMENT_IMPROVEMENTS.md.
      Secondary modelling note: the conclusion is the inequality form
      "the product has a zero forcing set of size at most zG + zH" rather than
      "z(G box H) <= z(G) + z(H)" with the product's number named, which is equivalent. *)
Definition zero_forcing_cartesian_product_subadditivity_statement : Prop :=
  forall (G H : sgraph) (zG zH : nat),
    x141_zero_forcing_number G zG ->
    x141_zero_forcing_number H zH ->
    x141_zero_forcing_number_le (cartesian_product G H) (zG + zH).
