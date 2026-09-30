(** * Topological.conjectures.X140 -- v2 random-embedding face-count row *)

From GTBase Require Export base.
From GraphTheory Require Import mgraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X140 vocabulary ***********************************************)

(** Maximum multiplicity of an unordered pair in a loopless multigraph. *)
Definition x140_edge_multiplicity (G : mgraph) (x y : G) : nat :=
  #|[set e : edge G | incident x e && incident y e]|.

Definition x140_max_edge_multiplicity_at_most
    (G : mgraph) (mu : nat) : Prop :=
  forall x y : G, x != y -> x140_edge_multiplicity x y <= mu.

Record x140_orientable_embedding (G : mgraph) := {
  x140_rotation_system : edge G -> bool;
  x140_faces : nat
}.

Definition x140_expected_random_embedding_faces_O
    (G : mgraph) (mu C : nat) : Prop :=
  exists (Emb : finType) (draw : Emb -> x140_orientable_embedding G),
    0 < #|{: Emb}| /\
    \sum_(e : Emb) x140_faces (draw e) <=
      C * (#|G| * (trunc_log 2 mu).+1) * #|{: Emb}|.

(** ** X140 statements *****************************************************)

(** Corpus row: studies:std_expected_number_of_faces_of_random_embeddings_co
    Site: none
    Review: none
    English statement: (Campion Loth, Halasz, Masarik, Mohar, Samal, "expected number of
      faces of random embeddings conjecture", studies slice)
      For every n-vertex multigraph G with maximum edge multiplicity mu >= 2, the expected
      number of faces of a uniformly random orientable embedding of G is O(n log mu).  The
      Rocq body reads: there are constants C and N such that for all n, mu and every loopless
      multigraph G with n >= N vertices, maximum edge multiplicity at most mu and mu >= 2,
      there is a non-empty finite index type Emb and a map [draw] from Emb to records of type
      [x140_orientable_embedding G] whose total face count is at most
      C * (n * (1 + floor(log2 mu))) * |Emb|.
    Definitions: [x140_edge_multiplicity G x y] - the number of edges incident to both x and
      y (this file); [x140_max_edge_multiplicity_at_most] - that count is at most mu for all
      distinct x, y (this file); [x140_orientable_embedding G] - a record with a field
      [x140_rotation_system : edge G -> bool] and a FREE natural [x140_faces] (this file);
      [x140_expected_random_embedding_faces_O] - the averaged face-count bound above (this
      file); [loopless] - no edge has equal endpoints (base/theories/base.v); [mgraph] -
      coq-graph-theory multigraphs.
    Notes: BLOCKED / VACUOUS - recorded by the 2026-07-17 faithfulness audit
      (meta/BLOCKED_RETARGETING_AUDIT.md).  All the content of the conjecture is
      prover-chosen: [x140_faces] is a FREE record field never computed from any rotation
      system, and the [x140_rotation_system] field is a meaningless [edge G -> bool], so one
      may take Emb to be a one-point type and [draw] to return a record with 0 faces, making
      the inequality trivially true.  The uniform random choice is replaced by an arbitrary
      finite index type with an averaged sum, so "uniformly random" and "expected" are not
      modelled either.  A faithful version would compute faces as the orbit count of
      [face_perm] on a genuine rotation system
      (topological-graph-theory/theories/foundations/embedding.v) over the multigraph, and
      would need a probability layer.  The log is rendered as [(trunc_log 2 mu).+1] and the
      asymptotics as explicit C and N. *)
Definition expected_faces_random_orientable_embeddings_statement : Prop :=
  exists C N : nat,
    forall (n mu : nat) (G : mgraph),
      N <= n ->
      #|G| = n ->
      loopless G ->
      2 <= mu ->
      x140_max_edge_multiplicity_at_most G mu ->
      x140_expected_random_embedding_faces_O G mu C.
