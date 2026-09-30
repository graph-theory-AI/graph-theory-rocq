(** * Packing.conjectures.X155 -- v2 identifying-code VC dichotomy row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X155 vocabulary ***********************************************)

Definition x155_hereditary_class (C : sgraph -> Prop) : Prop :=
  forall (G : sgraph) (S : {set G}), C G -> C (induced S).

Definition x155_closed_neighbourhood (G : sgraph) (v : G) : {set G} :=
  [set v] :|: N(v).

Definition x155_identifying_code (G : sgraph) (Code : {set G}) : Prop :=
  (forall v : G, Code :&: x155_closed_neighbourhood v != set0) /\
  forall u v : G,
    u != v ->
    Code :&: x155_closed_neighbourhood u != Code :&: x155_closed_neighbourhood v.

Definition x155_identifying_code_number_at_least (G : sgraph) (m : nat) : Prop :=
  forall Code : {set G}, x155_identifying_code Code -> m <= #|Code|.

Definition x155_identifying_code_number_at_most (G : sgraph) (m : nat) : Prop :=
  exists Code : {set G}, x155_identifying_code Code /\ #|Code| <= m.

Definition x155_shatters (G : sgraph) (S : {set G}) : Prop :=
  forall A : {set G},
    A \subset S ->
    exists v : G, x155_closed_neighbourhood v :&: S = A.

Definition x155_vc_dimension_at_most (C : sgraph -> Prop) (d : nat) : Prop :=
  forall (G : sgraph) (S : {set G}), C G -> x155_shatters S -> #|S| <= d.

Definition x155_log_lower_bound (C : sgraph -> Prop) : Prop :=
  forall n : nat,
    exists G : sgraph,
      C G /\ n <= #|G| /\ x155_identifying_code_number_at_least G (trunc_log 2 n).+1.

Definition x155_polynomial_lower_bound (C : sgraph -> Prop) : Prop :=
  exists e : nat,
    0 < e /\
    forall n : nat,
      exists G : sgraph,
        C G /\ n <= #|G| /\ x155_identifying_code_number_at_least G (n ^ e).

Definition x155_constant_factor_approximation_with (K : nat) (C : sgraph -> Prop) : Prop :=
  exists opt : sgraph -> nat,
    (forall G : sgraph, C G -> x155_identifying_code_number_at_most G (opt G)) /\
    polytime_outputs_graph_on C
      (fun G out =>
        exists Code : {set G},
          x155_identifying_code Code /\
          #|Code| <= K * (opt G).+1 /\
          data_nat_value out = #|Code|).

Definition x155_log_APX_hard (C : sgraph -> Prop) : Prop :=
  forall K : nat, 0 < K -> ~ x155_constant_factor_approximation_with K C.

Definition x155_constant_factor_approximation (C : sgraph -> Prop) : Prop :=
  exists K : nat, 0 < K /\ x155_constant_factor_approximation_with K C.

(** ** X155 statements *****************************************************)

(** Corpus row: arxiv:1407.5833#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1407.5833__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1407.5833__00.json
    English statement: (Bousquet, Lagoutte, Li, Parreau, Thomasse 2017, "VC-Dimension
      Dichotomy for Identifying Codes (Approximation)")
      For every class C of simple graphs closed under induced subgraphs, either (a) the
      minimum identifying-code size in C has a logarithmic lower bound — for every n
      some graph of C has at least n vertices and no identifying code with at most
      trunc_log 2 n vertices — and Min Id Code is log-APX-hard in C, meaning no positive
      constant factor K admits an approximation; or (b) it has a polynomial lower bound
      — there is an exponent e >= 1 such that for every n some graph of C has at least n
      vertices and every identifying code of it has at least n^e vertices — and Min Id
      Code admits a constant-factor approximation in C.
    Definitions: [x155_hereditary_class C] — C is closed under [induced] subgraphs
      (this file); [x155_closed_neighbourhood v] — v together with its neighbours (this
      file); [x155_identifying_code Code] — Code meets every closed neighbourhood and
      separates distinct vertices by those intersections (this file);
      [x155_identifying_code_number_at_least/at_most], [x155_shatters],
      [x155_vc_dimension_at_most], [x155_log_lower_bound],
      [x155_polynomial_lower_bound], [x155_constant_factor_approximation_with],
      [x155_constant_factor_approximation], [x155_log_APX_hard] (all this file);
      [polytime_outputs_graph_on], [data_nat_value] — the complexity layer of GTBase
      base; [induced] — coq-graph-theory sgraph.v; [trunc_log] — MathComp.
    Notes: BLOCKED, and refutable as written. Faithfulness audit 2026-07-17
      (meta/BLOCKED_RETARGETING_AUDIT.md): the body has the shape
      "forall C hereditary, (A1 /\ A2) \/ (B1 /\ B2)" where A1 and B1 both start with
      "exists G, C G /\ ..."; instantiating C with the empty class (vacuously
      hereditary) makes A1 and B1 false, so the whole disjunction is false regardless of
      B2 — machine-refuted by the probe. The corpus text is an informal survey
      observation about hereditary classes that contain graphs, and the Rocq body
      carries no such non-emptiness guard. Approximation and hardness are also modelled
      through the abstract complexity layer rather than a genuine machine model, and the
      VC-dimension notion [x155_vc_dimension_at_most] that motivates the dichotomy does
      not occur in the body at all. *)
Definition identifying_code_vc_dimension_approximation_dichotomy_statement : Prop :=
  forall C : sgraph -> Prop,
    x155_hereditary_class C ->
    (x155_log_lower_bound C /\ x155_log_APX_hard C) \/
    (x155_polynomial_lower_bound C /\ x155_constant_factor_approximation C).
