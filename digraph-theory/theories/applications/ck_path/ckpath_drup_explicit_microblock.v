(** * Explicit-base interface for hinted-RUP microblocks

    This compatibility layer lets generated certificates store selected
    clauses themselves instead of global-base indices.  Keeping it separate
    leaves the legacy selected-index checker unchanged. *)

From Stdlib Require Import List Bool.
From Digraph Require Import ckpath_cnf.
From Digraph Require Export ckpath_drup_microblock.
Import ListNotations.

(** A one-pass executable check that [selected] occurs in [base] in the same
    order.  The scan is greedy: a matching head consumes both lists, while a
    mismatch consumes only the head of [base]. *)
Fixpoint cnf_subsequenceb (base selected : cnf) : bool :=
  match base, selected with
  | _, [] => true
  | [], _ :: _ => false
  | b :: base', s :: selected' =>
      if clause_eq_dec b s
      then cnf_subsequenceb base' selected'
      else cnf_subsequenceb base' selected
  end.

Lemma cnf_subsequenceb_member base selected :
  cnf_subsequenceb base selected = true ->
  forall c, In c selected -> In c base.
Proof.
revert selected.
induction base as [|b base IH]; intros [|s selected] Hsub c Hc;
  simpl in *.
- contradiction.
- discriminate.
- contradiction.
- destruct (clause_eq_dec b s) as [Heq | Hneq].
  + subst s. destruct Hc as [<- | Hc].
    * now left.
    * right. exact (IH selected Hsub c Hc).
  + right. exact (IH (s :: selected) Hsub c Hc).
Qed.

Theorem cnf_subsequenceb_sound rho base selected :
  cnf_subsequenceb base selected = true ->
  satisfies_cnf rho base ->
  satisfies_cnf rho selected.
Proof.
intros Hsub Hbase.
unfold satisfies_cnf, eval_cnf.
apply forallb_forall.
intros c Hc.
eapply eval_cnf_member; [exact Hbase |].
exact (cnf_subsequenceb_member base selected Hsub c Hc).
Qed.

Definition check_explicit_microblock
    (base selected imported : cnf)
    (records : list (list nat * list nat)) (output : cnf) : bool :=
  cnf_subsequenceb base selected &&
  check_microblock_export (selected ++ imported) records output.

Theorem check_explicit_microblock_sound
    base selected imported records output :
  check_explicit_microblock base selected imported records output = true ->
  forall rho,
    satisfies_cnf rho base ->
    satisfies_cnf rho imported ->
    satisfies_cnf rho output.
Proof.
unfold check_explicit_microblock.
intros Hcheck rho Hbase Himported.
apply andb_true_iff in Hcheck.
destruct Hcheck as [Hselected Hblock].
apply (check_microblock_export_sound
         (selected ++ imported) records output Hblock rho).
apply satisfies_cnf_app_intro.
- exact (cnf_subsequenceb_sound rho base selected Hselected Hbase).
- exact Himported.
Qed.
