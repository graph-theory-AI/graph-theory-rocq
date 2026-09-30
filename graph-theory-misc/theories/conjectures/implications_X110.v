(** * GTMisc.conjectures.implications_X110 -- wave X110 corpus-relation edges

    The two corpus rows [studies:std_chen_chv_tal_conjecture]
    (graph-theory-misc/theories/conjectures/X55.v) and
    [studies:std_chen_chv_tal_conjecture_146]
    (graph-theory-misc/theories/conjectures/X110.v) encode ONE mathematical statement: the
    Chen-Chvatal line conjecture for finite integer-valued metric spaces.  X110 reuses the X55
    vocabulary verbatim ([x55_metric], [x55_between], [x55_line], [x55_universal_line],
    [x55_lines]) and its body is byte-identical to the X55 body -- the `2 <= #|V|` guard the
    second row is named for is already present in the first.  The equivalence below is therefore
    a definitional one, recorded so that the duplication is machine-witnessed rather than only
    noted in prose (meta/STATEMENT_IMPROVEMENTS.md:675, where the pair is flagged as a candidate
    for an alias decision).

    The file is axiom-free: no Axiom/Parameter/Admitted, and no [Theorem ... Qed] asserting an
    unproven edge. *)

From mathcomp Require Import all_boot.
From GTMisc.conjectures Require Import X55 X110.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*@EDGE from=chen_chvatal_metric_lines_statement to=chen_chvatal_guarded_metric_lines_statement kind=equiv status=verified proof=chen_chvatal_metric_lines_equiv_chen_chvatal_guarded_metric_lines cite="meta/STATEMENT_IMPROVEMENTS.md:675 (identical bodies; alias candidate)" note="byte-identical definitions: both rows quantify over a finite type V with 2 <= #|V| and a natural-valued metric d (x55_metric) and conclude x55_universal_line d \/ #|V| <= #|x55_lines d|, over the same X55 vocabulary. The equivalence holds by conversion in both directions; it records the duplicate encoding, it is no evidence for the conjecture." *)
Theorem chen_chvatal_metric_lines_equiv_chen_chvatal_guarded_metric_lines :
  chen_chvatal_metric_lines_statement <-> chen_chvatal_guarded_metric_lines_statement.
Proof. by split=> H V d hV hd; apply: H. Qed.
