(** Finite affirmative resolution of arXiv:2512.10438, Problem 5.1.
    The six-colored nontransitive tournament has 9 vertices and longest
    color-avoiding path 7 vertices. The exact transitive minimum is 8.
    The example is not strongly connected; the source does not require it.

    Source construction: Graph-Theory-LLM-Proofs/attacks/2512.10438__00/output.md
    Independent reference check: verification/2512.10438__00.md
    All finite certificates use vm_compute and their mathematical bridges
    are proved in color_avoiding_paths / color_avoiding_benchmark. *)
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented tournament dipath.
From Digraph.applications Require Import color_avoiding_paths color_avoiding_benchmark color_avoiding_word_certificate.
Set Implicit Arguments.

Theorem transitive_minimum_eight : transitive_minimum_is 8.
Proof. exact (benchmark_from_word_certificate all_eight_words_good). Qed.

Definition problem_5_1_q6_n9_statement :=
  exists (T : tournament) (chi : T -> T -> 'I_6),
    [/\ #|T| = 9, ~~ transb T, longest_avoiding_vertices chi 7 &
        transitive_minimum_is 8].

Theorem problem_5_1_q6_n9 : problem_5_1_q6_n9_statement.
Proof.
exists (Nine : tournament), nine_color; split.
- by rewrite card_ord.
- exact: nine_nontransitive.
- exact: nine_longest_avoiding_vertices.
- exact: transitive_minimum_eight.
Qed.

Print Assumptions problem_5_1_q6_n9.
