(** Color symmetry reduces the universal 6^8-word statement to two
    canonical suffixes. These checks each enumerate 6^6 words. *)
From mathcomp Require Import all_boot.
From Digraph.applications Require Import color_avoiding_paths color_avoiding_word_symmetry.
Set Implicit Arguments.

Lemma benchmark_suffix00 : every_word 6 [:: c0; c0].
Proof. by vm_compute. Qed.

Lemma benchmark_suffix10 : every_word 6 [:: c1; c0].
Proof. by vm_compute. Qed.

Theorem all_eight_words_good (w : seq 'I_6) : size w = 8 -> good_word w.
Proof. exact (@two_suffixes_suffice benchmark_suffix00 benchmark_suffix10 w). Qed.
