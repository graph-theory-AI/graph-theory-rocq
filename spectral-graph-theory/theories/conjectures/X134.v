(** * Spectral.conjectures.X134 -- v2 squared-energy duplicate row *)

From Spectral.conjectures Require Import X6.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Corpus row: studies:std_elphick_farber_goldberg_wocjan_conjecture_square
    Site: none
    Review: none
    English statement: (Elphick, Farber, Goldberg and Wocjan, "Elphick-Farber-Goldberg-
      Wocjan conjecture (squared-energy bound)")
      For every connected simple graph G of order n, the minimum of the two squared
      energies E2+(G) and E2-(G) is at least n - 1, where E2+(G) (resp. E2-(G)) is the sum
      of the squares of the positive (resp. negative) adjacency eigenvalues of G counted
      with multiplicity.
    Definitions: [elphick_farber_goldberg_wocjan_splus_sminus_statement] — the X6 statement,
      which this Definition unfolds to (spectral-graph-theory/theories/conjectures/X6.v);
      through it, [x6_splus] and [x6_sminus] (X6.v) and [adjmx], [is_spectrum]
      (spectral-graph-theory/theories/foundations/spectral.v).
    Notes: this Definition is literally a synonym of the X6 statement: E2+ / E2- and
      s+ / s- denote the same quantities (the sums of the squares of the positive, resp.
      negative, adjacency eigenvalues), so the two corpus rows state one and the same
      conjecture under two names. Recorded in the improvement ledger as a duplicate pair of
      corpus rows. *)
Definition elphick_farber_goldberg_wocjan_squared_energy_statement : Prop :=
  elphick_farber_goldberg_wocjan_splus_sminus_statement.

