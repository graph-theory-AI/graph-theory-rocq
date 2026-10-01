(** * Digraph.ckpath_kernel_cases -- exact CK kernel shapes for d = 4,5,6,7

    This module is the interface between the uniform Cheng--Keevash kernel
    and the three small directed-path endgames.  Besides retaining the full
    path/cycle/closure package, each theorem exposes a vertex of the CK set
    whose internal out-degree satisfies the oriented averaging bound. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Stdlib Require Import Lia.
From Digraph Require Import prelude digraph oriented dipath strong lemma7
  ckpath_shapes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma ckpath_sub2E n : Nat.sub n 2 = n.-2.
Proof. by lia. Qed.

Lemma ckpath_doubleE n : Nat.add n n = n.*2.
Proof. change (n + n = n.*2); exact: addnn. Qed.

(** The complete strengthened kernel package, with the exact A/B partition
    and the two-vertex improvement on the path prefix. *)
Definition ckpath_kernel_facts (H : orientedDigraph) (d : nat)
    (x : H) (p : seq H) (a : nat) : Prop :=
  [/\ #|ckA x p a| + #|ckB x p a| = d,
      #|ckA x p a| <= a.-2
    & [/\ [/\ dipath x p, size p = ell H, 1 <= a & a + d <= ell H],
          [/\ dicycle (ckC x p a), size (ckC x p a) = (ell H).+1 - a
            & #|ckCset x p a| = (ell H).+1 - a],
          [/\ #|ckS x p a| = #|ckB x p a|, #|ckB x p a| <= d,
              d <= #|ckB x p a| + a.-1 & last x p \in ckS x p a],
          (forall b z, b \in ckS x p a -> b --> z -> z \in ckC x p a)
        & (forall v, v \in ckS x p a ->
             [/\ #|ckS x p a| + d - outdeg_in (ckS x p a) v
                    <= #|ckCset x p a|
               & 2 * d - ell H <= outdeg_in (ckS x p a) v]) ]].

(** The chosen averaging witness.  The doubled inequality avoids division
    in every subsequent finite shape calculation. *)
Definition ckpath_average_witness (H : orientedDigraph) (x : H)
    (p : seq H) (a : nat) (u : H) (r : nat) : Prop :=
  [/\ u \in ckS x p a, outdeg_in (ckS x p a) u = r
    & r.*2 <= #|ckS x p a| - 1].

(** Uniform extraction of the strengthened kernel and its averaging
    witness.  The last four inequalities are precisely the nontrivial
    arithmetic inputs shared by the three shape tables. *)
Lemma ckpath_kernel_average (H : orientedDigraph) (d : nat) :
  0 < d -> (forall v : H, outdeg v = d) -> 0 < #|H| -> strongb H ->
  ell H < 2 * d ->
  exists (x : H) (p : seq H) (a : nat) (u : H) (r : nat),
    [/\ ckpath_kernel_facts d x p a,
        ckpath_average_witness x p a u r,
        #|ckS x p a| <= d,
        d <= #|ckS x p a| + a.-2
      & [/\ 2 * d - ell H <= r
         & #|ckS x p a| + d - r <= (ell H).+1 - a] ].
Proof.
move=> hd hreg hn hstr hell.
have [x [p [a [hAB hA2 hrest]]]] :=
  kernel_full_AB hreg hd hn hstr hell.
have hfacts : ckpath_kernel_facts d x p a.
  by split.
have hrest0 := hrest.
case: hrest0 => hpath hcycle hB hclose hcount.
case: hB => hScard hBle hBge hyS.
case: hcycle => hdc hsizeC hcardC.
have hSn0 : ckS x p a != set0.
  by apply/set0Pn; exists (last x p).
have [u hu hule] := oriented_avg_bound hSn0.
pose r := outdeg_in (ckS x p a) u.
have hrr : r.*2 <= #|ckS x p a| - 1.
  apply: leq_trans (_ : ((#|ckS x p a| - 1)./2).*2 <= _).
    by rewrite leq_double.
  by rewrite -[X in _ <= X]odd_double_half leq_addl.
have hwit : ckpath_average_witness x p a u r.
  by split.
have hSle : #|ckS x p a| <= d by rewrite hScard.
have hdSa : d <= #|ckS x p a| + a.-2.
  rewrite -hAB hScard addnC leq_add2l.
  exact: hA2.
have [hcountA hcountB] := hcount u hu.
have hrlo : 2 * d - ell H <= r by exact: hcountB.
have htop : #|ckS x p a| + d - r <= (ell H).+1 - a.
  by rewrite -hcardC.
exists x, p, a, u, r; split=> //.
Qed.

(** Exact kernel shape at out-degree four. *)
Theorem ckpath_kernel_cases4 (H : orientedDigraph) :
  (forall v : H, outdeg v = 4) -> 0 < #|H| -> strongb H -> ell H < 8 ->
  exists (x : H) (p : seq H) (a : nat) (u : H) (r : nat),
    [/\ ckpath_kernel_facts 4 x p a,
        ckpath_average_witness x p a u r
      & [/\ ell H = 7, #|ckS x p a| = 4, r = 1 & a = 1] ].
Proof.
move=> hreg hn hstr hell.
have [x [p [a [u [r [hfacts hwit hSle hdSa [hrlo htop]]]]]]]
  := ckpath_kernel_average (H := H) (d := 4) isT hreg hn hstr hell.
have hfacts0 := hfacts.
case: hfacts0 => hAB hA2 [hpath hcycle hB hclose hcount].
case: hpath => hp hsize ha1 hale.
have hwit0 := hwit.
case: hwit0 => hu hrE hrr.
have hmin : forall v : H, 4 <= outdeg v by move=> v; rewrite hreg.
have hLlow : 7 <= ell H.
  have h := ck_theorem4_oriented hn hmin.
  by move: h; rewrite /=.
have hshape : [/\ ell H = 7, #|ckS x p a| = 4, r = 1 & a = 1].
  apply: ckpath_shape4.
  - exact: (elimT leP hLlow).
  - exact: (elimT ltP hell).
  - exact: (elimT leP ha1).
  - exact: (elimT leP hale).
  - exact: (elimT leP hSle).
  - apply: (elimT leP).
    by rewrite ckpath_sub2E.
  - exact: (elimT leP hrlo).
  - apply: (elimT leP).
    by rewrite ckpath_doubleE.
  - exact: (elimT leP htop).
by exists x, p, a, u, r; split.
Qed.

(** Exact kernel shapes at out-degree five. *)
Theorem ckpath_kernel_cases5 (H : orientedDigraph) :
  (forall v : H, outdeg v = 5) -> 0 < #|H| -> strongb H -> ell H < 10 ->
  exists (x : H) (p : seq H) (a : nat) (u : H) (r : nat),
    [/\ ckpath_kernel_facts 5 x p a,
        ckpath_average_witness x p a u r
      & [\/
          [/\ ell H = 8, #|ckS x p a| = 5, r = 2 & a = 1],
          [/\ ell H = 9, #|ckS x p a| = 5, r = 1 & a = 1],
          [/\ ell H = 9, #|ckS x p a| = 5, r = 2 & a = 1]
        | [/\ ell H = 9, #|ckS x p a| = 5, r = 2 & a = 2]] ].
Proof.
move=> hreg hn hstr hell.
have [x [p [a [u [r [hfacts hwit hSle hdSa [hrlo htop]]]]]]]
  := ckpath_kernel_average (H := H) (d := 5) isT hreg hn hstr hell.
have hfacts0 := hfacts.
case: hfacts0 => hAB hA2 [hpath hcycle hB hclose hcount].
case: hpath => hp hsize ha1 hale.
have hwit0 := hwit.
case: hwit0 => hu hrE hrr.
have hmin : forall v : H, 5 <= outdeg v by move=> v; rewrite hreg.
have hLlow : 8 <= ell H.
  have h := ck_theorem4_oriented hn hmin.
  by move: h; rewrite /=.
have hshape :
    [\/ 
      [/\ ell H = 8, #|ckS x p a| = 5, r = 2 & a = 1],
      [/\ ell H = 9, #|ckS x p a| = 5, r = 1 & a = 1],
      [/\ ell H = 9, #|ckS x p a| = 5, r = 2 & a = 1]
    | [/\ ell H = 9, #|ckS x p a| = 5, r = 2 & a = 2]].
  apply: ckpath_shape5.
  - exact: (elimT leP hLlow).
  - exact: (elimT ltP hell).
  - exact: (elimT leP ha1).
  - exact: (elimT leP hale).
  - exact: (elimT leP hSle).
  - apply: (elimT leP).
    by rewrite ckpath_sub2E.
  - exact: (elimT leP hrlo).
  - apply: (elimT leP).
    by rewrite ckpath_doubleE.
  - exact: (elimT leP htop).
by exists x, p, a, u, r; split.
Qed.

(** Exact kernel shapes at out-degree six. *)
Theorem ckpath_kernel_cases6 (H : orientedDigraph) :
  (forall v : H, outdeg v = 6) -> 0 < #|H| -> strongb H -> ell H < 12 ->
  exists (x : H) (p : seq H) (a : nat) (u : H) (r : nat),
    [/\ ckpath_kernel_facts 6 x p a,
        ckpath_average_witness x p a u r
      & [\/
          [/\ ell H = 10, #|ckS x p a| = 6, r = 2 & a = 1],
          [/\ ell H = 11, #|ckS x p a| = 5, r = 2 & a = 3],
          [/\ ell H = 11, #|ckS x p a| = 6, r = 1 & a = 1]
        | ([/\ ell H = 11, #|ckS x p a| = 6, r = 2 & a = 1] \/
           [/\ ell H = 11, #|ckS x p a| = 6, r = 2 & a = 2]) ] ].
Proof.
move=> hreg hn hstr hell.
have [x [p [a [u [r [hfacts hwit hSle hdSa [hrlo htop]]]]]]]
  := ckpath_kernel_average (H := H) (d := 6) isT hreg hn hstr hell.
have hfacts0 := hfacts.
case: hfacts0 => hAB hA2 [hpath hcycle hB hclose hcount].
case: hpath => hp hsize ha1 hale.
have hwit0 := hwit.
case: hwit0 => hu hrE hrr.
have hmin : forall v : H, 6 <= outdeg v by move=> v; rewrite hreg.
have hLlow : 10 <= ell H.
  have h := ck_theorem4_oriented hn hmin.
  by move: h; rewrite /=.
have hshape :
    [\/ 
      [/\ ell H = 10, #|ckS x p a| = 6, r = 2 & a = 1],
      [/\ ell H = 11, #|ckS x p a| = 5, r = 2 & a = 3],
      [/\ ell H = 11, #|ckS x p a| = 6, r = 1 & a = 1]
    | ([/\ ell H = 11, #|ckS x p a| = 6, r = 2 & a = 1] \/
       [/\ ell H = 11, #|ckS x p a| = 6, r = 2 & a = 2])].
  apply: ckpath_shape6.
  - exact: (elimT leP hLlow).
  - exact: (elimT ltP hell).
  - exact: (elimT leP ha1).
  - exact: (elimT leP hale).
  - exact: (elimT leP hSle).
  - apply: (elimT leP).
    by rewrite ckpath_sub2E.
  - exact: (elimT leP hrlo).
  - apply: (elimT leP).
    by rewrite ckpath_doubleE.
  - exact: (elimT leP htop).
by exists x, p, a, u, r; split.
Qed.

(** Exact kernel shapes at out-degree seven.  The explicit lower bound on
    [ell H] avoids a dependency cycle: the assembly theorem obtains it from
    [ck_conj1_delta6] before invoking this arithmetic interface. *)
Theorem ckpath_kernel_cases7 (H : orientedDigraph) :
  (forall v : H, outdeg v = 7) -> 0 < #|H| -> strongb H -> ell H < 14 ->
  12 <= ell H ->
  exists (x : H) (p : seq H) (a : nat) (u : H) (r : nat),
    [/\ ckpath_kernel_facts 7 x p a,
        ckpath_average_witness x p a u r
      & ckpath_shape7_cases (ell H) #|ckS x p a| r a ].
Proof.
move=> hreg hn hstr hell hLlow.
have [x [p [a [u [r [hfacts hwit hSle hdSa [hrlo htop]]]]]]]
  := ckpath_kernel_average (H := H) (d := 7) isT hreg hn hstr hell.
have hfacts0 := hfacts.
case: hfacts0 => hAB hA2 [hpath hcycle hB hclose hcount].
case: hpath => hp hsize ha1 hale.
have hwit0 := hwit.
case: hwit0 => hu hrE hrr.
have hshape : ckpath_shape7_cases (ell H) #|ckS x p a| r a.
  apply: ckpath_shape7.
  - exact: (elimT leP hLlow).
  - exact: (elimT ltP hell).
  - exact: (elimT leP ha1).
  - exact: (elimT leP hale).
  - exact: (elimT leP hSle).
  - apply: (elimT leP).
    by rewrite ckpath_sub2E.
  - exact: (elimT leP hrlo).
  - apply: (elimT leP).
    by rewrite ckpath_doubleE.
  - exact: (elimT leP htop).
by exists x, p, a, u, r; split.
Qed.
