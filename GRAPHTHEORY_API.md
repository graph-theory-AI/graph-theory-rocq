# API de coq-graph-theory 0.9.7 (core/) — énoncés sans preuves

Digest généré mécaniquement depuis
`~/.opam/default/.opam-switch/sources/coq-graph-theory.0.9.7/theories/core/`
en supprimant les blocs `Proof. ... Qed.` (script : suppression des lignes entre
`Proof` et `Qed./Defined./Abort.`). Régénérer à chaque mise à jour de la bibliothèque.

Usage : citer un lemme en copiant son énoncé EXACT d'ici ; `Search`/`About` reste le
filet de sécurité en cas de doute (le digest est fidèle aux sources mais sans types
implicites élaborés). Les sections `Section ... Variables ... Hypothesis ... End`
donnent le contexte des énoncés qu'elles contiennent.

Fichiers omis (multigraphes étiquetés et algèbres 2p, inutiles pour le travail sur
`sgraph`) : mgraph, mgraph2, mgraph2_tw2, skeleton, ptt, pttdom, structures,
setoid_bigop, equiv, finite_quotient, finmap_plus, bounded, rewriting,
open_confluence, reduction, transfer, completeness, wpgt.

Rappels de pièges connus :
- `width B <= 3` signifie « treewidth ≤ 2 » (la largeur n'est pas décrémentée).
- Le type des sommets de `'K_n,m` est `('I_n + 'I_m)%type`, aretes exactement
  entre `inl` et `inr` (`kb_rel u v = is_inl u (+) is_inl v`).
- `2.-connected G` = `kconnected 2 G` = `2 < #|G| /\ forall S, vseparator S -> 2 <= #|S|`.
- Il n'existe AUCUN lemme sur `'K_2,3` dans la bibliothèque.

## edone.v
```coq
(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)

(** * A slightly more powerful done tactic 

We replace the default implementation of [done] by one that
- tries setoid reflexivity
- uses [eassumption] rather than [assumption]
- applies the right hand side simplifications for Boolean operations 
*)

From Coq Require Import Setoid Morphisms.
From mathcomp Require Import ssreflect ssrbool.

Ltac done := trivial; hnf in |- *; intros;
(
  solve [
    (do !
      [ reflexivity
      | solve [ trivial | apply : sym_equal; trivial ]
      | discriminate
      | contradiction
      | split
      | apply/andP;split
      | rewrite ?andbT ?andbF ?orbT ?orbF ]
    )
    | match goal with
        | H:~ _ |- _ => solve [ case H; trivial ]
      end
  ]
).
```

## preliminaries.v
```coq
From Coq Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import edone.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Preliminaries *)

(** Use capitalized names for Coq.Relation_Definitions *)
(* Definition Symmetric := Relation_Definitions.symmetric. *)
(* Definition Transitive := Relation_Definitions.transitive. *)

(** *** Tactics *)

(** Coq treats axioms of type [False] specially: the [Print Asssumptions] command
prints the types that are inhabited by an (empty) case analysis on the
axiom. The alternative definition of [admit] below allows closing proofs that
contain admits by [Qed], leading to a more precise tracking of the "holes"
during proof development.

Of course, the axiom makes the global context inconsistent, making it necessary
to check final results using [Print Assumptions] to ensure the axiom is not
acually used. *)

(** The tactics below should be commented out in released and review versions. *)

(* Axiom admitted_case : False. *) 
(* Ltac admit := case admitted_case. *)

Ltac reflect_eq := 
  repeat match goal with [H : is_true (_ == _) |- _] => move/eqP : H => H end.
Ltac contrab := 
  match goal with 
    [H1 : is_true ?b, H2 : is_true (~~ ?b) |- _] => by rewrite H1 in H2
  end.
Tactic Notation "existsb" uconstr(x) := apply/existsP;exists x.

#[export]
Hint Extern 0 (injective Some) => exact: @Some_inj : core.

(** *** Σ-Types *)

Declare Scope sigT_scope.
Open Scope sigT_scope.

Notation "'Σ' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p%type)) ..))
  (at level 200, x binder, y binder, right associativity) : sigT_scope.

Notation "⟨ x , m ⟩" := (existT _ x m) : sigT_scope.

Lemma tagged_eq (T : eqType) (T_ : T -> eqType) (x : T) (u v : T_ x) : 
  (⟨ x , u ⟩ == ⟨ x , v ⟩) = (u == v).

Lemma tagged_eqF (T : eqType) (T_ : T -> eqType) (x y : T) (u : T_ x) (v : T_ y) : 
  x != y -> (⟨ x , u ⟩ == ⟨ y , v ⟩) = false.

(** *** Generic Trivialities *)

Lemma enum_sum (T1 T2 : finType) (p : pred (T1 + T2)) :
  enum p = 
  map inl (enum [pred i | p (inl i)]) ++ map inr (enum [pred i | p (inr i)]).

Lemma enum_unit (p : pred unit) : enum p = filter p [:: tt].

(** usage: [rewrite [pat]rwT] replaces [pat] with [true] and creates [pat] as a subgoal *)
Definition rwT (b : bool) := @id (is_true b).
(** [rewrite [pat]rwF] replaces [pat] with [false] and creates [~~ pat] as a subgoal *)
Definition rwF := negbTE.

Lemma forall_imset (aT rT : finType) (f : aT -> rT) (p : {pred aT}) (q : {pred rT}) :
  [forall x in [set f z | z in p], q x] = [forall x in p, q (f x)].

Lemma forall2_imset (aT rT : finType) (f g : aT -> rT) (p : {pred aT}) (q : rel rT) :
  [forall x in [set f z | z in p], forall y in [set g z | z in p], q x y] = 
  [forall x in p, forall y in p, q (f x) (g y)].

Lemma eq_forall_in (T : finType) (A P1 P2 : {pred T}) : 
  {in A, P1 =1 P2} -> [forall x in A, P1 x] = [forall x in A, P2 x].

Lemma insubdT (T : Type) (P : pred T) (sT : subType P) (d : sT) (x : T) (Px : P x) : 
  insubd d x = Sub x Px.

Section Val2.
Variables (T : Type) (P : pred T) (sT : subType P) (P' : pred sT) (sT' : subType P').
Definition val2 (x : sT') := val (val x).

Lemma val2_inj : injective val2.
End Val2.
Prenex Implicits val2.

Variant xchoose_spec (T : choiceType) (P : pred T) (E : ex P) : T -> Prop :=
  XChosen x of P x : xchoose_spec E x.

Lemma xchooseP' (T : choiceType) (P : pred T) (E : ex P) : 
  xchoose_spec E (xchoose E).

Lemma exists_inPnn {T : finType} {D P : pred T} : 
  reflect (forall x : T, x \in D -> P x) (~~ [exists x in D, ~~ P x]).

Lemma existsb_case (P : pred bool) : [exists b, P b] = P true || P false.

Lemma all_cons (T : eqType) (P : T -> Prop) a (s : seq T) : 
  {in a::s, forall x, P x} <-> P a /\ {in s, forall x, P x}.

Lemma cons_subset (T : eqType) (a:T) s1 (s2 : pred T) : 
  {subset a::s1 <= s2} <-> a \in s2 /\ {subset s1 <= s2}.

Lemma subrelP (T : finType) (e1 e2 : rel T) : 
  reflect (subrel e1 e2) ([pred x | e1 x.1 x.2] \subset [pred x | e2 x.1 x.2]).

Lemma eqb_negR (b1 b2 : bool) : (b1 == ~~ b2) = (b1 != b2).

Lemma orb_sum (a b : bool) : a || b -> (a + b)%type.

(* should possibly be called [inj_leq] but that's aleady used *)
Lemma inj_card_leq (A B: finType) (f : A -> B) : injective f -> #|A| <= #|B|.

Lemma bij_card_eq (A B: finType) (f : A -> B) : bijective f -> #|A| = #|B|.

(** Note: [u : [the subType P of {x : T | P x}]] provides for the decidable equality *)
Lemma sub_val_eq (T : eqType) (P : pred T)
    (u : [the subType P of {x : T | P x}]) x (Px : x \in P) :
  (u == Sub x Px) = (val u == x).

Lemma valK' (T : Type) (P : pred T) (sT : subType P) (x : sT) (p : P (val x)) :
  Sub (val x) p = x.

Lemma inl_inj (A B : Type) : injective (@inl A B).

Lemma inr_inj (A B : Type) : injective (@inr A B).

Lemma inr_codom_inl (T1 T2 : finType) x : inr x \in codom (@inl T1 T2) = false.

Lemma inl_codom_inr (T1 T2 : finType) x : inl x \in codom (@inr T1 T2) = false.

Lemma Some_eqE (T : eqType) (x y : T) : (Some x == Some y) = (x == y).

Lemma inl_eqE (A B : eqType) x y : (@inl A B x == @inl A B y) = (x == y).

Lemma inr_eqE (A B : eqType) x y : (@inr A B x == @inr A B y) = (x == y).

Definition sum_eqE := (inl_eqE,inr_eqE).

Lemma sum_nat_mulnr [I : finType] (A : pred I) (n : nat) (F : I -> nat) :
  (n * \sum_(i in A) F i)%N = \sum_(i in A) n * F i.

Lemma sum_cardI (T : finType) (A B : {set T}): 
  \sum_(x in A) (x \in B) = #|A :&: B|.

Lemma sum_cond1 (I : finType) (r : seq I) (P Q : I -> bool) : 
  \sum_(x <- r | Q x ) P x = \sum_(x <- r | Q x && P x) 1.

Lemma card_gtnE (T : finType) n (p : {pred T}) : n < #|p| -> { x | x \in p }.

(** getting the "n-th element" of a set of ordinals *)
(** TOTHINK: generalize ot aribtaryy ordered types? *)
Lemma nth_ord (k n : nat) (A : {set 'I_k}) : 
  n < #|A| -> { i : 'I_k | i \in A & #|[set j in A | j < i]| = n}.

Lemma inj_omap T1 T2 (f : T1 -> T2) : injective f -> injective (omap f).

Definition ord1 {n : nat} : 'I_n.+2 := Ordinal (isT : 1 < n.+2).
Definition ord2 {n : nat} : 'I_n.+3 := Ordinal (isT : 2 < n.+3).
Definition ord3 {n : nat} : 'I_n.+4 := Ordinal (isT : 3 < n.+4).

Lemma ord_size_enum n (s : seq 'I_n) : uniq s -> n <= size s -> forall k, k \in s.

Lemma ord_fresh n (s : seq 'I_n) : size s < n -> exists k : 'I_n, k \notin s.

Lemma bigmax_leq_pointwise (I :finType) (P : pred I) (F G : I -> nat) :
  {in P, forall x, F x <= G x} -> \max_(i | P i) F i <= \max_(i | P i) G i.

Lemma set1_inj (T : finType) : injective (@set1 T).

Lemma id_bij T : bijective (@id T).

Lemma card_ltnT (T : finType) (p : pred T) x : ~~ p x -> #|p| < #|T|.

Lemma leq_cardsD1 (T : finType) (a : T) (A : {set T}) : #|A|.-1 <= #|A :\ a|.

Lemma setE (T : finType) (A : {set T}) : [set x in A] = A.

Lemma setDK (T : finType) (A B : {set T}) : B \subset A -> (A :\: B :|: B) = A.

(* what's a good name? *)
Lemma setUUC (T : finType) (A B : {set T}) : (A :|: B) :&: (~: A :|: B) = B.

Lemma setU1_mem (T : finType) x (A : {set T}) : x \in A -> x |: A = A.

Variant picks_spec (T : finType) (A : {set T}) : option T -> Type := 
| Picks x & x \in A : picks_spec A (Some x)
| Nopicks & A = set0 : picks_spec A None.

Lemma picksP (T : finType) (A : {set T}) : picks_spec A [pick x in A].

Lemma set10 (T : finType) (e : T) : [set e] != set0.

Lemma setU1_neq (T : finType) (e : T) (A : {set T}) : e |: A != set0.

(** TOTHINK: [#|P| <= #|aT|] would suffice, the other direction is
implied. But the same is true for [inj_card_onto]. *)
Lemma inj_card_onto_pred (aT rT : finType) (f : aT -> rT) (P : pred rT) : 
  injective f -> (forall x, f x \in P) -> #|aT| = #|P| -> {in P, forall y, y \in codom f}.

(** TODO: check whether the collection of lemmas on sets/predicates
and their cardinalities can be simplified *)

Lemma cards3 (T : finType) (a b c : T) : #|[set a;b;c]| <= 3.

Lemma eq_set1P (T : finType) (A : {set T}) (x : T) : 
  reflect (x \in A /\ {in A, all_equal_to x}) (A == [set x]).

Lemma setN01E (T : finType) A (x:T) : 
  A != set0 -> A != [set x] -> exists2 y, y \in A & y != x.

Lemma sub_filter (T : eqType) (p : {pred T}) (s : seq T) : 
  {subset [seq x <- s | p x] <= s}.

Lemma sub_filter_cond (T : eqType) (p : {pred T}) (s : seq T) : 
  {subset [seq x <- s | p x] <= p}.

Lemma subseq_of_subset (T : finType) (A : pred T) (s : seq T) n : 
  uniq s -> {subset A <= s} -> n <= #|A| -> 
  exists p : seq T, [/\ {subset p <= A}, size p = n & subseq p s].

Lemma bigcup_set1 (T I : finType) (i0 : I) (F : I -> {set T}) :
  \bigcup_(i in [set i0]) F i = F i0.

(** usage: [elim/(size_ind f) : x] *)
Lemma size_ind (X : Type) (f : X -> nat) (P : X -> Type) : 
  (forall x, (forall y, (f y < f x) -> P y) -> P x) -> forall x, P x.
Arguments size_ind [X] f [P].

Ltac eqxx := match goal with
             | [ H : is_true (?x != ?x) |- _ ] => by rewrite eqxx in H
             end.

(** use tactics in terms to obtain the argument type when doing
induction on the size of something (e.g., a type, set, or
predicate). This works since at the time where [elim/V] evaluates [V],
the last assumption is [_top_assumption_ : T] with [T] being the type of
the variable one want's to do induction on. Usage: [elim/card_ind] *)
Notation card_ind := 
  (size_ind (fun x : (ltac:(match goal with  [ _ : ?X |- _ ] => exact X end)) => #|x|))
  (only parsing). 

(* TOTHINK: is there a [card_ind] LEMMA that does not require manual
instantiation or Ltac trickery?  The following works for [pred T] but
not for [{set T}]. *)
(*
Lemma card_ind' (T : finType) (pT : predType T) (P : pT -> Type) : 
  (forall x : pT, (forall y : pT, (#|y| < #|x|) -> P y) -> P x) -> forall x : pT, P x. 
*)

Lemma proper_ind (T: finType) (P : pred T  -> Type) : 
  (forall A : pred T, (forall B : pred T, B \proper A -> P B) -> P A) -> forall A, P A.

Lemma propers_ind (T: finType) (P : {set T} -> Type) : 
  (forall A : {set T}, (forall B : {set T}, B \proper A -> P B) -> P A) -> forall A, P A.

Section Smallest.

Variables (T : finType).
Implicit Types (P : {set T} -> Prop) (p : {set T} -> bool) (U V : {set T}).

Definition smallest P U := P U /\ forall V : {set T}, P V -> #|U| <= #|V|.
Definition largest P U := P U /\ forall V : {set T}, P V -> #|V| <= #|U|.

Lemma below_smallest P U V : smallest P U -> #|V| < #|U| -> ~ P V.

Lemma above_largest P U V : largest P U -> #|V| > #|U| -> ~ P V.

Variables (P : {set T} -> Prop) (p : {set T} -> bool).
Hypothesis PP : forall x, reflect (P x) (p x). 

Lemma smallestPP A : smallest P A <-> smallest p A.

Lemma argmin_smallest A : p A -> smallest p [arg min_(B < A | p B) #|B|].

Lemma ex_smallest A : P A -> exists B, smallest P B.

End Smallest.

Lemma sub_in2W (T1 : predArgType) (D1 D2 D1' D2' : pred T1) (P1 : T1 -> T1 -> Prop) :
 {subset D1 <= D1'} -> {subset D2 <= D2'} -> 
 {in D1' & D2', forall x y : T1, P1 x y} -> {in D1&D2, forall x y: T1, P1 x y}.

Definition restrict_mem (T:Type) (A : mem_pred T) (e : rel T) := 
  [rel u v | (in_mem u A) && (in_mem v A) && e u v].
Notation restrict A := (restrict_mem (mem A)).

Lemma sub_restrict (T : Type) (e : rel T) (a : pred T) : 
  subrel (restrict a e) e.

Lemma restrict_mono (T : Type) (A B : {pred T}) (e : rel T) : 
  {subset A <= B} -> subrel (restrict A e) (restrict B e).

Lemma restrict_irrefl (T : Type) (e : rel T) (A : pred T) : 
  irreflexive e -> irreflexive (restrict A e).

Lemma restrict_sym (T : Type) (A : pred T) (e : rel T) : 
  symmetric e -> symmetric (restrict A e).

Notation vfun := (fun x: void => match x with end).  
Notation rel0 := [rel _ _ | false].
Definition surjective (aT : finType) (rT : eqType) (f : aT -> rT) := forall x, x \in codom f.

Fact rel0_irrefl {T:Type} : @irreflexive T rel0.

Fact rel0_sym {T:Type} : @symmetric T rel0.

Lemma relU_sym' (T : Type) (e e' : rel T) :
  symmetric e -> symmetric e' -> symmetric (relU e e').

Lemma codom_Some (T : finType) (s : seq (option T)) : 
  None \notin s -> {subset s <= codom Some}.

(** Unlike Logic.unique, the following does not actually require existence *)
Definition unique X (P : X -> Prop) := forall x y, P x -> P y -> x = y.

Lemma empty_uniqe X (P : X -> Prop) : (forall x, ~ P x) -> unique P.

(** *** Disjointness *)

(* Lemma in mathcomp-1.12 has [A : {set T}] *)
Lemma disjoints1 (T : finType) (A : {pred T}) x : 
  [disjoint [set x] & A] = (x \notin A).

Lemma disjoints0 (T : finType) (A : {pred T}) : [disjoint set0 & A].

Lemma disjointP (T : finType) (A B : pred T):
  reflect (forall x, x \in A -> x \in B -> False) [disjoint A & B].
Arguments disjointP {T A B}.

Definition disjointE (T : finType) (A B : pred T) (x : T) 
  (D : [disjoint A & B]) (xA : x \in A) (xB : x \in B) := disjointP D _ xA xB.

Lemma disjointsU (T : finType) (A B C : {set T}):
  [disjoint A & C] -> [disjoint B & C] -> [disjoint A :|: B & C].

(** *** Function Update *)

Section update.
Variables (aT : eqType) (rT : Type) (f : aT -> rT).
Definition update x a := fun z => if z == x then a else f z.

Lemma update_neq x z a : x != z -> update z a x = f x.

Lemma update_eq z a : update z a z = a.

End update.
Definition updateE := (update_eq,update_neq).
Notation "f [upd x := y ]" := (update f x y) (at level 1, left associativity, format "f [upd  x  :=  y ]").

Lemma update_same (aT : eqType) (rT : Type) (f : aT -> rT) x a b : 
  f[upd x := a][upd x := b] =1 f[upd x := b].

Lemma update_fx (aT : eqType) (rT : Type) (f : aT -> rT) (x : aT):
  f[upd x := f x] =1 f.

(** *** Sequences and Paths *)

Lemma eq_in_pmap (aT : eqType) rT (f1 f2 : aT -> option rT) (s : seq aT) : 
  {in s, f1 =1 f2} -> pmap f1 s = pmap f2 s.

(** Variants of [splitP] and [splitPr] that remembers that provides
the information that the split is performed at the first occurrence. *)
Section SplitPlus.
Variables (n0 : nat) (T : eqType).
Implicit Type p : seq T.

Variant split x : seq T -> seq T -> seq T -> Type :=
  Split p1 p2 of x \notin p1 : split x (rcons p1 x ++ p2) p1 p2.

Lemma splitP p x (i := index x p) :
  x \in p -> split x p (take i p) (drop i.+1 p).

Variant splitr x : seq T -> Type :=
  Splitr p1 p2 of x \notin p1 : splitr x (p1 ++ x :: p2).

Lemma splitPr p x : x \in p -> splitr x p.
End SplitPlus.

Lemma tnth_uniq (T : eqType) n (t : n.-tuple T) (i j : 'I_n) : 
  uniq t -> (tnth t i == tnth t j) = (i == j).

Lemma mem_tail (T : eqType) (x y : T) s : y \in s -> y \in x :: s.
Arguments mem_tail [T] x [y s].

Lemma in_set_seq (T : finType) (s : seq T) : [set z in s] =i s.
  
(* inline? *)
Lemma subset_seqR (T : finType) (A : pred T) (s : seq T) : 
  (A \subset s) = (A \subset [set x in s]).

Lemma subset_seqL (T : finType) (A : pred T) (s : seq T) : 
  (s \subset A) = ([set x in s] \subset A).

Lemma mem_catD (T:finType) (x:T) (s1 s2 : seq T) : 
  [disjoint s1 & s2] -> (x \in s1 ++ s2) = (x \in s1) (+) (x \in s2).
Arguments mem_catD [T x s1 s2].

Lemma rpath_sub (T : eqType) (e : rel T) (a : pred T) x p : 
  path (restrict a e) x p -> {subset p <= a}.

Lemma closed_path_sub (T : eqType) (e : rel T) (x : T) (s : seq T) (p : {pred T}) :
  (forall z y, e z y -> p z -> p y) -> p x -> path e x s -> {subset s <= p}.

Lemma path_rpath (T : eqType) (e : rel T) (A : pred T) x p :
  path e x p -> x \in A -> {subset p <= A} -> path (restrict A e) x p.

Lemma last_take (T : eqType) (x : T) (p : seq T) (n : nat): 
  n <= size p -> last x (take n p) = nth x (x :: p) n.

Lemma take_find (T : Type) (a : pred T) s : ~~ has a (take (find a s) s).

Lemma rev_inj (T : Type) : injective (@rev T).

Lemma last_mem (T : eqType) (x : T) (s : seq T) : 
  x \in s -> last x s \in s.

Lemma last_belast_eq (T : Type) (x : T) p q : 
  last x p = last x q  -> belast x p = belast x q -> p = q.

Lemma lift_path (aT : finType) (rT : eqType) (e : rel aT) (e' : rel rT) (f : aT -> rT) a p' : 
  (forall x y, f x \in f a :: p' -> f y \in f a :: p' -> e' (f x) (f y) -> e x y) ->
  path e' (f a) p' -> {subset p' <= codom f} -> exists p, path e a p /\ map f p = p'.

Lemma mem_bigcup (T1 T2 : finType) (F : T1 -> {set T2}) (P : pred T1) z y : 
  P y -> z \in F y -> z \in \bigcup_(x | P x) F x.
Arguments mem_bigcup [T1 T2 F P z] y _ _.

(** *** Reflexive Transitive Closure *)

Lemma connectUP (T : finType) (e : rel T) (x y : T) :
  reflect (exists p, [/\ path e x p, last x p = y & uniq (x::p)])
          (connect e x y).
Arguments connectUP {T e x y}.

Lemma sub_connect (T : finType) (e : rel T) : subrel e (connect e).
Arguments sub_connect [T] e _ _ _.

Lemma sub_trans (T:Type) (e1 e2 e3: rel T) : 
  subrel e1 e2 -> subrel e2 e3 -> subrel e1 e3.

Lemma connect_mono (T : finType) (e1 e2 : rel T) : 
  subrel e1 e2 -> subrel (connect e1) (connect e2).

Lemma sub_restrict_connect (T : finType) (e : rel T) (a : pred T) : 
  subrel (connect (restrict a e)) (connect e).

Lemma connect_restrict_mono (T : finType) (e : rel T) (A B : pred T) :
  A \subset B -> subrel (connect (restrict A e)) (connect (restrict B e)).

Lemma restrictE (T : finType) (e : rel T) (A : pred T) : 
  A =i predT -> connect (restrict A e) =2 connect e.

Lemma connect_restrictP (T : finType) (e : rel T) (A : pred T) x y (xDy : x != y) :
  reflect (exists p, [/\ path e x p, last x p = y, uniq (x::p) & {subset x::p <= A}])
          (connect (restrict A e) x y).
Arguments connect_restrictP {T e A x y _}.

Lemma connect_symI (T : finType) (e : rel T) : symmetric e -> connect_sym e.

Lemma equivalence_rel_of_sym (T : finType) (e : rel T) :
  symmetric e -> equivalence_rel (connect e).

Lemma homo_connect (aT rT : finType) (e : rel aT) (e' : rel rT) (f : aT -> rT) a b :
  {homo f : x y / e x y >-> e' x y} -> connect e a b -> connect e' (f a) (f b).

Lemma eq_connect_sym (T : finType) (e e' : rel T) : 
  e =2 e' -> connect_sym e -> connect_sym e'.

Definition sc (T : Type) (e : rel T) := [rel x y | e x y || e y x].

Lemma sc_sym (T : Type) (e : rel T) : symmetric (sc e).

Lemma sc_eq T T' (e : rel T) (e' : rel T') f x y :
  (forall x y, e' (f x) (f y) = e x y) -> sc e' (f x) (f y) = sc e x y.

(** Equivalence Closure *)

Section Equivalence.

Variables (T : finType) (e : rel T).

Definition equiv_of := connect (sc e).

Definition equiv_of_refl : reflexive equiv_of.

Lemma equiv_of_sym : symmetric equiv_of.

Definition equiv_of_trans : transitive equiv_of.

(* Canonical equiv_of_equivalence := *)
(*   EquivRel equiv_of equiv_of_refl equiv_of_sym equiv_of_trans. *)

Lemma sub_equiv_of : subrel e equiv_of.

End Equivalence.

Lemma lift_equiv (T1 T2 : finType) (E1 : rel T1) (E2 : rel T2) h :
  bijective h -> (forall x y, E1 x y = E2 (h x) (h y)) ->
  (forall x y, equiv_of E1 x y = equiv_of E2 (h x) (h y)).

#[export]
Hint Resolve Some_inj inl_inj inr_inj : core.

(** *** Set preimage *)

Notation "f @^-1 x" := (preimset f (mem (pred1 x))) (at level 24) : set_scope.  

Lemma mem_preim (aT rT : finType) (f : aT -> rT) x y : 
  (f x == y) = (x \in f @^-1 y).

Lemma can_preimset (aT rT : finType) (f : aT -> rT) (A : {set rT}) : 
  A \subset codom f -> [set f x | x in f @^-1: A] = A.
Arguments can_preimset [aT rT] f [A] _.

Lemma preim_omap_Some (aT rT : finType) (f : aT -> rT) y :
  (omap f @^-1 Some y) = Some @: (f @^-1 y).

Lemma preim_omap_None (aT rT : finType) (f : aT -> rT) :
  (omap f @^-1 None) = [set None].

(** *** Set image *)

Lemma imset_inj (aT rT : finType) (f : aT -> rT) : 
  injective f -> injective (fun A : {set aT} => f @: A).

Lemma imset_pre_val (T : finType) (P : pred T) (s : subFinType P) (A : {set T}) :
  A \subset P -> val @: (val @^-1: A : {set s}) = A.

Lemma imset_valT (T : finType) (P : pred T) (s : subFinType P) :
  val @: [set: s] = finset P.

Lemma imset_codom (aT rT : finType) (f : aT -> rT) (A : {set aT}) : 
  [set f x | x in A] \subset codom f.

Lemma memKset (T : finType) (A : {set T}) : finset (mem A) = A.

Lemma inj_card_preimset (aT rT : finType) (f : aT -> rT) (A : {set rT}) : 
  injective f -> A \subset codom f -> #|f @^-1: A| = #|A|.

Lemma inj_imsetS (aT rT : finType) (f : aT -> rT) (A B : {pred aT}) : 
  injective f -> (f @: A \subset f @: B) = (A \subset B).

Lemma val_subset (T: finType) (H : {set T}) (A B : {set sig [eta mem H]}) :
  (val @: A \subset val @: B) = (A \subset B).

(** *** Replacement for partial functions *)

Definition pimset (aT rT : finType) (f : aT -> option rT) (A : {set aT}) := 
  [set x : rT | [exists (x0 | x0 \in A), f x0 == Some x]].

Lemma pimsetP (aT rT : finType) (f : aT -> option rT) (A : {set aT}) x : 
  reflect (exists2 x0, x0 \in A & f x0 == Some x) (x \in pimset f A).
      
Lemma pimset_card (aT rT : finType) (f : aT -> option rT) (A : {set aT}) : 
  #|[set x : rT | [exists x0 in A, f x0 == Some x]]| <= #|A|.

(** *** Partitions *)

Lemma mem_cover (T : finType) (P : {set {set T}}) (x : T) (A : {set T}) : 
  A \in P -> x \in A -> x \in cover P.

Lemma pblock_eqvE (T : finType) (R : rel T) (D : {set T}) x y : 
  {in D & &, equivalence_rel R} ->
  y \in pblock (equivalence_partition R D) x -> [/\ x \in D, y \in D & R x y].

(* TOTHINK: This proof appears to complicated/monolithic *)
Lemma equivalence_partition_gt1P (T : finType) (R : rel T) (D : {set T}) :
   {in D & &, equivalence_rel R} ->
   reflect (exists x y, [/\ x \in D, y \in D & ~~ R x y]) (1 < #|equivalence_partition R D|).

(** Partitions possibly including the empty equivalence class *)
Definition pe_partition (T : finType) (P : {set {set T}}) (D : {set T}) :=
  (cover P == D) && (trivIset P).

Lemma trivIset3 (T : finType) (A B C : {set T}) : 
  [disjoint A & B] -> [disjoint B & C] -> [disjoint A & C] -> 
  trivIset [set A;B;C].

(** Extra Morphism declatations *)

#[export]
Instance ex2_iff_morphism (A : Type) :  
  Proper (pointwise_relation A iff ==> pointwise_relation A iff ==> iff) (@ex2 A).

(** *** Extra Preliminaries used in Domination Theory *)

Section Preliminaries_dom.

Lemma properC (T : finType) (A B : {set T}) : A \proper B = (~: B \proper ~: A).

Lemma in11_in2 (T1 T2 : predArgType) (P : T1 -> T2 -> Prop) (A1 : {pred T1}) (A2 : {pred T2}) : 
  {in A1, forall x, {in A2, forall y,  P x y}} <-> {in A1 & A2, forall x y, P x y}.

Lemma eq_extremum (T : eqType) (I : finType) r x0 (p1 p2 : pred I) (F1 F2 : I -> T) : 
  p1 =1 p2 -> F1 =1 F2 -> extremum r x0 p1 F1 = extremum r x0 p2 F2.

Lemma eq_arg_min (I : finType) (x : I) (p1 p2 : pred I) (w1 w2 : I -> nat) :
  p1 =1 p2 -> w1 =1 w2 -> arg_min x p1 w1 = arg_min x p2 w2.

Lemma eq_arg_max (I : finType) (x : I) (p1 p2 : pred I) (w1 w2 : I -> nat) :
  p1 =1 p2 -> w1 =1 w2 -> arg_max x p1 w1 = arg_max x p2 w2.

Variable T : finType.

Proposition maxset_properP (p : pred {set T}) (D : {set T}) :
  reflect (p D /\ (forall F : {set T}, D \proper F -> ~~ p F)) (maxset p D).

Proposition minset_properP (p : pred {set T}) (D : {set T}) :
  reflect (p D /\ (forall F : {set T}, F \proper D -> ~~ p F)) (minset p D).

(* not used *)
Lemma largest_maxset (p : pred {set T}) (A : {set T}) :
  largest p A -> maxset p A.

(* not used *)
Lemma smallest_minset (p : pred {set T}) (A : {set T}) : 
  smallest p A -> minset p A.

Lemma doubleton_eq_left (u v w : T) : [set u; v] = [set u; w] <-> v = w.

Lemma doubleton_eq_right (u v w : T) : [set u; w] = [set v; w] <-> u = v.

Lemma doubleton_eq_iff (u v w x : T) : [set u; v] = [set w; x] <->
  ((u = w /\ v = x) \/ (u = x /\ v = w)).

End Preliminaries_dom.

Arguments in11_in2 [T1 T2 P] A1 A2.
Arguments maxset_properP {T p D}.
Arguments minset_properP {T p D}.

(** *** Extra Preliminaries from Kuratowski/Wagner development *)

#[export] Hint Extern 0 (injective (isSub.val_subdef _)) =>
  exact val_inj : core.
#[export] Hint Extern 0 (injective sval) => exact val_inj : core.

Lemma in_setP (T : finType) (p : {pred T}) (x : T) : 
  reflect (p x) (x \in [set y | p y]).

Lemma Sub_imset (T : finType) (P : {pred T}) (s : subFinType P) {A : {set s}} (x : T) (Px : P x) :
  (Sub x Px \in A) = (x \in val @: A).

Lemma Sub_map (T : eqType) (P : {pred T}) (s : subType P) {A : seq (sub_type s)} (x : T) (Px : P x) :
  (Sub x Px \in A) = (x \in map val A).

Section AltE.
Variables (T rT : Type) (p : pred T) (x : T) (fT : p x -> rT) (fF : ~~ p x -> rT).

Lemma altT (px : p x) :
  match boolP (p x) with AltTrue b => fT b | AltFalse b => fF b end = fT px.

Lemma altF (px : ~~ p x) :
  match boolP (p x) with AltTrue b => fT b | AltFalse b => fF b end = fF px.
End AltE.

Arguments card_gt0P {T A}.  

(**The following two lemmas are adapted from their [face] instances in [revsnip.v]. *)
(* TODO: move to preliminaries/mathcomp *)
Lemma fcard0P (T : finType) (A : pred T) f :
  injective f -> fclosed f A -> reflect (exists x, x \in A) (0 < fcard f A).

Lemma fcard1P (T : finType) (A : pred T) f :
  injective f -> fclosed f A ->
  reflect (exists2 x, x \in A & exists2 y, y \in A & ~~ fconnect f x y)
          (1 < fcard f A).

Lemma index_inj (T : eqType) (s : seq T) : {in s &, injective (index^~ s)}.

Section Closure.
Variables (T : finType).
Implicit Types (e : rel T) (a : pred T) (x y : T).

Lemma closureP e a y : 
  reflect (exists2 x, x \in a & connect e y x) (y \in closure e a).

Lemma closure_connect e a x y : connect e x y -> y \in closure e a -> x \in closure e a.

Lemma eq_closure e e' a : connect e =2 connect e' -> closure e a =i closure e' a.

Lemma eq_closure_r e a a': a =i a' -> closure e a =i closure e a'.

Lemma eq_fclosure (f f' : T -> T) a : f =1 f' -> fclosure f a =i fclosure f' a.

Lemma eq_closed (e e' : rel T) (a : {pred T}) : 
  e =2 e' -> closed e a <-> closed e' a.

Lemma eq_closed_r (e : rel T) (a b : {pred T}) : 
  a =i b -> closed e a <-> closed e b.

Lemma predD_closed (e : rel T) (a b : {pred T}) : 
  connect_sym e -> closed e a -> closed e b -> closed e [predD a & b].

(* TOTHINK: connect_sym should not be necessary with a good def of closure *)
Lemma closure1 e x : connect_sym e -> connect e x =i closure e (pred1 x).

Lemma closure_pred2 e x y :
  connect_sym e -> 
  closure e (pred2 x y) =i [predU closure e (pred1 x) & closure e (pred1 y)].

Lemma codom_id : codom (@id T) =i predT. 

Lemma in_eq_n_comp e e' a : 
  connect_sym e -> connect_sym e' -> closed e a -> closed e' a ->
  {in a &, e =2 e'} -> n_comp e a = n_comp e' a.

End Closure.
Arguments eq_closed [T e e' a].
Arguments eq_closed_r [T e a b].

Section order.
Variables (T : finType) (f : T -> T).

Lemma before_findex x z m : 
  fconnect f x z -> m < findex f x z -> iter m f x != z.

Lemma order_le_looping m z : looping f z m -> order f z <= m.

Lemma order_le_fix m z : iter m.+1 f z = z -> order f z <= m.+1.

Lemma iter_looping m z y :
  (forall n, n < m -> iter n f z != y) -> looping f z m -> ~~ fconnect f z y.

Lemma findex_finv z : findex f z (finv f z) = (order f z).-1.

Lemma index_orbit (x : T) :
  index x (orbit f x) = 0.

Lemma arc_orbit (x y : T) : 
  fconnect f x y -> arc (orbit f x) x y = traject f x (findex f x y).

Lemma findex_bound (x y : T) n : iter n f x = y -> findex f x y <= n.

(** [injective f] could be weakened to [fcycle f (orbit f x)] *)
Lemma findex_f (x y : T) : injective f -> fconnect f x y -> 
  findex f (f x) (f y) = findex f x y.

Lemma fconnect_findex_r (x y : T) : 
  injective f -> fconnect f x y -> y != x -> 
  findex f x y = (findex f x (finv f y)).+1.

Lemma orbit_prefix n x :
  n <= order f x -> orbit f x = traject f x n ++ drop n (orbit f x).

(** generalizes [orbit_id] *)
Lemma orbit_fix x : f x = x -> orbit f x = [:: x].

Lemma order_f (inj_f : injective f) x: 
  order f (f x) = order f x.

Lemma orbit_rot1 (inj_f : injective f) x : orbit f (f x) = rot 1 (orbit f x).

Lemma orbit_rot_iter n (inj_f : injective f) x o :
  orbit f x = o -> orbit f (iter n f x) = iter n (rot 1) o.

End order.

Arguments eq_closure_r [T e a a'].

Lemma forall_all (T : finType) (p : {pred T}) : [forall x, p x] = all p (enum T).

Lemma exists_has (T : finType) (p : {pred T}) : [exists x, p x] = has p (enum T).

Lemma n_compD (T : finType) (a b : {pred T}) e : 
  n_comp e a = n_comp e [predI a & b] + n_comp e [predD a & b].

Arguments n_compD [T a] b.

Lemma n_comp0 (T : finType) (e : rel T) (a : {pred T}) : 
  a =i pred0 -> n_comp e a = 0.

Lemma set_inP (T : finType) (A : {pred T}) (p : pred T) x :
  reflect (x \in A /\ p x) (x \in [set x in A | p x]).

Section RootPartition.
Variables (T : finType) (e : rel T) (A : {set T}).
Hypothesis sym_e : connect_sym e.
Hypothesis closed_A : closed e A.

Lemma closed_root x : (root e x \in A) = (x \in A).

Let block x := [set y in connect e x].
Definition root_partition := [set block x | x in A & x \in roots e].

Lemma root_partitionE : 
  root_partition = equivalence_partition (connect e) A.

Lemma connect_equivalence : equivalence_rel (connect e).

Lemma root_partitionP : partition root_partition A.

Let rpP := root_partitionP.

Lemma sum_roots : #|A| = \sum_(x in roots e | x \in A) #|connect e x|.

Lemma n_comp_partition : n_comp e A = #|equivalence_partition (connect e) A|.

End RootPartition.

Lemma closedT (T : finType) (e : rel T) : closed e [set: T].

Lemma sum_rootsT (T : finType) (e : rel T) : 
  connect_sym e -> #|T| = \sum_(x in roots e) #|connect e x|.

Lemma sum_roots_order (T : finType) (f : T -> T) (inj_f : injective f) :
  #|T| = \sum_(x in froots f) order f x.

Lemma sub_in_connect (T : finType) (e e' : rel T) (x : T) : 
  (forall y, connect e x y -> e y =1 e' y) -> forall y, connect e x y -> connect e' x y.
```

## set_tac.v
```coq
From mathcomp Require Import all_ssreflect.

From GraphTheory Require Import preliminaries.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Simple Experimental Tactic for finite sets *)

(** We use a simple "tableau style" tactic for finite sets. We start
by turning the goal into the form [A1, ..., An |- False] and then derive
facts from the [Ai] until a constdiction is obtained or no more rules
are applicable. *)

Section SetTac.
Variables (T : finType) (A B C : {set T}).

Lemma set_tac_subUl: A :|: B \subset C -> A \subset C /\ B \subset C.

Lemma set_tac_subIr: A \subset B :&: C -> A \subset B /\ A \subset C.

Lemma set_tac_subIl x : 
  x \in A -> x \in B -> A :&: B \subset C -> x \in C.

End SetTac.

Lemma setIPn (T : finType) (A B : {set T}) (x:T) : 
  reflect (x \notin A \/ x \notin B) (x \notin A :&: B).

Lemma setUPn (T : finType) (A B : {set T}) (x:T) : 
  reflect (x \notin A /\ x \notin B) (x \notin A :|: B).

Ltac notHyp b := assert_fails (assert b by assumption).

Ltac extend H T := notHyp H; have ? : H by T.

Ltac convertible A B := assert_succeeds (assert (A = B) by reflexivity).

(** NOTE: since Ltac is untyped, we need to provide the coercions
usually hidden, e.g., [is_true] or [SetDef.pred_of_set]. *)

(** TOTHINK: For some collective predicates, in particular for paths,
the coercion to a predicates can take several different forms. This
means that rules involving [_ \subset _] should match up to conversion
to not miss instances. Similarly, we need to perform a full conversion
check when testing whether a given fact is already present. Otherwise,
the "same" fact might be added multiple times *) 

(** NOTE: The only rules that introduce hypotheses of the form
[_\subset _] are those eliminating equalities between sets. Since
these remove their hypotheses, the trivial subset assumption 
[[set _] \subset A] can be modified in place *)

Local Notation pos := pred_of_set.

(** TODO:
- reverse propagation for subset 
- dealing with setT and set0
- dealing with existential hypotheses 
  + A != B (possibly do the A != set0 case separately)
  + ~~ (A \subset B) (this is never generated, do as init?)

*)

Ltac no_inhabitant A :=
  match goal with [ _ : ?x \in _ A |- _ ] => fail 1 | _ => idtac end.

(* non-branching / closure rules *)
Ltac set_tab_close := 
  match goal with 
  | [H : is_true (?x == ?y) |- _ ] =>
    assert_fails (have: x = y by []); (* [x = y] is nontrivial and unknown *)
    move/eqP : (H) => ?; subst
  | [H : is_true (_ \in _ set0) |- _] => by rewrite in_set0 in H  

  | [H : is_true (?x \in pos (?A :&: ?B)) |- _] => 
    first [notHyp (x \in A)|notHyp(x \in B)]; case/setIP : (H) => [? ?]
  | [H : is_true (?x \in _ (?A :\: ?B)) |- _] => 
    first [notHyp (x \in A)|notHyp(x \notin B)]; case/setDP : (H) => [? ?]
  | [H : is_true (?x \notin _ (?A :|: ?B)) |- _] => 
    first [notHyp (x \notin A)|notHyp(x \notin B)]; case/setUPn : (H) => [? ?]
  | [H : is_true (?x \in pos (~: ?A)) |- _] =>
    extend (x \notin A) ltac:(move: H; rewrite in_setC)
  | [H : is_true (?x \notin pos (~: ?A)) |- _] => 
    extend (x \in A) ltac:(move: H; rewrite in_setC negbK)

  | [H : is_true (?x \in _ [set _ in ?p]) |- _ ] => 
    extend (x \in p) ltac:(move: H; rewrite inE)
  | [H : is_true (?x \notin _ [set _ in ?p]) |- _ ] => 
    extend (x \notin p) ltac:(move: H; rewrite inE)

  | [H : is_true (?x \in _ [set ?y]) |- _ ] => 
    assert_fails (have: x = y by []); (* [x = y] is nontrivial and unknown *)
    move/set1P : (H) => ?;subst
  | [H : is_true (?x \notin _ [set ?y]) |- _ ] => 
    extend (x != y) ltac:(move: H ; rewrite inE)

    (* These rules will be tried (and fail) on equalities between non-sets, but
    set types can take many different shapes *)
  | [ H : ?A = ?B |- _] => 
    first [notHyp (A \subset B)|notHyp(B \subset A)];
    have/andP[? ?]: (A \subset B) && (B \subset A) by 
      (move/eqP : (H); rewrite eqEsubset; apply)
  | [ H : is_true (pos (?A :|: ?B) \subset ?C) |- _] => 
    first[notHyp (A \subset C)|notHyp (B \subset C)];
    case/set_tac_subUl : (H) => [? ?]
  | [ H : is_true (?A \subset pos (?B :&: ?C)) |- _] => 
    first[notHyp (A \subset B)|notHyp (A \subset C)];
    case/set_tac_subIr : (H) => [? ?]
  | [ H : is_true (pos [set ?x] \subset ?A) |- _] => 
    extend (x \in A) ltac:(move: (H); rewrite sub1set; apply)

  | [H : is_true (in_mem ?x (mem ?A)), S : is_true (subset (mem ?A') (mem ?B)) |- _] => 
    convertible (mem A) (mem A'); 
    extend (x \in B) ltac:(move/(subsetP S) : (H) => ?)

  | [H : is_true (?x \in ?B), D : is_true [disjoint ?A & ?B] |- _] => 
    notHyp (x \notin A); have ? : x \notin A by rewrite (disjointFl D H)
  | [H : is_true (?x \in ?A), D : is_true [disjoint ?A & ?B] |- _] => 
    notHyp (x \notin B); have ? : x \notin B by rewrite (disjointFr D H)

  | [ H : is_true (?A != set0) |- _] => 
    no_inhabitant A; case/set0Pn : H => [? ?]
                                         
  | [ xA : is_true (?x \in _ ?A), xB : is_true (?x \in _ ?B), 
       H : is_true (_ (?A :&: ?B) \subset ?D) |- _] =>
    notHyp (x \in D); have ? := set_tac_subIl xA xB H
  end.

(*branching rules *)
Ltac set_tab_branch :=
  match goal with 
  | [H : is_true (?x \in pos (?A :|: ?B)) |- _] => 
    notHyp (x \in A); notHyp (x \in B); case/setUP : (H) => [?|?]
  | [ H : is_true (?x \notin pos (?A :&: ?B)) |- _] => 
    notHyp (x \notin A); notHyp (x \notin B); case/setIPn : (H) => [?|?]
  end.

(** Note that the rules on disjointness and subset do not restricted
to the type [{set _}] *)

Ltac set_init :=
  match goal with
  | [ |- forall _,_ ] => intro;set_init
  | [ |- _ -> _] => intro;set_init
  | [ |- is_true (~~ _) ] => apply/negP => ?
  | [ |- is_true _] => apply: contraTT isT => ?
  | [ |- _ ] => idtac (* nothing to be done here *)
  end.

Ltac clean_mem := 
  repeat match goal with 
           [ H : _ |- _ ] => rewrite !mem_mem in H 
         end; rewrite !mem_mem.

(** Tactics intened to be redefined when combining sets with set-like
structures (e.g., paths in graphs) *)

Ltac set_tac_close_plus := fail.
Ltac set_tac_branch_plus := fail.

Ltac eqxx := match goal with
             | [ H : is_true (?x != ?x) |- _ ] => by rewrite eqxx in H
             end.

(** Use theory rules (plus) before set rules *)
Ltac set_tac_step := first [eqxx
                           |contrab
                           |set_tac_close_plus
                           |set_tab_close
                           |set_tac_branch_plus
                           |set_tab_branch].
                                          
Ltac set_tac := set_init; subst; repeat set_tac_step.

(** Use typeclass inference to trigger set_tac using rewrite lemmas *)

Class setBox (P : Prop) : Prop := SetBox { setBoxed : P }.
#[export]
Hint Extern 0 (setBox _) => apply SetBox; set_tac : typeclass_instances.

Lemma inD (T : finType) (x : T) (A : pred T) `{setBox (x \in A)} : x \in A. 

Lemma inD_debug (T : finType) (x : T) (A : pred T) : (x \in A) -> x \in A. 

Lemma notinD (T : finType) (x : T) (A : pred T) `{setBox (x \notin A)} : x \notin A. 

Lemma notinD_debug (T : finType) (x : T) (A : pred T) : (x \notin A) -> x \notin A. 

(* examples / unit tests *)

Goal forall (T:finType) (S V1 V2 : {set T}) x b, x \in S -> S = V1 :&: V2 -> b || (x \in V1).

Goal forall (T:finType) (A B : {set T}) x b, x \in B -> B \subset A -> (x \in A) || b.

Goal forall (T:finType) (A B : {set T}) x b, x \in B -> [disjoint A & B] -> (x \notin A) || b.

Goal forall (T:finType) (A B : {set T}) x b, x \in A -> [disjoint A & B] -> b || (x \notin B).

Goal forall (T:finType) (A B : {set T}) x b, x \notin A -> x \in A :|: B -> b || (x \in B).

(** NOTE: This does not require backward propagation of \subset since [x \in B] is assumed *)
Goal forall (T:finType) (A B : {set T}) x b, x \notin A -> B \subset A -> (x \notin B) || b.

Goal forall (T:finType) (A B : {set T}) x,  x \in A -> A = B -> x \in B.

Goal forall (T:finType) (A B : {set T}) x,  x \in A -> A == B -> x \in B.
```

## bij.v
```coq
From Coq Require Import Setoid CMorphisms.
From Coq Require Relation_Definitions.
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import edone preliminaries.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Bijections between Types  *)

Set Primitive Projections.
Record bij (A B: Type): Type := Bij
  { bij_fwd:> A -> B;
    bij_bwd: B -> A;
    bijK: cancel bij_fwd bij_bwd;
    bijK': cancel bij_bwd bij_fwd }.
Notation "h '^-1'" := (bij_bwd h). 

(** Facts about Bijections *)

Lemma bij_bijective A B (f : bij A B) : bijective f.

Lemma bij_bijective' A B (f : bij A B) : bijective f^-1.

#[export]
Hint Resolve bij_bijective bij_bijective' : core.

Lemma bij_injective A B (f: bij A B) : injective f.

Lemma bij_injective' A B (f: bij A B) : injective f^-1.

#[export]
Hint Resolve bij_injective bij_injective' : core.

Lemma card_bij (A B: finType) (f : bij A B) : #|A| = #|B|.
Arguments card_bij [A B] f.

Lemma bij_imset_f (aT rT : finType) (f : bij aT rT) (x : aT) (A : {set aT}): 
  (f x \in [set f x | x in A]) = (x \in A).

Lemma imset_bijT (aT rT : finType) (i : bij aT rT) : i @: setT = setT.

Lemma bij_imsetC (aT rT : finType) (f : bij aT rT) (A : {set aT}) : 
  ~: [set f x | x in A] = [set f x | x in ~: A].

Lemma bij_eqLR (aT rT : finType) (f : bij aT rT) x y : 
  (f x == y) = (x == f^-1 y).

(** Specific Bijections *)

Definition bij_id {A}: bij A A := @Bij A A id id (@erefl A) (@erefl A).

Definition bij_ord {T : finType} : bij T 'I_#|T| := Bij enum_rankK enum_valK.

Definition bij_sym {A B}: bij A B -> bij B A.

Definition bij_comp {A B C}: bij A B -> bij B C -> bij A C.

#[export]
Instance bij_Equivalence: Equivalence bij.

(* bijections about [sum] *)

Definition sumf {A B C D} (f: A -> B) (g: C -> D) (x: A+C): B+D :=
  match x with inl a => inl (f a) | inr c => inr (g c) end. 

#[export]
Instance sum_bij: Proper (bij ==> bij ==> bij) sum.

Definition sumC {A B} (x: A + B): B + A := match x with inl x => inr x | inr x => inl x end.
Lemma bij_sumC {A B}: bij (A+B) (B+A).

Definition sumA {A B C} (x: A + (B + C)): (A + B) + C :=
  match x with inl x => inl (inl x) | inr (inl x) => inl (inr x) | inr (inr x) => inr x end.
Definition sumA' {A B C} (x: (A + B) + C): A + (B + C) :=
  match x with inr x => inr (inr x) | inl (inr x) => inr (inl x) | inl (inl x) => inl x end.
Lemma bij_sumA {A B C}: bij (A+(B+C)) ((A+B)+C).

Lemma sumUx {A}: bij (void + A) A.
Lemma sumxU {A}: bij (A + void) A.

(* bijections for [option] types *)

Definition option_bij (A B : Type) (f : bij A B) : bij (option A) (option B).

Lemma option_sum_unit {A}: bij (option A) (A+unit).

(* the definitions below also follow from [option_sum_unit] and the bijections about [sum] *)
Definition option_void: bij (option void) unit.

Lemma sum_option_l {A B}: bij ((option A) + B) (option (A + B)).

Lemma sum_option_r {A B}: bij (A + option B) (option (A + B)).

Definition option2x {A}: option (option A) -> option (option A) :=
  fun x => match x with Some (Some a) => Some (Some a) | Some None => None | None => Some None end.
Definition option2_swap {A}: bij (option (option A)) (option (option A)).
  exists option2x option2x; abstract by repeat case. 
Defined.

(* bijections for [bool] *)

Definition bool_swap: bij bool bool.

Lemma bool_two: bij bool (unit+unit).

Definition bool_option_unit: bij bool (option unit).

(** Moving a single element out of a type *)

Section BijD1. 
  Variables (T : finType) (z : T).
  
(** We use [x \notin [set z]] rather than [x != z], because the former is
the form that occurs when removing a single edge via [remove_edges] *)

  Definition bijD1_fwd (x : option { x : T | x \notin [set z]}) : T :=
    if x is Some y then val y else z.
  Definition bijD1_bwd (x : T) : option { x : T | x \notin [set z]} := 
    if @boolP (x \in [set z]) is AltFalse p then Some (Sub x p) else None.
  
  Lemma can_bijD1_fwd : cancel bijD1_fwd bijD1_bwd.

  Lemma can_bijD1_bwd : cancel bijD1_bwd bijD1_fwd.

  Definition bijD1 := Bij can_bijD1_fwd can_bijD1_bwd.
End BijD1.

Section BijT.
Variables (T : finType) (P : pred T).
Hypothesis inP : forall x, P x.
Definition subT_bij : bij {x : T | P x} T.
End BijT.

Definition setT_bij (T : finType) : bij {x : T | x \in setT} T := 
  Eval hnf in subT_bij (@in_setT T).
Arguments setT_bij {T}.

(** Useful to obtain bijections with good simplification properties *)
(* not used for now *)
Lemma bij_same A B (f : A -> B) (f_inv : B -> A) (i : bij A B) :
  f =1 i -> f_inv =1 i^-1 -> bij A B.
Arguments bij_same [A B] f f_inv i _ _.

Lemma perm_index_enum (I1 I2 : finType) (f : I1 -> I2) :
  bijective f -> perm_eq (index_enum I2) [seq f i | i <- index_enum I1].

Lemma bij_perm_enum (I1 I2 : finType) (f : bij I1 I2) :
  perm_eq (index_enum I2) [seq f i | i <- index_enum I1]. 
```

## digraph.v
```coq
From HB Require Import structures.
From Coq Require Import Setoid CMorphisms.
From Coq Require Relation_Definitions.
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import edone preliminaries bij.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Directed Graphs  *)

(** This file contains a number of constructions and lemmas to reason about
paths in (finite) graphs. The most basic notion of a graph is just a type
packaged together with a relation. *)

(** The underlying type could be more permissive e.g. [countType] or even
[eqType]. However, this would required a more complicated setup in order to
ensure that the coercions to [countType] and [finType] (for finite graphs) are
not just convertible but indeed equal. Otherwise, some automation using [auto]
fails. So far, we only deal with with finite graphs, so "telescopes" suffice *)

Record relType := RelType { rel_car :> finType; edge_rel : rel rel_car }.
Notation "x -- y" := (edge_rel x y) (at level 30).
Prenex Implicits edge_rel.

(** experimental notation for passing [edge_rel] or [sedge] *)
(* TODO/TOTHINK : use this pervasively *)
Notation "(--)" := (fun x y => x -- y).

(** maintain the notation [x -- y] under simplification *)

Arguments edge_rel : simpl never.

(** For [G : relType] and [x, y : G] we define two auxiliary notions: *) 

(** [pathp x y p] == the list (x::p) is an xy-path in G. *)
  
(** [upath x y p] == the list (x::p) is an irredundant xy-path in G. *)

(** Due to the asymmetry in the definitions of of [path],[pathp], and [upath], these
are ill-suited for the symmetry reasoning prevalent in graph theory. We remedy
this by providing a type family of packaged paths [Path x y] which abstracts
away this asymmetry. We then lift many of the lemmas from the path library to
the setting of simple graphs. *)

(** ** Unpackaged Paths *)

Section PathP.
Variable (T : relType).
Implicit Types (x y : T) (p : seq T).

Definition pathp x y p := path (--) x p && (last x p == y).

Lemma pathpW y x p : pathp x y p -> path (--) x p.

Lemma pathp_last y x p : pathp x y p -> last x p = y.

Lemma pathp_cat x y p1 p2 : 
  pathp x y (p1++p2) = (pathp x (last x p1) p1) && (pathp (last x p1) y p2).

Lemma pathp_concat x y z p q : 
  pathp x y p -> pathp y z q -> pathp x z (p++q).

Lemma pathpxx x : pathp x x [::].

Lemma pathp_nil x y : pathp x y [::] -> x = y.

Lemma pathp_cons x y z p : 
  pathp x y (z :: p) = x -- z && pathp z y p. 

Lemma pathp_rcons x y z p: pathp x y (rcons p z) -> y = z.

Lemma rcons_pathp x y p : path (--) x (rcons p y) = pathp x y (rcons p y).

CoInductive pathp_split z x y : seq T -> Prop := 
  PPSplit p1 p2 : pathp x z p1 -> pathp z y p2 -> pathp_split z x y (p1 ++ p2).

Lemma ppsplitP z x y p : z \in x :: p -> pathp x y p -> pathp_split z x y p.

Lemma pathp_shorten x y p :
  pathp x y p -> exists p', [/\ pathp x y p', uniq (x::p') & {subset p' <= p}].

(** Irredundant paths *)

Definition upath x y p := uniq (x::p) && pathp x y p.

Lemma upathW x y p : upath x y p -> pathp x y p.

Lemma upathWW x y p : upath x y p -> path (--) x p.

Lemma upath_uniq x y p : upath x y p -> uniq (x::p).

Lemma upath_cons x y z p : 
  upath x y (z::p) = [&& x -- z, x \notin (z::p) & upath z y p].

Lemma upath_consE x y z p : 
  upath x y (z :: p) -> [/\ x -- z, x \notin z :: p & upath z y p].

Lemma upath_nil x p : upath x x p -> p = [::].

End PathP.

(** Lifting Lemmas for unpackaged paths *)

Lemma subrel_pathp (T : finType) (e1 e2 : rel T) (x y : T) (p : seq T) :
  subrel e1 e2 -> @pathp (RelType e1) x y p -> @pathp (RelType e2) x y p.

Lemma lift_pathp_on (G H : relType) (f : G -> H) a b p' : 
  (forall x y, f x \in f a :: p' -> f y \in f a :: p' -> f x -- f y -> x -- y) -> injective f -> 
  pathp (f a) (f b) p' -> {subset p' <= codom f} -> exists p, pathp a b p /\ map f p = p'.

Lemma lift_pathp (G H : relType) (f : G -> H) a b p' : 
  (forall x y, f x -- f y -> x -- y) -> injective f -> 
  pathp (f a) (f b) p' -> {subset p' <= codom f} -> exists p, pathp a b p /\ map f p = p'.

Lemma lift_upath_on (G H : relType) (f : G -> H) a b p' : 
  (forall x y, f x \in f a :: p' -> f y \in f a :: p' -> f x -- f y -> x -- y) -> injective f -> 
  upath (f a) (f b) p' -> {subset p' <= codom f} -> exists p, upath a b p /\ map f p = p'.

Lemma lift_upath (G H : relType) (f : G -> H) a b p' : 
  (forall x y, f x -- f y -> x -- y) -> injective f -> 
  upath (f a) (f b) p' -> {subset p' <= codom f} -> exists p, upath a b p /\ map f p = p'.

(** ** Packaged paths *)

(** We now define packaged paths (i.e., a vertex-indexed collection of
types [Path x y] whose elements are the paths between [x] and [y]). In
particular, this abstracts from the asymmetry in [spath x y p] which
states that [x::p] is an xy-path (paths are never empty). *)

Section Pack.
Variables (T : relType).
Implicit Types x y z : T.

Section PathDef.
  Variables (x y : T).

  Record Path : predArgType := { pval : seq T; _ : pathp x y pval }.

  HB.instance Definition _ := [isSub for pval].
  HB.instance Definition _ := [Countable of Path by <:].

  Record UPath : predArgType := { uval : seq T; _ : upath x y uval }.

  HB.instance Definition _ := [isSub for uval].
  HB.instance Definition _ := [Countable of UPath by <:].

End PathDef.
End Pack.

(** constructor for [Path x (last x p)] given [pth_p : path (--) x p] *)
Lemma Path_of_proof (G : relType) (x : G) (p : seq G) : 
  path (--) x p -> pathp x (last x p) p.

Definition Path_of_path (G : relType) (x : G) (p : seq G) (pth_p : path (--) x p)
  := Build_Path (Path_of_proof pth_p).

Section PathOps.
Variables (T : relType) (x y z : T) (p : Path x y) (q : Path y z).

Definition nodes := locked (x :: val p).
Lemma nodesE : nodes = x :: val p. by rewrite /nodes -lock. Qed.
Definition irred := uniq nodes.
Lemma irredE : irred = uniq nodes. by []. Qed.
Definition tail := val p.

Definition pcat_proof := pathp_concat (valP p) (valP q).
Definition pcat : Path x z := Sub (val p ++ val q) pcat_proof.

Lemma path_last: last x (val p) = y.

End PathOps.

Definition in_nodes (T : relType) (x y : T) (p : Path x y) : collective_pred T := 
  [pred u | u \in nodes p].
Canonical Path_predType (T : relType) (x y :T) := 
  Eval hnf in @PredType T (Path x y) (@in_nodes T x y).
Coercion in_nodes : Path >-> collective_pred.

Section PathTheory.
Variable (G : relType).
Implicit Types (x y z u : G).

Lemma nodes_eqE x y (p q : Path x y) : (nodes p == nodes q) = (p == q).

Lemma mem_path x y (p : Path x y) u : u \in p = (u \in nodes p).

Section Fixed.
Variables (x y z : G) (p : Path x y) (q : Path y z).

Lemma in_tail : z != x -> z \in p -> z \in tail p.

Lemma path_end : y \in p. 

Lemma path_begin : x \in p.

Lemma mem_pcatT u : (u \in pcat p q) = (u \in p) || (u \in tail q).

Lemma tailW : {subset tail q <= q}.

Lemma mem_pcat u :  (u \in pcat p q) = (u \in p) || (u \in q).

Lemma nodes_pcat : nodes (pcat p q) = nodes p ++ behead (nodes q).

End Fixed.

Lemma pcatA u v x y (p : Path u v) (q : Path v x) (r : Path x y) : 
  pcat (pcat p q) r = pcat p (pcat q r).

(** The one-node path *)

Definition idp (u : G) := Build_Path (pathpxx u).

Lemma mem_idp (x u : G) : (x \in idp u) = (x == u).

Lemma irred_idp (x : G) : irred (idp x).

Lemma pcat_idL (x y : G) (p : Path x y) : 
  pcat (idp x) p = p.

Lemma pcat_idR (x y : G) (p : Path x y) : 
  pcat p (idp y) = p.

Lemma irredxx (x : G) (p : Path x x) : irred p -> p = idp x.

(** Paths with a single edge using an injection from (proofs of) [x -- y] *)

Lemma edgep_proof x y (xy : x -- y) : pathp x y [:: y]. 

Definition edgep x y (xy : x -- y) := Build_Path (edgep_proof xy).

Lemma mem_edgep x y z (xy : x -- y) :
  z \in edgep xy = (z == x) || (z == y).

Lemma mem_pcat_edgeL x y z (xy : x -- y) (p : Path y z) u : 
  (u \in pcat (edgep xy) p) = (u == x) || (u \in p).

Lemma mem_pcat_edgeR x y z (yz : y -- z) (p : Path x y) u : 
  (u \in pcat p (edgep yz)) = (u == z) || (u \in p).

Lemma edgeLP x y z (xy : x -- y) (p : Path y z) u : 
  reflect (u = x \/ u \in p) (u \in pcat (edgep xy) p).

(** These are easier to prove by breaking the abstraction barrier than by using
[irred_cat] below. *)

Lemma irred_edge x y (xy: x -- y) : irred (edgep xy) = (x != y).

Lemma irred_edgeL y x z1 (xz1 : x -- z1) (p : Path z1 y) : 
  irred (pcat (edgep xz1) p) = (x \notin p) && irred p.

Lemma irred_edgeR y x z (yz : y -- z) (p : Path x y) : 
  irred (pcat p (edgep yz)) = (z \notin p) && irred p.

(** Induction principles for packaged paths *)

Lemma Path_ind (P : forall x x0 : G, Path x x0 -> Type) (y : G) (x : G) (p : Path x y) :
  P y y (idp y) ->
  (forall (x z : G) (p : Path z y) (xz : x -- z), P z y p -> P x y (pcat (edgep xz) p)) ->
  P x y p.

Lemma irred_ind P (y : G) :
  P y y (idp y) ->
  (forall x z (p : Path z y) (xz : x -- z),
      irred p -> x \notin p -> P z y p -> P x y (pcat (edgep xz) p)) ->
  forall x (p : Path x y), irred p -> P x y p.

Lemma path_closed (A : pred G) x y (p : Path x y) : 
  x \in A -> (forall y z, y \in A -> y -- z -> z \in A) -> {subset p <= A}.

Lemma uncycle x y (p : Path x y) :
  exists2 p' : Path x y, {subset p' <= p} & irred p'.

End PathTheory.
Definition inE := (inE,mem_pcat,path_begin,path_end).

(** NOTE: Up to here, nothing depends on the vertex type being finite. The
constuctions below make use of functions that are only defined on finite types,
e.g., [connect] or [#|G|] *)

(* 
Record diGraph := DiGraph { di_vertex : finType; 
                            di_edge : rel di_vertex }.

Canonical digraph_relType (D : diGraph) := RelType (@di_edge D).
Coercion digraph_relType : diGraph >-> relType.
Coercion di_vertex : diGraph >-> finType.
Prenex Implicits di_edge. 
*)

(** The simple setup above causes the coercion to [finType] to be different from
(but convertible to) the coercions to [choiceType]. This causes [auto] and hence
[trivial] and [by] to fail. *)

Notation diGraph := relType.
Notation DiGraph := RelType.
Goal forall (T : diGraph) (A : pred T), A \subset [set: T]. by []. Qed.

Section DiGraphTheory.
Variables (D : diGraph).
Implicit Types (x y : D).

Lemma upath_size x y p : upath x y p -> size p < #|D|.

CoInductive usplit z x y : seq D -> Prop := 
  USplit p1 p2 : upath x z p1 -> upath z y p2 -> [disjoint x::p1 & p2]
                 -> usplit z x y (p1 ++ p2).

Lemma usplitP z x y p : z \in x :: p -> upath x y p -> usplit z x y p.

Lemma upathP x y : reflect (exists p, upath x y p) (connect (--) x y).

Lemma pathpP x y : reflect (exists p, pathp x y p) (connect (--) x y).

(* Set Printing All. *)

Section Fixed.
Variables (x y z : D) (p : Path x y) (q : Path y z).

(** NOTE: [rewrite mem_pcat] requres [digraph_relType] to be canonical *)
Lemma subset_pcatL : p \subset pcat p q.

Lemma subset_pcatR : q \subset pcat p q.

Lemma pcat_subset (A : pred D) : p \subset A -> q \subset A -> pcat p q \subset A.

(** This is easy to prove and in some contetxs exactly what is needed. However,
it introduces an unpleasant asymmetry between [p] and [q]. *)
Lemma irred_catD :
  irred (pcat p q) = [&& irred p, irred q & [disjoint p & tail q]].

(** This lemma is more symmetric than [irred_catD], but the set equality is
sometimes cumbersome to use. *)
Lemma irred_cat : 
  irred (pcat p q) = [&& irred p, irred q & [set u : D in p | u \in q] == [set y]].

(** Introduction and elimination lemmas for [irred (pcat p q)] that avoid the
use of set equality *)
Lemma irred_catI : 
  (forall k : D, k \in p -> k \in q -> k = y) -> irred p -> irred q -> irred (pcat p q).

(** TODO: This lemma should be used instead of the [irred_cat] where appropriate *)
Lemma irred_catE : 
  irred (pcat p q) -> [/\ irred p, irred q & forall k, k \in p -> k \in q -> k = y].

End Fixed.

Lemma connect_irredP x y : 
  reflect (exists p : Path x y, irred p) (connect (--) x y).

Lemma Path_connect x y (p : Path x y) : connect (--) x y.

(** *** Splitting Paths **)

Lemma splitL x y (p : Path x y) : 
  x != y -> exists z xz (p' : Path z y), p = pcat (edgep xz) p' /\ p' =i tail p.

Lemma splitR x y (p : Path x y) : 
  x != y -> exists z (p' : Path x z) zy, p = pcat p' (edgep zy).

CoInductive psplit z x y : Path x y -> Prop := 
  PSplit (p1 : Path x z) (p2 : Path z y) : psplit z (pcat p1 p2).

Lemma psplitP z x y (p : Path x y) : z \in p -> psplit z p.

(** This should be the canonical way to split irredundant paths *)
CoInductive isplit z x y : Path x y -> Prop := 
  ISplit (p1 : Path x z) (p2 : Path z y) : 
    irred p1 -> irred p2 -> (forall k, k \in p1 -> k \in p2 -> k = z) -> isplit z (pcat p1 p2).

Lemma isplitP z x y (p : Path x y) : irred p -> z \in p -> isplit z p.

Lemma split_at_first_aux {A : pred D} x y (p : seq D) k : 
    pathp x y p -> k \in A -> k \in x::p -> 
    exists z p1 p2, [/\ p = p1 ++ p2, pathp x z p1, pathp z y p2, z \in A 
                & forall z', z' \in A -> z' \in x::p1 -> z' = z].

Lemma split_at_first {A : pred D} x y (p : Path x y) k :
  k \in A -> k \in p ->
  exists z (p1 : Path x z) (p2 : Path z y), 
    [/\ p = pcat p1 p2, z \in A & forall z', z' \in A -> z' \in p1 -> z' = z].

Lemma irred_is_edge (x y : D) (p : Path x y) :
  irred p -> x != y -> {subset p <= [set x;y]} -> exists xy : x -- y, p = edgep xy.

(** *** Between nodes (reflection lemmas) *)

(** NOTE: need to require either x != y or x \in A since packaged
paths are never empty *)
Lemma connect_irredRP {A : pred D} x y : x != y ->
  reflect (exists2 p: Path x y, irred p & p \subset A) 
          (connect (restrict A (--)) x y).

(* This is only useful if the [x = y] case does not require [x \in A] *)
Lemma connect_restrict_case x y (A : pred D) : 
  connect (restrict A (--)) x y -> 
  x = y \/ [/\ x != y, x \in A, y \in A & connect (restrict A (--)) x y].

Lemma connectRI (A : pred D) x y (p : Path x y) :
  {subset p <= A} -> connect (restrict A (--)) x y.

End DiGraphTheory.
Arguments connect_irredRP {D A x y}.
Arguments connectRI {D A x y} p.
Arguments irred_is_edge [D x y] p.

Section DiPathTheory.
Variable (G : diGraph).
Implicit Types (x y z : G).

Section Finite.
  Variables x y : G.
  Notation UPath := (UPath x y).

  Definition UPath_tuple (up : UPath) : {n : 'I_#|G| & n.-tuple G} :=
    let (p, Up) := up in existT _ (Ordinal (upath_size Up)) (in_tuple p).
  Definition tuple_UPath (s : {n : 'I_#|G| & n.-tuple G}) : option UPath :=
    let (_, p) := s in match boolP (upath x y p) with
      | AltTrue Up => Some (Sub (val p) Up)
      | AltFalse _ => None
    end.
  Lemma UPath_tupleK : pcancel UPath_tuple tuple_UPath.

  HB.instance Definition _ : isFinite UPath := PCanIsFinite UPath_tupleK.

  Definition UPathW (up : UPath) : Path x y := let (p, Up) := up in Sub p (upathW Up).
End Finite.

(** ** Packaged Irredundant Paths

Quantification over all paths is, a priori, undecidable. However,
quantification over irredundant paths is decidable and usually
sufficient. We define a type family of irredundant paths and endow it
with a finType structure. *)

Section IPath.
  Variables (x y : G).
  Record IPath : predArgType := { ival : Path x y; ivalP : irred ival }.

  HB.instance Definition _ := [isSub for ival].
  HB.instance Definition _ := [Countable of IPath by <:].

  Lemma upath_irred p (Up : upath x y p) : irred (Build_Path (upathW Up)).

  Lemma irred_upath (p : Path x y) : irred p -> upath x y (val p).

  Definition irred_of (p0 : UPath x y) : IPath := 
    let (p,Up) := p0 in (Sub (Build_Path (upathW Up)) (upath_irred Up)).
  Definition upath_of (p0 : IPath) : UPath x y := 
    let (p,Ip) := p0 in Sub (val p) (irred_upath Ip).

  Lemma can_irred_of : cancel upath_of irred_of. 

  HB.instance Definition _ : isFinite IPath := CanIsFinite can_irred_of.

  Definition path_of_ipath (p : IPath) := ival p. 
  Definition in_ipath p x := x \in path_of_ipath p.
  Canonical IPath_predType := Eval hnf in @PredType G (IPath) in_ipath.
  Coercion path_of_ipath : IPath >-> Path.
End IPath.

End DiPathTheory.
#[export]
Hint Resolve ivalP : core.

(** In some constructions a vertex can be typed as belonging to different
graphs. This makes [Path x y] or [x -- y] insufficent for understanding the
proofs. In these contexts one can open the implicit scope to display implicit
types for the most frequently used constructions *)

Declare Scope implicit_scope.
Notation "x -- y :> G" := (@edge_rel G x y) (at level 30, y at next level) : implicit_scope.
Notation "'PATH' G x y" := (@Path G x y) (at level 4) : implicit_scope.
Notation "'IPATH' G x y" := (@IPath G x y) (at level 4) : implicit_scope.

(** ** Basic Constructions on digraphs *)

(** *** Induced Subgraphs *)

Section InducedSubgraph.
  Variables (G : diGraph) (S : {set G}).

  Definition induced_type := { x | x \in S}.

  Definition induced_rel := [rel x y : induced_type | val x -- val y].

  Definition induced := DiGraph induced_rel.

End InducedSubgraph.

Lemma path_to_induced (G : diGraph) (S : {set G}) (x y : induced S) p' : 
  @pathp G (val x) (val y) p' -> {subset p' <= S} -> 
  exists2 p, pathp x y p & p' = map val p.

Lemma induced_path (G : diGraph) (S : {set G}) (x y : induced S) (p : seq (induced S)) : 
  pathp x y p -> @pathp G (val x) (val y) (map val p).

Lemma Path_to_induced (G : diGraph) (S : {set G}) (x y : induced S) 
  (p : Path (val x) (val y)) : {subset p <= S} -> exists q : Path x y, map val (nodes q) = nodes p.

Lemma Path_from_induced (G : diGraph) (S : {set G}) (x y : induced S) (p : Path x y) : 
  { q : Path (val x) (val y) | {subset q <= S} & nodes q = map val (nodes p) }.

(** *** Edge Deletion *)

Definition num_edges (G : diGraph) := #|[pred x : G * G | x.1 -- x.2]|.

Section DelEdge.

Variable (G : diGraph) (a b : G).

Definition del_rel a b := [rel x y : G | x -- y && ((x != a) || (y != b))].

Definition del_edge := DiGraph (del_rel a b).

Definition subrel_del_edge : subrel (del_rel a b) (@edge_rel G).

Hypothesis ab : a -- b.

Lemma card_del_edge : num_edges del_edge < num_edges G.

(** This is the fundamental case analysis for irredundant paths in [G] in
terms of paths in [del_edge a b] *)

(** TOTHINK: The proof below is a slighty messy induction on
[p]. Informally, one would simply check wether [nodes p] contains and
[a] followed by a [b] *)
Lemma del_edge_path_case (x y : G) (p : Path x y) (Ip : irred p) :
    (exists (p1 : @IPath del_edge x a) (p2 : @IPath del_edge b y), 
        [/\ nodes p = nodes p1 ++ nodes p2, a \notin p2 & b \notin p1])
  \/ (exists p1 : @IPath del_edge x y, nodes p = nodes p1).

End DelEdge.

Lemma del_edge_lift_proof (G : diGraph) (a b x y : G) p : 
  @pathp (del_edge a b) x y p -> @pathp G x y p.

(** ** Interior of irredundant paths *)

(* TOTHINK: This definition really only makes sense for irredundant paths *)
Section Interior.
Variable (G : diGraph) (x y : G).
Implicit Types (p : Path x y).

Definition interior p := [set x in p] :\: [set x;y].

Lemma interior_edgep (xy : x -- y) : interior (edgep xy) = set0.

Lemma interiorN p z : z \in interior p -> z \notin [set x; y].

Lemma interiorW p z : z \in interior p -> z \in p.

Lemma interior0E p : x != y -> irred p -> interior p = set0 -> exists xy, p = edgep xy.

Definition independent (p q : Path x y) := 
  [disjoint interior p & interior q].

Lemma independent_sym (p q : Path x y):
  independent p q -> independent q p.

End Interior.

(** The lemma below loses the connection between [p1]/[p2] and
[p1']/[p2']. However adding [p1' \subset p1] and [p2' \subset p2]
means that we would only get [interior p1' :|: interior p2' != set0] *)
Lemma disjoint_part (G : diGraph) (x y : G) (p1 p2 : Path x y) : 
  irred p1 -> irred p2 -> p1 != p2 -> 
  exists (x' y' : G) (p1' p2' : IPath x' y'), independent p1' p2' /\ interior p1' != set0.

Section Transfer.
  Variables (T : finType) (e1 e2 : rel T).
  Let D1 := DiGraph e1.
  Let D2 := DiGraph e2.
  Variables (x y : T) (p p' : @Path D1 x y) (q q' : @Path D2 x y).
  Hypothesis Npq : nodes p = nodes q.
  Hypothesis Npq' : nodes p' = nodes q'.

  Lemma irred_eq_nodes : irred p = irred q.

  Lemma mem_eq_nodes : p =i q.

  Lemma interior_eq_nodes : interior p = interior q.

End Transfer.

Lemma independent_nodes (T : finType) (e1 e2 : rel T) x y (p p' : @Path (DiGraph e1) x y) 
  (q q' : @Path (DiGraph e2) x y) (Npq : nodes p = nodes q) (Npq' : nodes p' = nodes q') : 
  independent p p' = independent q q'.

(** ** Isomorphisms *)

Definition is_dhom (F G: diGraph) (h: F -> G): Prop := forall x y, x -- y -> h x -- h y.

Lemma dhom_id G: @is_dhom G G id.

Lemma dhom_comp F G H h k:
  @is_dhom F G h -> @is_dhom G H k -> is_dhom (k \o h).

Record diso (F G: diGraph): Type := Diso
  { diso_v:> bij F G;
    diso_hom: is_dhom diso_v;
    diso_hom': is_dhom diso_v^-1 }.

Lemma edge_diso F G (h: diso F G) x y: h x -- h y = x -- y.

(* TODO: scope ... *)
Notation "F ≃ G" := (diso F G) (at level 79).

Definition diso_id {A}: diso A A := @Diso A A bij_id (@dhom_id A) (@dhom_id A). 

Definition diso_sym {A B}: diso A B -> diso B A.

Definition diso_comp {A B C}: diso A B -> diso B C -> diso A C.

#[export] Instance diso_Equivalence: Equivalence diso.
constructor. exact @diso_id. exact @diso_sym. exact @diso_comp. Defined.

Lemma edge_diso' F G (h: diso F G) x y: h^-1 x -- h^-1 y = x -- y.

Lemma Diso' [F G : diGraph] [f : F -> G] [g : G -> F] : 
  cancel f g -> cancel g f -> {mono f : x y / x -- y} -> F ≃ G.

Lemma Diso'' (F G: diGraph) (f: F -> G) (g: G -> F):
  cancel f g -> cancel g f ->
  (forall x y, x--y -> f x -- f y) -> (forall x y, x--y -> g x -- g y) -> diso F G.

(** *** Induced Subgraphs *)

(** A graph [G] contains a graph [F] as in induced subgraph, written
[F ⇀ G], if there exists an injection from [F] to [G] that preserves
edges in both directions. In particular, we have [induced A ⇀ G] for
every [A : {set G}]. *)

(* This is almost the same statement as the [Diso'] constructor in
digraph.v, but the {mono f: ...} assumtion is better behaved in
proofs. So this should replace the old lemma. *)

(** [G] contains [F] as an induced subgraph *)
Record isubgraph (F G : diGraph) := 
  ISubgraph { isubgraph_fun :> F -> G ; 
              isubgraph_inj : injective isubgraph_fun ; 
              isubgraph_mono : {mono isubgraph_fun : x y / x -- y} }.
Arguments isubgraph_inj [F G] i.
Notation "F ⇀ G" := (isubgraph F G) (at level 30).

Lemma isubgraph_iso (F G : diGraph) (i : F ⇀ G) : #|G| <= #|F| -> F ≃ G.

Lemma isubgraph_comp (F G H : diGraph) (i : F ⇀ G) (j : G ⇀ H) : F ⇀ H.

(** ** Unindexed paths *)

(** In order to define the notion of [AB]-connector, we need to
abstract from the incices in [Path x y] *)

Section PathS.
Variable (G : diGraph).

Definition pathS := { x : G * G & Path x.1 x.2 }.
Definition PathS x y (p : Path x y) : pathS := existT (fun x : G * G => Path x.1 x.2) (x,y) p.

Definition in_pathS (p : pathS) : collective_pred G := [pred x | x \in tagged p].
Canonical pathS_predType := Eval hnf in PredType (@in_pathS).
Arguments in_pathS _ /.

(** We can override fst because MathComp uses .1 *)
Definition fst (p : pathS) := (tag p).1.
Definition lst (p : pathS) := (tag p).2.
Arguments fst _ /.
Arguments lst _ /.

Lemma pathS_eta (p : pathS) : 
  p = @PathS (fst p) (lst p) (tagged p).

Lemma fst_mem (p : pathS) : fst p \in p.

Lemma lst_mem (p : pathS) : lst p \in p.

(** Concatenation on [pathS] *)

Definition castL (x' x y : G) (E : x = x') (p : Path x y) : Path x' y :=
  match E in (_ = y0) return (Path y0 y) with erefl => p end.

Definition pcatS (p1 p2 : pathS) : pathS :=
  let: (existT x p,existT y q) := (p1,p2) in
  match altP (y.1 =P x.2) with
    AltTrue E => PathS (pcat p (castL E q))
  | AltFalse _ => PathS p
  end.

Lemma pcatSE (x y z : G) (p : Path x y) (q : Path y z) : 
  pcatS (PathS p) (PathS q) = PathS (pcat p q).

End PathS.

Definition del_edge_liftS (G : diGraph) (a b : G) (p : pathS (del_edge a b)) :=
  let: existT (x,y) p' := p in PathS (Build_Path (del_edge_lift_proof (valP p'))).

Lemma mem_del_edge_liftS (G : diGraph) (a b : G) (p : pathS (del_edge a b))  x : 
  (x \in del_edge_liftS p) = (x \in p).

(** ** Neighborhoods *)

Section Neighborhood_def.

Variable G : diGraph.

Definition open_neigh (u : G) := [set v | u -- v].
Local Notation "N( x )" := (open_neigh x) (at level 0, format "N( x )").

Definition closed_neigh (u : G) := u |: N(u).
Local Notation "N[ x ]" := (closed_neigh x) (at level 0, format "N[ x ]").

Definition dominates (u v : G) : bool := (u == v) || (u -- v).

Variable D : {set G}.

Definition open_neigh_set : {set G} := \bigcup_(w in D) N(w).

Definition closed_neigh_set : {set G} := \bigcup_(w in D) N[w].

End Neighborhood_def.

Notation "x -*- y" := (dominates x y) (at level 30).

Notation "N( x )" := (@open_neigh _ x) 
   (at level 0, format "N( x )").
Notation "N[ x ]" := (@closed_neigh _ x) 
   (at level 0, format "N[ x ]").
Notation "N( G ; x )" := (@open_neigh G x)
   (at level 0, only parsing).
Notation "N[ G ; x ]" := (@closed_neigh G x)
   (at level 0, only parsing).
   
Notation "NS( G ; D )" := (@open_neigh_set G D) 
   (at level 0, only parsing).
Notation "NS( D )" := (open_neigh_set D) 
   (at level 0, format "NS( D )").
Notation "NS[ G ; D ]" := (@closed_neigh_set G D) 
   (at level 0, only parsing).
Notation "NS[ D ]" := (closed_neigh_set D) 
   (at level 0, format "NS[ D ]").

Notation "N( G ; x )" := (@open_neigh G x)
   (at level 0, format "N( G ; x )") : implicit_scope.
Notation "N[ G ; x ]" := (@closed_neigh G x)
   (at level 0, format "N[ G ; x ]") : implicit_scope.

Section Basic_Facts_Neighborhoods.

Variable G : diGraph.
Implicit Types (u v : G).

Lemma dominates_refl : reflexive (@dominates G). 

Lemma in_opn u v : u \in N(v) = (v -- u).

Lemma in_cln u v : u \in N[v] = (v -*- u). 

Lemma opns0 : NS(G;set0) = set0. 

Lemma clns0 : NS[G;set0] = set0.

Variables D1 D2 : {set G}.

Lemma opn_sub_opns v : v \in D1 -> N(v) \subset NS(D1).

Lemma cln_sub_clns v : v \in D1 -> N[v] \subset NS[D1].

Lemma v_in_clneigh v : v \in N[v].

Lemma set_sub_clns : D1 \subset NS[D1].

Lemma mem_opns u v : u \in D1 -> u -- v -> v \in NS(D1).

Lemma opns_sub_clns : NS(D1) \subset NS[D1].

Lemma mem_clns u v : u \in D1 -> u -- v -> v \in NS[D1].

Lemma subset_clns : D1 \subset D2 -> NS[D1] \subset NS[D2]. 

End Basic_Facts_Neighborhoods.
```

## sgraph.v
```coq
From Coq Require Import Setoid CMorphisms.
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import edone preliminaries bij digraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Simple Graphs

This file defines (finite) simple graphs, i.e. undirected and
unlabeled graphs without self-loops. *)

Record sgraph := SGraph { svertex : finType ; 
                          sedge: rel svertex; 
                          sg_sym': symmetric sedge;
                          sg_irrefl': irreflexive sedge}.

Canonical digraph_of (G : sgraph) := DiGraph (@sedge G).
Coercion digraph_of : sgraph >-> diGraph.

(** The notation [x -- y] is now inherited *)
(* Notation "x -- y" := (sedge x y) (at level 30). *)

Definition sg_sym (G : sgraph) : @symmetric G (--). exact: sg_sym'. Qed.
Definition sg_irrefl (G : sgraph) : @irreflexive G (--). exact: sg_irrefl'. Qed.

Definition sgP := (sg_sym,sg_irrefl).
Prenex Implicits sedge.

Lemma sg_edgeNeq (G : sgraph) (x y : G) : x -- y -> (x == y = false).

Lemma sconnect_sym (G : sgraph) : @connect_sym G (--). 

Lemma sedge_equiv (G : sgraph) : 
  equivalence_rel (connect (@sedge G)).

Lemma symmetric_restrict_sedge (G : sgraph) (A : pred G) :
  symmetric (restrict A (--)).

Lemma srestrict_sym (G : sgraph) (A : pred G) :
  connect_sym (restrict A (--)).

Lemma sedge_in_equiv (G : sgraph) (A : {set G}) :
  equivalence_rel (connect (restrict A (--))).

Lemma sedge_equiv_in (G : sgraph) (A : {set G}) :
  {in A & &, equivalence_rel (connect (restrict A (--)))}.

Declare Scope sgraph_scope.
Delimit Scope sgraph_scope with sg.
Bind Scope sgraph_scope with sgraph.

(** ** Disjoint Union *)

Section JoinSG.
  Variables (G1 G2 : sgraph).
  
  Definition join_rel (a b : G1 + G2) := 
    match a,b with
    | inl x, inl y => x -- y
    | inr x, inr y => x -- y
    | _,_ => false
    end.

  Lemma join_rel_sym : symmetric join_rel.

  Lemma join_rel_irrefl : irreflexive join_rel.

  Definition sjoin := SGraph join_rel_sym join_rel_irrefl. 

  Lemma join_disc (x : G1) (y : G2) : 
    connect join_rel (inl x) (inr y) = false.

End JoinSG.

Notation "G ∔ H" := (sjoin G H) (at level 20, left associativity) : sgraph_scope.

Lemma sjoin_disconnected (G H : sgraph) (x : G) (y : H) :
  ~~ connect (--) (inl x : (G ∔ H)%sg) (inr y).

Prenex Implicits join_rel.

(** ** Homomorphisms *)

Definition hom_s (G1 G2 : sgraph) (h : G1 -> G2) := 
  forall x y, x -- y -> h x != h y -> (h x -- h y).

Definition subgraph (S G : sgraph) := 
  exists2 h : S -> G, injective h & hom_s h.

Section InducedSubgraph.
  Variables (G : sgraph) (S : {set G}).

  Definition induced_type := { x | x \in S}.

  Definition induced_rel := [rel x y : induced_type | val x -- val y].

  Lemma induced_sym : symmetric induced_rel.  
         
  Lemma induced_irrefl : irreflexive induced_rel.  

  Definition induced := SGraph induced_sym induced_irrefl.

  Lemma induced_sub : subgraph induced G.

  Lemma induced_edge (x y : induced) : (x -- y) = (val x -- val y).

  Lemma ucycle_induced (s : seq induced) : 
    ucycle (--) s = ucycle (--) [seq val x | x <- s].
  
  Lemma sub_induced (A : {set induced}) : val @: A \subset S.

End InducedSubgraph.

(** Link to isubgraph *)
Lemma induced_isubgraph (G : sgraph) (A : {set G}) : induced A ⇀ G.

Lemma isubgraph_induced (F G : sgraph) (i : F ⇀ G) : 
  F ≃ induced [set x in codom i].

Definition srestrict (G : sgraph) (A : pred G) :=
  Eval hnf in SGraph (restrict_sym A (@sg_sym G))
                     (restrict_irrefl A (@sg_irrefl G)).

(** ** Isomorphism of simple graphs *)

Lemma eq_diso (T : finType) (e1 e2 : rel T) 
  (e1_sym : symmetric e1) (e1_irrefl : irreflexive e1) 
  (e2_sym : symmetric e2) (e2_irrefl : irreflexive e2) :
e1 =2 e2 -> diso (SGraph e1_sym e1_irrefl) (SGraph e2_sym e2_irrefl).

Lemma iso_subgraph (G H : sgraph) : diso G H -> subgraph G H.

(** Splitting off disconnected parts *)
Lemma ssplit_disconnected (G:sgraph) (V : {set G}) : 
  (forall x y, x \in V -> y \notin V -> ~~ x -- y) ->
  diso (sjoin (induced V) (induced (~: V))) G.

(** ** Unpackaged Simple Paths

We establish those properties of [pathp] and [upath] that require symmetry or
irreflexivity, i.e. path reversal *)

Section SimplePaths.
Variable (G : sgraph).
Implicit Types (x y z : G).

Definition srev x p := rev (belast x p).

Lemma last_rev_belast x y p : 
  last x p = y -> last y (srev x p) = x.

Lemma path_srev x p : 
  path (--) x p = path (--) (last x p) (srev x p).

Lemma srev_rcons x z p : srev x (rcons p z) = rcons (rev p) x.

(** Note that the converse of the following does not hold since [srev
x p] forgets the last element of [p]. Consequently, double reversal
only cancels if the right nodes are added back. *)
Lemma pathp_rev x y p : pathp x y p -> pathp y x (srev x p).

Lemma srevK x y p : last x p = y -> srev y (srev x p) = p.

Lemma srev_nodes x y p : pathp x y p -> x :: p =i y :: srev x p.

Lemma rev_upath x y p : upath x y p -> upath y x (srev x p).

Lemma upath_sym x y : unique (upath x y) -> unique (upath y x).

End SimplePaths.

Lemma upathPR (G : sgraph) (x y : G) A :
  reflect (exists p : seq G, @upath (srestrict A) x y p)
          (connect (restrict A (--)) x y).

(* TOTHINK: is this the best way to transfer path from induced subgraphs *)
Lemma induced_path (G : sgraph) (S : {set G}) (x y : induced S) (p : seq (induced S)) : 
  pathp x y p -> @pathp G (val x) (val y) (map val p).

Section Packaged.
Variables (G : sgraph).
Implicit Types x y z : G.

Section Prev.
Variables (x y z : G) (p : Path x y) (q : Path y z).

Definition prev_proof := pathp_rev (valP p).
Definition prev : Path y x := Sub (srev x (val p)) prev_proof.

End Prev.

Lemma prevK x y (p : Path x y) : prev (prev p) = p.

Lemma prev_inj x y : injective (@prev x y).

Lemma mem_prev x y (p : Path x y) u : (u \in prev p) = (u \in p).

Lemma nodes_prev (x y : G) (p : Path x y) : 
  nodes (prev p) = rev (nodes p).

Definition inE := (inE,mem_prev).

Lemma prev_cat x y z (p : Path x y) (q : Path y z) :
  prev (pcat p q) = pcat (prev q) (prev p).

Lemma prev_irred x y (p : Path x y) : irred p -> irred (prev p).

Lemma irred_rev x y (p : Path x y) : irred (prev p) = irred p.

(** Paths with a single edge using an injection from (proofs of) [x -- y] *)

Fact prev_edge_proof x y (xy : x -- y) : y -- x. by rewrite sgP. Qed.
Lemma prev_edge x y (xy : x -- y) : prev (edgep xy) = edgep (prev_edge_proof xy).

Lemma irred_edge x y (xy : x -- y) : irred (edgep xy).

(** TODO: The following lemma hold for digraphs, but the proof uses
symmetry of the edge relation *)
                                                                
Lemma split_at_last {A : pred G} (x y : G) (p : Path x y) (k : G) : 
  k \in A -> k \in p ->
  exists (z : G) (p1 : Path x z) (p2 : Path z y),
    [/\ p = pcat p1 p2, z \in A & forall z' : G, z' \in A -> z' \in p2 -> z' = z].

End Packaged.

#[export]
Hint Resolve path_begin path_end : core.

(** *** Transporting paths to and from induced subgraphs *)

Lemma path_to_induced (G : sgraph) (S : {set G}) (x y : induced S) p' : 
  @pathp G (val x) (val y) p' -> {subset p' <= S} -> 
  exists2 p, pathp x y p & p' = map val p.

Lemma Path_to_induced (G : sgraph) (S : {set G}) (x y : induced S) 
  (p : Path (val x) (val y)) : 
  {subset p <= S} -> exists q : Path x y, map val (nodes q) = nodes p.

Lemma Path_from_induced (G : sgraph) (S : {set G}) (x y : induced S) (p : Path x y) : 
  { q : Path (val x) (val y) | {subset q <= S} & nodes q = map val (nodes p) }.

(* TOTHINK: Use this to prove the lemmas above? *)
Lemma lift_Path_on (G H : sgraph) (f : G -> H) a b (p' : Path (f a) (f b)) : 
  (forall x y, f x \in p' -> f y \in p' -> f x -- f y -> x -- y) -> injective f -> {subset p' <= codom f} -> 
  exists2 p : Path a b, map f (nodes p) = nodes p' & irred p = irred p'.

Lemma lift_Path (G H : sgraph) (f : G -> H) a b (p' : Path (f a) (f b)) : 
  (forall x y, f x -- f y -> x -- y) -> injective f -> {subset p' <= codom f} -> 
  exists2 p : Path a b, map f (nodes p) = nodes p' & irred p = irred p'.

(** *** Path indexing and 3-way split *)

Definition idx (G : sgraph) (x y : G) (p : Path x y) u := index u (nodes p).

(* TOTHINK: This only parses if the level is at most 10, why? *)
Notation "x '<[' p ] y" := (idx p x < idx p y) (at level 10, format "x  <[ p ]  y").
(* (at level 70, p at level 200, y at next level, format "x  <[ p ]  y"). *)

Section PathIndexing.
  Variables (G : sgraph).
  Implicit Types x y z : G.

  Lemma idx_mem x y (p : Path x y) z :
    z \in p -> idx p z <= size (tail p).

  Lemma idx_start x y (p : Path x y) : idx p x = 0.

  Lemma idx_end x y (p : Path x y) : 
    irred p -> idx p y = size (tail p).

  Lemma idx_catL (x y z u v : G) (p : Path x y) (q : Path y z) :
    u \in p -> v \in p -> idx (pcat p q) u <= idx (pcat p q) v = (idx p u <= idx p v).

  Lemma idx_catR (x y z u v : G) (p : Path x y) (q : Path y z) :
    u \notin p -> v \notin p ->
    idx (pcat p q) u <= idx (pcat p q) v = (idx q u <= idx q v).

  Section IDX.
    Variables (x z y : G) (p : Path x z) (q : Path z y).
    Implicit Types u v : G.

    Lemma idx_inj : {in nodes p, injective (idx p) }.

    Hypothesis irr_pq : irred (pcat p q).
    
    Let dis_pq : [disjoint nodes p & tail q].

    Let irr_p : irred p. by case/irred_catE : irr_pq. Qed.

    Let irr_q : irred q. by case/irred_catE : irr_pq. Qed.

    Lemma idxR u : u \in pcat p q -> u \in tail q = z <[pcat p q] u.

    Lemma idx_nLR u : u \in nodes (pcat p q) -> 
      idx (pcat p q) z < idx (pcat p q) u -> u \notin nodes p /\ u \in tail q.
  
  End IDX.

  Lemma index_rcons (T : eqType) a b (s : seq T):
    a \in b::s -> uniq (b :: s) ->
    index a (rcons s b) = if a == b then size s else index a s.

  Lemma index_rev (T : eqType) a (s : seq T) : 
    a \in s -> uniq s -> index a (rev s) = (size s).-1 - index a s.
    
  Lemma idx_srev a x y (p : Path x y) : 
    a \in p -> irred p -> idx (prev p) a = size (pval p) - idx p a.

  Lemma idx_swap_aux a b x y (p : Path x y) : a \in p -> b \in p -> irred p ->
    idx p a < idx p b -> idx (prev p) b < idx (prev p) a.

  Lemma idx_swap a b x y (p : Path x y) :
    a \in p -> b \in p -> irred p -> a <[p] b = b <[prev p] a.

  Lemma three_way_split x y (p : Path x y) a b :
    irred p -> a \in p -> b \in p -> a <[p] b -> 
    exists (p1 : Path x a) (p2 : Path a b) p3, 
      [/\ p = pcat p1 (pcat p2 p3), a \notin p3 & b \notin p1].

End PathIndexing.

(** ** Connectedness *)

(** *** Of subsets *)

Definition connected (G : sgraph) (S : {set G}) :=
  {in S & S, forall x y : G, connect (restrict S edge_rel) x y}.

Lemma eq_connected (V : finType) (e1 e2 : rel V) (A : {set V}) 
  (e1_sym : symmetric e1) (e1_irrefl : irreflexive e1) 
  (e2_sym : symmetric e2) (e2_irrefl : irreflexive e2):
  e1 =2 e2 -> 
  @connected (SGraph e1_sym e1_irrefl) A <-> @connected (SGraph e2_sym e2_irrefl) A.

Definition disconnected (G : sgraph) (S : {set G}) :=
  exists x y : G, [/\ x \in S, y \in S & ~~ connect (restrict S edge_rel) x y].

Lemma disconnectedE (G : sgraph) (S : {set G}) : disconnected S <-> ~ connected S.

Lemma connectedTE (G : sgraph) : 
  connected [set: G] -> forall x y : G, connect (--) x y. 

Lemma connectedTI (G : sgraph) : 
  (forall x y : G, connect (--) x y) -> connected [set: G].

Lemma connected_restrict (G : sgraph) (A : pred G) x : 
  connected [set y | connect (restrict A (--)) x y].

Lemma connect_range (G : sgraph) (A : pred G) x : x \in A -> 
  [set y | connect (restrict A (--)) x y] = 
  [set y in A | connect (restrict A (--)) x y].

Lemma connected_restrict_in (G : sgraph) (A : pred G) x : x \in A -> 
  connected [set y in A | connect (restrict A (--)) x y].

(* NOTE: This could be generalized to sets and their images *)
Lemma iso_connected (G H : sgraph) :
  diso G H -> connected [set: H] -> connected [set: G].

Lemma connected0 (G : sgraph) : connected (@set0 G).

Lemma connected1 (G : sgraph) (x : G) : connected [set x].

Lemma connected2 (G : sgraph) (x y: G) : x -- y -> connected [set x; y].

Lemma connected_center (G:sgraph) x (S : {set G}) :
  {in S, forall y, connect (restrict S (--)) x y} -> x \in S ->
  connected S.

Lemma connectedU_common_point (G : sgraph) (U V : {set G}) (x : G):
  x \in U -> x \in V -> connected U -> connected V -> connected (U :|: V).

Lemma connectedU_edge (G : sgraph) (U V : {set G}) (x y : G) :
  x \in U -> y \in V -> x -- y -> connected U -> connected V -> connected (U :|: V).

Lemma path_in_connected (G:sgraph) (T : {set G}) x y : connected T -> x \in T -> y \in T ->
  exists2 p : Path x y, irred p & p \subset T.

Lemma connected_path (G : sgraph) (x y : G) (p : Path x y) :
  connected [set z in p].

Lemma connected_in_subgraph (G : sgraph) (S : {set G}) (A : {set induced S}) : 
  connected A -> connected [set val x | x in A].

Lemma connected_induced (G : sgraph) (S : {set G}) : 
  connected S -> connected [set: induced S].

Lemma connected_card_gt1 (G : sgraph) (S : {set G}) :
  connected S -> {in S &, forall x y, x != y -> exists2 z, z \in S & x -- z }.

(** *** Connected components *)

Definition components (G : sgraph) (H : {set G}) : {set {set G}} :=
  equivalence_partition (connect (restrict H (--))) H.

Lemma partition_components (G : sgraph) (H : {set G}) :
  partition (components H) H.

Lemma trivIset_components (G : sgraph) (U : {set G}) : trivIset (components U).

Lemma partition0 (T : finType) (P : {set {set T}}) (D : {set T}) :
  partition P D -> set0 \in P = false.
Arguments partition0 [T P] D.

#[export]
Hint Resolve partition_components trivIset_components : core.

Lemma components_pblockP (G : sgraph) (H : {set G}) (x y : G) :
  reflect (exists p : Path x y, p \subset H) (y \in pblock (components H) x).

Lemma components_nonempty (G : sgraph) (U C : {set G}) :
  C \in components U -> exists x, x \in C.

Lemma components_subset (G : sgraph) (U C : {set G}) : 
  C \in components U -> C \subset U.

Lemma connected_in_components (G : sgraph) (H C : {set G}) :
  C \in components H -> connected C.

Lemma connected_one_component (G : sgraph) (U C : {set G}) :
  C \in components U -> U \subset C -> connected U.

Lemma component_exit (G : sgraph) (V C : {set G}) (x y : G) :
  x -- y -> C \in components V -> x \in C -> y \in ~: V :|: C.

Lemma remove_component (G : sgraph) (V C : {set G}) (x0 : G) : x0 \notin V ->
  C \in components V -> connected [set: G] -> connected (~: V) -> connected (~: C).

(** Component of a given vertex *)

Definition component_of (G : sgraph) (x : G) := pblock (components [set: G]) x.

Lemma in_component_of (G : sgraph) (x : G) : x \in component_of x.

Lemma component_of_components (G : sgraph) (x : G) : 
  component_of x \in components [set: G].

Lemma connected_component_of (G : sgraph) (x : G) : 
  connected (component_of x). 

Lemma same_component (G : sgraph) (x y : G) : 
  x \in component_of y -> component_of x = component_of y.

Lemma component_exchange (G : sgraph) (x y : G) : 
  (y \in component_of x) = (x \in component_of y).

Lemma mem_component (G : sgraph) (C : {set G}) x : 
  C \in components [set: G] -> x \in C -> C = component_of x.

(** *** Cliques *)

Section Cliques.
Variables (G : sgraph).
Implicit Types S : {set G}.

Definition clique S := {in S&, forall x y, x != y -> x -- y}.

Definition cliqueb S := [forall x in S, forall y in S, (x != y) ==> x -- y]. 

Lemma cliqueP S : reflect (clique S) (cliqueb S).

Lemma cliquePn S : 
  reflect (exists x y, [/\ x \in S, y \in S, x != y & ~~ x -- y]) (~~ cliqueb S).

Lemma clique1 (x : G) : clique [set x].

Lemma clique2 (x y : G) : x -- y -> clique [set x;y].

Lemma small_clique (S : {set G}) : #|S| <= 1 -> clique S.

End Cliques.

(** ** Forests and Trees

As with connected, we define forest and set predicates for sets of
vertices of some graph. This avoids having to package subtrees (such
as [CP U] for neighbors U) as a graph *)

Section Forests.

Variables (G : sgraph).
Implicit Types (x y : G) (S : {set G}).

Definition is_forest S :=
  forall x y : G, unique (fun p : Path x y => irred p /\ (p \subset S)).

Definition is_tree S := is_forest S /\ connected S.

Definition is_forestb S := 
  [forall x, forall y, #|[pred p : IPath x y| val p \subset S]| <= 1] .

Lemma is_forestP S : reflect (is_forest S) (is_forestb S).

Lemma is_forestPn (S : {set G}) : 
  reflect (exists x y (p1 p2 : IPath x y), [/\ p1 \subset S, p2 \subset S & p1 != p2])
          (~~ is_forestb S).

Lemma forest3 : is_forest [set: G] -> 3 <= #|G| -> exists x y : G, x != y /\ ~~ x -- y.

Definition connectedb S := 
  [forall x in S, forall y in S, connect (restrict S (--)) x y].

Lemma connectedP S : reflect (connected S) (connectedb S).

Lemma forestT_unique : 
  is_forest [set: G] -> forall x y, unique (fun p : Path x y => irred p).

Lemma unique_forestT : 
  (forall x y, unique (fun p : Path x y => irred p)) -> is_forest [set: G].

Lemma forestI S : 
  ~ (exists x y (p1 p2 : Path x y), [/\ irred p1, irred p2 & p1 != p2] /\ 
     [/\ x \in S, y \in S, p1 \subset S & p2\subset S]) ->
  is_forest S.

Lemma treeI S : 
  connected S -> 
  ~ (exists x y (p1 p2 : Path x y), [/\ irred p1, irred p2 & p1 != p2] /\ 
     [/\ x \in S, y \in S, p1 \subset S & p2\subset S]) ->
  is_tree S.

Lemma sub_forest S S' : 
  S' \subset S -> is_forest S -> is_forest S'.

End Forests.

Lemma induced_forest (G : sgraph) (F : {set G}) : 
  is_forest F -> is_forest [set: induced F].

(** *** Forest Type (for tree decompositions) *)

(** We define forests to be simple graphs where there exists at most one
duplicate free path between any two nodes *)

Record forest := Forest { sgraph_of_forest :> sgraph ;
                          forest_is_forest :> is_forest [set: sgraph_of_forest] }.

Lemma forestP (T : forest) (x y : T) (p q : Path x y) :
  irred p -> irred q -> p = q.

Definition sunit := @SGraph unit rel0 rel0_sym rel0_irrefl.

Definition unit_forest : is_forest [set: sunit].

Definition tunit := Forest unit_forest.

(** Non-standard: we do not substract 1 *)
Definition width (T G : finType) (D : T -> {set G}) := \max_(t:T) #|D t|.

Lemma width_bound (T G : finType) (D : T -> {set G}) : width D <= #|G|.

Definition rename (T G G' : finType) (B: T -> {set G}) (h : G -> G') :=
  [fun x => h @: B x].

(** ** Complete graphs *)

Definition complete_rel n := [rel x y : 'I_n | x != y].
Fact complete_sym n : symmetric (@complete_rel n).
Fact complete_irrefl n : irreflexive (@complete_rel n).
Definition complete n := SGraph (@complete_sym n) (@complete_irrefl n).
Notation "''K_' n" := (complete n)
  (at level 8, n at level 2, format "''K_' n").

Definition C3 := 'K_3.
Definition K4 := 'K_4.

Lemma diso_Kn (G : sgraph) : (forall x y : G, x != y -> x -- y) -> diso G 'K_#|G|.

Lemma sub_Kn n (G : sgraph) : #|G| <= n -> subgraph G 'K_n.

(** ** Complete bipartite graphs *)
Section Knm.
Variables n m : nat.
Definition kb_rel (x y : 'I_n + 'I_m) := is_inl x (+) is_inl y.
Lemma kb_rel_sym : symmetric kb_rel. exact: addbC. Qed. 
Lemma kb_rel_irrefl : irreflexive kb_rel.
Definition KB := SGraph kb_rel_sym kb_rel_irrefl.

(** Injection from ['K_n,m] to nat, used to order the vertices to
break symmeties *)
Definition pickle_Knm (i : KB) : nat := 
  match i with inl (Ordinal k _) => k | inr (Ordinal k _) => n + k end.

Lemma pickle_Knn_inj : injective pickle_Knm.

End Knm.
Notation "''K_' n , m" := (KB n m)
  (at level 8, n at level 2, m at level 2,format "''K_' n , m").

Lemma Knm_connected n m : connected [set: 'K_n.+1,m.+1].

(** ** Adding Edges *)

Definition add_edge_rel (G:sgraph) (i o : G) := 
  relU (@edge_rel G) (sc [rel x y | [&& x != y, x == i & y == o]]).

Lemma add_edge_sym_ (G:sgraph) (i o : G) : symmetric (add_edge_rel i o).

Lemma add_edge_irrefl_ (G:sgraph) (i o : G) : irreflexive (add_edge_rel i o).

Definition add_edge (G:sgraph) (i o : G) :=
  {| svertex := G;
     sedge := add_edge_rel i o;
     sg_sym' := add_edge_sym_ i o;
     sg_irrefl' := add_edge_irrefl_ i o |}.

Lemma add_edge_Path (G : sgraph) (i o x y : G) (p : @Path G x y) :
  exists q : @Path (add_edge i o) x y, nodes q = nodes p.

Lemma add_edge_connected (G : sgraph) (i o : G) (U : {set G}) :
  @connected G U -> @connected (add_edge i o) U.

(** Lemmas to swap the nodes of add_edge, useful for wlog. reasoning *)

Lemma add_edgeC (G : sgraph) (s1 s2 : G):
  @edge_rel (add_edge s1 s2) =2 @edge_rel (add_edge s2 s1).
Arguments add_edgeC [G].

Lemma add_edge_sym (G : sgraph) (s1 s2 : G):
  diso (@add_edge G s1 s2) (@add_edge G s2 s1).

Lemma add_edge_connected_sym (G : sgraph) s1 s2 A:
  @connected (@add_edge G s1 s2) A <-> @connected (@add_edge G s2 s1) A.

Lemma add_edge_pathC (G : sgraph) (s1 s2 x y : G) (p : @Path (add_edge s1 s2) x y) :
  exists q : @Path (add_edge s2 s1) x y, nodes q = nodes p.

Lemma add_edge_avoid (G : sgraph) (s1 s2 x y : G) (p : @Path (add_edge s1 s2) x y) : 
  (s1 \notin p) || (s2 \notin p) -> exists q : @Path G x y, nodes q = nodes p.
Arguments add_edge_avoid [G s1 s2 x y] p.  

Lemma add_edge_subgraph (G : sgraph) (x y : G) : subgraph G (add_edge x y).

(** Andding all edges between two sets of vertices (i.e., adding a complete bipartite subgraph graph) *)

Section AddEdges2.
Variables (G : sgraph) (U V : {set G}).
Definition add_edges2_rel := 
  [rel u v : G | u -- v || (u != v) && ((u \in U) && (v \in V) || (u \in V) && (v \in U))].

Fact add_edges2_irrefl : irreflexive add_edges2_rel.

Fact add_edges2_sym : symmetric add_edges2_rel.

Definition add_edges2 := SGraph add_edges2_sym add_edges2_irrefl.
End AddEdges2.

Arguments add_edges2 : clear implicits.

(* TODO: load earlier *)
From GraphTheory Require Import set_tac.

Ltac set_tac_close_plus ::=
  match goal with
  (* coercion free variants ... *)                                                                         
  | [ H : is_true (?x \notin (pcat ?p ?q)) |- _] => 
    first[notHyp (x \notin p)|notHyp (x \notin q)];
    have/andP [? ?]: (x \notin p) && (x \notin q) by rewrite mem_pcat negb_or in H
  | [H : is_true (?u \notin (@edgep _ ?x ?y _)) |- _] => 
    first[notHyp (u != x)|notHyp (u != y)];
    have/andP[? ?]: (u != x) && (u != y) by (move: H; rewrite mem_edgep negb_or; apply)
  | [H : is_true (?x \notin ?p), p : Path ?x _ |- _] => by rewrite path_begin in H
  | [H : is_true (?x \notin ?p), p : Path _ ?x |- _] => by rewrite path_end in H
  (* variant with coercions ... TOHINK: remove? *)
  | [ H : is_true (?x \notin _ (pcat ?p ?q)) |- _] =>
    first[notHyp (x \notin p)|notHyp (x \notin q)];
    have/andP [? ?]: (x \notin p) && (x \notin q) by rewrite mem_pcat negb_or in H
  end.

Ltac set_tac_branch_plus ::=
  match goal with
  | [ H : is_true (?x \in (pcat ?p ?q)) |- _] =>
    notHyp (x \in p);notHyp (x \in q);
    have/orP [?|?]: (x \in p) || (x \in q) by rewrite mem_pcat in H
  end.

Lemma add_edge_keep_connected_l (G : sgraph) s1 s2 A:
  @connected (@add_edge G s1 s2) A -> s1 \notin A -> @connected G A.

(** Adding Vertices *)

Section AddNode.
  Variables (G : sgraph) (N : {set G}).
  
  Definition add_node_rel (x y : option G) := 
    match x,y with 
    | None, Some y => y \in N
    | Some x, None => x \in N
    | Some x,Some y => x -- y
    | None, None => false
    end.

  Lemma add_node_sym : symmetric add_node_rel.

  Lemma add_node_irrefl : irreflexive add_node_rel.

  Definition add_node := SGraph add_node_sym add_node_irrefl.

  Lemma add_node_lift_Path (x y : G) (p : Path x y) :
    exists q : @Path add_node (Some x) (Some y), nodes q = map Some (nodes p).
End AddNode.
Arguments add_node : clear implicits.

Lemma diso_add_nodeK (G : sgraph) (A : {set G}) : 
  G ≃ @induced (add_node G A) [set~ None].

(** recursive characterization of ['K_n] *)
Lemma diso_add_edge_KSn n : diso 'K_n.+1 (add_node 'K_n setT).

Lemma connected_add_node (G : sgraph) (U A : {set G}) : 
  connected A -> @connected (add_node G U) (Some @: A).

(** Spliting [add_node] into adding one edge/node and the remaining
edges. Useful for constructing plane embeddings *)

Lemma add_node_diso_proof (G : sgraph) (A : {set G}) (x : G) : x \in A ->
     @add_edges2_rel (add_node G [set x]) [set None] [set Some x | x in A :\ x] 
  =2 add_node_rel A.

Lemma add_node_diso (G : sgraph) (A : {set G}) (x : G) : 
  x \in A -> 
  diso (add_edges2 (add_node G [set x]) [set None] (Some @: (A :\ x))) (add_node G A).

(** Complement Graph *)
Section complement.
Variable (G : sgraph).
Definition compl_rel := [rel x y : G | (x != y) && ~~ x -- y].

Fact compl_rel_irrefl : irreflexive compl_rel. 

Fact compl_rel_sym : symmetric compl_rel. 

Definition compl := SGraph compl_rel_sym compl_rel_irrefl.

End complement.

Lemma diso_compl (G : sgraph) : compl (compl G) ≃ G.

Open Scope implicit_scope.

Lemma isubgraph_compLR_mono (F G : sgraph) (i : compl F ⇀ G) (x y : F) :
  i x -- i y :> compl G = x -- y.

Lemma isubgraph_complLR (F G : sgraph) (i : compl F ⇀ G) : F ⇀ compl G.

Lemma iso_isubgraph (F G : sgraph) (i : F ≃ G) : F ⇀ G.

Lemma isubgraph_compl (F G : sgraph) (i : F ⇀ G) : compl F ⇀ compl G.

Close Scope implicit_scope.

(** ** Neighboring sets *)

Section Neighbor.
  Variable (G : sgraph).
  Implicit Types A B C D : {set G}.
  
  Definition neighbor A B := [exists x in A, exists y in B, x -- y].
  
  Lemma neighborP A B : reflect (exists x y, [/\ x \in A, y \in B & x -- y]) (neighbor A B).

  Lemma neighbor1P (x : G) (A : {set G}) : 
    reflect (exists2 y, x -- y & y \in A) (neighbor [set x] A).

  Lemma neighborC A B : neighbor A B = neighbor B A.

  Lemma neighbor_connected A B : 
    connected A -> connected B -> neighbor A B -> connected (A :|: B).

  Lemma neighborW C D A B : 
    C \subset A -> D \subset B -> neighbor C D -> neighbor A B.

  Lemma neighborUl A B C : neighbor A B -> neighbor A (B :|: C).

  Lemma neighborUr A B C : neighbor A C -> neighbor A (B :|: C).

  Lemma neighbor11 x y: neighbor [set x] [set y] = x -- y.

End Neighbor.
Arguments neighborW : clear implicits.

Lemma neighbor_add_edgeC (G : sgraph) (s1 s2 : G) :
  @neighbor (add_edge s1 s2) =2 @neighbor (add_edge s2 s1).

Lemma neighbor_del_edgeR (G : sgraph) (s1 s2 : G) (A B : {set G}) :
  s1 \notin B -> s2 \notin B -> @neighbor (add_edge s1 s2) A B -> @neighbor G A B.

Lemma neighbor_del_edge2 (G : sgraph) (s1 s2 : G) (A B : {set G}) :
  s2 \notin A -> s2 \notin B -> @neighbor (add_edge s1 s2) A B -> @neighbor G A B.

Lemma neighbor_del_edge1 (G : sgraph) (s1 s2 : G) (A B : {set G}) :
  s1 \notin A -> s1 \notin B -> @neighbor (add_edge s1 s2) A B -> @neighbor G A B.

Lemma neighbor_add_edge (G : sgraph) (s1 s2 : G) : 
  subrel (@neighbor G) (@neighbor (add_edge s1 s2)).

Lemma neighbor_split (G : sgraph) (A B C1 C2 : {set G}) :
  B \subset C1 :|: C2 -> neighbor A B -> neighbor A C1 || neighbor A C2.

Lemma path_neighborL (G : sgraph) (x y : G) (p : Path x y) (A : {set G}) :
  irred p -> interior p != set0 -> x \in A -> neighbor A (interior p).

(** Interior of irredundant paths *)

Lemma interior_idp (G : sgraph) (x : G) : interior (idp x) = set0.

Lemma interior_rev (G : sgraph) (x y : G) (p : Path x y): 
  interior (prev p) = interior p.

Lemma path_neighborR (G : sgraph) (x y : G) (p : Path x y) (A : {set G}) :
  irred p -> interior p != set0 -> y \in A -> neighbor A (interior p).

Lemma connected_interior (G : sgraph) (x y : G) (p : Path x y) :
  irred p -> connected (interior p).

Lemma connected_interiorR (G : sgraph) (x y : G) (p : Path x y) : 
  irred p -> connected (y |: interior p).

(* TOTHINK: This lemma looks bespoke, but it is actually used multiple times *)
Lemma neighbor_interiorL (G : sgraph) (x y : G) (p : Path x y) :
  x != y -> irred p -> neighbor [set x] (y |: interior p).

(** ** Edge Sets *)

Definition sg_edge_set (G : sgraph) := [set [set x;y] | x in G, y in G & x -- y].
Notation "E( G )" := (sg_edge_set G) (at level 0, G at level 99, format "E( G )").

Lemma edgesP (G : sgraph) (e : {set G}) : 
  reflect (exists x y, e = [set x;y] /\ x -- y) (e \in E(G)).

Lemma in_edges (G : sgraph) (u v : G) : [set u; v] \in E(G) = (u -- v).

Lemma edges_opn0 (G : sgraph) (x : G) : E(G) = set0 -> #|N(x)| = 0.

(* TODO: this shoudld be the definition of subgraph *)
Lemma sub_card_edge (G H : sgraph) (h : G -> H) : 
  injective h -> is_dhom h -> #|E(G)| <= #|E(H)|. 
Arguments sub_card_edge [G H] h.

Lemma diso_card_edge (G H : sgraph) : diso G H -> #|E(G)| = #|E(H)|.

(** useful to define functions (morally on edge-sets) that need access
to the endpoints of the edge *)
Variant edge_spec (G : sgraph) (e : {set G}) : Type :=
| Edge x y of x -- y & e = [set x; y] : edge_spec e 
| NoEdge of e \notin E(G) : edge_spec e.

Lemma edgeP (G : sgraph) (e : {set G}) : edge_spec e.

(* TODO: use [disjoint e1 & e2] *)
Lemma edges_eqn_sub (G : sgraph) (e1 e2 : {set G}) : 
  e1 \in E(G) -> e2 \in E(G) -> e1 != e2 -> ~~ (e1 \subset e2).

(** edge sets and neighboorhoods for ['K_n] *)

Lemma deg_Kn n (x : 'K_n.+1) : n <= #|N(x)|.

Lemma card_edge_Kn n : #|E('K_n)| = 'C(n,2).

(** edge sets and neighboorhoods for 'K_3,3 *)

Lemma Knm_edges n m : 
  E('K_n,m) = [set [set inl x; inr y] | x in [set:'I_n], y in [set: 'I_m]].

Lemma card_edge_Knm n m : #|E('K_n,m)| = n * m.

Lemma opn_Knm_l n m (x : 'I_n) : 
  N(inl x : 'K_n,m) = [set inr y | y in [set: 'I_m]].

Lemma opn_Knm_r n m (y : 'I_m) : 
  N(inr y : 'K_n,m) = [set inl x | x in [set: 'I_n]].

Lemma deg_Knm_l n m (x : 'I_n) : #|N(inl x : 'K_n,m)| = m.

Lemma deg_Knm_r n m (y : 'I_m) : #|N(inr y : 'K_n,m)| = n.
  
Lemma deg_Knm n m (x : 'K_n,m) : minn n m <= #|N(x)|.

(** edge sets for add_node *)

(* not used currently *)
Lemma edges_add_node (G : sgraph) (A : {set G}) :
  E(add_node G A) = [set [set None; Some x] | x in A] :|: 
                    [set Some @: (e : {set G}) | e in E(G)].

Lemma card_edge_add_node (G : sgraph) (A : {set G}) :
  #|E(add_node G A)| = #|A| + #|E(G)|.

(** ** Edge Deletion  *)

Section del_edges.
Variables (G : sgraph) (A : {set G}).

Definition del_edges_rel := [rel x y : G | x -- y && ~~ ([set x;y] \subset A)]. 

Definition del_edges_sym : symmetric del_edges_rel. 

Definition del_edges_irrefl : irreflexive del_edges_rel.

Definition del_edges := SGraph del_edges_sym del_edges_irrefl.
End del_edges.

Section del_edges_facts.
Variables (G : sgraph).
Implicit Types (x y z : G) (A e : {set G}).

Local Open Scope implicit_scope.

Lemma mem_del_edges e A : e \in E(del_edges A) = (e \in E(G)) && ~~ (e \subset A).

(** Neighborhood version of the above *)
Lemma del_edges_opn A x z : 
  z \in N(del_edges A;x) = (z \in N(G;x)) && ~~ ([set x; z] \subset A).

Lemma del_edges_sub A : E(del_edges A) \subset E(G).

Lemma del_edges_proper e A : 
  e \in E(G) -> e \subset A -> E(del_edges A) \proper E(G).

(** Two useful lemmas for the case of deleting a single edge *)
Lemma del_edgesN e : e \notin E(del_edges e).

Lemma del_edges1 e : e \in E(G) -> E(G) = e |: E(del_edges e).

End del_edges_facts.

(** ** Neighborhood lemmas for simple graphs *)

Section Neighborhood_theory.
Variable G : sgraph.
Implicit Types (u v : G).

Lemma v_notin_opneigh v : v \notin N(v).

Lemma cl_sg_sym : symmetric (@dominates G).

Lemma opn_cln u : N(u) = N[u] :\ u.

Lemma opn_proper_cln v : N(v) \proper N[v].

Lemma opn_edges (u : G) : N(u) = [set v | [set u; v] \in E(G)].

Lemma cln_eq (x x' y : G) : 
  N[x] = N[x'] -> y != x -> y != x' -> x -- y = x' -- y.

Lemma eq_cln_iso (v v' : G) : N[v] = N[v'] -> induced [set~ v'] ≃ induced [set~ v].

End Neighborhood_theory.

Local Open Scope implicit_scope.
Theorem edges_sum_degrees (G : sgraph) : 2 * #|E(G)| = \sum_(x in G) #|N(x)|.
```

## helly.v
```coq
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import edone preliminaries digraph sgraph set_tac.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Preliminaries *)

Lemma ltn_subn n m o : n < m -> n - o < m.

Lemma ord3P (P : 'I_3 -> Type) : P ord0 -> P ord1 -> P ord2 -> forall i : 'I_3, P i.

(* Notation "A ∩ B" := (A :&: B) (at level 30). *)

(** We first show that for intersection closed properties, the helly
property of families of size three extends to the families of
arbitrary (finite) cardinalities. *)

(** TOTHINK: This should extend also to [T:choiceType] using the finmap library *)
Lemma helly3_lifting (T : finType) (P : {set T} -> Prop) :
  (forall A B, P A -> P B -> P (A :&: B)) ->
  (forall f : 'I_3 -> {set T}, 
    (forall i, P (f i)) -> (forall i j, f i :&: f j != set0) -> exists x, forall i, x \in f i) ->
  forall F : {set {set T}}, 
    0 < #|F| -> (forall A, A \in F -> P A) -> {in F &, forall A B, A :&: B != set0} -> exists x, forall A, A \in F -> x \in A.

Section Tree.
Variable (G : sgraph).
Hypothesis tree_G : is_forest [set: G].

(** If the whole graph is a forest, every connected set of vertices is a subtree *)

(** Subtrees are closed under intersection *)
Lemma tree_connectI (T1 T2 : {set G}) : 
  connected T1 -> connected T2 -> connected (T1 :&: T2).

(** NOTE: The [irred p] assumption could be removed, but it doesn't hurt *)
Lemma subtree_cut (T1 T2 : {set G}) (x1 x2 : G) (p : Path x1 x2) :
  connected T1 -> connected T2 -> T1 :&: T2 != set0 -> x1 \in T1 -> x2 \in T2 ->
  irred p -> exists y, [/\ y \in p, y \in T1 & y \in T2].

Lemma tree_I3 (T : 'I_3 -> {set G}) : 
  (forall i, connected (T i)) -> (forall i j, T i :&: T j != set0) -> exists z, forall i, z \in T i.

Theorem tree_helly (F : {set {set G}}) : 
  (forall T : {set G}, T \in F -> connected T) -> F != set0 -> 
  {in F &, forall A B, A :&: B != set0} -> \bigcap_(A in F) A != set0.

End Tree.

```

## treewidth.v
```coq
From Coq Require Import RelationClasses.

From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import edone preliminaries digraph sgraph.
From GraphTheory Require Import connectivity set_tac.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.
Set Bullet Behavior "Strict Subproofs". 

(** * Tree Decompositions and treewidth *)

(** Covering is not really required, but makes the renaming theorem
easier to state *)

Record sdecomp (T : forest) (G : sgraph) (B : T -> {set G}) := SDecomp
  { sbag_cover x : exists t, x \in B t; 
    sbag_edge x y : x -- y -> exists t, (x \in B t) && (y \in B t);
    sbag_conn x t1 t2  : x \in B t1 -> x \in B t2 ->
      connect (restrict [pred t | x \in B t] sedge) t1 t2}.

Arguments sdecomp T G B : clear implicits.

Lemma sdecomp_subrel (V : finType) (e1 e2 : rel V) (T:forest) (D : T -> {set V}) 
      (e1_sym : symmetric e1) (e1_irrefl : irreflexive e1) 
      (e2_sym : symmetric e2) (e2_irrefl : irreflexive e2):
  subrel e2 e1 -> 
  sdecomp T (SGraph e1_sym e1_irrefl) D -> 
  sdecomp T (SGraph e2_sym e2_irrefl) D.

Lemma sdecomp_tree_subrel 
      (G:sgraph) (V : finType) (D : V -> {set G}) (e1 e2 : rel V) 
      (e1_sym : symmetric e1) (e1_irrefl : irreflexive e1)
      (e2_sym : symmetric e2) (e2_irrefl : irreflexive e2)
      (e1_forest : is_forest [set: SGraph e1_sym e1_irrefl])
      (e2_forest : is_forest [set: SGraph e2_sym e2_irrefl]):
  subrel e1 e2 -> 
  sdecomp (Forest e1_forest) G D -> sdecomp (Forest e2_forest) G D.

Definition triv_sdecomp (G : sgraph) :
  sdecomp tunit G (fun _ => [set: G]).

Lemma decomp_iso (G1 G2 : sgraph) (T : forest) B1 : 
  sdecomp T G1 B1 -> diso G1 G2 -> 
  exists2 B2, sdecomp T G2 B2 & width B2 = width B1.

Definition triv_decomp (G : sgraph) :
  sdecomp tunit G (fun _ => [set: G]).

Lemma decomp_small (G : sgraph) k : #|G| <= k -> 
  exists T D, [/\ sdecomp T G D & width D <= k].

(** ** Renaming *)

Lemma rename_decomp (T : forest) (G H : sgraph) D (dec_D : sdecomp T G D) (h : G -> H) : 
  hom_s h -> 
  surjective h -> 
  (forall x y : H, x -- y -> exists x0 y0, [/\ h x0 = x, h y0 = y & x0 -- y0]) ->
  (forall x y, h x = h y -> 
    (exists t, (x \in D t) && (y \in D t)) \/ (exists t1 t2, [/\ t1 -- t2, x \in D t1 & y \in D t2])) ->
  @sdecomp T _ (rename D h).

Lemma rename_width (T : forest) (G : sgraph) (D : T -> {set G}) (G' : finType) (h : G -> G') :
  width (rename D h) <= width D.

(** ** Disjoint Union *)

Section JoinT.
  Variables (T1 T2 : forest).

  Lemma sub_inl (a b : T1) (p : @Path (sjoin T1 T2) (inl a) (inl b)) :
    {subset p <= codom inl}.

  Lemma sub_inr (a b : T2) (p : @Path (sjoin T1 T2) (inr a) (inr b)) :
    {subset p <= codom inr}.

  Arguments inl_inj [A B].
  Prenex Implicits inl_inj.

  Lemma join_is_forest : is_forest [set: sjoin T1 T2].
      
  Definition tjoin := @Forest (sjoin T1 T2) join_is_forest.

  Definition decompU (G1 G2 : sgraph) (D1 : T1 -> {set G1}) (D2 : T2 -> {set G2}) : 
    tjoin -> {set sjoin G1 G2} := 
    [fun a => match a with 
          | inl a => [set inl x | x in D1 a]
          | inr a => [set inr x | x in D2 a]
          end].

  Lemma join_decomp (G1 G2 : sgraph) (D1 : T1 -> {set G1}) (D2 : T2 -> {set G2})  :
    sdecomp T1 G1 D1 -> sdecomp T2 G2 D2 -> sdecomp tjoin (sjoin G1 G2) (decompU D1 D2).

  Lemma join_width (G1 G2 : sgraph) (D1 : T1 -> {set G1}) (D2 : T2 -> {set G2}) : 
    width (decompU D1 D2) <= maxn (width D1) (width D2).

End JoinT.

(** ** Link Construction (without intermediate node) *)

(* TOTHINK: The assumption [s1 != s2] is redundant, but usually available. *)
Lemma add_edge_break (G : sgraph) (s1 s2 x y : G) (p : @Path (add_edge s1 s2) x y) :
  s1 != s2 ->
  let U := [set s1;s2] in
  irred p -> ~~ @connect G sedge x y ->
  exists u v : G, exists q1 : Path x u, exists q2 : Path v y, 
  [/\ u \in U, v \in U, u != v & nodes p = nodes q1 ++ nodes q2].

Lemma path_return (G : sgraph) z (A : {set G}) (x y : G) (p : Path x y) :
  x \in A -> y \in A -> irred p -> 
  (forall u v, u -- v -> u \in A -> v \notin A -> u = z) -> p \subset A.
Abort.

Section AddEdge.
  Variables (T : forest) (t0 t1 : T).
  Hypothesis discT : ~~ connect sedge t0 t1.

  Let T' := add_edge t0 t1.
  Notation Path G x y := (@Path G x y).

  Lemma add_edge_is_forest : is_forest [set: T'].

End AddEdge.

(** ** Link Construction (with intermediate node) *)

Section Link.
  Variables (T : forest) (U : {set T}).
  Hypothesis U_disc : {in U &,forall x y, x != y -> ~~ connect sedge x y}.
  
  Definition link := add_node T U.
  
  Lemma link_unique_lift (x y : link) : 
    unique (fun p : Path x y => irred p /\ None \notin p).

  Lemma link_bypass (x y : T) (p : @Path link (Some x) (Some y)) : 
    x \in U -> y \in U -> None \notin p -> x = y.

  Lemma link_unique_None (x : link) : 
    unique (fun p : @Path link None x => irred p).

  Lemma link_has_None (x y : link) (p q : Path x y) : 
    irred p -> irred q -> None \in p -> None \in q.

  Lemma link_is_forest : is_forest [set: link].
      
  Definition tlink := @Forest link link_is_forest.

  Definition decompL (G:sgraph) (D : T -> {set G}) A a := 
    match a with Some x => D x | None => A end.

  Lemma decomp_link (G : sgraph) (D : T -> {set G}) (A  : {set G}) : 
    A \subset \bigcup_(t in U) D t ->
    sdecomp T G D -> @sdecomp tlink G (decompL D A).

  Lemma width_link (G : sgraph) (D : T -> {set G}) (A  : {set G}) : 
    width (decompL D A) <= maxn (width D) #|A|.

End Link.

(** ** Every clique is contained in some bag *)

Section DecompTheory.
  Variables (G : sgraph) (T : forest) (B : T -> {set G}).
  Implicit Types (t u v : T) (x y z : G).

  Hypothesis decD : sdecomp T G B.

  Arguments sbag_conn [T G B] dec x t1 t2 : rename.

  (** This proof is based on a stackexchange post to be found here:
      https://math.stackexchange.com/questions/1227867/
      a-clique-in-a-tree-decomposition-is-contained-in-a-bag 

      The assumption [0 < #|S|] ensures that [T] is nonempty. *)
  Lemma decomp_clique (S : {set G}): 
    0 < #|S| -> clique S -> exists t : T, S \subset B t.
      
End DecompTheory.
Arguments rename_decomp [T G H D].

(** decompositsions of ['K_m] have width at least [m] *)

Lemma Km_bag m (T : forest) (D : T -> {set 'K_m.+1}) : 
  sdecomp T 'K_m.+1 D -> exists t, m.+1 <= #|D t|.

Lemma Km_width m (T : forest) (D : T -> {set 'K_m.+1}) : 
  sdecomp T 'K_m.+1 D -> m.+1 <= width D.

(** Obtaining a tree decomposition from tree decompositions of (induced) subgraphs *)
Lemma separation_decomp (G:sgraph) (V1 V2 : {set G}) T1 T2 B1 B2 :
  @sdecomp T1 (induced V1) B1 -> @sdecomp T2 (induced V2) B2 -> 
  separation V1 V2 -> clique (V1 :&: V2) ->
  exists T B, @sdecomp T G B /\ width B <= maxn (width B1) (width B2).

(** ** Forests have treewidth 1 *)

Lemma forest_vseparator (G : sgraph) : 
  is_forest [set: G] -> 3 <= #|G| -> exists2 S : {set G}, vseparator S & #|S| <= 1.

Lemma forest_TW1 (G : sgraph) : 
  is_forest [set: G] -> exists T B, sdecomp T G B /\ width B <= 2.
```

## minor.v
```coq
From Coq Require Import RelationClasses.

From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import edone preliminaries digraph.
From GraphTheory Require Import sgraph treewidth set_tac.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.
Set Bullet Behavior "Strict Subproofs". 

(** * Minors *)

Definition minor_map (G H : sgraph) (phi : G -> option H) := 
  [/\ (forall y : H, exists x : G, phi x = Some y),
     (forall y : H, connected (phi @^-1 Some y)) &
     (forall x y : H, x -- y -> exists x0 y0 : G,
      [/\ x0 \in phi @^-1 Some x, y0 \in phi @^-1 Some y & x0 -- y0])].

Definition minor_rmap (G H : sgraph) (phi : H -> {set G}) :=
  [/\ (forall x : H, phi x != set0),
     (forall x : H, connected (phi x)),
     (forall x y : H, x != y -> [disjoint phi x & phi y]) &
     (forall x y : H, x -- y -> neighbor (phi x) (phi y))].

(** introduction lemma for minor maps, that uses an injection [m : H -> nat] 
to order the vertices and reduce the number of cases when constructing minor
maps from constant graphs (e.g., 'K_5 or 'K_3,3). *)

Lemma ordered_rmap (G H : sgraph) (phi : H -> {set G}) (m : H -> nat) :
  injective m ->
  [/\ forall x : H, phi x != set0, 
     forall x : H, sgraph.connected (phi x),
     forall x y : H, m x < m y -> x != y -> [disjoint phi x & phi y]
   & forall x y : H, m x < m y -> x -- y -> neighbor (phi x) (phi y)]
  -> minor_rmap phi.
Arguments ordered_rmap [G H phi] m.  

Lemma minor_map_rmap (G H : sgraph) (phi : H -> {set G}) : 
  minor_rmap phi -> minor_map (fun x : G => [pick x0 : H | x \in phi x0]).

Lemma minor_rmap_map (G H : sgraph) (phi : G -> option H) : 
  minor_map phi -> minor_rmap (fun x => [set y | phi y == Some x]).

Lemma rmap_add_edge_sym (G H : sgraph) (s1 s2 : G) (phi : H -> {set G}) :
  @minor_rmap (add_edge s1 s2) H phi -> @minor_rmap (add_edge s2 s1) H phi.

Lemma rmap_disjE (G H : sgraph) (phi : H -> {set G}) x i j :
  minor_rmap phi -> x \in phi i -> x \in phi j -> i=j.

(** H is a minor of G -- The order allows us to write [minor G] for the
collection of [G]s minors *)
Definition minor (G H : sgraph) : Prop := exists phi : G -> option H, minor_map phi.

Fact minor_of_map (G H : sgraph) (phi : G -> option H): 
  minor_map phi -> minor G H.

Fact minor_of_rmap (G H : sgraph) (phi : H -> {set G}): 
  minor_rmap phi -> minor G H.

Lemma minorRE G H : minor G H -> exists phi : H -> {set G}, minor_rmap phi.

Lemma minor_rmap_comp (G H K : sgraph) (f : H -> {set G}) (g : K -> {set H}) :
  minor_rmap f -> minor_rmap g -> minor_rmap (fun x => \bigcup_(y in g x) f y).

Lemma minor_map_comp (G H K : sgraph) (f : G -> option H) (g : H -> option K) :
  minor_map f -> minor_map g -> minor_map (obind g \o f).

Lemma minor_trans : Transitive minor.

Definition total_minor_map (G H : sgraph) (phi : G -> H) :=
  [/\ (forall y : H, exists x, phi x = y), 
     (forall y : H, connected (phi @^-1 y)) &
     (forall x y : H, x -- y -> 
     exists x0 y0, [/\ x0 \in phi @^-1 x, y0 \in phi @^-1 y & x0 -- y0])].

Definition strict_minor (G H : sgraph) : Prop := 
  exists phi : G -> H, total_minor_map phi.

Lemma map_of_total (G H : sgraph) (phi : G -> H) :
  total_minor_map phi -> minor_map (Some \o phi).

Lemma strict_is_minor (G H : sgraph) : strict_minor G H -> minor G H.

Lemma sub_minor (S G : sgraph) : subgraph S G -> minor G S.

Lemma iso_strict_minor (G H : sgraph) : diso G H -> strict_minor H G.

(** Induced subgraphs are trivially minors *)
Section induced_rmap.
Variables (G : sgraph) (S : {set G}).

Definition induced_rmap := (fun x : induced S => [set val x]).

Lemma induced_rmapP : minor_rmap induced_rmap.

Lemma induced_rmap_sub u : induced_rmap u \subset S.

Lemma induced_minor : minor G (induced S).

End induced_rmap.

Definition edge_surjective (G1 G2 : sgraph) (h : G1 -> G2) :=
  forall x y : G2 , x -- y -> exists x0 y0, [/\ h x0 = x, h y0 = y & x0 -- y0].

(** ** Links with Treewidth *)

(* The following should hold but does not fit the use case for minors *)
Lemma rename_sdecomp (T : forest) (G H : sgraph) D (dec_D : sdecomp T G D) (h :G -> H) : 
  hom_s h -> surjective h -> edge_surjective h -> 
  (forall x y, h x = h y -> exists t, (x \in D t) && (y \in D t)) -> 
  @sdecomp T _ (rename D h).
Abort. 

Lemma width_minor (G H : sgraph) (T : forest) (B : T -> {set G}) : 
  sdecomp T G B -> minor G H -> exists B', @sdecomp T H B' /\ width B' <= width B.

Lemma minor_of_clique (G : sgraph) (S : {set G}) n :
  n <= #|S| -> clique S -> minor G 'K_n.

Lemma Kn_clique n : clique [set: 'K_n].

Definition K4_free (G : sgraph) := ~ minor G K4.

Lemma minor_K4_free (G H : sgraph) : 
  minor G H -> K4_free G -> K4_free H.

Lemma subgraph_K4_free (G H : sgraph) : 
  subgraph H G -> K4_free G -> K4_free H.

Lemma iso_K4_free (G H : sgraph) : 
  diso G H -> K4_free H -> K4_free G.

Lemma treewidth_K_free (G : sgraph) (T : forest) (B : T -> {set G}) m : 
  sdecomp T G B -> width B <= m -> ~ minor G 'K_m.+1.

Lemma TW2_K4_free (G : sgraph) (T : forest) (B : T -> {set G}) : 
  sdecomp T G B -> width B <= 3 -> K4_free G.

Lemma small_K_free m (G : sgraph): #|G| <= m -> ~ minor G 'K_m.+1.

(* TODO: theory for [induced [set~ : None : add_node]] *)
Lemma minor_induced_add_node (G : sgraph) (N : {set G}) : @minor_map (induced [set~ None : add_node G N]) G val.

Lemma add_node_minor (G G' : sgraph) (U : {set G}) (U' : {set G'}) (phi : G -> G') :
  (forall y, y \in U' -> exists2 x, x \in U & phi x = y) ->
  total_minor_map phi ->
  minor (add_node G U) (add_node G' U').

Lemma minor_with (H G': sgraph) (S : {set H}) (i : H) (N : {set G'})
  (phi : (sgraph.induced S) -> option G') : 
  i \notin S -> 
  (forall y, y \in N -> exists2 x , x \in phi @^-1 (Some y) & val x -- i) ->
  @minor_map (sgraph.induced S) G' phi -> 
  minor H (add_node G' N).

(** ** Excluded-Minor Characterization of Forests *)

Lemma non_forerst_K3 (G : sgraph) : ~ is_forest [set: G] -> minor G 'K_3.

Theorem K3_free_forest G : ~ minor G 'K_3 <-> is_forest [set: G].

Theorem TW1_forest G : (exists T B, sdecomp T G B /\ width B <= 2) <-> is_forest [set: G].
```

## connectivity.v
```coq
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import edone preliminaries digraph mgraph sgraph set_tac.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(** * Graph Connectivty *)

(** In this file we prove Menger's Theorem and some of its most
well-known and most-used corollaries. The proof follows Göring's
"Short Proof of Menger's Theorem".  The two most central notions in
the proof are those of an AB-separator and an AB-connector. *)

(** ** Connectors, Separators, and Separations *)

Section SeparatorConnector.
Variables (G : diGraph).
Implicit Types (x y z u v : G) (A B S U V : {set G}).

(** There are two notions af separators used in the literature,
"AB-separators" (i.e., sets disconnecting two not necessariliy
disjoint sets of vertices) and "(vertex) separarors" (i.e., sets of
vertices disconnecting a given graph). *)

Definition separator (A B S : {set G}) :=
  forall (a b : G) (p : Path a b), a \in A -> b \in B -> exists2 s, s \in S & s \in p.

Lemma separatorI A B S : 
  (forall (a b : G) (p : Path a b), irred p -> a \in A -> b \in B -> exists2 s, s \in S & s \in p)
  -> separator A B S.

Definition separatorb (A B S : {set G}) := 
  [forall a in A, forall b in B, forall p : IPath a b, exists s in S, s \in p].

Lemma separatorP (A B S : {set G}) : reflect (separator A B S) (separatorb A B S).

Lemma separatorPn (A B S : {set G}) : 
  reflect (exists x y (p: IPath x y), [/\ x \in A, y \in B & [disjoint p & S]]) (~~ separatorb A B S).

Lemma separator_cap A B S : separator A B S -> A :&: B \subset S.

Lemma separator_min A B S : separator A B S -> #|A :&: B| <= #|S|.

Definition separates x y U := [/\ x \notin U, y \notin U & forall p : Path x y, exists2 z, z \in p & z \in U].

(** Standard trick to show decidability: quantify only over irredundant paths *)
Definition separatesb x y U := [&& x \notin U, y \notin U & [forall p : IPath x y, exists z in p, z \in U]].

Lemma separatesI x y (U : {set G}) :
  [/\ x \notin U, y \notin U & forall p : Path x y, irred p -> exists2 z, z \in p & z \in U] -> separates x y U.

Lemma separatesP x y U : reflect (separates x y U) (separatesb x y U).
Arguments separatesP {x y U}.

Fact separatesNeq x y U : separates x y U -> x != y.

(** TOTHINK: [conn_disjoint] could also be expressed as [x \in p i -> x \in p j ->  i = j] *)
(** NOTE: Unlike the definition of Göring, we do not allow single edge paths inside [A :&: B] *)
Record connector (A B : {set G}) n (p : 'I_n -> pathS G) : Prop := 
  { conn_irred    : forall i, irred (tagged (p i)); 
    conn_begin    : forall i, [set x in p i] :&: A = [set fst (p i)];
    conn_end      : forall i, [set x in p i] :&: B = [set lst (p i)];
    conn_disjoint :  forall i j, i != j -> [set x in p i] :&: [set x in p j] = set0 }.

Section ConnectorTheory.
Variables (A B : {set G}) (n : nat) (p : 'I_n -> pathS G).
Hypothesis conn_p : connector A B p.

Lemma connector_fst i : fst (p i) \in A.

Lemma connector_lst i : lst (p i) \in B.

Lemma connector_left i x : x \in p i -> x \in A -> x = fst (p i).

Lemma connector_right i x : x \in p i -> x \in B -> x = lst (p i).

Lemma lst_idp i : lst (p i) \in A -> lst (p i) = fst (p i).

Lemma fst_idp i : fst (p i) \in B -> fst (p i) = lst (p i).

Lemma connector_eq i j x : x \in p i -> x \in p j -> i = j.

Lemma fst_lst_eq i j : fst (p i) = lst (p j) -> i = j.

Lemma fst_inj : injective (@fst G \o p).

Lemma lst_inj : injective (@lst G \o p).

End ConnectorTheory.

Lemma connector_extend A B n (p : 'I_n -> pathS G) x y i : 
  x \notin \bigcup_i [set z in p i] -> fst (p i) = y -> x -- y -> x \notin B ->
  connector A B p -> exists q : 'I_n -> pathS G, connector (x |: (A :\ y)) B q.

Lemma connector_sep P A B n (p q : 'I_n -> pathS G) i j x : 
  separator A B P -> connector A P p -> connector P B q -> 
  x \in p i -> x \in q j -> (x \in P) (* * (lst (p i) = fst (q j)) *).

Lemma connector_cat (P A B : {set G}) n (p q : 'I_n -> pathS G) : 
  #|P| = n -> separator A B P ->
  connector A P p -> connector P B q -> 
  exists (r : 'I_n -> pathS G), connector A B r.

Lemma trivial_connector A B : exists p : 'I_#|A :&: B| -> pathS G, connector A B p.

Lemma sub_connector A B n m (p : 'I_m -> pathS G) : 
  n <= m -> connector A B p -> exists q : 'I_n -> pathS G, connector A B q.

End SeparatorConnector.
Arguments separatesP {G x y U}.

Section VSeparator.
Variable (G : sgraph).
Implicit Types (x y z u v : G) (S U V : {set G}).

Lemma separates_sym x y S : separates x y S <-> separates y x S.

Fact separates0P x y : reflect (separates x y set0) (~~ connect edge_rel x y).

Lemma opn_separates x y : x != y -> ~~ x -- y -> separates x y N(x).

(** TODO: this does not actually depend on G being simple *)
Lemma separatesNE x y (U : {set G}) :
  x \notin U -> y \notin U -> ~ separates x y U -> connect (restrict [predC U] edge_rel) x y.

Lemma induced_separates (V : {set G}) (S : {set induced V}) (x y : induced V) :
  separates x y S -> separates (val x) (val y) (val @: S :|: ~:V).

Definition vseparator U := exists x y, separates x y U.

Lemma vseparatorNE U x y : ~ vseparator U -> ~ separates x y U.

Lemma separates_vseparator (x y : G) (S : {set G}) : 
  separates x y S -> vseparator S. 

Lemma svseparator_connected S : 
  smallest vseparator S -> 0 < #|S| -> connected [set: G].

(** vseparators do not make precises what the separated comonents are,
i.e., a vseparator can disconnect the graph into more than two
components. Hence, we also define separations, which make the
separated sides explicit *)
Definition separation V1 V2 := 
  ((forall x, x \in V1 :|: V2) * (forall x1 x2, x1 \notin V2 -> x2 \notin V1 -> x1 -- x2 = false))%type.

Lemma sep_inR x V1 V2 : separation V1 V2 -> x \notin V1 -> x \in V2.

Lemma sep_inL x V1 V2 : separation V1 V2 -> x \notin V2 -> x \in V1.

Definition proper_separation V1 V2 := separation V1 V2 /\ exists x y, x \notin V2 /\ y \notin V1.

Lemma separate_nonadjacent x y : x != y -> ~~ x -- y -> proper_separation [set~ x] [set~ y].

Lemma separation_separates x y V1 V2:
  separation V1 V2 -> x \notin V2 -> y \notin V1 -> separates x y (V1 :&: V2).

Lemma proper_vseparator V1 V2 :
  proper_separation V1 V2 -> vseparator (V1 :&: V2).

Lemma vseparator_separation S : 
  vseparator S -> exists V1 V2, proper_separation V1 V2 /\ S = V1 :&: V2.

Lemma proper_separation_card V1 V2 : 
  proper_separation V1 V2 -> (#|V1| < #|G|)%type * (#|V2| < #|G|)%type.

Definition vseparatorb U := [exists x, exists y, separatesb x y U].

Lemma vseparatorP U : reflect (vseparator U) (vseparatorb U).

Lemma minimal_separation x y : x != y -> ~~ x -- y -> 
  exists V1 V2, proper_separation V1 V2 /\ smallest vseparator (V1 :&: V2).

Lemma separation_sym V1 V2 : separation V1 V2 <-> separation V2 V1.

Lemma proper_separation_symmetry V1 V2 :
  proper_separation V1 V2 <-> proper_separation V2 V1.

Lemma svseparator_neighbours V1 V2 s : 
  proper_separation V1 V2 -> smallest vseparator (V1 :&: V2) -> 
  s \in V1 :&: V2 -> exists x1 x2, [/\ x1 \notin V2, x2 \notin V1, s -- x1 & s -- x2].

(** Note: This generalizes the corresponding lemma on checkpoints *)
Lemma avoid_nonseperator U x y : ~ vseparator U -> x \notin U -> y \notin U -> 
  exists2 p : Path x y, irred p & [disjoint p & U].

Lemma svseparator_uniq x y S:
  smallest vseparator S -> separates x y S -> S != set0 ->
  exists2 p : Path x y, irred p & exists! z, z \in p /\ z \in S.

Lemma separation_connected_same_component V1 V2:
  separation V1 V2 -> forall x0 x, x0 \notin V2 ->
  connect (restrict [predC (V1:&:V2)] sedge) x0 x -> x \notin V2.

Lemma diso_separation V1 V2 : 
  separation V1 V2 -> [disjoint V1 & V2] -> 
  diso ((induced V1) ∔ (induced V2))%sg G.

End VSeparator.
Arguments vseparator {G} _.

(** lifing a [vseparator] from an induced subgraph *)
Lemma induced_vseparator (G : sgraph) (A : {set G}) (S : {set induced A}) : 
  vseparator S -> vseparator (val @: S :|: ~: A).

(** Lifting separations to/from [add_edge] *)

Section AddEdgeSep.

Local Arguments separation : clear implicits.
Local Arguments proper_separation : clear implicits.
Local Arguments vseparator : clear implicits.

Lemma add_edge_separation' (G : sgraph) (V1 V2 : {set G}) x y:
  separation (add_edge x y) V1 V2 -> separation G V1 V2.

Lemma add_edge_separation (G : sgraph) V1 V2 x y:
  x \in V1:&:V2 -> y \in V1:&:V2 -> separation G V1 V2 -> separation (add_edge x y) V1 V2.

Lemma add_edge_proper_separation (G : sgraph) (V1 V2 : {set G}) x y :
  x \in V1 :&: V2 -> y \in V1 :&: V2 -> 
  proper_separation G V1 V2 -> proper_separation (add_edge x y) V1 V2.

Lemma add_edge_proper_separation' (G : sgraph) (V1 V2 : {set G}) x y :
  proper_separation (add_edge x y) V1 V2 -> proper_separation G V1 V2.

Lemma add_edge_vseparator' (G : sgraph) (x y : G) (S : {set G}) :
  vseparator (add_edge x y) S -> vseparator G S.

Lemma add_edge_vseparator (G : sgraph) (x y : G) (S : {set G}) :
  x \in S -> y \in S -> vseparator G S -> vseparator (add_edge x y) S.

Lemma add_edge_smallest_vseparator (G : sgraph) (x y : G) (S : {set G}) :
  x \in S -> y \in S -> 
  smallest (vseparator G) S -> smallest (vseparator (add_edge x y)) S.

End AddEdgeSep.

Arguments separator : clear implicits.
Arguments separatorb : clear implicits.

Lemma connector_nodes (T : finType) (e1 e2 : rel T) (A B : {set T}) : 
  forall s (p : 'I_s -> pathS (DiGraph e1)) (q : 'I_s -> pathS (DiGraph e2)), 
  (forall i, nodes (tagged (p i)) = nodes (tagged (q i)) :> seq T) -> 
  @connector (DiGraph e1) A B s p -> @connector (DiGraph e2) A B s q.
 
Lemma del_edge_connector (G : diGraph) (a b : G) (A B : {set G}) s (p : 'I_s -> pathS (del_edge a b)) : 
  @connector (del_edge a b) A B s p -> connector A B (fun i : 'I_s => del_edge_liftS (p i)).

(** ** Menger's Theorem *)

Theorem Menger (G : diGraph) (A B : {set G}) s : 
  (forall S, separator G A B S -> s <= #|S|) -> exists (p : 'I_s -> pathS G), connector A B p.

(** ** Independent Path Corollaries *)

(** *** Vertex version *)

Corollary theta (G : diGraph) (x y : G) s :
  ~~ x -- y -> x != y ->
  (forall S, separates x y S -> s <= #|S|) -> 
  exists p : 'I_s -> IPath x y, forall i j : 'I_s, i != j -> independent (p i) (p j).

(** In addition to the independent paths, we also get a function providing a
default vertex on each path *)
Fact theta_vertices (G : diGraph) (x y : G) s (p : 'I_s -> IPath x y) :
  x != y -> ~~ x -- y ->
  exists (f : 'I_s -> G), forall i, f i \in interior (p i).

(** *** Edge Version *)

Corollary independent_walks Lv Le (G : graph Lv Le) (a b : G) n : 
  a != b -> (forall E, eseparates a b E -> n <= #|E|) -> 
  exists2 W : 'I_n -> seq (edge G), 
    forall i, walk a b (W i) & forall i j, i != j -> [disjoint W i & W j].

(** ** Hall's Marriage Theorem *)

(** Neighboorhoods and bipartitions are the same for digraphs and simple graphs *)

Definition bipartition (G : diGraph) (A : {set G}) :=
  forall x y : G, x -- y -> (x \in A) = (y \notin A).

Lemma bipartition_path (G : diGraph) (A : {set G}) (x : G) (s: seq G) : 
  bipartition A -> 
  path (--) x s -> ~~ odd (((last x s \in A) (+) (x \in A)) + size s).

Lemma bipartition_cycle (G : diGraph) (A : {set G}) (s: seq G) : 
  bipartition A -> cycle (--) s -> ~~ odd (size s).

Lemma even_cycle_Knm n m (s : seq 'K_n,m) : cycle (--) s -> ~~ odd (size s).

(** The (natural) notion of a matching on digraphs - a set of ordered
pairs - is not a resonable notion of matching on simple graphs, where
we should use unordered pairs. Hence, we have two separate definitions *)

Definition dimatching (G : diGraph) (M : {set G * G}) :=
    (forall e, e \in M -> e.1 -- e.2) 
  /\ {in M &, forall e1 e2 x, x \in [set e1.1;e1.2] -> x \in [set e2.1 ; e2.2] -> e1 = e2}.

Definition matching (G : sgraph) (M : {set {set G}}) := 
  {subset M <= E(G) } /\ 
  {in M&, forall (e1 e2 : {set G}) (x:G), x \in e1 -> x \in e2 -> e1 = e2}.

Lemma connectorC_edge (G : diGraph) (A : {set G}) n (p : 'I_n -> pathS G) i : 
  connector A (~: A) p -> 
  exists fl : fst (p i) -- lst (p i), p i = PathS (edgep fl).

Definition dimatching_of (G : diGraph) n (p : 'I_n -> pathS G) := 
  [set (fst (p i),lst (p i)) | i : 'I_n].

Lemma connector_dimatching (G : diGraph) (A : {set G} ) n (p : 'I_n -> pathS G) :
  connector A (~:A) p -> dimatching (dimatching_of p).

Lemma card_dimatching_of (G : diGraph) A B n (p : 'I_n -> pathS G) :
  connector A B p -> #|dimatching_of p| = n.

Definition matching_of (G : diGraph) (M' : {set G * G}) := 
  [set [set e.1;e.2] | e in M'].

Lemma matching_of_dimatching (G : sgraph) (A : {set G}) M : 
  dimatching M -> @matching G (matching_of M).

Lemma card_matching_of (G : diGraph) (M : {set G * G}) : 
  dimatching M -> #|matching_of M| = #|M|.

Theorem diHall (G : diGraph) A : 
  bipartition A -> (forall S : {set G}, S \subset A -> #|S| <= #|NS(S)|) -> 
  exists M, dimatching M /\ A = [set x.1 | x in M].

Theorem Hall (G : sgraph) A : 
  bipartition A -> (forall S : {set G}, S \subset A -> #|S| <= #|NS(S)|) -> 
  exists M, matching M /\ A \subset cover M.

(** ** König's Theorem *)

Section vcover.
Variables (G : sgraph) (V :{set G}).

Definition vcover := [forall x, forall (y | x -- y), (x \in V) || (y \in V)].

Lemma vcoverP : reflect (forall x y, x -- y -> (x \in V) \/ (y \in V)) vcover.

(** The [x0] is needed to ensure that [G] is inhabited. 
    Otherwise, [{set G} -> G] is empty as well. *)
Lemma matching_cover_map (x0 : G) M :
  matching M -> vcover -> 
  exists2 f : {set G} -> G, (forall e : {set G}, e \in M -> f e \in V :&: e) & {in M&, injective f}.

Lemma cover_matching (M :{set {set G}}) : 
  matching M -> vcover -> #|M| <= #|V|.

Proposition min_max_cover (M : {set {set G}}) :  
  vcover -> matching M -> #|M| = #|V| -> V \subset cover M.

End vcover.
Prenex Implicits vcover.
Prenex Implicits matching.

Lemma bip_separation_vcover (G : sgraph) (A S : {set G}) : 
  bipartition A -> separator G A (~: A) S -> vcover S.

Lemma min_vcover_matching (G : sgraph) (A V : {set G}) : 
  bipartition A -> smallest vcover V ->
  exists2 M, @matching G M & #|V| = #|M|.

Theorem Konig (G : sgraph) (A V : {set G}) (M : {set {set G}}) : 
  bipartition A -> smallest vcover V -> largest matching M -> #|V| = #|M|.

(** ** k-connectivity *)

Definition kconnected (k : nat) (G : sgraph) := 
  k < #|G| /\ forall S : {set G}, vseparator S -> k <= #|S|.

Definition kconnectedb (k : nat) (G : sgraph) := 
  (k < #|G|) && [forall (S | @vseparatorb G S), k <= #|S|].

Lemma kconnectedP k G : reflect (kconnected k G) (kconnectedb k G).

Notation "k .-connected" := (kconnected k)
  (at level 2, format "k .-connected") : type_scope.

Lemma connectedVseparator (G : sgraph) k : 
  k < #|G| -> k.-connected G + { S : {set G} | #|S| < k & vseparator S}.

Lemma kconnected_degree (G : sgraph) k (x : G) : k.-connected G -> k <= #|N(x)|.

Lemma kconnected_edge (G : sgraph) (k : nat) : 
  k.+1.-connected G -> exists x y : G , x -- y.

Lemma kconnected_induced (G : sgraph) (A : {set G}) k : 
  (k + #|~: A|).-connected G -> k.-connected (induced A).

Lemma konnected_del1 k (G : sgraph) (x : G) : 
  k.+1.-connected G -> k.-connected (induced [set~ x]).

Lemma kconnected_bounds (G : sgraph) k : 
  k.+1 < #|G| -> k.-connected G -> ~ k.+1.-connected G -> 
  exists2 S : {set G}, #|S| == k & smallest vseparator S.

Lemma kconnectedW n k G : (k+n).-connected G -> k.-connected G.

Lemma kconnected_complete G k : 
  k.-connected G -> #|G| <= k.+1 -> (forall x y : G, x != y -> x -- y).
```

## excluded.v
```coq
From Coq Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect.
(* Note: ssrbool is empty and shadows Coq.ssr.ssrbool, use Coq.ssrbool for "Find" *)

From GraphTheory Require Import edone preliminaries set_tac digraph.
From GraphTheory Require Import sgraph treewidth minor connectivity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs". 

(** * Tree Decompositions for K4-free graphs *)

Ltac notHyp b ::= assert_fails (assert b by assumption).

Prenex Implicits vseparator.
Implicit Types G H : sgraph.
Arguments sdecomp : clear implicits.
Arguments rename_decomp [T G H D]. 

(* Pushing M-freeness (for some excluded minor M) to the subgraphs of
[add_edge G x y] induced by [V1] and [V2] where [V1,V2] is a proper
separation whose shared part is the minimal separator [[set x;y]]. *)

Section AddEdgeMinor.
Variables (G : sgraph) (x y : G) (V1 V2 : {set G}).
Let G' := add_edge x y.

Lemma unused_add_edge_connect_r (A : {pred G}) : 
  y \notin A -> subrel (restrict A (@sedge G')) (restrict A (@sedge G)).

Lemma unused_rmap_add_edge_r (M : sgraph) (phi : M -> {set G'}) : 
  (forall i, y \notin phi i) -> minor_rmap phi -> @minor_rmap G M phi.

Hypothesis xDy : x != y.
Hypothesis psepV : proper_separation V1 V2.
Let S := V1 :&: V2.
Hypothesis defS : S = [set x;y].
Hypothesis ssepS : smallest vseparator S.

Lemma add_edge_rmap_separation_minor (M : sgraph) (phi : M -> {set G'}) : 
  minor_rmap phi -> (forall u, phi u \subset V1) -> minor G M.

Lemma add_edge_separation_minor M : minor (@induced G' V1) M -> minor G M.

Lemma add_edge_separation_excluded M : 
  ~ minor G M -> ~ minor (@induced G' V1) M.

End AddEdgeMinor.

Lemma connectedI_clique (G : sgraph) (A B S : {set G}) :
  connected A -> clique S -> 
  (forall x y (p : Path x y), p \subset A -> x \in B -> y \notin B -> 
     exists2 z, z \in p & z \in S :&: B) ->
  connected (A :&: B).

(** only needed for [K4_free_add_edge_sep_size2] *)
Lemma separation_K4side G (V1 V2 : {set G}) : 
  separation V1 V2 -> clique (V1 :&: V2) -> #|V1 :&: V2| <= 2 ->
  minor G K4 -> 
  exists2 phi : K4 -> {set G}, minor_rmap phi & 
     (forall x, phi x \subset V1) \/ (forall x, phi x \subset V2).

Lemma K4_of_paths (G : sgraph) x y s0 s1' (p0 p1 p2 : Path x y) (q1 : Path s0 s1') : 
  x!=y -> independent p0 p1 -> independent p0 p2 -> independent p1 p2 ->
  s0 \in interior p0 -> s1' \in interior p1 -> 
  irred p0 -> irred p1 -> irred p2 -> irred q1 -> 
  [disjoint q1 & [set x; y]] -> 
  (forall z' : G, z' \in [predU interior p1 & interior p2] -> z' \in q1 -> z' = s1') -> 
  minor G K4.

Lemma K4_of_vseparators (G : sgraph) : 
  3 < #|G| -> (forall S : {set G}, vseparator S -> 2 < #|S|) -> minor G K4.

Lemma no_K4_smallest_vseparator (G : sgraph) :
  ~ minor G K4 -> #|G| <= 3 \/ (exists S : {set G}, smallest vseparator S /\ #|S| <= 2).

Theorem TW2_of_K4F (G : sgraph) :
  K4_free G -> exists (T : forest) (B : T -> {set G}), sdecomp T G B /\ width B <= 3.

Theorem excluded_minor_TW2 (G : sgraph) :
  K4_free G <-> 
  exists (T : forest) (B : T -> {set G}), sdecomp T G B /\ width B <= 3.

Lemma K4_free_add_edge_sep_size2 (G : sgraph) (s1 s2 : G):
  K4_free G -> smallest vseparator [set s1; s2] -> s1 != s2 -> K4_free (add_edge s1 s2).
```

## smerge.v
```coq
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import edone preliminaries digraph sgraph.
From GraphTheory Require Import connectivity minor treewidth arc set_tac.

(* TOTHINK : arc is only included for the [path0] definition *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Canonical edge_app_pred (G : diGraph) (x : G) := ApplicativePred (edge_rel x).
Canonical sedge_app_pred (G : sgraph) (x : G) := ApplicativePred (sedge x).

(** If [S] is a smallest separator, then every (maximal) component of G-S 
    can be seen as one part of a proper separation *)
Lemma component_separation (G : sgraph) (A S : {set G}) x : 
  smallest vseparator S -> 
  x \in A -> [disjoint A & S] -> connected A -> {in A & ~: A, forall x y, x--y -> y \in S} ->
  proper_separation (A :|: S) (~: A :|: S).

(** * Merging Vertices  *)

(** The definition of [smerge2 G x y] is simply to remove [y] and
attach all edges of [y] to [x], regardless of whether [x -- y] holds
or not. We use both variants. Edge-constraction drives the main
argument for the 3-connected case of Wagner's theorem. On the other
hand, vertex merging is used extensively when extending the result
from 3-connected graphs to general graphs *)

Section SMerge2.
Variables (G : sgraph) (x y : G).

Definition smerge2_vertex := { z : G | z != y }.
Definition smerge2_rel := 
  [rel u v : smerge2_vertex | 
   if (val u == x) && (val v != x) then val v -- x || val v -- y else 
   if (val v == x) && (val u != x) then val u -- x || val u -- y else 
   val u -- val v].

Lemma smerge2_irrefl : irreflexive smerge2_rel. 

Lemma smerge2_sym : symmetric smerge2_rel.

Definition smerge2 := SGraph smerge2_sym smerge2_irrefl.

Lemma smerge2_edge (u v : smerge2) : val u -- val v -> u -- v.

Lemma smerge2_minor : x -- y -> minor G smerge2.

End SMerge2.
Arguments smerge2 : clear implicits.

Lemma card_smerge2 (G : sgraph) (x y : G) : 
  #|smerge2 G x y|.+1 = #|G|.

Lemma smerge2_val_edge (G : sgraph) (x y : G) (u v : smerge2 G x y) : 
  val u != x -> val v != x -> val u -- val v = u -- v.

(* not used, but it probably should by *)
Lemma smerge2_neighbor (G : sgraph) (x y : G) (xDy : x != y) : 
  val @: N(Sub x xDy : smerge2 G x y) = (N(x) :|: N(y)) :\: [set x;y]. 

Lemma smerge2_path0 (G : sgraph) (x y : G) (s : seq (smerge2 G x y)) : 
  let s0 := [seq val x | x <- s] in path0 (--) s -> x \notin s0 -> path0 (--) s0.

Lemma smerge2_ucycle (G : sgraph) (x y : G) (s : seq (smerge2 G x y)) : 
  let s0 := [seq val x | x <- s] in
  ucycle (--) s -> x \notin s0 -> ucycle (--) s0.

Lemma smerge2edgeD (G : sgraph) (x y : G) (u v : smerge2 G x y) : 
  ~~ x -- y -> 
  u -- v = [|| val u -- val v, (val u == x) && val v -- y | (val v == x) && val u -- y].

Lemma smerge2edgeL (G : sgraph) (x y : G) (u v : smerge2 G x y) : 
  ~~ x -- y -> val u == x -> val v -- y -> u -- v.

(** wlog reasoning for edges of [smerge2 G x y] when the conclusion is symmetric *)
Lemma smerge2Ecase (G : sgraph) (x y : G) (G' := smerge2 G x y) (P : G' -> G' -> Prop) :
  ~~ x -- y -> (forall u v, P u v <-> P v u) -> 
  (forall u v, val u -- val v -> P u v) -> (forall u v, (val u == x) && val v -- y -> P u v) ->
  forall u v, u -- v -> P u v.

Lemma smerge2_separator (G : sgraph) (x y : G) (S : {set smerge2 G x y}) :
  vseparator S -> vseparator (y |: val @: S).

Lemma smerge_konnected k (G : sgraph) (x y : G) : 
  x -- y -> k.+1.-connected G -> k.-connected (smerge2 G x y).

(** ** Edge Contraction in 3-connected graphs *)

(** Any separator of [smerge2 G x y] that does not contain [x] can be
lifted to a separator in of [G] *)
Lemma separator_from_smerge2 (G : sgraph) (x y : G) (xDy : x != y) 
  (x' := Sub x xDy) (S : {set smerge2 G x y}) :
  vseparator S -> x' \notin S -> vseparator (val @: S).

Lemma edge_separator (G : sgraph) (x y : G) : 
  4 < #|G| -> 3.-connected G -> x -- y -> ~ 3.-connected (smerge2 G x y) -> 
  exists z, vseparatorb [set x;y;z].

(* This could be an alterative to the direct argument in
[contract_three_connected] 
Lemma component_two_connected (G : sgraph) (x y a : G) (A : {set G}) (S := [set x; y]) : 
  2.-connected G -> vseparator S -> 
  a \in A -> [disjoint A & S] -> connected A -> {in A & ~: A, forall x y, x--y -> y \in S} ->
  forall w, connected ((S :|: A) :\ w). *)

(** The following proposition drives the inductive proof of Wagner's
Theorem, as it allows maintainig 3-connectedness thoughout the
induction. *)
Proposition contract_three_connected (G : sgraph) :
  5 <= #|G| ->
  3.-connected G -> exists x y, x -- y /\ 3.-connected (smerge2 G x y).

(** ** Isomorphims for vertex merging *)

Arguments inl_inj {A B}.
Arguments inr_inj {A B}.

(** The case for overlap 1 - one [smerge2] operation *)

Lemma diso_separation1 (G : sgraph) (V1 V2 : {set G}) (x : G) (xV1 : x \in V1) (xV2 : x \in V2) : 
  separation V1 V2 -> V1 :&: V2 = [set x] -> 
  let G' := (induced V1 ∔ induced V2)%sg in
  diso (smerge2 G' (inl (Sub x xV1)) (inr (Sub x xV2))) G.

(** The case for overlap 2 - two [smerge2] operations *)

(** In the case of a proper separtion [(V1,V2)] that overlaps in a set
[[set x;y]] with [x -- y], we need two [smerge2] operations to
collapse [induced V1] and [induced V2]. Given the complex definition
of the edge relation for [smerge2], this leads to a rather messy
construction. To alleviate this somewhat, we introduce an intermediate
construction [glue2] that merges two vertices from different graphs in
one go. *)

Section Glue2.
Variables (G : sgraph) (x y : G) (H : sgraph) (x' y' : H).

Definition glue2_vertex : Type := G + { z | z \notin [set x';y'] }.

Definition glue2_rel (u v : glue2_vertex) :=
  match u,v with
  | inl u, inl v => u -- v
  | inr u, inr v => val u -- val v
  | inl u, inr v => (u == x) && x' -- val v || (u == y) && y' -- val v
  | inr v, inl u => (u == x) && x' -- val v || (u == y) && y' -- val v
  end.

Lemma glue2_sym : symmetric glue2_rel.

Lemma glue2_irrefl : irreflexive glue2_rel.

Definition glue2 := SGraph glue2_sym glue2_irrefl.

(** injection for elements of H *)
Definition glue2_r (z : H) : glue2.
refine (
  if @boolP (z == x') isn't AltFalse b1 then inl x else
    if @boolP (z == y') isn't AltFalse b2 then inl y else
      inr (Sub z _)  
); abstract (by rewrite !inE negb_or b1 b2).
Defined.

End Glue2.
Arguments glue2 : clear implicits.
Arguments glue2_r [G x y H x' y'] _.

Open Scope implicit_scope.

Lemma smerge2_glue2 (G H : sgraph) (x1 y1 : G) (x2 y2 : H) (p1 : inl y1 != inr x2) (p2 : inr y2 != inr x2) :
  x1 != y1 -> x1 -- y1 ->
  diso (smerge2 (smerge2 (G ∔ H)%sg (inl x1) (inr x2)) (Sub (inl y1) p1) (Sub (inr y2) p2))
       (glue2 G x1 y1 H x2 y2).

Lemma separation_capN (G : sgraph) (V1 V2 : {set G}) u v :
  separation V1 V2 -> u \in V1 -> v \in V2 -> u -- v -> (u \in V1 :&: V2) || (v \in V1 :&: V2).

Lemma diso_separation2_glue (G : sgraph) (V1 V2 : {set G}) (x y : G) 
  (xV1 : x \in V1) (xV2 : x \in V2) (yV1 : y \in V1) (yV2 : y \in V2) : 
  separation V1 V2 -> V1 :&: V2 = [set x;y] -> 
  diso (glue2 (induced V1) (Sub x xV1) (Sub y yV1) (induced V2) (Sub x xV2) (Sub y yV2)) G.

Lemma diso_separation2 (G : sgraph) (V1 V2 : {set G}) (x y : G) 
   (xV1 : x \in V1) (xV2 : x \in V2) (yV1 : y \in V1) (yV2 : y \in V2)
   (G1 := induced V1) (G2 := induced V2) (G12 := (G1 ∔ G2)%sg)
   (x1 : G12 := inl (Sub x xV1)) (x2 : G12 := inr (Sub x xV2))
   (y1 : G12 := inl (Sub y yV1)) (y2 : G12 := inr (Sub y yV2))
   (y1Gm : y1 != x2) (y2Gm : y2 != x2) :
  separation V1 V2 -> V1 :&: V2 = [set x; y] -> x -- y ->
  diso (smerge2 (smerge2 (G1 ∔ G2) x1 x2) (Sub y1 y1Gm) (Sub y2 y2Gm)) G.
```

## arc.v
```coq
From Coq Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma iter_id (T : Type) n : @iter T n id =1 id.

Lemma iterK n (T : Type) (f g : T -> T) : 
  cancel f g -> cancel (iter n f) (iter n g).

Lemma leq_subl n m o : n <= m -> n - o <= m.

(** *** Lemmas on [index] and [subseq] *)
(** could go to seq.v *)

Lemma mem2_index (T : eqType) (x y : T) (s : seq T) : 
  uniq s -> y \in s -> mem2 s x y = (index x s <= index y s).

Lemma index_subseq (T : eqType) x y (s1 s2 : seq T) :
  y \in s1 -> subseq s1 s2 -> uniq s2 -> 
  index x s1 <= index y s1 -> index x s2 <= index y s2.

Section Path.

Lemma eq_traject (T : Type) (f g : T -> T) : f =1 g -> traject f =2 traject g.

Variable (T : eqType). 
Implicit Types (s p : seq T) (x y : T).

Lemma head_rot s x0 n : n < size s -> head x0 (rot n s) = nth x0 s n.

Lemma next_cons x0 x s : next (x::s) x = head x0 (rcons s x).

Lemma next_neq x p : x \in p -> uniq p -> 1 < size p -> x != next p x.

Lemma prev_neq x p : x \in p -> uniq p -> 1 < size p -> x != prev p x.

Lemma iter_next_rot x0 s n :
  n < size s -> uniq s -> iter n (next s) (head x0 s) = head x0 (rot n s).

Lemma iter_next_nth x0 s n : 
  uniq s -> n < size s -> iter n (next s) (head x0 s) = nth x0 s n.

Lemma traject_next x0 s : 
  uniq s -> traject (next s) (head x0 s) (size s) = s.

Lemma mem_arc (p : seq T) (x y : T) : {subset arc p x y <= p}.

End Path.

Lemma map_arc (aT rT : eqType) (f : aT -> rT) (s : seq aT) (x y : aT) : 
  injective f -> [seq f z | z <- arc s x y] = arc (map f s) (f x) (f y).

Lemma next_map (aT rT : eqType) (f : aT -> rT) (s : seq aT) (x : aT) : 
  injective f -> next (map f s) (f x) = f (next s x).

(** *** Lemmas on [index] *)
(** could go to [fingraph.v] *)

Lemma eq_findex (T : finType) (f g : T -> T) : 
  f =1 g -> findex f =2 findex g.

Lemma findex_head (T : finType) (x y : T) (s : seq T) (uniq_xs : uniq (x::s)) :
  findex (next (x :: s)) x y = index y (x :: s).

From GraphTheory Require Import preliminaries.
Local Notation splitPr := path.splitPr.

(* Only the lemmas below are actually used: 
(* already on mathcomp master *)
Axiom card_gt1P : 
   forall {T : finType} {A : pred T}, reflect (exists x y : T, [/\ x \in A, y \in A & x != y]) (1 < #|A|).
Axiom disjointFr :  
  forall (T : finType) (A B : pred T), reflect (forall x : T, x \in A -> x \in B -> False) [disjoint A & B].
*)

Lemma head_arc (T: eqType) (s : seq T) (x y : T) (xDy : x != y) : 
  uniq s -> x \in s -> y \in s -> x \in arc s x y.

Lemma next_mem_arc (T : eqType) (s : seq T) (x y : T) : 
  uniq s -> x \in s -> y \in s -> x != y -> next s x \in rcons (arc s x y) y.

(* Not used *)
Lemma arc_next (T : eqType) (s : seq T) (x : T) : 
  1 < size s -> uniq s -> x \in s -> arc s x (next s x) = [:: x].

Definition path0 (T : Type) (e : rel T) (s : seq T) :=
  if s is x::s then path e x s else true.

Lemma path_path0 (T : Type) (e : rel T) x (s : seq T) : 
  path e x s -> path0 e s.

Section UcycleArc.
Variables (T : finType) (e : rel T) (s : seq T).

Lemma arc_path x y (xDy : x != y) :
  ucycle e s -> x \in s -> y \in s -> path0 e (arc s x y).

Lemma arc_edge x y : 
  ucycle e s -> x \in s -> y \in s -> x != y -> e (last x (arc s x y)) y.

Lemma arc_findex x y z (xDy : x != y) : 
  uniq s -> x \in s -> y \in s -> 
  (z \in arc s x y) = (findex (next s) x z < findex (next s) x y).

Lemma arc_disjoint2 x y : 
  uniq s -> x \in s -> y \in s -> x != y -> [disjoint arc s x y & arc s y x].

Lemma arc_disjoint x1 x2 y1 y2 : 
  uniq s -> x1 \in s -> x2 \in s -> y1 \in s -> y2 \in s -> x1 != x2 -> y1 != y2 ->
  findex (next s) x1 x2 <= findex (next s) x1 y1 ->
  findex (next s) y1 y2 <= findex (next s) y1 x1 ->
  [disjoint arc s x1 x2 & arc s y1 y2].

Variable p : seq T.
Hypothesis uniq_s : uniq s.
Hypothesis p_sub_s : subseq p s.
Let p_in_s := mem_subseq p_sub_s.
Let uniq_p := subseq_uniq p_sub_s uniq_s.

Lemma findex_next_other (x y : T) :
  x \in p -> y \in p -> x != y -> findex (next s) x (next p x) <= findex (next s) x y.

Lemma arc_next_disjoint x y : 
  x \in p -> y \in p -> x != y ->
  [disjoint arc s x (next p x) & arc s y (next p y)].

Lemma arc_cover x y : x \in s -> y \in s -> x != y -> s =i [predU arc s x y & arc s y x].

Lemma mem_arc_other x y z : x \in s -> y \in s -> z \in s -> x != y -> 
  (z \in arc s x y) = (z \notin arc s y x).

Lemma arc_remainder x : 1 < size p -> x \in p -> {subset p <= rcons (arc s (next p x) x) x}.

End UcycleArc.

Section SubCycle.
Variables (T : eqType).
Implicit Types (p s : seq T).

Definition subcycle p s := [exists n : 'I_(size p).+1, subseq (rot n p) s].

Lemma subcycleP p s : reflect (exists n, subseq (rot n p) s) (subcycle p s).

Lemma subcycle_rot_l n p s : subcycle (rot n p) s = subcycle p s.

Lemma subcycle_rot_r n p s : subcycle p (rot n s) = subcycle p s.

Lemma subcycle_rot n m s p : subcycle (rot n p) (rot m s) = subcycle p s.

Lemma subseq_subcyle p s : subseq p s -> subcycle p s.

Lemma subcycle_trans : transitive subcycle.

Lemma subcycle_uniq p s : subcycle p s -> uniq s -> uniq p.

Lemma mem_subcycle p s : subcycle p s -> {subset p <= s}.

Lemma subcycle_get_arc x p s :
  x \in s -> uniq s -> subcycle p s -> 1 < size p ->
  exists2 z, z \in p & x \in arc s z (next p z).

End SubCycle.

Lemma arc_iterP (T : eqType) (x y z : T) (s : seq T) (xDy : x != y) : 
  uniq s -> x \in s -> y \in s -> 
  reflect (exists2 n, iter n (next s) x = z 
                    & forall m, m <= n -> iter m (next s) x != y) 
          (z \in arc s x y).

Lemma next_iter (T : eqType) (x y : T) (s : seq T) :
  uniq s -> x \in s -> y \in s -> exists n, iter n (next s) x == y.

Lemma prev_iter (T : eqType) (x y : T) (s : seq T) :
  uniq s -> x \in s -> y \in s -> exists n, iter n (prev s) x == y.

Lemma subcycle_get_arc' (T : eqType) x (p s : seq T) : 
  x \in s -> uniq s -> subcycle p s -> 1 < size p ->
  exists2 z, z \in p & x \in arc s z (next p z).

Lemma arc_subcycle_disjoint (T : finType) (p s : seq T) (x y : T) : 
  uniq s -> subcycle p s -> x \in p -> y \in p -> x != y -> 
  [disjoint arc s x (next p x) & arc s y (next p y)].

Lemma arc_subcycle_disjoints (T : finType) (p s : seq T) (x y nx ny : T) : 
  uniq s -> subcycle p s -> x \in p -> y \in p -> x != y -> nx = next p x -> ny = next p y ->
  [disjoint [set z in arc s x nx] & [set z in arc s y ny]].
```

## checkpoint.v
```coq
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import edone preliminaries digraph.
From GraphTheory Require Import sgraph connectivity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.
Set Bullet Behavior "Strict Subproofs". 

(** * Checkpoints *)

Section CheckPoints.
  Variables (G : sgraph).
  Implicit Types (x y z : G) (U : {set G}).

  Definition cp x y := locked [set z | separatorb G [set x] [set y] [set z]].

  Lemma cpPn x y z : reflect (exists2 p : Path x y, irred p & z \notin p) (z \notin cp x y).

  Lemma cpNI x y (p : Path x y) z : z \notin p -> z \notin cp x y.
  
  Lemma cpP x y z : reflect (forall p : Path x y, z \in p) (z \in cp x y).
  Arguments cpP {x y z}.

  Lemma cpTI x y z : (forall p : Path x y, irred p -> z \in p) -> z \in cp x y.

  Hypothesis G_conn' : connected [set: G].
  Let G_conn : forall x y:G, connect sedge x y.

  Lemma cp_sym x y : cp x y = cp y x.

  Lemma mem_cpl x y : x \in cp x y.

  Lemma subcp x y : [set x;y] \subset cp x y.

  Lemma cpxx x : cp x x = [set x].

  Lemma cp_triangle z {x y} : cp x y \subset cp x z :|: cp z y.
  
  Lemma cpN_trans a x z y : a \notin cp x z -> a \notin cp z y -> a \notin cp x y.

  Lemma cp_mid (z x y t : G) : t != z -> z \in cp x y ->
   exists (p1 : Path z x) (p2 : Path z y), t \notin p1 \/ t \notin p2.

  Lemma cp_widenR (x y u v : G) :
    u \in cp x y -> v \in cp x u -> v \in cp x y.
  Abort.

  Lemma cp_widen (i o x y z : G) :
    x \in cp i o -> y \in cp i o -> z \in cp x y -> z \in cp i o.

  Lemma cp_tightenR (x y z u : G) : z \in cp x y -> x \in cp u y -> x \in cp u z.

  (* The two-sided version of the previous lemma, not used. *)
  Lemma cp_tighten (i o p x y : G) :
    i \in cp x p -> o \in cp p y -> p \in cp x y -> p \in cp i o.
  (* Proof sketch:
   * Let [pi : Path i o]. By connectedness, there are irredundant paths
   * [pi_i : Path x i] and [pi_o : Path o y]. Then [p] must be in the
   * concatenation [pi_i ++ pi ++ pi_o]. It cannot be in the tail of [pi_o]
   * because [o \in cp p z] but [pi_o] is assumed to be irredundant. A
   * symmetrical reasoning for [pi_i] shows that [p \in pi].             Qed. *)
  Abort.
  
  Lemma cp_neighbours (x y : G) z : x != y ->
    (forall x' (p : Path x' y), x -- x' -> irred p -> x \notin p -> z \in p) ->
    z \in cp x y.

  Lemma connected_cp_closed (x y : G) (V : {set G}) :
    connected V -> [set x; y] \subset V -> cp x y \subset V.

  (** ** Link Graph *)

  Definition link_rel := [rel x y | (x != y) && (cp x y \subset [set x; y])].

  Lemma link_sym : symmetric link_rel.

  Lemma link_irrefl : irreflexive link_rel.

  Definition link_graph := SGraph link_sym link_irrefl.

  Local Notation "x ⋄ y" := (@sedge link_graph x y) (at level 30).

  Lemma link_avoid (x y z : G) : 
    z \notin [set x; y] -> link_rel x y -> exists2 p, pathp x y p & z \notin (x::p).
  Abort. (* not acutally used *)

  Lemma link_seq_cp (y x : G) p :
    @pathp link_graph x y p -> cp x y \subset x :: p.

  Lemma link_path_cp (x y : G) (p : @Path link_graph x y) : 
    {subset cp x y <= p}.

  (** ** CP Closure Operator *)

  (* NOTE: The nodes of G and its link graph are the same, but CP U usually makes
   * more sense as a subgraph of the link graph (e.g. for is_tree). *)
  Definition CP (U : {set G}) : {set link_graph} := \bigcup_(xy in setX U U) cp xy.1 xy.2.
  
  Unset Printing Implicit Defensive.

  Lemma CP_set2 (x y : G) : CP [set x; y] = cp x y.
  
  Lemma CP_extensive (U : {set G}) : {subset U <= CP U}.

  (** was only used in the CP_tree lemma, but we keep it here *)
  Lemma CP_mono (U U' : {set G}) : U \subset U' -> CP U \subset CP U'.
  
  Lemma CP_closed U x y : 
    x \in CP U -> y \in CP U -> cp x y \subset CP U.

  Lemma connected_CP_closed (U V : {set G}) :
    connected V -> U \subset V -> CP U \subset V.

  (* Lemma 16 *)
  Lemma CP_base U x y : x \in CP U -> y \in CP U ->
    exists x' y':G, [/\ x' \in U, y' \in U & [set x;y] \subset cp x' y'].

  (** *** Checkpoint graph *)

  Arguments Path : clear implicits.
  Arguments pathp : clear implicits.

  (* Lemma 14 *)
  Lemma CP_path (U : {set G}) (x y : G) (p : Path G x y) :
    x \in CP U -> y \in CP U -> irred p ->
    exists q : Path link_graph x y, [/\ irred q, q \subset CP U & q \subset p].

  (**: If [CP_ U] is a tree, the uniqe irredundant path bewteen any
  two nodes contains exactly the checkpoints bewteen these nodes *)
  Lemma CP_tree_paths (U : {set G}) (x y : G) (p : Path link_graph x y) : 
    is_tree (CP U) -> p \subset CP U -> irred p ->
    {in CP U, p =i cp x y}.

  Arguments Path : default implicits.
  Arguments pathp : default implicits.

  (** ** Intervals and bags *)

  (** *** Strict intervals *)

  Definition sinterval x y := [set u | (x \notin cp u y) && (y \notin cp u x)].

  Lemma sinterval_sym x y : sinterval x y = sinterval y x.

  Lemma sinterval_bounds x y : (x \in sinterval x y = false) * 
                               (y \in sinterval x y = false).

  Lemma sintervalP2 x y u :
    reflect ((exists2 p : Path u x, irred p & y \notin p) /\
             (exists2 q : Path u y, irred q & x \notin q)) (u \in sinterval x y).

  Lemma sinterval_sub x y z : z \in cp x y -> sinterval x z \subset sinterval x y.

  Lemma sinterval_exit x y u v : u \notin sinterval x y -> v \in sinterval x y ->
    x \in cp u v \/ y \in cp u v.

  Lemma sinterval_outside x y u : u \notin sinterval x y ->
    forall (p : Path u x), irred p -> y \notin p -> [disjoint p & sinterval x y].

  Lemma sinterval_disj_cp (x y z : G) :
    z \in cp x y -> [disjoint sinterval x z & sinterval z y].

  Lemma sinterval_noedge_cp (x y z u v : G) :
    u -- v -> u \in sinterval x z -> v \in sinterval z y -> z \notin cp x y.

  Lemma sinterval_connectL (x y z : G) : z \in sinterval x y ->
    exists2 u, x -- u & connect (restrict (sinterval x y) sedge) z u.

  Lemma sinterval_connectedL (x y : G) : connected (x |: sinterval x y).

  Lemma sinterval_components (C : {set G}) x y :
    C \in components (sinterval x y) ->
    (exists2 u, u \in C & x -- u) /\ (exists2 v, v \in C & y -- v).

  (** *** Intervals *)

  Definition interval x y := [set x;y] :|: sinterval x y.

  Fact intervalL (x y : G) : x \in interval x y.

  Fact intervalR (x y : G) : y \in interval x y.

  Lemma interval_sym x y : interval x y = interval y x.

  Lemma cp_sub_interval x y : cp x y \subset interval x y.

  Lemma intervalI_cp (x y z : G) :
    z \in cp x y -> interval x z :&: interval z y = [set z].

  Lemma connected_interval (x y : G) : 
    connected (interval x y).

  (** *** Bags *)

  Definition bag (U : {set G}) x :=
    locked [set z | [forall y in CP U, x \in cp z y]].

  Lemma bag_id (U : {set G}) x : x \in bag U x.

  Lemma bag_nontrivial (U : {set G}) x : 
    bag U x != [set x] -> exists2 y, y \in bag U x & y != x.

  Lemma bagP (U : {set G}) x z : 
    reflect (forall y, y \in CP U -> x \in cp z y) (z \in bag U x).
  Arguments bagP {U x z}.

  (** was only used in the CP_tree lemma, but we keep it here *)
  Lemma bagPn (U : {set G}) x z : 
    reflect (exists2 y, y \in CP U & x \notin cp z y) (z \notin bag U x).

  Lemma bag_sub_sinterval (U : {set G}) x y z :
    x \in CP U -> y \in CP U -> z \in cp x y :\: [set x; y] ->
    bag U z \subset sinterval x y.

  (** ** Neighouring Checkpoints *)

  Definition ncp (U : {set G}) (p : G) : {set G} := 
    locked [set x in CP U | 
            connect (restrict [pred z:G | (z \in CP U) ==> (z == x)] sedge) p x].

  (* TOTHINK: Do we also want to require [irred q] *)
  Lemma ncpP (U : {set G}) (p : G) x : 
    reflect (x \in CP U /\ exists q : Path p x, forall y, y \in CP U -> y \in q -> y = x) 
            (x \in ncp U p).
  
  Lemma ncp_CP (U : {set G}) (u : G) :
    u \in CP U -> ncp U u = [set u].

  Lemma ncp_bag (U : {set G}) (p : G) x :
    x \in CP U -> (p \in bag U x) = (ncp U p == [set x]).

  Lemma ncp0 (U : {set G}) x p : 
    x \in CP U -> ncp U p == set0 = false.
  Arguments ncp0 [U] x p.
  
  Lemma ncp_interval U (x y p : G) : 
    x != y -> [set x; y] \subset ncp U p -> p \in sinterval x y.

  (** *** Application to bags *)

  (** the root of a bag is a checkpoint separating the bag from
  the rest of the graph *)
  Lemma bag_exit (U : {set G}) x u v : 
    x \in CP U -> u \in bag U x -> v \notin bag U x -> x \in cp u v.

  Lemma bag_exit' (U : {set G}) x u v : 
    x \in CP U -> u \in bag U x -> v \in x |: ~: bag U x -> x \in cp u v.

  Lemma bag_exit_edge (U : {set G}) x u v :
    x \in CP U -> u \in bag U x -> v \notin bag U x -> u -- v -> u = x.

  Lemma connected_bag x (U : {set G}) : x \in CP U -> connected (bag U x).

  (** ** Partitioning with intervals, bags and checkpoints *)

  (** *** Disjointness statements *)

  (** A small part of Proposition 20. *)
  Lemma CP_tree_sinterval (U : {set G}) (x y : G) :
    is_tree (CP U) -> x \in CP U -> y \in CP U -> x ⋄ y -> [disjoint CP U & sinterval x y].
  
  Lemma bag_disj (U : {set G}) x y :
    x \in CP U -> y \in CP U -> x != y -> [disjoint bag U x & bag U y].

  Lemma bag_cp (U : {set G}) x y : 
    x \in CP U -> y \in CP U -> x \in bag U y = (x == y).
  
  (** NOTE: This looks fairly specific, but it also has a fairly
  straightforward proof *)
  Lemma interval_bag_disj U (x y : G) :
    y \in CP U -> [disjoint bag U x & sinterval x y].

  (** *** Covering statements *)

  Lemma sinterval_bag_cover x y : x != y ->
    [set: G] = bag [set x; y] x :|: sinterval x y :|: bag [set x; y] y.

  Lemma sinterval_cp_cover x y z : z \in cp x y :\: [set x; y] ->
    sinterval x y = sinterval x z :|: bag [set x; y] z :|: sinterval z y.

  Lemma interval_cp_cover x y z : z \in cp x y :\: [set x; y] ->
    interval x y = (x |: sinterval x z) :|: bag [set x; y] z :|: (y |: sinterval z y).

  Lemma interval_edge_cp (x y z u v : G) : z \in cp x y -> u -- v ->
    u \in interval x z -> v \in interval z y -> (u == z) || (v == z).

  (** Variants of the lemmas above that go together with quotient graphs *)
  Lemma bag_interval_cap (x y z: G) (U : {set G}) :
    connected [set: G] -> x \in CP U -> y \in CP U -> 
    z \in bag U x -> z \in interval x y -> z = x.

  Lemma interval_interval_cap (x y u z: G) :
    u \in cp x y ->
    z \in interval x u -> z \in interval u y -> z = u.
 
End CheckPoints.

Notation "x ⋄ y" := (@sedge (link_graph _) x y) (at level 30).

(** ** Checkpoint Order *)

Section CheckpointOrder.

  Variables (G : sgraph) (i o : G).
  Hypothesis conn_io : connect sedge i o.
  Implicit Types x y : G.

  Lemma the_uPath_proof : exists p : Path i o, irred p.
                                                                
  Definition the_uPath := xchoose (the_uPath_proof).

  Lemma the_connect_irredP : irred (the_uPath).

  Definition cpo x y := let p := the_uPath in idx p x <= idx p y.

  Lemma cpo_refl : reflexive cpo.

  Lemma cpo_trans : transitive cpo.

  Lemma cpo_total : total cpo.

  Lemma cpo_antisym : {in cp i o&,antisymmetric cpo}.

  (** All paths visist all checkpoints in the same order as the canonical upath *)
  (* TOTHINK: Is this really the formulation that is needed in the proofs? *)
  Lemma cpo_order (x y : G) (p : Path i o) :
    x \in cp i o -> y \in cp i o -> irred p -> cpo x y = (idx p x <= idx p y).

  Lemma cpo_min x : cpo i x.

  Lemma cpo_max x : x \in cp i o -> cpo x o.

  Lemma cpo_cp x y : x \in cp i o -> y \in cp i o -> cpo x y ->
    forall z, z \in cp x y = [&& (z \in cp i o), cpo x z & cpo z y].

End CheckpointOrder.

```

## cp_minor.v
```coq
From mathcomp Require Import all_ssreflect.

From GraphTheory Require Import edone preliminaries digraph sgraph minor.
From GraphTheory Require Import checkpoint connectivity excluded set_tac.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs". 

(** * Combined Minor and Checkpoint Properties *)

(** This file is where we combine the theory of checkpoints and the theory of
minors and prove the lemmas underlying the correctness arguments for the term
extraction function. *)

Section CheckpointsAndMinors.
Variables (G : sgraph).
Hypothesis (conn_G : connected [set: G]).

(** ** Collapsing Bags *)

Lemma collapse_bags (U : {set G}) u0' (inU : u0' \in U) :
  let T := U :|: ~: (\bigcup_(x in U) bag U x) in
  let G' := sgraph.induced T in 
  exists phi : G -> G',
    [/\ total_minor_map phi,
     (forall u : G', val u \in T :\: U -> phi @^-1 u = [set val u]) &
     (forall u : G', val u \in U -> phi @^-1 u = bag U (val u))].

End CheckpointsAndMinors.
Arguments collapse_bags [G] conn_G U u0' _.

(** Neighbor Tree Lemma *)

Definition neighbours (G : sgraph) (x : G) := [set y | x -- y].

(** Proposition 21(ii) *)
Definition igraph (G : sgraph) (x y : G) : sgraph     := induced (interval  x y).
Definition istart (G : sgraph) (x y : G) : igraph x y := Sub  x  (intervalL x y).
Definition iend   (G : sgraph) (x y : G) : igraph x y := Sub  y  (intervalR x y).

Arguments add_edge : clear implicits.
Arguments igraph : clear implicits.
Arguments istart {G x y}.
Arguments iend {G x y}.

(* TOTHINK: This lemma can have a more general statement.
 * add_edge preserves sg_iso when the nodes are applied to the actual iso. *)
Lemma add_edge_induced_iso (G : sgraph) (S T : {set G})
      (u v : induced S) (x y : induced T) :
  S = T -> val u = val x -> val v = val y ->
  diso (add_edge (induced S) u v) (add_edge (induced T) x y).

(** ** K4-freenes of Intervals *)

Lemma igraph_K4F (G : sgraph) (i o x y : G) :
  connected [set: G] -> 
  x \in cp i o -> y \in cp i o -> x != y ->
  K4_free (add_edge G i o) ->
  K4_free (add_edge (igraph G x y) istart iend).

Lemma igraph_K4F_add_node (G : sgraph) (U : {set G}) :
  connected [set: G] -> forall x y, x \in CP U -> y \in CP U -> x != y ->
  K4_free (add_node G U) -> K4_free (add_edge (igraph G x y) istart iend).

(** ** Parallel Split Lemma *)

Lemma sepatates_cp (G : sgraph) (x y z : G) : separates x y [set z] -> z \in cp x y :\: [set x; y].

(** TOTHINK: Make this the definition of the link relation? Is the
link relation realiy needed in the first place ? *)
Lemma link_rel_sep2 (G : sgraph) (x y : G) :
  connected [set: G] -> ~~ x -- y -> link_rel x y -> 
  x != y /\ forall S, separates x y S -> 2 <= #|S|.

Lemma set_pred0 (T : finType) : @set0 T =i pred0. 
#[export]
Hint Resolve set_pred0 : core.

Lemma irred_in_sinterval (G : sgraph) (i o : G) (p : Path i o) : 
  irred p -> {subset interior p <= sinterval i o}.

Open Scope implicit_scope.

Lemma ssplit_K4_nontrivial (G : sgraph) (i o : G) : 
  ~~ i -- o -> link_rel i o -> K4_free (add_edge G i o) -> 
  (* bag [set i;o] i = [set i] -> *)
  connected [set: G] -> disconnected (sinterval i o).

Close Scope implicit_scope.
```

## coloring.v
```coq
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import preliminaries bij digraph.
From GraphTheory Require Import sgraph dom partition.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Clique Number, Stable Set Number and Chromatic Number *)

(** In this file, we define the graph parameters α,ω, and χ. As much
of the reasoning about these parameters is concerned with the values
for the parameters on induced subgraphs, we define the parameters as
functions of type [mem_pred G \to nat] and introduce a notation that
insertes the required [mem] cast. For [G : sgraph] and [A : {set G}],
we can therefore write both both χ(G) and χ(A). This (drastically)
reduces the amount of (induced) subgraphs that need to be constructed,
significantly simplifying the proofs. *)

(** ** Clique number *)

Section Cliques.
Variables (G : sgraph).
Implicit Types (H K : {set G}).

Definition cliques H := [set K : {set G} | (K \subset H) && cliqueb K].

Lemma cliques_gt0 A : 0 < #|cliques A|. 

Lemma cliquesW (A B K : {set G}) : A \subset B -> K \in cliques A -> K \in cliques B.

Lemma cliques_subset (A K : {set G}) : K \in cliques A -> K \subset A.

Lemma cliqueU1 x K : K \subset N(x) -> clique K -> clique (x |: K).

Lemma sub_clique K K' : K' \subset K -> clique K -> clique K'.

Lemma cliqueD K H : clique K -> clique (K :\: H).

Lemma cliquesD K H S : K \in cliques (H :\: S) -> K \in cliques H.

Definition omega_mem (A : mem_pred G) := 
  \max_(B in cliques [set x in A]) #|B|.

End Cliques.

Notation "ω( A )" := (omega_mem (mem A)) (format "ω( A )").

Definition maxcliques (G : sgraph) (H : {set G}) := 
  [set K in cliques H | ω(H) <= #|K|].

Section OmegaBasics.
Variables (G : sgraph).
Implicit Types (A B K H : {set G}).

Lemma maxclique_clique K H : K \in maxcliques H -> clique K.

Lemma maxcliquesW S H : S \in maxcliques H -> S \in cliques H.

Variant omega_spec A : nat -> Prop :=
  OmegaSpec K of K \in maxcliques A : omega_spec A #|K|.

Lemma omegaP A : omega_spec A ω(A).

Lemma clique_bound K A : K \in cliques A -> #|K| <= ω(A).

Lemma card_maxclique K H : K \in maxcliques H -> #|K| = ω(H).

Lemma sub_omega A B : A \subset B -> ω(A) <= ω(B).

Lemma maxclique_disjoint K H A : 
  K \in maxcliques H -> [disjoint K & A] -> K \in maxcliques (H :\: A).

Lemma maxclique_opn H K v : 
  v \in H -> K \in maxcliques H -> K \subset N(v) -> v \in K.

Lemma omega0 : ω(@set0 G) = 0.

Lemma omega_eq0 A : (ω(A) == 0) = (A == set0).

(** TODO: if [stable S], the difference is exactly 1 *)
Lemma omega_cut H S : 
  {in maxcliques H, forall K, S :&: K != set0} -> ω(H :\: S) < ω(H).

End OmegaBasics.

(** ** Stable Set Number *)

Section StableSets.
Variable (G : sgraph).
Implicit Types (H A S : {set G}).

Definition stabsets H := [set S : {set G} | S \subset H & stable S].

(* mostly useful in the right to left region to reestablish [stabsets] *)
Lemma in_stabsets B H : B \in stabsets H = (B \subset H) && @stable G B.

Lemma stabsetsP H S : reflect (S \subset H /\ stable S) (S \in stabsets H).

Lemma stabsets_gt0 A : 0 < #|stabsets A|. 

Definition alpha_mem (A : mem_pred G) := 
  \max_(S in stabsets [set x in A]) #|S|.

Lemma stable_compl A : stable (A : {set compl G}) = cliqueb A.

(** alternative proof, using duality, likely not worth it *)
Lemma clique_compl A : cliqueb (A : {set compl G}) = stable A.

End StableSets.

Notation "α( A )" := (alpha_mem (mem A)) (format "α( A )").

Definition maxstabsets (G : sgraph) (H : {set G}) := 
  [set S in stabsets H | α(H) <= #|S|].

Section AlphaBasics.
Variables (G : sgraph).
Implicit Types (A B K S H : {set G}).

Variant alpha_spec A : nat -> Prop :=
  AlphaSpec S of S \in maxstabsets A : alpha_spec A #|S|.

Lemma maxstabset_stable S H : S \in maxstabsets H -> stable S.

Lemma maxstabsetW S H : S \in maxstabsets H -> S \in stabsets H.

Lemma maxstabsetS S H : S \in maxstabsets H -> S \subset H.

Lemma alphaP A : alpha_spec A α(A).

Lemma stabset_bound S A : S \in stabsets A -> #|S| <= α(A).

Lemma card_maxstabset K H : K \in maxstabsets H -> #|K| = α(H).

Lemma alpha0 : α(set0 : {set G}) = 0.

Lemma alpha_eq0 H : (α(H) == 0) = (H == set0).

End AlphaBasics.

(** ** chromatic number *)

Definition coloring (G : sgraph) (P : {set {set G}}) (D : {set G}) :=
  partition P D && [forall S in P, stable S].

Definition trivial_coloring (G : sgraph) (A : {set G}) := 
  [set [set x] | x in A].

Lemma trivial_coloringP (G : sgraph) (A : {set G}) :
  coloring (trivial_coloring A) A.
Arguments trivial_coloringP {G A}.

Definition chi_mem (G : sgraph) (A : mem_pred G) := 
  #|[arg min_(P < trivial_coloring [set x in A] | coloring P [set x in A]) #|P|]|.

Notation "χ( A )" := (chi_mem (mem A)) (format "χ( A )").

Section Basics.
Variable (G : sgraph).
Implicit Types (P : {set {set G}}) (A B C D H : {set G}).

(** the [sub_partition] is actually a sub_coloring *)
Lemma sub_coloring P D A :
  coloring P D -> A \subset D -> coloring (sub_partition P A) A.

Lemma empty_coloring : coloring set0 (@set0 G).

Lemma coloringD1 P S H : coloring P H -> S \in P -> coloring (P :\ S) (H :\: S).

Lemma coloringU1 P S H : 
  stable S -> S != set0 -> coloring P H -> [disjoint S & H] -> coloring (S |: P) (S :|: H).

Variant chi_spec A : nat -> Prop :=
  ChiSpec P of coloring P A & (forall P', coloring P' A -> #|P| <= #|P'|) 
  : chi_spec A #|P|.

(** We can always replace [χ(A)] with [#|P|] for some optimal coloring [P]. *)
Lemma chiP A : chi_spec A χ(A).

Lemma color_bound P A : coloring P A -> χ(A) <= #|P|.

Lemma coloring_stabsetP P D : 
  reflect (partition P D /\ {in P, forall B, B \in stabsets D}) (coloring P D).

Lemma chi0 : χ(@set0 G) = 0.

Lemma leq_chi A : χ(A) <= #|A|.

Lemma sub_chi A B : A \subset B -> χ(A) <= χ(B).

Lemma cliqueIstable A C : clique C -> stable A -> #|C :&: A| <= 1.

Lemma chi_clique C : clique C -> χ(C) = #|C|.

Lemma omega_leq_chi A : ω(A) <= χ(A).

Lemma chiD1 H S : stable S -> χ(H) <= χ(H :\: S).+1.

Let setG : [set x in mem [set: G]] = [set x in mem G]. 

Lemma alphaT : α([set: G]) = α(G). 

Lemma omegaT : ω([set: G]) = ω(G). 

Lemma chiT : χ([set: G]) = χ(G).

End Basics.

Notation sval := (@sval _ _).

Section ISubgraph.
Variables (F G : sgraph) (i : F ⇀ G).
Let i_inj := isubgraph_inj i.

Lemma cliqueb_isubgraph (K : {set F}) : cliqueb K = cliqueb (i @: K).

Lemma stable_isubgraph (S  : {set F}) : stable S = stable (i @: S).

Lemma coloring_isubgraph (P : {set {set F}}) (D : {set F}) : 
  coloring P D = @coloring G [set i @: (S : {set F}) | S in P] (i @: D).

Lemma preim_coloring (P : {set {set G}}) (D : {set F}) : 
  coloring P (i @: D) -> coloring [set i @^-1: (B : {set G}) | B in P] D.

Lemma chi_isubgraph (A : {set F}) : χ(A) = χ(i @: A).

Lemma isubgraph_cliques (B K : {set F}) : 
  (K \in cliques B) = (i @: K \in cliques (i @: B)).

Lemma clique_to_isubgraph (K A : {set G}) : 
  K \in cliques A -> i @^-1: K \in cliques (i @^-1: A).

Lemma can_inj_imset (A : {set F}) : i @^-1: (i @: A) = A.

Lemma omega_isubgraph (B : {set F}) : ω(B) = ω(i @: B).

End ISubgraph.

(** We have proper duality reasoning at this point *)
Lemma maxcliques_compl (G : sgraph) (H : {set G}) : 
  maxcliques (H : {set compl G}) = maxstabsets H.

Lemma omega_compl (G : sgraph) (A : {set G}) : ω(A : {set compl G}) = α(A).

Lemma alpha_isubgraph (F G : sgraph) (i : F ⇀ G) (A : {set F}) : α(A) = α(i @: A).

Lemma maxstabsets_compl (G : sgraph) (H : {set G}) : 
  maxstabsets (H : {set compl G}) = maxcliques H.
Abort. 

Lemma alpha_compl (G : sgraph) (A : {set G}) : α(A : {set compl G}) = ω(A).
Abort.

Section Induced.
Variables (G : sgraph) (H : {set G}).
Let i := induced_isubgraph H.

Lemma alpha_induced : α(induced H) = α(H).

Lemma omega_induced : ω(induced H) = ω(H).

Lemma chi_induced : χ(induced H) = χ(H).

Lemma cliqueb_induced (K : {set induced H}) : cliqueb K = cliqueb (val @: K).

Lemma stable_induced (K : {set induced H}) : stable K = stable (val @: K).

End Induced.

Lemma maxstabset_to_induced (G : sgraph) (H : {set G}) (S : {set G}) : 
  S \in maxstabsets H -> val @^-1: S \in maxstabsets [set: induced H].

(** A coloring consisting of maximal stable sets is optimal *)
Lemma maxstabset_coloring (G : sgraph) (P : {set {set G}}) (D : {set G}) :
  partition P D -> {in P, forall S, S \in maxstabsets D} -> χ(D) = #|P|.

Section Iso.
Variables (F G : sgraph) (i : diso F G).
Implicit Types (A : {set F}).

Let i_mono : {mono i : x y / x -- y}.

Let i_inj : injective i.

Definition i' : F ⇀ G := ISubgraph i_inj i_mono.

(* TODO *)

Lemma diso_stable A : stable A = stable (i @: A).
Abort.

Lemma diso_clique A : cliqueb A = cliqueb (i @: A).
Abort.

Lemma diso_omega A : ω(A) = ω(i @: A).
Abort.

Lemma diso_chi A : χ(A) = χ(i @: A).
Abort.

End Iso.
```

## dom.v
```coq
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import preliminaries digraph sgraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(** * Domination Theory *)

(** ** Hereditary and superhereditary properties *)
Section Hereditary.
Variable (T : finType).

Implicit Types (p : pred {set T}) (F D : {set T}).

Definition hereditary p : bool := [forall (D : {set T} | p D), forall (F : {set T} | F \subset D), p F].

Definition superhereditary p : bool := hereditary [pred D | p (~: D)].

Proposition hereditaryP p : 
  reflect (forall D F : {set T}, (F \subset D) -> p D -> p F) (hereditary p).

Proposition superhereditaryP (p : pred {set T}) : 
  reflect (forall D F : {set T}, (D \subset F) -> p D -> p F) (superhereditary p).

Proposition maximal_indsysP p D : hereditary p ->
  reflect (p D /\ forall v : T, v \notin D -> ~~ p (v |: D)) (maxset p D).

Proposition minimal_indsysP p D : superhereditary p ->
  reflect (p D /\ forall v : T, v \in D -> ~~ p (D :\ v)) (minset p D).

End Hereditary.

(** ** Weighted Sets *)

Section Weighted_Sets.
Variables (T : finType) (weight : T -> nat).
Implicit Types (A B S : {set T}) (p : pred {set T}).

Definition weight_set (S : {set T}) := \sum_(v in S) weight v.
Let W := weight_set.

Lemma leqwset A B : A \subset B -> W A <= W B.

Hypothesis positive_weights : forall v : T, weight v > 0.

Lemma wset0 A : (A == set0) = (W A == 0).

Lemma ltnwset A B :  A \proper B -> W A < W B.

(* Sets of minimum/maximum weight *)

Lemma maxweight_maxset p A : p A -> (forall B, p B -> W B <= W A) -> maxset p A.

Lemma minweight_minset p A : p A -> (forall B, p B -> W A <= W B) -> minset p A.

Lemma arg_maxset p A : p A -> maxset p (arg_max A p W).

Lemma arg_minset p A : p A -> minset p (arg_min A p W).

End Weighted_Sets.

Section Domination_Theory.

Variable G : sgraph.

(** ** Stable, Dominating and Irredundant Sets *)
Section Stable_Set.

Variable S : {set G}.

Definition stable : bool := [disjoint NS(S) & S].

Local Lemma stableP_alt :
  reflect {in S&, forall u v, ~~ u -- v} [forall u in S, forall v in S, ~~ (u -- v)].

Lemma stableEedge : stable = [forall u in S, forall v in S, ~~ (u -- v)].

Proposition stableP : reflect {in S&, forall u v, ~~ u -- v} stable.

Proposition stablePn : reflect (exists x y, [/\ x \in S, y \in S & x -- y]) (~~ stable).

End Stable_Set.

(* the empty set is stable *)
Lemma stable0 : stable set0.

Lemma stable1 x : stable [set x].

(* if D is stable, any subset of D is also stable *)
Lemma st_hereditary : hereditary stable.

(* TOTHINK: do we need that [hereditary] is a boolean predicate? *)
Lemma sub_stable (B A : {set G}) : 
  A \subset B -> stable B -> stable A.

(**********************************************************************************)
Section Dominating_Set.

Variable D : {set G}.

Definition dominating : bool := [forall v, v \in NS[D]].

Local Lemma dominatingP_alt : reflect
  (forall v : G, v \notin D -> exists2 u : G, u \in D & u -- v)
  [forall (v | v \notin D), exists u in D, u -- v].

Lemma dominatingEedge : dominating = [forall (v | v \notin D), exists u in D, u -- v].

Proposition dominatingP : reflect
  (forall v : G, v \notin D -> exists2 u : G, u \in D & u -- v) dominating.

Lemma dominatingPn : 
  reflect (exists2 v : G, v \notin D & {in D, forall u, ~~ u -- v}) (~~ dominating).

End Dominating_Set.

(* V(G) is dominating *)
Lemma domT : dominating [set: G].

(* if D is dominating, any supraset of D is also dominating *)
Lemma dom_superhereditary : superhereditary dominating.

(**********************************************************************************)
Section Irredundant_Set.

Variable D : {set G}.
Implicit Types x y v w : G.

Definition private_set (v : G) := N[v] :\: NS[D :\ v].

Lemma privateP v w : 
  reflect (v -*- w /\ {in D, forall u, u -*- w -> u = v}) (w \in private_set v).

Definition irredundant : bool := [forall v : G, (v \in D) ==> (private_set v != set0)].

Proposition irredundantP: reflect {in D, forall v, (private_set v != set0)} irredundant.

Proposition irredundantPn : reflect (exists2 v, v \in D & private_set v == set0) (~~ irredundant).

End Irredundant_Set.

(* the empty set is irredundant *)
Lemma irr0 : irredundant set0.

(* if D is irredundant, any subset of D is also irredundant *)
Lemma irr_hereditary : hereditary irredundant.

(** ** Fundamental facts about Domination Theory *)
Section Relations_between_stable_dominating_irredundant_sets.

Variable D : {set G}.

(* A stable set D is maximal iff D is stable and dominating
 * See Prop. 3.5 of Fundamentals of Domination *)
Theorem maximal_st_iff_st_dom : maxset stable D <-> (stable D /\ dominating D).

(* A maximal stable set is minimal dominating
 * See Prop. 3.6 of Fundamentals of Domination *)
Theorem maximal_st_is_minimal_dom : maxset stable D -> minset dominating D.

(* A dominating set D is minimal iff D is dominating and irredundant
 * See Prop. 3.8 of Fundamentals of Domination *)
Theorem minimal_dom_iff_dom_irr : minset dominating D <-> (dominating D /\ irredundant D).

(* A minimal dominating set is maximal irredundant
 * See Prop. 3.9 of Fundamentals of Domination *)
Theorem minimal_dom_is_maximal_irr : minset dominating D -> maxset irredundant D.

End Relations_between_stable_dominating_irredundant_sets.

(**********************************************************************************)
Section Existence_of_stable_dominating_irredundant_sets.

(* Definitions of "maximal stable", "minimal dominating" and "maximal irredundant" sets *)

Definition max_st := maxset stable.

Definition min_dom := minset dominating.

Definition max_irr := maxset irredundant.

(* Inhabitants that are "maximal stable", "minimal dominating" and "maximal irredundant"
 * Recall that ex_minimal and ex_maximal requires a proof of an inhabitant of "stable",
 * "dominating" and "irredudant" to be able to generate the maximal/minimal set. *)

Definition inhb_max_st := s2val (maxset_exists stable0).

Definition inhb_min_dom := s2val (minset_exists domT).

Definition inhb_max_irr := s2val (maxset_exists irr0).

Lemma inhb_max_st_is_maximal_stable : max_st inhb_max_st.

Lemma inhb_min_dom_is_minimal_dominating : min_dom inhb_min_dom.

Lemma inhb_max_irr_is_maximal_irredundant : max_irr inhb_max_irr.

End Existence_of_stable_dominating_irredundant_sets.

(**********************************************************************************)
Section Weighted_domination_parameters.

Variable weight : G -> nat.
Hypothesis positive_weights : forall v : G, weight v > 0.

Let W := weight_set weight.

(* Definition of weighted parameters. *)

Definition ir_w : nat := W (arg_min inhb_max_irr max_irr W).

Fact ir_min D : max_irr D -> ir_w <= W D.

Fact ir_witness : exists2 D, max_irr D & W D = ir_w.

Fact ir_minset D : max_irr D -> W D = ir_w -> minset max_irr D.

Definition gamma_w : nat := W (arg_min setT dominating W).

Fact gamma_min D : dominating D -> gamma_w <= W D.

Fact gamma_witness : exists2 D, dominating D & W D = gamma_w.

Fact gamma_minset D : dominating D -> W D = gamma_w -> minset dominating D.

Definition ii_w : nat := W (arg_min inhb_max_st max_st W).

Fact ii_min S : max_st S -> ii_w <= W S.

Fact ii_witness : exists2 S, max_st S & W S = ii_w.

Fact ii_minset D : max_st D -> W D = ii_w -> minset max_st D.

Definition alpha_w : nat := W (arg_max set0 stable W).

Fact alpha_max S : stable S -> W S <= alpha_w.

Fact alpha_witness : exists2 S, stable S & W S = alpha_w.

Fact alpha_maxset S : stable S -> W S = alpha_w -> maxset stable S.

Definition Gamma_w : nat := W (arg_max inhb_min_dom min_dom W).

Fact Gamma_max D : min_dom D -> W D <= Gamma_w.

Fact Gamma_witness : exists2 D, min_dom D & W D = Gamma_w.

Fact Gamma_maxset D : min_dom D -> W D = Gamma_w -> maxset min_dom D.

Definition IR_w : nat := W (arg_max set0 irredundant W).

Fact IR_max D : irredundant D -> W D <= IR_w.

Fact IR_witness : exists2 D, irredundant D & W D = IR_w.

Fact IR_maxset D : irredundant D -> W D = IR_w -> maxset irredundant D.

(** ** Weighted version of the Cockayne-Hedetniemi domination chain. *)

Proposition ir_w_leq_gamma_w : ir_w <= gamma_w.

Proposition gamma_w_leq_ii_w : gamma_w <= ii_w.

Proposition ii_w_leq_alpha_w : ii_w <= alpha_w.

Proposition alpha_w_leq_Gamma_w : alpha_w <= Gamma_w.

Proposition Gamma_w_leq_IR_w : Gamma_w <= IR_w.

Theorem Cockayne_Hedetniemi_chain_w: 
  sorted leq [:: ir_w; gamma_w; ii_w; alpha_w; Gamma_w; IR_w].

(* Usage: [apply: (Cockayne_Hedetniemi_w i j)] with i,j concrete
indices into the above list [i < j] *)

Definition Cockayne_Hedetniemi_w_leq := 
  @sorted_leq_nth nat leq leq_trans leqnn 0 _ Cockayne_Hedetniemi_chain_w.

Notation Cockayne_Hedetniemi_w i j := 
  (@Cockayne_Hedetniemi_w_leq i j erefl erefl erefl).

(** Example *)
Let gamma_w_leq_Gamma_w: gamma_w <= Gamma_w. 

End Weighted_domination_parameters.

(* "argument" policy:
   every weighted parameter requires a graph, the weight vector and a proof that their
   components are positive *)
Arguments ir_w : clear implicits.
Arguments gamma_w : clear implicits.
Arguments ii_w : clear implicits.
Arguments alpha_w : clear implicits.
Arguments Gamma_w : clear implicits.
Arguments IR_w : clear implicits.

(** ** Classic (unweighted) parameters (use cardinality instead of weight)        *)

Section Classic_domination_parameters.

Definition ones : (G -> nat) := (fun _ => 1).

Let W1 : ({set G} -> nat) := (fun A => #|A|).

Lemma cardwset1 (A : {set G}) : #|A| = weight_set ones A.

Local Notation eq_arg_min := (eq_arg_min _ (frefl _) cardwset1).
Local Notation eq_arg_max := (eq_arg_max _ (frefl _) cardwset1).

(** Definition of unweighted parameters and its conversion to weighted ones. *)

Definition ir : nat := #|arg_min inhb_max_irr max_irr W1|.

Fact eq_ir_ir1 : ir = ir_w ones.

Definition gamma : nat := #|arg_min setT dominating W1|.

Fact eq_gamma_gamma1 : gamma = gamma_w ones.

Definition ii : nat := #|arg_min inhb_max_st max_st W1|.

Fact eq_ii_ii1 : ii = ii_w ones.

Definition alpha : nat := #|arg_max set0 stable W1|.

Fact eq_alpha_alpha1 : alpha = alpha_w ones.

Definition Gamma : nat := #|arg_max inhb_min_dom min_dom W1|.

Fact eq_Gamma_Gamma1 : Gamma = Gamma_w ones.

Definition IR : nat := #|arg_max set0 irredundant W1|.

Fact eq_IR_IR1 : IR = IR_w ones.

(** ** Classic Cockayne-Hedetniemi domination chain. *)

Corollary ir_leq_gamma : ir <= gamma.

Corollary gamma_leq_ii : gamma <= ii.

Corollary ii_leq_alpha : ii <= alpha.

Corollary alpha_leq_Gamma : alpha <= Gamma.

Corollary Gamma_leq_IR : Gamma <= IR.

Corollary Cockayne_Hedetniemi_chain: 
  sorted leq [:: ir; gamma; ii; alpha; Gamma; IR].

Definition Cockayne_Hedetniemi_leq := 
  @sorted_leq_nth nat leq leq_trans leqnn 0 _ Cockayne_Hedetniemi_chain.

Notation Cockayne_Hedetniemi i j := 
  (@Cockayne_Hedetniemi_leq i j erefl erefl erefl).

(** Example *)
Let gamma_leq_Gamma: gamma <= Gamma. 

End Classic_domination_parameters.

End Domination_Theory.

Arguments ir_w : clear implicits.
Arguments gamma_w : clear implicits.
Arguments ii_w : clear implicits.
Arguments alpha_w : clear implicits.
Arguments Gamma_w : clear implicits.
Arguments IR_w : clear implicits.
Arguments ir : clear implicits.
Arguments gamma : clear implicits.
Arguments ii : clear implicits.
Arguments alpha : clear implicits.
Arguments Gamma : clear implicits.
Arguments IR : clear implicits.
```

## partition.v
```coq
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** *** partitions and related properties *)

(** The majority of the lemmas in this file is part of mathcomp PR 731 *)

Section BigSetOps.

Variables T I : finType.
Implicit Types (U : {pred T}) (P : pred I) (A B : {set I}) (F :  I -> {set T}).

Lemma bigcup0P P F : 
  reflect (forall i, P i -> F i = set0) (\bigcup_(i | P i) F i == set0).

Lemma bigcup_disjointP U P F  :
  reflect (forall i : I, P i -> [disjoint U & F i]) 
          [disjoint U & \bigcup_(i | P i) F i].

End BigSetOps.

Lemma imset_cover (aT rT : finType) (P : {set {set aT}}) (f : aT -> rT) :
  [set f x | x in cover P] = \bigcup_(i in P) [set f x | x in i].

Section partition.
Variable (T : finType) (P : {set {set T}}) (D : {set T}).
Implicit Types (A B S : {set T}).

Lemma partition0 : partition P D -> set0 \in P = false.

Lemma partition_neq0 B : partition P D -> B \in P -> B != set0.

Lemma partition_trivIset: partition P D -> trivIset P.

Lemma partitionS B : partition P D -> B \in P -> B \subset D.

Lemma cover1 A : cover [set A] = A.

Lemma trivIset1 A : trivIset [set A].

Lemma trivIsetD Q : trivIset P -> trivIset (P :\: Q).

Lemma trivIsetU Q : 
  trivIset Q -> trivIset P -> [disjoint cover Q & cover P] -> trivIset (Q :|: P).

Lemma coverD1 S : trivIset P -> S \in P -> cover (P :\ S) = cover P :\: S.

Lemma partitionD1 S : 
  partition P D -> S \in P -> partition (P :\ S) (D :\: S).

Lemma partitionU1 S : 
  partition P D -> S != set0 -> [disjoint S & D] -> partition (S |: P) (S :|: D).

Lemma partition_set0 : partition P set0 = (P == set0).

Section Image.
Variables (T' : finType) (f : T -> T') (inj_f : injective f).
Let fP := [set f @: (S : {set T}) | S in P].

Lemma imset_inj : injective (fun A : {set T} => f @: A).

Lemma imset_disjoint (A B : {pred T}) :
  [disjoint f @: A & f @: B] = [disjoint A & B].

Lemma imset_trivIset : trivIset P = trivIset fP.

Lemma imset0mem : (set0 \in fP) = (set0 \in P).

Lemma imset_partition : partition P D = partition fP (f @: D).
End Image.

Lemma partition_pigeonhole A :
  partition P D -> #|P| <= #|A| -> A \subset D -> {in P, forall B, #|A :&: B| <= 1} ->
  {in P, forall B, A :&: B != set0}.

End partition.

Lemma indexed_partition (I T : finType) (J : {pred I}) (B : I -> {set T}) :
  let P := [set B i | i in J] in
  {in J &, forall i j : I, j != i -> [disjoint B i & B j]} -> 
  (forall i : I, J i -> B i != set0) -> partition P (cover P) /\ {in J&, injective B}.

(* TOTHINK: an alternative definition would be [[set B :&: A | B in P]:\ set0]. 
   Then one has to prove the partition properties, but the lemmas below 
   are simpler to prove. *)

(* This is not part of PR 731 *)

Section partition.
Variable (T : finType) (P : {set {set T}}) (D : {set T}).
Implicit Types (A B S : {set T}).

Definition sub_partition A : {set {set T}} := 
  preim_partition (pblock P) A.

Lemma sub_partitionP A : partition (sub_partition A) A.

Lemma sub_partition_sub A : 
  partition P D -> A \subset D -> sub_partition A \subset [set B :&: A | B in P].

Lemma card_sub_partition A : 
  partition P D -> A \subset D -> #|sub_partition A| <= #|P|.

End partition.
```
