(** * A cost-coupled computation model — Track-B foundation for positive algorithmic claims.

    THE PROBLEM THIS SOLVES (D7 audit): with a decoupled abstract model
    ([exists (alg cost : Input -> nat), ...]) every "there is an efficient
    algorithm" statement is VACUOUSLY TRUE via [alg := exact-answer, cost := 0].
    Bundling run and cost in a Record does not help — the junk inhabitant still
    exists — and an uninterpreted [realizes] predicate is either trivially
    satisfiable (existential) or trivially refutable (universal).  The honest fix
    is a FIXED CLASS OF ALGORITHMS: programs are SYNTAX ([prog], a small total
    combinator language), and BOTH the output ([prun]) and the cost ([pcost]) are
    computed by ONE fixed interpreter ([eval]) from that same syntax.  Cost is
    therefore FORCED by the object that produces the output:
      - [pcost_pos]            : every program costs ≥ 1 on every input;
      - [no_zero_cost_program] : the old attack is impossible by construction.

    THE MODEL.  [data] = unary naturals + pairs + lists (a universal first-order
    data type); [prog] = identity/constants/composition/pairing/projections/
    cons/list-case/structural equality/arithmetic/bounded iteration ([Pnatrec])/
    list catamorphism ([Pfold]) — total primitive recursion over lists and nats,
    with unit-cost metering (primitive steps cost 1; [Peq]/[Padd]/[Pmul] cost the
    input size).  Totality keeps everything axiom-free (no fuel, no partiality).

    FAITHFULNESS META-NOTE (the model's analogue of wagner_planar = planarity):
    the class contains P — any polynomial-time algorithm is implementable as a
    [prog] with polynomially bounded [pcost] (simulate the machine's step
    function with [Pnatrec] under a [Pmul]-computed clock) — and conversely a
    poly-[pcost] program is a poly-time algorithm up to the interpreter's
    polynomial overhead.  So [exists p, realizes ... /\ poly_cost_on ... p] is
    the poly-time Church–Turing reading of "there is a polynomial algorithm";
    the model also CONTAINS super-polynomial programs (primitive recursion is
    bigger than P), which the cost bound excludes from positive claims — that
    direction is fully formal.  SIZE IS UNARY ([dsize]); for graph encodings
    [dsize (enc_graph G)] is Θ(#|G|²), so poly-in-[dsize] = poly-in-vertices. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph.
Set Implicit Arguments.
Unset Strict Implicit.

(** ** Data *)

Inductive data : Type :=
| Dnat  of nat
| Dpair of data & data
| Dnil
| Dcons of data & data.

Fixpoint dsize (d : data) : nat :=
  match d with
  | Dnat n => n.+1
  | Dpair a b => (dsize a + dsize b).+1
  | Dnil => 1
  | Dcons a b => (dsize a + dsize b).+1
  end.

Lemma dsize_pos (d : data) : 0 < dsize d.
Proof. by case: d. Qed.

Fixpoint deq (a b : data) : bool :=
  match a, b with
  | Dnat m, Dnat n => m == n
  | Dpair x y, Dpair u v => deq x u && deq y v
  | Dnil, Dnil => true
  | Dcons x y, Dcons u v => deq x u && deq y v
  | _, _ => false
  end.

Lemma deq_refl (d : data) : deq d d.
Proof. by elim: d => /= [n|a IHa b IHb||a IHa b IHb]; rewrite ?eqxx ?IHa ?IHb. Qed.

(** ** Programs (a fixed class of algorithms) *)

Inductive prog : Type :=
| Pid | Pconst of data
| Pcomp of prog & prog          (* left, then right *)
| Ppair of prog & prog | Pfst | Psnd
| PconsP of prog & prog
| PcaseL of prog & prog         (* Dcons a b ⇒ right on (Dpair a b); else left *)
| Peq                           (* Dpair a b ⇒ Dnat (deq a b) *)
| Padd | Pmul | Ppred
| Pnatrec of prog               (* Dpair (Dnat n) seed ⇒ iterate body n times *)
| Pfold of prog & prog.         (* list catamorphism: nil-case, cons-case *)

(** ** The ONE interpreter computing output AND step count *)

Fixpoint eval (p : prog) (d : data) : data * nat :=
  match p with
  | Pid => (d, 1)
  | Pconst k => (k, 1)
  | Pcomp p1 p2 =>
      let r1 := eval p1 d in let r2 := eval p2 r1.1 in
      (r2.1, (r1.2 + r2.2).+1)
  | Ppair p1 p2 =>
      let r1 := eval p1 d in let r2 := eval p2 d in
      (Dpair r1.1 r2.1, (r1.2 + r2.2).+1)
  | Pfst => (if d is Dpair a _ then a else d, 1)
  | Psnd => (if d is Dpair _ b then b else d, 1)
  | PconsP p1 p2 =>
      let r1 := eval p1 d in let r2 := eval p2 d in
      (Dcons r1.1 r2.1, (r1.2 + r2.2).+1)
  | PcaseL p1 p2 =>
      match d with
      | Dcons a b => let r := eval p2 (Dpair a b) in (r.1, r.2.+1)
      | _ => let r := eval p1 d in (r.1, r.2.+1)
      end
  | Peq => (if d is Dpair a b then Dnat (deq a b) else Dnat 0, dsize d)
  | Padd => (if d is Dpair (Dnat a) (Dnat b) then Dnat (a + b) else Dnat 0, dsize d)
  | Pmul => (if d is Dpair (Dnat a) (Dnat b) then Dnat (a * b) else Dnat 0, dsize d)
  | Ppred => (if d is Dnat n then Dnat n.-1 else Dnat 0, 1)
  | Pnatrec body =>
      match d with
      | Dpair (Dnat n) seed =>
          (fix N (n : nat) (acc : data) (c : nat) : data * nat :=
             match n with
             | 0 => (acc, c.+1)
             | m.+1 => N m (eval body acc).1 (c + (eval body acc).2).+1
             end) n seed 0
      | _ => (d, 1)
      end
  | Pfold pn pc =>
      (fix F (d : data) : data * nat :=
         match d with
         | Dcons a b =>
             (  (eval pc (Dpair a (F b).1)).1,
                ((F b).2 + (eval pc (Dpair a (F b).1)).2).+1 )
         | _ => ((eval pn d).1, (eval pn d).2.+1)
         end) d
  end.

Definition prun  (p : prog) (d : data) : data := (eval p d).1.
Definition pcost (p : prog) (d : data) : nat  := (eval p d).2.

(** ** The coupling guarantee *)

Lemma pcost_pos (p : prog) (d : data) : 0 < pcost p d.
Proof.
rewrite /pcost; case: p => [|k|p1 p2|p1 p2|||p1 p2|p1 p2|||||body|pn pc] //=;
  try exact: dsize_pos.
- by case: d.
- case: d => [n|a s||a b] //=; case: a => [n|||] //=.
  elim: n s (0) => [|m IH] acc c //=.
  by apply: ltn_trans (IH _ _); rewrite ltnS leq_addr.
- by case: d.
Qed.

(** The D7-audit attack ([alg := exact-answer, cost := 0]) is impossible. *)
Lemma no_zero_cost_program : ~ (exists p : prog, forall d : data, pcost p d = 0).
Proof. by case=> p H; have := pcost_pos p Dnil; rewrite H. Qed.

(** ** Cost and correctness predicates (both about the SAME program) *)

(** Polynomially bounded step count over an encoded instance family. *)
Definition poly_cost_on (T : Type) (enc : T -> data) (p : prog) : Prop :=
  exists c k : nat, forall x : T, pcost p (enc x) <= c * (dsize (enc x)) ^ k + c.

(** The program's OUTPUT satisfies a per-instance specification. *)
Definition realizes_on (T : Type) (enc : T -> data) (Spec : T -> data -> Prop)
  (p : prog) : Prop :=
  forall x : T, Spec x (prun p (enc x)).

(** Decision problems: output [Dnat 1] exactly on yes-instances. *)
Definition decides_on (T : Type) (enc : T -> data) (P : T -> Prop) (p : prog) : Prop :=
  forall x : T, prun p (enc x) = Dnat 1 <-> P x.

Definition decides_on_class (T : Type) (enc : T -> data)
    (Class P : T -> Prop) (p : prog) : Prop :=
  forall x : T, Class x -> (prun p (enc x) = Dnat 1 <-> P x).

Definition polytime_decides_on_class (T : Type) (enc : T -> data)
    (Class P : T -> Prop) : Prop :=
  exists p : prog, poly_cost_on enc p /\ decides_on_class enc Class P p.

Definition polytime_outputs_on_class (T : Type) (enc : T -> data)
    (Class : T -> Prop) (Spec : T -> data -> Prop) : Prop :=
  exists p : prog, poly_cost_on enc p /\
    forall x : T, Class x -> Spec x (prun p (enc x)).

(** ** Encodings *)

Definition enc_list (ds : seq data) : data := foldr Dcons Dnil ds.
Definition enc_bool (b : bool) : data := Dnat b.
Definition enc_nat (n : nat) : data := Dnat n.

Definition data_nat_value (d : data) : nat :=
  if d is Dnat n then n else 0.

(** The natural output decoder: [data_nth_nat d i] is the natural at position [i] of an output
    datum, read through its [Dcons] cells.  Position [0] of a cell [Dcons e rest] is [e]'s natural
    value ([n] for [e = Dnat n], [0] for any other entry), position [j.+1] is position [j] of
    [rest]; a scalar [Dnat n], as a whole datum or as a malformed list tail, reads [n] at its
    position [0] and [0] after it; [Dnil] and [Dpair] read [0] at every position
    ([data_nth_nat0], [data_nth_natS]).  On an encoded list of naturals it is [nth 0], positions
    past the end reading [0] ([data_nth_nat_enc_list]).  It reads naturals only: a colouring
    adapter (modulo [k], or the enum rank of a vertex) is a separate layer. *)
Fixpoint data_nth_nat (d : data) (i : nat) : nat :=
  match d, i with
  | Dcons (Dnat n) _, 0 => n
  | Dcons _ rest, j.+1 => data_nth_nat rest j
  | Dnat n, 0 => n
  | _, _ => 0
  end.

Lemma data_nth_nat0 (d : data) :
  data_nth_nat d 0 = data_nat_value (if d is Dcons e _ then e else d).
Proof. by case: d => // -[]. Qed.

Lemma data_nth_natS (d : data) (i : nat) :
  data_nth_nat d i.+1 = if d is Dcons _ rest then data_nth_nat rest i else 0.
Proof. by case: d => // -[]. Qed.

Lemma data_nth_nat_Dnil (i : nat) : data_nth_nat Dnil i = 0.
Proof. by case: i. Qed.

Lemma data_nth_nat_enc_list (s : seq nat) (i : nat) :
  data_nth_nat (enc_list [seq enc_nat n | n <- s]) i = nth 0 s i.
Proof. by rewrite /enc_list; elim: s i => [|n s IHs] [|i] //=. Qed.

Lemma data_nth_nat_enc_list_default (s : seq nat) (i : nat) :
  size s <= i -> data_nth_nat (enc_list [seq enc_nat n | n <- s]) i = 0.
Proof. by move=> le_s_i; rewrite data_nth_nat_enc_list nth_default. Qed.

(** A graph as its adjacency matrix (row-major list of boolean lists). *)
Definition enc_graph (G : sgraph) : data :=
  enc_list [seq enc_list [seq enc_bool (i -- j) | j <- enum G] | i <- enum G].

Definition polytime_decides_graph_on
    (Class P : sgraph -> Prop) : Prop :=
  polytime_decides_on_class enc_graph Class P.

Definition polytime_outputs_graph_on
    (Class : sgraph -> Prop) (Spec : sgraph -> data -> Prop) : Prop :=
  polytime_outputs_on_class enc_graph Class Spec.

Definition linear_time_cost_on (T : Type) (enc : T -> data) (p : prog) : Prop :=
  exists c : nat, forall x : T, pcost p (enc x) <= c * dsize (enc x) + c.

Definition linear_time_outputs_on_class (T : Type) (enc : T -> data)
    (Class : T -> Prop) (Spec : T -> data -> Prop) : Prop :=
  exists p : prog, linear_time_cost_on enc p /\
    forall x : T, Class x -> Spec x (prun p (enc x)).

Definition linear_time_outputs_graph_on
    (Class : sgraph -> Prop) (Spec : sgraph -> data -> Prop) : Prop :=
  linear_time_outputs_on_class enc_graph Class Spec.

(** ** Non-vacuity grounding *)

(** A concrete program deciding a (trivial) predicate within a poly budget —
    the positive-claim SHAPE is inhabited... *)
Lemma trivial_decider :
  exists p : prog,
    decides_on enc_graph (fun _ : sgraph => True) p /\ poly_cost_on enc_graph p.
Proof.
exists (Pconst (Dnat 1)); split=> [x|]; first by [].
by exists 1, 0; move=> x; rewrite /pcost /= expn0 muln1.
Qed.

(** ...and the model genuinely computes: structural equality on real data. *)
Lemma Peq_diag (d : data) : prun Peq (Dpair d d) = Dnat 1.
Proof. by rewrite /prun /= deq_refl. Qed.
