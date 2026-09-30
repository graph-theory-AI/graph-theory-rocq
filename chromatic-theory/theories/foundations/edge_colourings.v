(** * Chromatic.foundations.edge_colourings -- the complete graph as a multigraph,
      and its chromatic index for an even number of vertices

    GTBase reduces edge colouring to VERTEX colouring of the line graph of a
    loopless MULTIGRAPH ([line_graph], [chromatic_index]), whereas the X219 row
    [list_chromatic_index_even_clique_statement] speaks about the SIMPLE graph
    ['K_n] through the predicate [x219_edge_choosable].  This file provides the
    ingredients that bridge the two encodings (corpus relation e039):

      [kn_mgraph n]          -- ['K_n] as a loopless multigraph: one edge per
                                strictly increasing pair of vertices, so the
                                edge set is exactly that of ['K_n] and there are
                                no parallel edges;
      [kn_loopless]          -- it is loopless;
      [kn_mk] / [kn_mkP]     -- the edge carrying an unordered pair [{u, v}];
      [kn_edge_choosable_of] -- [choosable (line_graph (kn_mgraph n)) k] yields
                                the [x219_edge_choosable]-shaped conclusion for
                                ['K_n]: a list colouring of the line graph's
                                vertices IS a proper list edge colouring;
      [kn_rr] / [kn_rr_core] -- the ROUND-ROBIN colouring and its arithmetic
                                core;
      [kn_chi_line]          -- F8: for an ODD [N], the line graph of
                                [kn_mgraph N.+1] is [N]-colourable, i.e.
                                chi'(K_n) <= n - 1 for even [n].

    The round-robin 1-factorisation: the vertex [N] of [K_{N+1}] plays the role
    of "infinity"; colour the edge [{i, j}] with [i, j < N] by [(i + j) %% N] and
    the edge [{i, N}] by [(2 * i) %% N].  Properness at a finite vertex [i] is
    cancellation of [i] in [i + j = i + j'] modulo [N] (the edge to infinity
    counts as [i + i]); properness at infinity is that [2] is invertible modulo
    an ODD [N].

    Nothing here resolves a conjecture: [kn_chi_line] is the classical
    1-factorisation of a complete graph of even order, and the rest is carrier
    bookkeeping. *)

From GTBase Require Import base.
From GraphTheory Require Import mgraph.
From Chromatic.foundations Require Import chi_bounding.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Two modular-cancellation lemmas ************************************)

Lemma modn_addl_inj (N m a c : nat) :
  a < N -> c < N -> (m + a) %% N = (m + c) %% N -> a = c.
Proof.
move=> aN cN /eqP; rewrite eqn_modDl => /eqP.
by rewrite !modn_small.
Qed.

(** [2] is invertible modulo an ODD [N]. *)
Lemma modn_dbl_inj (N a c : nat) :
  odd N -> a < N -> c < N -> (a * 2) %% N = (c * 2) %% N -> a = c.
Proof.
have key : forall p q : nat, odd N -> p <= q -> q < N ->
    (p * 2) %% N = (q * 2) %% N -> p = q.
  move=> p q oN pq qN e2.
  have dvd : N %| q * 2 - p * 2.
    by rewrite -eqn_mod_dvd ?leq_mul2r ?pq ?orbT // e2.
  rewrite -mulnBl mulnC Gauss_dvdr ?coprimen2 // in dvd.
  have qp0 : q - p = 0.
    case: (posnP (q - p)) => // lt.
    by move: dvd; rewrite gtnNdvd //; apply: leq_ltn_trans (leq_subr _ _) qN.
  by apply/eqP; rewrite eqn_leq pq andTb -subn_eq0 qp0.
move=> oN aN cN eqac; case: (leqP a c) => [le|lt].
  exact: key oN le cN eqac.
by apply/esym; apply: key oN (ltnW lt) aN (esym eqac).
Qed.

(** ** ['K_n] as a loopless multigraph ************************************)

Section KnMulti.
Variable n : nat.

(** One edge per strictly increasing pair of vertices. *)
Definition kn_edge : Type := {p : 'I_n * 'I_n | p.1 < p.2}.

Definition kn_mgraph : mgraph :=
  @Graph unit unit 'I_n kn_edge
    (fun b e => if b then (sval e).2 else (sval e).1)
    (fun _ => tt) (fun _ => tt).

Lemma kn_loopless : loopless kn_mgraph.
Proof. by move=> e /=; rewrite neq_ltn (svalP e). Qed.

Lemma kn_edge_eq (e e' : kn_edge) : sval e = sval e' -> e = e'.
Proof. by move=> h; apply: val_inj; exact: h. Qed.

Lemma kn_incident (x : kn_mgraph) (e : edge kn_mgraph) :
  incident x e = ((sval e).1 == x) || ((sval e).2 == x).
Proof.
apply/existsP/idP => [[b]|]; first by case: b => /= /eqP ->; rewrite eqxx ?orbT.
by case/orP=> h; [exists false | exists true].
Qed.

(** The increasing representative of the unordered pair [{u, v}], and the edge
    of ['K_n] it defines (as a partial function, [None] when [u = v]). *)
Definition kn_srt (u v : 'I_n) : 'I_n * 'I_n := if (u < v)%N then (u, v) else (v, u).

Definition kn_mk (u v : 'I_n) : option kn_edge := insub (kn_srt u v).

Lemma kn_srtE (u v : 'I_n) : kn_srt u v = (u, v) \/ kn_srt u v = (v, u).
Proof. by rewrite /kn_srt; case: ifP => _; [left | right]. Qed.

Lemma kn_srtC (u v : 'I_n) : kn_srt u v = kn_srt v u.
Proof.
rewrite /kn_srt; case: ifP => h1; case: ifP => h2 //.
  by move: h2; rewrite ltnNge (ltnW h1).
have e : u = v by apply: val_inj; apply/eqP; rewrite eqn_leq leqNgt h2 leqNgt h1.
by rewrite e.
Qed.

Lemma kn_srtP (u v : 'I_n) : u != v -> (kn_srt u v).1 < (kn_srt u v).2.
Proof.
move=> uv; rewrite /kn_srt; case: ifP => h //=.
by move: uv; rewrite -val_eqE neq_ltn h.
Qed.

Lemma kn_mkC (u v : 'I_n) : kn_mk u v = kn_mk v u.
Proof. by rewrite /kn_mk kn_srtC. Qed.

(** For distinct [u], [v] the pair does have an edge, whose endpoint pair is one
    of the two orderings. *)
Lemma kn_mkP (u v : 'I_n) : u != v ->
  exists2 e : kn_edge, kn_mk u v = Some e &
    sval e = (u, v) \/ sval e = (v, u).
Proof.
move=> uv; rewrite /kn_mk; case: insubP => [e _ ve|nP].
  by exists e => //; case: (kn_srtE u v) => h; rewrite -h; [left | right];
     exact: ve.
by rewrite (kn_srtP uv) in nP.
Qed.

End KnMulti.

Arguments kn_edge : clear implicits.

(** ** The bridge: line-graph choosability gives edge-choosability ********)

Lemma kn_edge_choosable_of (n k : nat) : 1 < n ->
  choosable (line_graph (kn_mgraph n)) k ->
  forall (C : finType) (L : 'I_n -> 'I_n -> {set C}),
    (forall u v : 'I_n, L u v = L v u) ->
    (forall u v : 'I_n, u != v -> k <= #|L u v|) ->
    exists col : 'I_n -> 'I_n -> C,
      [/\ forall u v : 'I_n, col u v = col v u,
          forall u v : 'I_n, u != v -> col u v \in L u v &
          forall u v w : 'I_n, u != v -> u != w -> v != w ->
            col u v != col u w].
Proof.
move=> n2 ch C L Lsym Lcard.
pose L' (e : kn_edge n) : {set C} := L (sval e).1 (sval e).2.
have L'card : forall e : line_graph (kn_mgraph n), k <= #|L' e|.
  by move=> e; apply: Lcard; rewrite -val_eqE neq_ltn (svalP e).
have [f [fmem fprop]] := ch C L' L'card.
have e0 : kn_edge n := exist _ (Ordinal (ltnW n2), Ordinal n2) (ltn0Sn 0).
pose col (u v : 'I_n) : C := if kn_mk u v is Some e then f e else f e0.
exists col; split.
- by move=> u v; rewrite /col kn_mkC.
- move=> u v uv; have [e eE [de|de]] := kn_mkP uv; rewrite /col eE.
  + by move: (fmem e); rewrite /L' de.
  + by move: (fmem e); rewrite /L' de Lsym.
move=> u v w uv uw vw.
have [e eE de] := kn_mkP uv; have [e' e'E de'] := kn_mkP uw.
rewrite /col eE e'E; apply: fprop.
rewrite /= /line_rel /share_endpoint; apply/andP; split.
  apply/negP => /eqP ee'.
  have svE : sval e = sval e' by rewrite ee'.
  case: de => de; case: de' => de'; rewrite de de' in svE;
    move: (congr1 Datatypes.fst svE) (congr1 Datatypes.snd svE) => /= q1 q2.
  + by move: vw; rewrite q2 eqxx.
  + by move: uw; rewrite q1 eqxx.
  + by move: uv; rewrite -q1 eqxx.
  + by move: vw; rewrite q1 eqxx.
apply/existsP; exists u; apply/andP; split.
  by case: de => de; rewrite kn_incident de /= eqxx ?orbT.
by case: de' => de'; rewrite kn_incident de' /= eqxx ?orbT.
Qed.

(** ** F8: the round-robin 1-factorisation *******************************)

(** The round-robin colour of an edge of [kn_mgraph N.+1]: the vertex [N] is
    "infinity" and the edge [{i, N}] takes the colour [2 * i]. *)
Definition kn_rr (N : nat) (e : kn_edge N.+1) : nat :=
  if val (sval e).2 == N then val (sval e).1 * 2
  else val (sval e).1 + val (sval e).2.

(** The arithmetic core: two edges of [K_{N+1}] sharing a vertex [x] get the
    same round-robin colour only if they are equal. *)
Lemma kn_rr_core (N a b c d x : nat) :
  odd N ->
  a < b -> b <= N -> c < d -> d <= N ->
  ((x == a) || (x == b)) -> ((x == c) || (x == d)) ->
  (if b == N then a * 2 else a + b) %% N =
  (if d == N then c * 2 else c + d) %% N ->
  (a == c) && (b == d).
Proof.
move=> oN ab bN cd dN hx hx'.
have aN : a < N by apply: leq_trans ab bN.
have cN : c < N by apply: leq_trans cd dN.
case: (eqVneq b N) => [bE|bne]; case: (eqVneq d N) => [dE|dne].
- rewrite ?bE ?dE !eqxx => /(modn_dbl_inj oN aN cN) ->.
  by rewrite eqxx ?bE ?dE ?eqxx.
- (* b = N, d < N: the shared vertex cannot be b *)
  have dlt : d < N by rewrite ltn_neqAle dne dN.
  have xa : x = a.
    case/orP: hx => [/eqP->//|/eqP xb].
    case/orP: hx' => [/eqP xc|/eqP xd].
      by move: cN; rewrite -xc xb ?bE ltnn.
    by move: dlt; rewrite -xd xb ?bE ltnn.
  rewrite ?bE ?eqxx ?(negbTE dne) /= muln2 -addnn => eq2.
  case/orP: hx' => [/eqP xc|/eqP xd].
    have ac : a = c by rewrite -xa xc.
    rewrite -ac in eq2.
    have ad := modn_addl_inj aN dlt eq2.
    by move: cd; rewrite -ac -ad ltnn.
  have ad : a = d by rewrite -xa xd.
  rewrite -ad [c + a]addnC in eq2.
  have ac := modn_addl_inj aN cN eq2.
  by move: cd; rewrite -ac -ad ltnn.
- (* b < N, d = N: the shared vertex cannot be d *)
  have blt : b < N by rewrite ltn_neqAle bne bN.
  have xc : x = c.
    case/orP: hx' => [/eqP->//|/eqP xd].
    case/orP: hx => [/eqP xa|/eqP xb].
      by move: aN; rewrite -xa xd ?dE ltnn.
    by move: blt; rewrite -xb xd ?dE ltnn.
  rewrite ?dE ?eqxx ?(negbTE bne) /= muln2 -addnn => eq2.
  case/orP: hx => [/eqP xa|/eqP xb].
    have ca : c = a by rewrite -xc xa.
    rewrite ca in eq2.
    have ba := modn_addl_inj blt aN eq2.
    by move: ab; rewrite ba ltnn.
  have cb : c = b by rewrite -xc xb.
  rewrite cb addnC in eq2.
  have ab' := modn_addl_inj aN blt eq2.
  by move: ab; rewrite ab' ltnn.
- (* both edges finite *)
  have blt : b < N by rewrite ltn_neqAle bne bN.
  have dlt : d < N by rewrite ltn_neqAle dne dN.
  rewrite ?(negbTE bne) ?(negbTE dne) /= => eq2.
  case/orP: hx => [/eqP xa|/eqP xb]; case/orP: hx' => [/eqP xc|/eqP xd].
  + have ac : a = c by rewrite -xa xc.
    rewrite -ac in eq2.
    by rewrite ac eqxx (modn_addl_inj blt dlt eq2) eqxx.
  + have ad : a = d by rewrite -xa xd.
    rewrite -ad [c + a]addnC in eq2.
    have bc := modn_addl_inj blt cN eq2.
    by move: cd; rewrite -bc -ad ltnNge (ltnW ab).
  + have bc : b = c by rewrite -xb xc.
    rewrite -bc addnC in eq2.
    have ad := modn_addl_inj aN dlt eq2.
    by move: cd; rewrite -bc -ad ltnNge (ltnW ab).
  + have bd : b = d by rewrite -xb xd.
    rewrite -bd [a + b]addnC [c + b]addnC in eq2.
    by rewrite (modn_addl_inj aN cN eq2) eqxx bd eqxx.
Qed.

Lemma kn_chi_line (N : nat) :
  odd N -> χ([set: line_graph (kn_mgraph N.+1)]) <= N.
Proof.
move=> oN.
have Npos : 0 < N by case: N oN.
pose f (e : kn_edge N.+1) : 'I_N := Ordinal (ltn_pmod (kn_rr e) Npos).
have hf : forall e e' : line_graph (kn_mgraph N.+1), e -- e' -> f e != f e'.
  move=> e e' he.
  have [ne sh] : (e != e') /\ share_endpoint e e'.
    by move: he; rewrite /= /line_rel => /andP[].
  have [x /andP[xe xe']] :
      exists x : kn_mgraph N.+1, incident x e && incident x e'.
    by move: sh; rewrite /share_endpoint => /existsP.
  apply/negP => /eqP fe.
  have eqmod : kn_rr e %% N = kn_rr e' %% N.
    by have := f_equal (@nat_of_ord N) fe.
  have bN : val (sval e).2 <= N by rewrite -ltnS (ltn_ord (sval e).2).
  have dN : val (sval e').2 <= N by rewrite -ltnS (ltn_ord (sval e').2).
  have hx : (val x == val (sval e).1) || (val x == val (sval e).2).
    by move: xe; rewrite kn_incident => /orP[/eqP<-|/eqP<-]; rewrite eqxx ?orbT.
  have hx' : (val x == val (sval e').1) || (val x == val (sval e').2).
    by move: xe'; rewrite kn_incident => /orP[/eqP<-|/eqP<-]; rewrite eqxx ?orbT.
  move: eqmod; rewrite /kn_rr => eqmod.
  have /andP[/eqP q1 /eqP q2] :=
    kn_rr_core oN (svalP e) bN (svalP e') dN hx hx' eqmod.
  move/negP: ne; apply; apply/eqP; apply: kn_edge_eq.
  rewrite [sval e]surjective_pairing [sval e']surjective_pairing.
  by rewrite (val_inj q1) (val_inj q2).
by have := chi_le_palette hf; rewrite card_ord.
Qed.

Print Assumptions modn_dbl_inj.
Print Assumptions kn_edge_choosable_of.
Print Assumptions kn_chi_line.
