(** * Chromatic.conjectures.X210 -- v2 surface conflict-colouring row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X210 vocabulary ***********************************************)

Definition x210_euler_genus_embeddable (G : sgraph) (g : nat) : Prop :=
  surface_embeddable g G.

Definition x210_conflict_assignment
    (G : sgraph) (k C : nat) (F : G -> G -> 'I_k -> 'I_k -> bool) : Prop :=
  (forall u v : G, u -- v ->
    forall a b : 'I_k, F u v a b = F v u b a) /\
  (forall u v : G, u -- v ->
    #|[set ab : 'I_k * 'I_k | F u v ab.1 ab.2]| <= C * k).

Definition x210_conflict_colouring
    (G : sgraph) (k : nat) (F : G -> G -> 'I_k -> 'I_k -> bool) : Prop :=
  exists col : G -> 'I_k,
    forall u v : G, u -- v -> ~~ F u v (col u) (col v).

Definition x210_conflict_k_colourable_under_bound
    (G : sgraph) (k C : nat) : Prop :=
  forall F : G -> G -> 'I_k -> 'I_k -> bool,
    @x210_conflict_assignment G k C F -> @x210_conflict_colouring G k F.

(** The source's rational bound (repair of 2026-10-26): at most (p/q) * k forbidden pairs on every
    edge, i.e. q * #conflicts <= p * k.  The natural-constant helpers above stay for the frozen
    migration copy. *)
Definition x210_conflict_assignment_rat
    (G : sgraph) (k p q : nat) (F : G -> G -> 'I_k -> 'I_k -> bool) : Prop :=
  (forall u v : G, u -- v ->
    forall a b : 'I_k, F u v a b = F v u b a) /\
  (forall u v : G, u -- v ->
    q * #|[set ab : 'I_k * 'I_k | F u v ab.1 ab.2]| <= p * k).

Definition x210_conflict_k_colourable_under_rat_bound
    (G : sgraph) (k p q : nat) : Prop :=
  forall F : G -> G -> 'I_k -> 'I_k -> bool,
    @x210_conflict_assignment_rat G k p q F -> @x210_conflict_colouring G k F.

(** Teeth: the conflict bound is load-bearing.  With p = q = 1 (C = 1, outside the source's
    forced C < 1/2) the single edge K_2 with its one conflict (the only colour at both ends) is
    not conflict 1-colourable; with p = 0 no conflict is allowed and every colouring works, which
    is why the statement asks for 0 < p. *)
Lemma x210_conflict_bound_teeth : ~ x210_conflict_k_colourable_under_rat_bound 'K_2 1 1 1.
Proof.
move=> h; have [] := h (fun _ _ _ _ => true).
  split=> // u v _.
  by rewrite (_ : [set ab : 'I_1 * 'I_1 | true] = setT) ?cardsT ?card_prod ?card_ord //;
    apply/setP => ab; rewrite !inE.
by move=> col /(_ ord0 ord_max) /(_ isT).
Qed.

(** ** X210 statements *****************************************************)

(** Corpus row: arxiv:1803.10962#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1803.10962__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1803.10962__00.json
    English statement: (Dvorak, Esperet, Kang and Ozeki 2020, Conjecture 3, arXiv:1803.10962)
      There are positive rationals C = p/q and C'^2 = p'/q' such that every connected finite simple
      graph G embeddable in an orientable surface of genus g is conflict k-colourable, for every
      positive k with p' * g <= q' * k * k (that is, k >= C' * sqrt g), whenever every edge
      carries at most C*k forbidden colour pairs out of the k by k pairs: some colouring by k
      colours then avoids all of them.
    Definitions: [x210_conflict_assignment_rat G k p q F] - F is symmetric under swapping the two
      ends of an edge and every edge carries at most (p/q)*k forbidden ordered colour pairs (this
      file); [x210_conflict_colouring G k F] - a colouring by ['I_k] avoiding every forbidden pair
      on every edge (this file); [x210_conflict_k_colourable_under_rat_bound G k p q] (this file);
      [x210_euler_genus_embeddable G g] - a synonym for base's [surface_embeddable g G], the
      orientable genus of a connected graph at most g (this file, GTBase base/theories/surface.v);
      [connected [set: G]] - G is connected.
    Notes: PARTIAL: non-orientable surfaces are not modelled, so the row covers only the graphs
      embeddable on orientable surfaces.  REPAIRED 2026-10-26 (coordination/PROGRAMME.md A2;
      record meta/STATEMENT_IMPROVEMENTS.md; the row is frozen by the F1 surface_embeddable
      family; Lancelot's routing, message 10).  The earlier body was FALSE, not just
      vacuous-looking: it admitted k = 0, and K_1, which is planar, has no colouring by no colour,
      for every C and C' (X210Legacy_row_false in the certificate file).  Rational constants are
      equivalent to the source's real ones, by monotonicity: a smaller C asks for less and a
      larger C' admits fewer k, so a real pair (C, C') yields rationals 0 < p/q <= C and
      p'/q' >= C'^2, and conversely.  The guards: connected [set: G] is the rule for
      surface_embeddable, which understates the genus of a disconnected graph, and it loses
      nothing, since the source's claim applies to each component; 0 < k is the source's implicit
      positivity, since no graph with a vertex is 0-colourable.  An orientable surface of genus g
      has Euler genus 2g, a factor that C' absorbs.  Conflicts follow the source (arXiv:1803.10962
      e-print sha256 0db384dc, dp1.tex lines 80-83): each edge uv carries a list K(u,v) of ordered
      colour pairs, a pair (a, b) forbidding a at u together with b at v; F u v is K(u,v), F v u
      its transpose (F u v a b = F v u b a), so each edge's list is counted once against
      (p/q) * k.  The source's remark that C < 1/2 is forced is not encoded; it constrains the
      constants, not the claim.  The natural-constant helpers above stay unchanged for the frozen
      migration copy. *)
Definition surface_conflict_colouring_sqrt_genus_statement : Prop :=
  exists p q p' q' : nat,
    [/\ 0 < p, 0 < q, 0 < p', 0 < q' &
      forall (G : sgraph) (g k : nat),
        connected [set: G] ->
        0 < k ->
        x210_euler_genus_embeddable G g ->
        p' * g <= q' * (k * k) ->
        x210_conflict_k_colourable_under_rat_bound G k p q].
