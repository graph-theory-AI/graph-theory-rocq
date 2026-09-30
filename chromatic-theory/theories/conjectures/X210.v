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

(** ** X210 statements *****************************************************)

(** Corpus row: arxiv:1803.10962#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1803.10962__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1803.10962__00.json
    English statement: (Dvorak, Esperet, Kang and Ozeki 2020, Conjecture 3, arXiv:1803.10962)
      There are constants C and C' such that every finite simple graph G embeddable in a surface of
      genus g is conflict k-colourable whenever C' * g <= k * k, that is, whenever every edge
      carries at most C*k forbidden colour pairs out of the k by k pairs, some colouring by k
      colours avoids all of them.
    Definitions: [x210_conflict_assignment G k C F] - F is symmetric under swapping the two ends
      of an edge and every edge carries at most C*k forbidden ordered colour pairs (this file);
      [x210_conflict_colouring G k F] - a colouring by ['I_k] avoiding every forbidden pair on every
      edge (this file); [x210_conflict_k_colourable_under_bound G k C] (this file);
      [x210_euler_genus_embeddable G g] - a synonym for base's [surface_embeddable g G] (this file,
      GTBase base/theories/surface.v).
    Notes: KNOWN UNFAITHFUL ENCODING, corpus leg blocked. The faithfulness audit of 2026-07-17,
      meta/BLOCKED_RETARGETING_AUDIT.md and the row's verification_note, found that the positivity
      of the two constants is dropped: the source requires C, C' > 0, and the whole content of the
      conjecture lies in the positive constant C multiplying k in the conflict bound, the context
      even noting that C < 1/2 is forced, whereas the Rocq body quantifies over naturals C and C'
      with no positivity and leaves k otherwise unrestricted, so degenerate witnesses such as C = 0
      are admitted. The conflict machinery itself is faithful. The surface primitive is moreover
      orientable genus rather than Euler genus. The body is left untouched here, WP4 changes
      comments only.
      V counts every vertex including isolated ones (base fix 2026-09-23): the old count saw
      only the vertices carrying a dart, so the Euler count overstated the genus of every
      graph with an isolated vertex and this hypothesis admitted fewer graphs than intended. *)
Definition surface_conflict_colouring_sqrt_genus_statement : Prop :=
  exists C C' : nat,
    forall (G : sgraph) (g k : nat),
      x210_euler_genus_embeddable G g ->
      C' * g <= k * k ->
      x210_conflict_k_colourable_under_bound G k C.
