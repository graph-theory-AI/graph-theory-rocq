(** Public-only clients of the raw model support.  They import only GTBase.  The
    support counts branch images and members of supplied lists on genuine pattern
    edges, in either orientation; it ignores lists on non-edges, is empty for the
    empty pattern, and asks nothing of injectivity or of the shape of a list. *)
From GTBase Require Import base model_support.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Positive cases *)

Example branch_images_supported (H G : sgraph) (br : H -> G) (ep : H -> H -> seq G) (h : H) :
  model_support br ep (br h).
Proof. exact: model_support_branch. Qed.

Example genuine_edge_list_supported (H G : sgraph) (br : H -> G) (ep : H -> H -> seq G)
    (u v : H) (x : G) :
  u -- v -> x \in ep u v -> model_support br ep x.
Proof. exact: model_support_edge. Qed.

Example reverse_orientation_supported (H G : sgraph) (br : H -> G) (ep : H -> H -> seq G)
    (u v : H) (x : G) :
  u -- v -> x \in ep v u -> model_support br ep x.
Proof. exact: model_support_edge_rev. Qed.

(** A constant (non-injective) branch map and a list with a repeated vertex that is
    no path at all: the raw support still contains the listed vertex. *)
Example invalid_list_and_constant_branch (G : sgraph) (x y : G) :
  model_support (fun _ : 'K_2 => y) (fun _ _ => [:: x; x]) x.
Proof.
apply: (@model_support_edge 'K_2 G (fun _ => y) (fun _ _ => [:: x; x]) ord0 ord_max x); last by rewrite /= mem_head.
by [].
Qed.

(** ** Negative cases *)

Example empty_pattern_supports_nothing (G : sgraph) (br : 'K_0 -> G)
    (ep : 'K_0 -> 'K_0 -> seq G) (x : G) :
  ~ model_support br ep x.
Proof. exact: model_support_K0. Qed.

(** ['K_1] has no edge: its support is exactly its branch image, whatever the
    list on the non-edge [(ord0, ord0)] contains. *)
Example edgeless_pattern_is_branch_image (G : sgraph) (br : 'K_1 -> G)
    (ep : 'K_1 -> 'K_1 -> seq G) (x : G) :
  model_support br ep x <-> br ord0 = x.
Proof.
have edgeless : forall u v : ('K_1), ~~ (u -- v).
  by move=> u v; rewrite (fintype.ord1 u) (fintype.ord1 v).
apply: (iff_trans (model_support_edgeless br ep x edgeless)).
by split=> [[h <-]|<-]; [rewrite [h]fintype.ord1 | exists ord0].
Qed.

Example nonedge_list_ignored (G : sgraph) (br : 'K_1 -> G) (x : G) :
  br ord0 != x -> ~ model_support br (fun _ _ => [:: x]) x.
Proof.
move=> nx /edgeless_pattern_is_branch_image bx.
by move: nx; rewrite bx eqxx.
Qed.

(** Empty lists on all pattern edges leave only the branch images. *)
Example empty_lists_branch_image_only (H G : sgraph) (br : H -> G) (x : G) :
  model_support br (fun _ _ => [::]) x <-> exists h : H, br h = x.
Proof. by apply: model_support_nil. Qed.

(** Lists on non-edges can be changed freely. *)
Example nonedge_lists_irrelevant (H G : sgraph) (br : H -> G) (ep : H -> H -> seq G) (x : G) :
  model_support br ep x <->
  model_support br (fun u v => if u -- v then ep u v else [:: x]) x.
Proof. by apply: model_support_eq_on_edges => u v ->. Qed.
