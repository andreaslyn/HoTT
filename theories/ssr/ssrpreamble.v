Require Export HoTT.Basics.Overture.
Require Export HoTT.Types.Bool.

Global Unset Asymmetric Patterns.

Notation "'Prop' @{ i }" := Type@{i} (at level 0, no associativity, only parsing).
Notation "'Prop'" := Type (at level 0, only parsing).

Notation "'Set' @{ i }" := Type@{i} (at level 0, no associativity, only parsing).
Notation "'Set'" := Type (at level 0, only parsing).

Notation eq := paths.

Notation eq_refl := idpath.
Notation refl_equal := idpath.

Notation eq_ind := paths_rec.
Notation eq_ind_r := paths_rec_r.
Notation eq_rect := paths_rec.
Notation eq_rect_r := paths_rec_r.

Notation proj1 := fst.
Notation proj2 := snd.

Definition projT1 := @proj1_sig.
Arguments projT1 [A P].

Definition projT2 := @proj2_sig.
Arguments projT2 [A P].

Definition sym_eq := @inverse.
Arguments sym_eq [A x y] p.

Notation sym_equal := sym_eq.

Definition sym_not_eq := @symmetric_neq.
Arguments sym_not_eq [A x y].

Definition trans_eq := @concat.
Arguments trans_eq [A x y z] p q.

Definition f_equal := @ap.
Arguments f_equal [A B]%type_scope f%function_scope [x y] p%path_scope.

Definition f_equal2 (A1 A2 B : Type) (f : A1 -> A2 -> B)
  (x1 y1 : A1) (x2 y2 : A2) (p1 : x1 = y1) (p2 : x2 = y2)
  : f x1 x2 = f y1 y2
  := match ap f p1 in _ = g return f x1 x2 = g y2 with
     | idpath => ap (f x1) p2
     end.
Arguments f_equal2 [A1 A2 B] f [x1 y1 x2 y2] p1 p2.

Notation "{ A } + { B }" := (A + B) (at level 50, left associativity).
Notation "A + { B }" := (A + B) (at level 50, left associativity).
Notation "A \/ B" := (A + B).

Notation or := sum.

Notation left := inl.
Notation inleft := inl.

Notation bool := Bool.

Delimit Scope bool_scope with bool.

Notation unit := Unit.

(* Change #[universes(template)] to Cumulative. *)
