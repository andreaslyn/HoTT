Require Export HoTT.Basics.Overture.
Require Export HoTT.Types.Bool.

Global Unset Asymmetric Patterns.

Notation sym_equal := @inverse.
Notation eq := paths.

Notation proj1 := fst.
Notation proj2 := snd.

Notation projT1 := @proj1_sig.

Notation refl_equal := @idpath.
Notation sym_eq := @inverse.
Notation sym_not_eq := @symmetric_neq.
Notation trans_eq := @concat.
Notation f_equal := @ap.
Definition f_equal2 (A1 A2 B : Type) (f : A1 -> A2 -> B)
  (x1 y1 : A1) (x2 y2 : A2) (p1 : x1 = y1) (p2 : x2 = y2)
  : f x1 x2 = f y1 y2
  := match ap f p1 in _ = g return f x1 x2 = g y2 with
     | idpath => ap (f x1) p2
     end.

Notation left := inl.
Notation inleft := inl.

Notation "{ A } + { B }" := (A + B) (at level 50, left associativity).
Notation "A + { B }" := (A + B) (at level 50, left associativity).
Notation "A \/ B" := (A + B).

Notation or := sum.

Notation bool := Bool.
Notation unit := Unit.

Delimit Scope bool_scope with bool.

(* Search replace Prop -> Type *)
(* Change #[universes(template)] to Cumulative. *)
