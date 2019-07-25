Require Export HoTT.Basics.Overture.
Require Export HoTT.Types.Bool.
Require Export HoTT.Spaces.Nat.

Local Unset Elimination Schemes.

Global Set Printing Universes.
Global Set Default Goal Selector "1".

Notation "'Prop'" := Type (only parsing).

Notation le := Peano.le (only parsing).
Notation lt := Peano.lt (only parsing).

Notation "m <= n" := (le m n) : nat_scope.
Notation "m < n" := (lt m n) : nat_scope.
Notation "m >= n" := (n <= m) (only parsing) : nat_scope.
Notation "m > n" := (n < m) (only parsing) : nat_scope.

Notation eq := paths (only parsing).

Notation eq_refl := idpath (only parsing).
Notation refl_equal := idpath (only parsing).

Notation eq_ind := paths_rec  (only parsing).
Notation eq_ind_r := paths_rec_r (only parsing).
Notation eq_rect := paths_rec (only parsing).
Notation eq_rect_r := paths_rec_r (only parsing).

Notation proj1 := fst (only parsing).
Notation proj2 := snd (only parsing).

Definition projT1 := @proj1_sig.
Arguments projT1 [A P].

Definition projT2 := @proj2_sig.
Arguments projT2 [A P].

Definition sym_eq := @inverse.
Arguments sym_eq [A x y] p.

Notation sym_equal := sym_eq (only parsing).

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

Notation or := sum (only parsing).

Notation left := inl (only parsing).
Notation inleft := inl (only parsing).

Notation bool := Bool (only parsing).

Delimit Scope bool_scope with bool.

Notation unit := Unit (only parsing).


Record ssrsig {A} (P : A -> Prop) := ssrexist { ssr_pr1 : A ; ssr_pr2 : P ssr_pr1 }.

Scheme ssrsig_rect := Induction for sig Sort Type.
Definition ssrsig_ind := sig_rect.
Definition ssrsig_rec := sig_rect.

Arguments ssrsig_rect {A}.
Arguments ssrsig_ind {A}.
Arguments ssrsig_rec {A}.

Arguments ssrexist {A}%type P%type _ _.
Arguments ssr_pr1 {A P} _ / .
Arguments ssr_pr2 {A P} _ / .

Inductive ssrsig2 {A:Type} (P Q:A -> Prop) : Type :=
    ssrexist2 : forall x:A, P x -> Q x -> ssrsig2 P Q.

Scheme ssrsig2_rect := Induction for sig2 Sort Type.
Definition ssrsig2_ind := ssrsig2_rect.
Definition ssrsig2_rec := ssrsig2_rect.

Arguments ssrsig2_rect {A}.
Arguments ssrsig2_ind {A}.
Arguments ssrsig2_rec {A}.

Arguments ssrsig {A%type} P%type.
Arguments ssrsig2 {A%type} (P Q)%type.

Notation "{ x : A  |  P }" := (ssrsig (fun x : A => P)) (at level 0, x at level 99) : type_scope.
Notation "{ x : A  |  P  & Q }" := (ssrsig2 (fun x : A => P) (fun x : A => Q)) (at level 0, x at level 99) : type_scope.

Notation "{ x  |  P }" := { x : _ | P } (at level 0, x at level 99) : type_scope.
Notation "{ x  |  P  & Q }" := { x : _ | P & Q } (at level 0, x at level 99) : type_scope.

Notation sig := ssrsig (only parsing).
Notation proj1_sig := ssr_pr1 (only parsing).
Notation proj2_sig := ssr_pr2 (only parsing).
Notation exist := ssrexist (only parsing).

Notation sig2 := ssrsig2 (only parsing).
Notation exist2 := ssrexist2 (only parsing).
