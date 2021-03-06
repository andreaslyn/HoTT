Set Primitive Projections.
Unset Elimination Schemes.


(***** Function type ************************************************)


Notation id := (fun x => x).

Notation "g 'o' f" :=
  (fun x => g (f x)) (at level 40, left associativity).


(***** Path type former *********************************************)


Declare Scope Path_scope.
Open Scope Path_scope.

Cumulative Inductive Path {A : Type} (a : A) : A -> Type := .

Notation "x = y" := (Path x y) : type_scope.

Notation "f ~ g" :=
  (forall x, f x = g x) (at level 70, no associativity) : type_scope.


(***** Path structure ***********************************************)


Axiom refl : forall (A : Type) (a : A), a = a.

Arguments refl {A a} , {A} a.

Notation "1" := refl : Path_scope.


Axiom inverse :
  forall {A : Type} {a1 a2 : A}, a1 = a2 -> a2 = a1.

Notation "p ^" := (inverse p) (at level 3, format "p '^'") : Path_scope.


Axiom concat :
  forall {A : Type} {a1 a2 a3 : A},
  a1 = a2 -> a2 = a3 -> a1 = a3.

Notation "p @ q" := (concat p q) (at level 20) : Path_scope.


Axiom pap :
  forall {A : Type} {B : Type} {a1 a2 : A}
         (f : forall (x : A), a1 = x -> B) (p : a1 = a2),
  f a1 1 = f a2 p.


Axiom law_pap_1 :
  forall {A : Type} {a : A} {B : Type} (f : forall x, a = x -> B),
  pap f (refl a) = 1.

Axiom law_assoc :
  forall {A : Type} {a1 a2 a3 a4 : A}
         (p : a1 = a2) (q : a2 = a3) (r : a3 = a4),
  p @ (q @ r) = (p @ q) @ r.

Axiom law_left_inverse
  : forall {A : Type} {a1 a2 : A} (p : a1 = a2), p^ @ p = 1.

Axiom law_left_1
  : forall {A : Type} {a1 a2 : A} (p : a1 = a2),
    1 @ p = p.


(***** Derived path structure ***************************************)


Definition ap {A B : Type} (f : A -> B) {a1 a2 : A}
  : a1 = a2 -> f a1 = f a2
  := pap (fun x _ => f x).


Definition law_right_inverse {A : Type} {a1 a2 : A} (p : a1 = a2)
  : p @ p^ = 1.
Proof.
  refine (ap (fun q => q @ p^) (law_left_1 p)^ @ _).
  refine (ap (fun q => q @ p @ p^) (law_left_inverse p^)^ @ _).
  refine (ap (fun q => q @ p^) (law_assoc p^^ p^ p)^ @ _).
  refine (ap (fun q => p^^ @ q @ p^) (law_left_inverse p) @ _).
  refine ((law_assoc p^^ 1 p^)^ @ _).
  refine (ap (fun q => p^^ @ q) (law_left_1 p^) @ _).
  exact (law_left_inverse p^).
Defined.

Definition law_right_1 {A : Type} {a1 a2 : A} (p : a1 = a2)
  : p @ 1 = p.
Proof.
  refine (ap (fun q => p @ q) (law_left_inverse p)^ @ _).
  refine ((law_assoc p p^ p) @ _).
  refine (ap (fun q => q @ p) (law_right_inverse p) @ _).
  exact (law_left_1 p).
Defined.

Definition law_inverse_inverse {A : Type} {a1 a2 : A} (p : a1 = a2)
  : p^^ = p.
Proof.
  refine ((law_right_1 p^^)^ @ _).
  refine (ap (fun q => p^^ @ q) (law_left_inverse p)^ @ _).
  refine ((law_assoc p^^ p^ p) @ _).
  refine (ap (fun q => q @ p) (law_left_inverse p^) @ _).
  exact (law_left_1 p).
Defined.

Definition law_inverse_1 {A : Type} (a : A)
  : (refl a)^ = refl a.
Proof.
  exact ((law_right_1 1^)^ @ law_left_inverse 1).
Defined.


(***** Sig type *****************************************************)


Declare Scope Sig_scope.
Open Scope Sig_scope.

Cumulative Record Sig (A : Type) (B : A -> Type) : Type := MkSig
  { pr1 : A;  pr2 : B pr1 }.

Arguments Sig {A}.
Arguments MkSig {A B}.
Arguments pr1 {A B}.
Arguments pr2 {A B}.

Scheme Sig_ind := Elimination for Sig Sort Type.
Scheme Sig_rect := Elimination for Sig Sort Type.
Scheme Sig_rec := Elimination for Sig Sort Type.

Arguments Sig_ind {A B}.
Arguments Sig_rect {A B}.
Arguments Sig_rec {A B}.

Notation "{ x  |  P }" := (Sig (fun x => P)) : type_scope.
Notation "{ x : A  |  P }" := (Sig (fun x : A => P)) : type_scope.

Notation "( a ; b )" := (MkSig a b) : Sig_scope.

Notation "u .1" := (pr1 u) (at level 3, format "u '.1'").
Notation "u .2" := (pr2 u) (at level 3, format "u '.2'").


(***** Equivalence **************************************************)


Definition IsLinv {A B} (f : A -> B) : Type
  := {g : B -> A | f o g ~ id}.

Definition inv_islinv {A B} {f : A -> B} (L : IsLinv f) : B -> A
  := L.1.

Definition homot_islinv {A B} {f : A -> B} (L : IsLinv f)
  : f o inv_islinv L ~ id
  := L.2.


Definition IsRinv {A B} (f : A -> B) : Type
  := {h : B -> A | h o f ~ id}.

Definition inv_isrinv {A B} {f : A -> B} (R : IsRinv f) : B -> A
  := R.1.

Definition homot_isrinv {A B} {f : A -> B} (R : IsRinv f)
  : inv_isrinv R o f ~ id
  := R.2.


Definition IsEquiv {A B : Type} (f : A -> B) : Type
  := {_ : IsLinv f | IsRinv f}.

Definition islinv_isequiv {A B : Type} {f : A -> B} (E : IsEquiv f)
  : IsLinv f
  := E.1.

Definition isrinv_isequiv {A B : Type} {f : A -> B} (E : IsEquiv f)
  : IsRinv f
  := E.2.


Definition Equiv (A B : Type) := {f : A -> B | IsEquiv f}.

Notation "A <~> B" :=
  (Equiv A B) (at level 70, no associativity) : type_scope.

Definition equiv {A B : Type} (f : A <~> B) : A -> B := f.1.

Coercion equiv : Equiv >-> Funclass.

Definition isequiv_equiv {A B : Type} (f : A <~> B)
  : IsEquiv f
  := f.2.

Definition islinv_equiv {A B : Type} (f : A <~> B)
  : IsLinv f
  := islinv_isequiv (isequiv_equiv f).

Definition inv_islinv_equiv {A B : Type} (f : A <~> B) : B -> A
  := inv_islinv (islinv_equiv f).

Definition isrinv_equiv {A B : Type} (f : A <~> B)
  : IsRinv f
  := isrinv_isequiv (isequiv_equiv f).

Definition inv_isrinv_equiv {A B : Type} (f : A <~> B) : B -> A
  := inv_isrinv (isrinv_equiv f).

Definition inverseE' {A B : Type} : A <~> B -> B -> A
  := inv_islinv_equiv.

Definition homot_isrinv_inverseE {A B : Type} (f : A <~> B)
  : f o inverseE' f ~ id
  := homot_islinv (islinv_equiv f).

Definition isrinv_inverseE {A B} (f : A <~> B) : IsRinv (inverseE' f)
  := (equiv f; homot_isrinv_inverseE f).

Definition homot_islinv_inverseE {A B : Type} (f : A <~> B)
  : inverseE' f o f ~ id.
Proof.
  intro x.
  refine ((homot_isrinv (isrinv_equiv f) (inverseE' f (f x)))^ @ _).
  refine (ap (inv_isrinv_equiv _) (homot_islinv (islinv_equiv f) (f x)) @ _).
  exact (homot_isrinv _ x).
Defined.

Definition islinv_inverseE {A B : Type} (f : A <~> B) : IsLinv (inverseE' f)
  := (equiv f; homot_islinv_inverseE f).

Definition isequiv_inverseE {A B : Type} (f : A <~> B) : IsEquiv (inverseE' f)
  := (islinv_inverseE f; isrinv_inverseE f).

Definition inverseE {A B} (f : A <~> B) : B <~> A
  := (inverseE' f; isequiv_inverseE f).

Notation "f ^-1" := (inverseE f) (at level 3, format "f '^-1'").

Definition islinv_idE (A : Type) : IsLinv (id : A -> A)
  := (id; fun _ => 1).

Definition isrinv_idE (A : Type) : IsRinv (id : A -> A)
  := (id; fun _ => 1).

Definition isequiv_idE (A : Type) : IsEquiv (id : A -> A) :=
  (islinv_idE A; isrinv_idE A).

Definition idE {A:Type} : A <~> A
  := (id; isequiv_idE A).

Arguments idE {A} , A.

Definition homot_islinv_composeE {A B C : Type} (g : B <~> C) (f : A <~> B)
  : (g o f) o (inv_islinv_equiv f o inv_islinv_equiv g) ~ id.
Proof.
  intro x.
  refine (ap g (homot_islinv (islinv_equiv f) _) @ _).
  exact (homot_islinv (islinv_equiv g) x).
Defined.

Definition islinv_composeE {A B C : Type} (g : B <~> C) (f : A <~> B)
  : IsLinv (g o f)
  := ((inv_islinv_equiv f o inv_islinv_equiv g);
       homot_islinv_composeE g f).

Definition homot_isrinv_composeE {A B C : Type} (g : B <~> C) (f : A <~> B)
  : (inv_isrinv_equiv f o inv_isrinv_equiv g) o (g o f) ~ id.
Proof.
  intro x.
  refine (ap (inv_isrinv_equiv f) (homot_isrinv (isrinv_equiv g) _) @ _).
  exact (homot_isrinv (isrinv_equiv f) x).
Defined.

Definition isrinv_composeE {A B C : Type} (g : B <~> C) (f : A <~> B)
  : IsRinv (g o f)
  := ((inv_isrinv_equiv f o inv_isrinv_equiv g);
       homot_isrinv_composeE g f).

Definition isequiv_composeE {A B C : Type} (g : B <~> C) (f : A <~> B)
  : IsEquiv (g o f)
  := (islinv_composeE g f; isrinv_composeE g f).

Definition composeE {A B C} (g : B <~> C) (f : A <~> B) : A <~> C
  := (g o f; isequiv_composeE g f).

Notation "g 'oE' f" :=
  (composeE g f) (at level 40, left associativity) : Sig_scope.

Definition homot_inv_equiv {A B : Type} (f : A <~> B)
  : inv_isrinv_equiv f ~ inv_islinv_equiv f.
Proof.
  intro b.
  exact (ap (inv_isrinv_equiv f) (homot_islinv (islinv_equiv f) b)^
         @ homot_isrinv (isrinv_equiv f) _).
Defined.


(***** Basic path in type structure *********************************)


Axiom typeext : forall {A B : Type}, A <~> B -> A = B.

Axiom coe : forall {A B : Type}, A = B -> A <~> B.

Lemma beta_coe : forall {A B : Type} (e : A <~> B), coe (typeext e) = e.
Admitted.

Definition beta_coe_1 (A : Type) : coe (refl A) = idE.
Admitted.

Lemma beta_typeext : forall {A B : Type} (p : A = B), typeext (coe p) = p.
Admitted.

Definition islinv_typeext (A B : Type) : IsLinv (@typeext A B)
  := (@coe A B; @beta_typeext A B).

Definition isrinv_typeext (A B : Type) : IsRinv (@typeext A B)
  := (@coe A B; @beta_coe A B).

Definition isequiv_typeext (A B : Type) : IsEquiv (@typeext A B)
  := (islinv_typeext A B; isrinv_typeext A B).

Definition typeextE (A B : Type) : (A <~> B) <~> (A = B)
  := (@typeext A B; isequiv_typeext A B).

Definition refl_type (A : Type) : A = A
  := typeext idE.

Definition beta_refl_type (A : Type) : refl A = refl_type A.
Admitted.

Definition inverse_type {A B : Type} (p : A = B) : B = A
  := typeext (coe p)^-1.

Definition beta_inverse_type {A B : Type} (p : A = B) : p^ = inverse_type p.
Admitted.

Definition concat_type {A B C : Type} (p : A = B) (q : B = C) : A = C
  := typeext (coe q oE coe p).

Definition beta_concat_type {A B C : Type} (p : A = B) (q : B = C)
  : p @ q = concat_type p q.
Admitted.


(***** More path structure ******************************************)


Definition pind {A : Type} {a1 a2 : A}
  (B : forall (a : A), a1 = a -> Type) (p : a1 = a2)
  : B a1 1 <~> B a2 p
  := coe (pap B p).

Definition law_pind_1 {A : Type} (a : A) (B : forall x : A, a = x -> Type)
  : pind B (refl a) = idE
  := ap (fun p => coe p) (law_pap_1 _) @ beta_coe_1 _.

Definition tr {A : Type} (B : A -> Type) {a1 a2 : A}
  : a1 = a2 -> B a1 -> B a2
  := pind (fun a _ => B a).

Definition law_ap_compose {A B C : Type} (g : B -> C) (f : A -> B)
  {a1 a2 : A} (p : a1 = a2)
  : ap g (ap f p) = ap (g o f) p.
Proof.
  refine (pind (fun a p => ap g (ap f p) = ap (g o f) p) p _).
  refine (ap (ap g) (law_pap_1 _) @ _).
  refine (law_pap_1 _ @ _).
  exact ((law_pap_1 _)^).
Defined.

Definition law_ap_concat {A B : Type} (f : A -> B)
  {a1 a2 a3 : A} (p : a1 = a2)
  : forall q : a2 = a3, ap f (p @ q) = ap f p @ ap f q.
Proof.
  refine (pind (fun a p =>
            forall q, ap f (p @ q) = ap f p @ ap f q) p _).
  intro q.
  refine (ap (ap f) (law_left_1 _) @ _).
  refine (_ @ (ap (fun r => r @ ap f q) (law_pap_1 _))^).
  exact (law_left_1 _)^.
Defined.

Definition law_ap_inverse {A B : Type} (f : A -> B)
  {a1 a2 : A} (p : a1 = a2)
  : ap f p^ = (ap f p)^.
Proof.
  refine (pind (fun a p => ap f p^ = (ap f p)^) p _).
  refine (ap (ap f) (law_inverse_1 _) @ _).
  refine (law_pap_1 _ @ _).
  refine (_ @ (ap (fun q => q^) (law_pap_1 _))^).
  exact (law_inverse_1 _)^.
Defined.


(***** Basic path in function structure *****************************)

Axiom funext :
  forall {A : Type} {B : A -> Type} (f g : forall a, B a),
  f ~ g -> f = g.

Axiom fap :
  forall {A : Type} {B : A -> Type} {f g : forall a, B a},
  f = g -> f ~ g.

Lemma beta_fap :
  forall {A : Type} {B : A -> Type} (f g : forall a, B a) (h : f ~ g),
  fap (funext f g h) = h.
Admitted.

Definition beta_fap_1 {A : Type} {B : A -> Type} (f : forall a, B a)
  : fap (refl f) = fun x => refl (f x).
Admitted.

Lemma beta_funext :
  forall {A : Type} {B : A -> Type} {f g : forall a, B a} (p : f = g),
  funext f g (fap p) = p.
Admitted.

Definition islinv_funext {A : Type} {B : A -> Type} (f g : forall a, B a)
  : IsLinv (funext f g)
  := (@fap _ _ f g; @beta_funext _ _ f g).

Definition isrinv_funext {A : Type} {B : A -> Type} (f g : forall a, B a)
  : IsRinv (funext f g)
  := (@fap _ _ f g; beta_fap f g).

Definition isequiv_funext {A : Type} {B : A -> Type} (f g : forall a, B a)
  : IsEquiv (funext f g)
  := (islinv_funext f g; isrinv_funext f g).

Definition funextE {A : Type} {B : A -> Type} (f g : forall a, B a)
  : (f ~ g) <~> (f = g)
  := (funext f g; isequiv_funext f g).

Definition refl_fun {A : Type} {B : A -> Type} (f : forall a, B a)
  : f = f
  := funext f f (fun x => refl (f x)).

Definition beta_refl_fun {A : Type} {B : A -> Type} (f : forall a, B a)
  : refl f = refl_fun f.
Admitted.

Definition inverse_fun {A : Type} {B : A -> Type}
  {f g : forall a, B a} (p : f = g)
  : g = f
  := funext g f (fun x => (fap p x)^).

Definition beta_inverse_fun {A : Type} {B : A -> Type}
  {f g : forall a, B a} (p : f = g)
  : p^ = inverse_fun p.
Admitted.

Definition concat_fun {A : Type} {B : A -> Type}
  {f g h : forall a, B a} (p : f = g) (q : g = h)
  : f = h
  := funext f h (fun x => fap p x @ fap q x).

Definition beta_concat_fun {A : Type} {B : A -> Type}
  {f g h : forall a, B a} (p : f = g) (q : g = h)
  : p @ q = concat_fun p q.
Admitted.


(* Missing
     * pap
     * law_pap_1
     * law_assoc
     * law_inverse_left
     * law_left_1
*)


(***** Basic path in sigma structure ********************************)


(* see theories/uni6.v *)


(***** Path in type continued ***************************************)


Definition map_type_path1_pap {X : Type} {x1 x2 : X} (p : x1 = x2)
  (A : forall x : X, x1 = x -> Type)
  (f : forall (x : X) (r : x1 = x), A x r)
  : f x1 1 = (pind A p)^-1 (f x2 p)
  := (ap (fun e => e^-1 (f x1 1)) (beta_coe_1 _))^
     @ (ap (fun p => (coe p)^-1 (f x1 1)) (law_pap_1 _))^
     @ pap (fun x r => (pind A r)^-1 (f x r)) p.

Definition map_type_path1 {X : Type} {x1 x2 : X} (p : x1 = x2)
  (A : forall x : X, x1 = x -> Type)
  (f : forall (x : X) (r : x1 = x), A x r)
  (g : forall (x : X) (r : x1 = x), A x r)
  (q : f x1 1 = g x1 1)
  : (pind A p)^-1 (f x2 p) = (pind A p)^-1 (g x2 p)
  := (map_type_path1_pap p A f)^ @ q @ map_type_path1_pap p A g.

Definition inv_type_path1 {X : Type} {x1 x2 : X} (p : x1 = x2)
  (A : forall x : X, x1 = x -> Type)
  (f : forall (x : X) (r : x1 = x), A x r)
  (g : forall (x : X) (r : x1 = x), A x r)
  (q : (pind A p)^-1 (f x2 p) = (pind A p)^-1 (g x2 p))
  : f x1 1 = g x1 1
  := map_type_path1_pap p A f @ q @ (map_type_path1_pap p A g)^.

Definition homot_islinv_map_type_path1
  {X : Type} {x1 x2 : X} (p : x1 = x2)
  (A : forall x : X, x1 = x -> Type)
  (f : forall (x : X) (r : x1 = x), A x r)
  (g : forall (x : X) (r : x1 = x), A x r)
  : map_type_path1 p A f g o inv_type_path1 p A f g ~ id.
Proof.
  intro q.
  refine (ap (fun r => r @ _) (law_assoc _ _ _) @ _).
  refine (ap (fun r => r @ _ @ _) (law_assoc _ _ _) @ _).
  refine (ap (fun r => r @ _ @ _ @ _) (law_left_inverse _) @ _).
  refine (ap (fun r => r @ _ @ _) (law_left_1 _) @ _).
  refine ((law_assoc _ _ _)^ @ _).
  refine (ap (fun r => q @ r) (law_left_inverse _) @ _).
  exact (law_right_1 _).
Defined.

Definition islinv_map_type_path1
  {X : Type} {x1 x2 : X} (p : x1 = x2)
  (A : forall x : X, x1 = x -> Type)
  (f : forall (x : X) (r : x1 = x), A x r)
  (g : forall (x : X) (r : x1 = x), A x r)
  : IsLinv (map_type_path1 p A f g)
  := (inv_type_path1 p A f g; homot_islinv_map_type_path1 p A f g).

Definition homot_isrinv_map_type_path1
  {X : Type} {x1 x2 : X} (p : x1 = x2)
  (A : forall x : X, x1 = x -> Type)
  (f : forall (x : X) (r : x1 = x), A x r)
  (g : forall (x : X) (r : x1 = x), A x r)
  : inv_type_path1 p A f g o map_type_path1 p A f g ~ id.
Proof.
  intro q.
  refine (ap (fun r => r @ _) (law_assoc _ _ _) @ _).
  refine (ap (fun r => r @ _ @ _) (law_assoc _ _ _) @ _).
  refine (ap (fun r => r @ _ @ _ @ _) (law_right_inverse _) @ _).
  refine (ap (fun r => r @ _ @ _) (law_left_1 _) @ _).
  refine ((law_assoc _ _ _)^ @ _).
  refine (ap (fun r => q @ r) (law_right_inverse _) @ _).
  exact (law_right_1 _).
Defined.

Definition isrinv_map_type_path1
  {X : Type} {x1 x2 : X} (p : x1 = x2)
  (A : forall x : X, x1 = x -> Type)
  (f : forall (x : X) (r : x1 = x), A x r)
  (g : forall (x : X) (r : x1 = x), A x r)
  : IsRinv (map_type_path1 p A f g)
  := (inv_type_path1 p A f g; homot_isrinv_map_type_path1 p A f g).

Definition isequiv_map_type_path1
  {X : Type} {x1 x2 : X} (p : x1 = x2)
  (A : forall x : X, x1 = x -> Type)
  (f : forall (x : X) (r : x1 = x), A x r)
  (g : forall (x : X) (r : x1 = x), A x r)
  : IsEquiv (map_type_path1 p A f g)
  := (islinv_map_type_path1 p A f g; isrinv_map_type_path1 p A f g).

Definition pind_type_path1 {X : Type} {x1 x2 : X} (p : x1 = x2)
  (A : forall x : X, x1 = x -> Type)
  (f : forall (x : X) (r : x1 = x), A x r)
  (g : forall (x : X) (r : x1 = x), A x r)
  : (f x1 1 = g x1 1) <~> ((pind A p)^-1 (f x2 p) = (pind A p)^-1 (g x2 p))
  := (map_type_path1 p A f g; isequiv_map_type_path1 p A f g).

Definition map_type_path2 {X : Type} {x1 x2 : X} (p : x1 = x2)
  (A : forall x : X, x1 = x -> Type)
  (f : forall (x : X) (r : x1 = x), A x r)
  (g : forall (x : X) (r : x1 = x), A x r)
  (q : (pind A p)^-1 (f x2 p) = (pind A p)^-1 (g x2 p))
  : f x2 p = g x2 p
  := ((homot_isrinv_inverseE _ _)^
     @ ap (pind A p) q
     @ homot_isrinv_inverseE _ _).

Definition map_type_path {X : Type} {x1 x2 : X} (p : x1 = x2)
  (A : forall x : X, x1 = x -> Type)
  (f : forall (x : X) (r : x1 = x), A x r)
  (g : forall (x : X) (r : x1 = x), A x r)
  : f x1 1 = g x1 1 -> f x2 p = g x2 p
  := map_type_path2 p A f g o map_type_path1 p A f g.

Definition inv_islinv_type_path2 {X : Type} {x1 x2 : X} (p : x1 = x2)
  (A : forall x : X, x1 = x -> Type)
  (f : forall (x : X) (r : x1 = x), A x r)
  (g : forall (x : X) (r : x1 = x), A x r)
  (q : f x2 p = g x2 p)
  : (pind A p)^-1 (f x2 p) = (pind A p)^-1 (g x2 p)
  := ap (pind A p)^-1 q.

Definition homot_islinv_map_type_path2
  {X : Type} {x1 x2 : X} (p : x1 = x2)
  (A : forall x : X, x1 = x -> Type)
  (f : forall (x : X) (r : x1 = x), A x r)
  (g : forall (x : X) (r : x1 = x), A x r)
  : map_type_path2 p A f g o inv_islinv_type_path2 p A f g ~ id.
Proof.
  intro q.
  refine (
    map_type_path q (fun b _ => f x2 p = b)
    (fun b q => _ @ ap _ (ap (pind A p)^-1 q)
                  @ homot_isrinv_inverseE (pind A p) b)
    (fun b q => q) _).
  refine (ap (fun r => _ @ ap _ r @ _) (law_pap_1 _) @ _).
  refine (ap (fun r => _ @ r @ _) (law_pap_1 _) @ _).
  refine (ap (fun r => r @ _) (law_right_1 _) @ _).
  exact (law_left_inverse _).
Defined.

Definition islinv_map_type_path2
  {X : Type} {x1 x2 : X} (p : x1 = x2)
  (A : forall x : X, x1 = x -> Type)
  (f : forall (x : X) (r : x1 = x), A x r)
  (g : forall (x : X) (r : x1 = x), A x r)
  : IsLinv (map_type_path2 p A f g)
  := (inv_islinv_type_path2 p A f g; homot_islinv_map_type_path2 p A f g).

Definition inv_isrinv_type_path2 {X : Type} {x1 x2 : X} (p : x1 = x2)
  (A : forall x : X, x1 = x -> Type)
  (f : forall (x : X) (r : x1 = x), A x r)
  (g : forall (x : X) (r : x1 = x), A x r)
  (q : f x2 p = g x2 p)
  : (pind A p)^-1 (f x2 p) = (pind A p)^-1 (g x2 p)
  := (homot_isrinv_inverseE _ _)^
     @ ap (pind A p)^-1
          ((homot_isrinv_inverseE (pind A p) _)
           @ q
           @ (homot_isrinv_inverseE (pind A p) _)^)
     @ homot_isrinv_inverseE _ _.

Definition homot_isrinv_map_type_path2
  {X : Type} {x1 x2 : X} (p : x1 = x2)
  (A : forall x : X, x1 = x -> Type)
  (f : forall (x : X) (r : x1 = x), A x r)
  (g : forall (x : X) (r : x1 = x), A x r)
  : inv_isrinv_type_path2 p A f g o map_type_path2 p A f g ~ id.
Proof.
  intro q.
  set (h1 := homot_isrinv_inverseE (pind A p) (f x2 p)).
  set (h2 := homot_isrinv_inverseE (pind A p) (g x2 p)).
  refine (ap (fun r => _ @ ap _ (r @ h2^) @ _ ) (law_assoc _ _ _) @ _).
  refine (ap (fun r => _ @ ap _ (r @ h2 @ _) @ _ ) (law_assoc _ _ _) @ _).
  refine (ap (fun r => _ @ ap _ (r @ _ @ _ @ _) @ _ )
             (law_right_inverse _) @ _).
  refine (ap (fun r => _ @ ap _ (r @ _ @ h2^) @ _ ) (law_left_1 _) @ _).
  refine (ap (fun r => _ @ ap _ r @ _ ) (law_assoc _ _ _)^ @ _).
  refine (ap (fun r => _ @ ap _ (ap _ _ @ r) @ _ ) (law_right_inverse _) @ _).
  refine (ap (fun r => (_ @ ap (inverseE' (pind A p)) r) @ _ )
             (law_right_1 _) @ _).
  refine (
    map_type_path q (fun b _ => (pind A p)^-1 (f x2 p) = b)
    (fun b q => _ @ ap _ (ap (pind A p) q)
                  @ homot_islinv_inverseE (pind A p) b)
    (fun b q => q) _).
  refine (ap (fun r => _ @ ap _ r @ _) (law_pap_1 _) @ _).
  refine (ap (fun r => _ @ r @ _) (law_pap_1 _) @ _).
  refine (ap (fun r => r @ _) (law_right_1 _) @ _).
  exact (law_left_inverse _).
Defined.

Definition isrinv_map_type_path2
  {X : Type} {x1 x2 : X} (p : x1 = x2)
  (A : forall x : X, x1 = x -> Type)
  (f : forall (x : X) (r : x1 = x), A x r)
  (g : forall (x : X) (r : x1 = x), A x r)
  : IsRinv (map_type_path2 p A f g)
  := (inv_isrinv_type_path2 p A f g; homot_isrinv_map_type_path2 p A f g).

Definition isequiv_map_type_path2
  {X : Type} {x1 x2 : X} (p : x1 = x2)
  (A : forall x : X, x1 = x -> Type)
  (f : forall (x : X) (r : x1 = x), A x r)
  (g : forall (x : X) (r : x1 = x), A x r)
  : IsEquiv (map_type_path2 p A f g)
  := (islinv_map_type_path2 p A f g; isrinv_map_type_path2 p A f g).

Definition pind_type_path2
  {X : Type} {x1 x2 : X} (p : x1 = x2)
  (A : forall x : X, x1 = x -> Type)
  (f : forall (x : X) (r : x1 = x), A x r)
  (g : forall (x : X) (r : x1 = x), A x r)
  : ((pind A p)^-1 (f x2 p) = (pind A p)^-1 (g x2 p)) <~> (f x2 p = g x2 p)
  := (map_type_path2 p A f g; isequiv_map_type_path2 p A f g).

Definition pind_type_path
  {X : Type} {x1 x2 : X} (p : x1 = x2)
  (A : forall x : X, x1 = x -> Type)
  (f : forall (x : X) (r : x1 = x), A x r)
  (g : forall (x : X) (r : x1 = x), A x r)
  : (f x1 1 = g x1 1) <~> (f x2 p = g x2 p)
  := pind_type_path2 p A f g oE pind_type_path1 p A f g.

(* Pap in path type. *)

Definition pap_type_path
  {X : Type} {x1 x2 : X} (p : x1 = x2)
  (A : forall x : X, x1 = x -> Type)
  (f : forall (x : X) (r : x1 = x), A x r)
  (g : forall (x : X) (r : x1 = x), A x r)
  : (f x1 1 = g x1 1) = (f x2 p = g x2 p)
  := typeext (pind_type_path p A f g).

Definition path_map_type_path_1 {X : Type} {x0 : X}
  (A : forall x : X, x0 = x -> Type)
  (f : forall (x : X) (r : x0 = x), A x r)
  (g : forall (x : X) (r : x0 = x), A x r)
  (q : f x0 1 = g x0 1)
  : map_type_path (refl x0) A f g q = q.
Proof.
  refine (ap (fun r => _ @ ap (pind A 1) (_ @ (_ @ r)) @ _)
         (law_pap_1 _) @ _).
  refine (ap (fun r => _ @ ap (pind A 1) (_ @ r) @ _) (law_right_1 _) @ _).
  refine (
    map_type_path q (fun b _ => f x0 1 = b)
      (fun b q =>
        _ @ ap (pind A 1)
              (_ @ q
                 @ ((ap (fun e => e^-1 b) (beta_coe_1 (A x0 1)))^
                    @ (ap (fun p => (coe p)^-1 b) (law_pap_1 A))^))
         @ homot_isrinv_inverseE (pind A 1) b)
      (fun b q => q) _).
  refine (ap (fun r => _ @ ap (pind A 1) ((_ @ r)^ @ 1 @ _) @ _)
             (law_pap_1 _) @ _).
  refine (ap (fun r => _ @ ap (pind A 1) (r^ @ 1 @ _) @ _ )
             (law_right_1 _) @ _).
  refine (ap (fun r => _ @ ap (pind A 1) (r @ _) @ _) (law_right_1 _) @ _).
  refine (ap (fun r => _ @ ap (pind A 1) r @ _) (law_left_inverse _) @ _). 
  refine (ap (fun r => _ @ r @ _) (law_pap_1 _) @ _).
  refine (ap (fun r => r @ _) (law_right_1 _) @ _).
  exact (law_left_inverse _).
Defined.

(* Missing
     * finish law_pap_1
     * law_assoc
     * law_inverse_left
     * law_left_1
   Define first prop_isequiv to do this.
   But this probably requires funext.
*)
