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

Definition beta_coe : forall {A B : Type} (e : A <~> B), coe (typeext e) = e.
Admitted.

Definition beta_coe_1 (A : Type) : coe (refl A) = idE.
Admitted.

Definition beta_typeext : forall {A B : Type} (p : A = B), typeext (coe p) = p.
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

Definition law_pind_1' {A : Type} (a : A)
  (B : forall x : A, a = x -> Type) (b : B a 1)
  : pind B (refl a) b = b
  := ap (fun e => equiv e b) (law_pind_1 a B).

Definition law_inverse_pind_1' {A : Type} (a : A)
  (B : forall x : A, a = x -> Type) (b : B a 1)
  : (pind B (refl a))^-1 b = b
  := ap (fun e => equiv e^-1 b) (law_pind_1 a B).

Definition tr {A : Type} (B : A -> Type) {a1 a2 : A}
  : a1 = a2 -> B a1 <~> B a2
  := pind (fun a _ => B a).

Definition papDR {A : Type} {a1 a2 : A} (B : forall a, a1 = a -> Type)
  (f : forall (a : A) (r : a1 = a), B a r) (p : a1 = a2)
  : f a1 1 = (pind B p)^-1 (f a2 p)
  := (law_inverse_pind_1' a1 B (f a1 1))^
      @ pap (fun x r => (pind B r)^-1 (f x r)) p.

Definition papDL {A : Type} {a1 a2 : A} (B : forall a, a1 = a -> Type)
  (f : forall (a : A) (r : a1 = a), B a r) (p : a1 = a2)
  : pind B p (f a1 1) = f a2 p
  := ap (pind B p) (papDR B f p)
     @ homot_isrinv_inverseE (pind B p) (f a2 p).

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
  {a1 a2 a3 : A} (p : a1 = a2) (q : a2 = a3)
  : ap f (p @ q) = ap f p @ ap f q.
Proof.
  refine ((papDL (fun x _ => f a1 = f x) (fun x q => ap f (p @ q)) q)^ @ _).
  refine (_ @ papDL (fun x _ => f a1 = f x) (fun x q => ap f p @ ap f q) q).
  refine (ap (fun r => _ (ap f r)) (law_right_1 _) @ _).
  refine (_ @ (ap (fun r => _ (ap f p @ r)) (law_pap_1 _))^).
  exact (ap (fun r => _ r) (law_right_1 _))^.
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

Definition law_tr_inverse {A : Type} {a1 a2 : A}
  (B : A -> Type) (p : a1 = a2) (b : B a2)
  : tr B p^ b = (tr B p)^-1 b.
Proof.
  refine (ap (fun r => coe r b) (law_ap_inverse _ _) @ _).
  refine (ap (fun r => coe r b) (beta_inverse_type _) @ _).
  exact (ap (fun e => equiv e b) (beta_coe _)).
Defined.

Definition law_tr_inverse_tr {A : Type} {a1 a2 : A}
  (B : A -> Type) (p : a1 = a2) (b : B a1)
  : (tr B p^) (tr B p b) = b.
Proof.
  refine (law_tr_inverse B p (tr B p b) @ _).
  exact (homot_islinv_inverseE (tr B p) _).
Defined.

Definition law_tr_tr_inverse {A : Type} {a1 a2 : A}
  (B : A -> Type) (p : a1 = a2) (b : B a2)
  : tr B p (tr B p^ b) = b.
Proof.
  refine (ap (tr B p) (law_tr_inverse B p b) @ _).
  exact (homot_isrinv_inverseE (tr B p) _).
Defined.

Definition law_tr_concat {A : Type} (B : A -> Type)
  {a1 a2 a3 : A} (p : a1 = a2) (q : a2 = a3) (b : B a1)
  : tr B (p @ q) b = tr B q (tr B p b).
Proof.
  refine (ap (fun r => coe r b) (law_ap_concat B p q) @ _).
  refine (ap (fun r => coe r b) (beta_concat_type _ _) @ _).
  exact (ap (fun f => equiv f b) (beta_coe _)).
Defined.

(***** Basic path in function structure *****************************)


Axiom funext :
  forall {A : Type} {B : A -> Type} (f g : forall a, B a),
  f ~ g -> f = g.

Axiom fap :
  forall {A : Type} {B : A -> Type} {f g : forall a, B a},
  f = g -> f ~ g.

Definition beta_fap :
  forall {A : Type} {B : A -> Type} (f g : forall a, B a) (h : f ~ g),
  fap (funext f g h) = h.
Admitted.

Definition beta_fap_1 {A : Type} {B : A -> Type} (f : forall a, B a)
  : fap (refl f) = fun x => refl (f x).
Admitted.

Definition beta_funext :
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


(***** Basic path in sigma structure ********************************)


Axiom sigext :
  forall {A : Type} {B : A -> Type} (u v : {a | B a}),
  {r : u.1 = v.1 | tr B r u.2 = v.2} -> u = v.

Axiom ppr :
  forall {A : Type} {B : A -> Type} {u v : {a | B a}} (p : u = v),
  {r : u.1 = v.1 | tr B r u.2 = v.2}.

Definition beta_ppr {A : Type} {B : A -> Type} (u v : {a | B a})
  (p : {r : u.1 = v.1 | tr B r u.2 = v.2})
  : ppr (sigext u v p) = p.
Admitted.

Definition beta_ppr_1 {A : Type} {B : A -> Type} (u : {a | B a})
  : ppr (refl u) = (refl u.1; law_pind_1' u.1 (fun a _ => B a) u.2).
Admitted.

Definition beta_sigext :
  forall {A : Type} {B : A -> Type} {u v : {a | B a}} (p : u = v),
  sigext u v (ppr p) = p.
Admitted.

Definition islinv_sigext {A : Type} {B : A -> Type} (u v : {a | B a})
  : IsLinv (sigext u v)
  := (@ppr _ _ u v; @beta_sigext _ _ u v).

Definition isrinv_sigext {A : Type} {B : A -> Type} (u v : {a | B a})
  : IsRinv (sigext u v)
  := (@ppr _ _ u v; beta_ppr u v).

Definition isequiv_sigext {A : Type} {B : A -> Type} (u v : {a | B a})
  : IsEquiv (sigext u v)
  := (islinv_sigext u v; isrinv_sigext u v).

Definition sigextE {A : Type} {B : A -> Type} (u v : {a | B a})
  : {r : u.1 = v.1 | tr B r u.2 = v.2} <~> (u = v)
  := (sigext u v; isequiv_sigext u v).

Definition refl_sig {A : Type} {B : A -> Type} (u : {a | B a})
  : u = u
  := sigext u u (refl u.1; law_pind_1' u.1 (fun a _ => B a) u.2).

Definition beta_refl_sig {A : Type} {B : A -> Type} (u : {a | B a})
  : refl u = refl_sig u.
Admitted.

Definition inverse_sig' {A : Type} {B : A -> Type} (u v : {a | B a})
  (p : {r : u.1 = v.1 | tr B r u.2 = v.2})
  : {r : v.1 = u.1 | tr B r v.2 = u.2}.
Proof.
  refine (p.1^; _).
  refine (ap (tr B p.1^) p.2^ @ _).
  exact (law_tr_inverse_tr _ _ _).
Defined.

Definition inverse_sig {A : Type} {B : A -> Type}
  {u v : {a | B a}} (p : u = v)
  : v = u
  := sigext v u (inverse_sig' u v (ppr p)).

Definition beta_inverse_sig {A : Type} {B : A -> Type}
  {u v : {a | B a}} (p : u = v)
  : p^ = inverse_sig p.
Admitted.

Definition concat_sig' {A : Type} {B : A -> Type} (u v w : {a | B a})
  (p : {r : u.1 = v.1 | tr B r u.2 = v.2})
  (q : {r : v.1 = w.1 | tr B r v.2 = w.2})
  : {r : u.1 = w.1 | tr B r u.2 = w.2}.
Proof.
  refine (p.1 @ q.1; _).
  refine (law_tr_concat _ _ _ _ @ _).
  refine (ap (tr B q.1) p.2 @ _).
  exact q.2.
Defined.

Definition concat_sig {A : Type} {B : A -> Type}
  {u v w : {a | B a}} (p : u = v) (q : v = w)
  : u = w
  := sigext u w (concat_sig' u v w (ppr p) (ppr q)).

Definition beta_concat_sig {A : Type} {B : A -> Type}
  {u v w : {a | B a}} (p : u = v) (q : v = w)
  : p @ q = concat_sig p q.
Admitted.


(***** Basic path in path structure *********************************)


(* NOTE: Here, elim is one of the path elimination rules:
         coe, fap, ppr, pathelim _, ... *)


Axiom pathext :
  forall {X E : Type} {a b : X} (elim : a = b -> E) (p q : a = b),
  elim p = elim q -> p = q.

Axiom pathelim :
  forall {X E : Type} {a b : X} (elim : a = b -> E) {p q : a = b},
  p = q -> elim p = elim q.

Axiom beta_pathelim :
  forall {X E : Type} {a b : X}
         (elim : a = b -> E) (p q : a = b) (e : elim p = elim q),
  pathelim elim (pathext elim p q e) = e.

Axiom beta_pathext :
  forall {X E : Type} {a b : X}
         (elim : a = b -> E) {p q : a = b} (pp : p = q),
  pathext elim p q (pathelim elim pp) = pp.

Definition beta_pathext_1 :
   forall {X E : Type} {a b : X} (elim : a = b -> E) (p : a = b),
   pathext elim p p 1 = 1.
Admitted.

Definition islinv_pathext {X E : Type} {a b : X}
  (elim : a = b -> E) (p q : a = b)
  : IsLinv (pathext elim p q)
  := (@pathelim X E a b elim p q; @beta_pathext X E a b elim p q).

Definition isrinv_pathext {X E : Type} {a b : X}
  (elim : a = b -> E) (p q : a = b)
  : IsRinv (pathext elim p q)
  := (@pathelim X E a b elim p q; beta_pathelim elim p q).

Definition isequiv_pathext {X E : Type} {a b : X}
  (elim : a = b -> E) (p q : a = b)
  : IsEquiv (pathext elim p q)
  := (islinv_pathext elim p q; isrinv_pathext elim p q).

Definition pathextE {X E : Type} {a b : X}
  (elim : a = b -> E) (p q : a = b)
  : (elim p = elim q) <~> (p = q)
  := (pathext elim p q; isequiv_pathext elim p q).

Definition refl_path {X E : Type} {a b : X} (elim : a = b -> E) (p : a = b)
  : p = p
  := pathext elim p p 1.

Definition beta_refl_path {X E : Type} {a b : X}
  (elim : a = b -> E) (p : a = b)
  : refl p = refl_path elim p.
Admitted.

Definition inverse_path {X E : Type} {a b : X}
  (elim : a = b -> E) {p q : a = b} (pp : p = q)
  : q = p
  := pathext elim q p (pathelim elim pp)^.

Definition beta_inverse_path {X E : Type} {a b : X}
  (elim : a = b -> E) {p q : a = b} (pp : p = q)
  : pp^ = inverse_path elim pp.
Admitted.

Definition concat_path {X E : Type} {a b : X}
  (elim : a = b -> E) {p q r : a = b} (pp : p = q) (qq : q = r)
  : p = r
  := pathext elim p r (pathelim elim pp @ pathelim elim qq).

Definition beta_concat_path {X E : Type} {a b : X}
  (elim : a = b -> E) {p q r : a = b} (pp : p = q) (qq : q = r)
  : pp @ qq = concat_path elim pp qq.
Admitted.

(* Example of higher paths: *)

Definition typeext2 {A B : Type} (p q : A = B) (pp : coe p = coe q) : p = q
  := pathext coe p q pp.

Definition coe2 {A B : Type} {p q : A = B} (pp : p = q) : coe p = coe q
  := pathelim coe pp.

Definition funext2 {A : Type} {B : A -> Type} {f g : forall a : A, B a}
  (p q : f = g) (pp : fap p = fap q)
  : p = q
  := pathext fap p q pp.

Definition fap2 {A : Type} {B : A -> Type} {f g : forall a : A, B a}
  (p q : f = g) (pp : p = q)
  : fap p = fap q
  := pathelim fap pp.

Definition sigext2 {A : Type} {B : A -> Type} {u v : {a : A | B a}}
  (p q : u = v) (pp : ppr p = ppr q)
  : p = q
  := pathext ppr p q pp.

Definition ppr2 {A : Type} {B : A -> Type} {u v : {a : A | B a}}
  (p q : u = v) (pp : p = q)
  : ppr p = ppr q
  := pathelim ppr pp.

Definition typeext3 {A B : Type} {p q : A = B}
  (pp qq : p = q) (ppp : coe2 pp = coe2 qq)
  : pp = qq
  := pathext coe2 pp qq ppp.

Definition coe3 {A B : Type} {p q : A = B}
  {pp qq : p = q} (ppp : pp = qq)
  : coe2 pp = coe2 qq
  := pathelim coe2 ppp.

(* And so on ... *)


(***** Pap of path introduction rules *******************************)


(* pap (fun x r => typeext (a x r)) p *)

Definition pap_typeext {X : Type} {x1 x2 : X} (p : x1 = x2)
  (A B : Type) (a : forall (x : X), x1 = x -> A <~> B)
  : typeext (a x1 1) = typeext (a x2 p).
Proof.
  refine (pathext coe _ _ _).
  refine (beta_coe (a x1 1) @ _ @ (beta_coe (a x2 p))^).
  exact (pap a p).
Defined.

(* pap (fun x r => funext (a x r)) p *)

Definition pap_funeext {X : Type} {x1 x2 : X} (p : x1 = x2)
  {A : Type} {B : A -> Type} (f g : forall a : A, B a)
  (a : forall (x : X), x1 = x -> f ~ g)
  : funext f g (a x1 1) = funext f g (a x2 p).
Proof.
  refine (pathext fap _ _ _).
  refine (beta_fap f g (a x1 1) @ _ @ (beta_fap f g (a x2 p))^).
  exact (pap a p).
Defined.

(* pap (fun x r => sigext (a x r)) p *)

Definition pap_sigext {X : Type} {x1 x2 : X} (p : x1 = x2)
  {A : Type} {B : A -> Type} (u v : {a : A | B a})
  (a : forall (x : X), x1 = x -> {s : u.1 = v.1 | tr B s u.2 = v.2})
  : sigext u v (a x1 1) = sigext u v (a x2 p).
Proof.
  refine (pathext ppr _ _ _).
  refine (beta_ppr u v (a x1 1) @ _ @ (beta_ppr u v (a x2 p))^).
  exact (pap a p).
Defined.

(* pap (fun x r => pathext elim (a x r)) p *)

Definition pap_pathext {X : Type} {x1 x2 : X} (p : x1 = x2)
  {Y E : Type} {u v : Y} (elim : u = v -> E) (s t : u = v)
  (a : forall (x : X), x1 = x -> elim s = elim t)
  : pathext elim s t (a x1 1) = pathext elim s t (a x2 p).
Proof.
  refine (pathext (pathelim elim) _ _ _).
  refine (beta_pathelim elim s t (a x1 1)
          @ _ @ (beta_pathelim elim s t (a x2 p))^).
  exact (pap a p).
Defined.

(* The law_pap_1 for pap_pathext.
   The law_pap_1 laws for the others are analogous. *)

Definition law_pap_1_pathext {X : Type} (x1 : X)
  {Y E : Type} {u v : Y} (elim : u = v -> E) (s t : u = v)
  (a : forall (x : X), x1 = x -> elim s = elim t)
  : pap_pathext (refl x1) elim s t a = 1.
Proof.
  refine (ap (fun r => _ (_ @ r @ _)) (law_pap_1 _) @ _). 
  refine (ap (fun r => _ (r @ _)) (law_right_1 _) @ _).
  refine (ap (fun r => _ r) (law_right_inverse _) @ _).
  exact (beta_pathext_1 _ _).
Defined.


(***** Pap of path type *********************************************)


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


(***** Pap of lambda ************************************************)

(* THIS SECTION IS WRONG! *)

(* THIS IS LOOPING ! *)
Definition pap_funap {X : Type} {x1 x2 : X} (p : x1 = x2)
  (A : forall (x : X), x1 = x -> Type) {B : Type}
  (a : forall (x : X) (r : x1 = x), A x r)
  (b : forall (x : X) (r : x1 = x), A x r -> B)
  : b x1 1 (a x1 1) = b x2 p (a x2 p)
  := (ap (b x1 1) (law_pind_1' x1 A (a x1 1)))^
     @ pap (fun x r => b x r (pind A r (a x1 1))) p
     @ ap (b x2 p) (papDL A a p).

Definition pap_lambda {X : Type} {x1 x2 : X} (p : x1 = x2)
  {A B : Type} (b : forall (x : X), x1 = x -> A -> B)
  : (fun a => b x1 1 a) = (fun a => b x2 p a)
  := funext (b x1 1) (b x2 p)
      (fun a => pap_funap p (fun _ _ => A) (fun _ _ => a) b).

Definition law_pap_1_funap {X : Type} (x1 : X)
  (A : forall (x : X), x1 = x -> Type) {B : Type}
  (a : forall (x : X) (r : x1 = x), A x r)
  (b : forall (x : X) (r : x1 = x), A x r -> B)
  : pap_funap (refl x1) A a b = 1.
Proof.
  unfold pap_funap.
  refine (ap (fun r => _ @ r @ _) (law_pap_1 _) @ _).
  refine (ap (fun r => r @ _) (law_right_1 _) @ _).
  unfold papDL.
  unfold papDR.
  unfold law_inverse_pind_1'.
  refine (ap (fun r => _ @ ap (b x1 1) (ap (pind A 1) (_ @ r) @ _))
             (law_pap_1 _) @ _).
  refine (ap (fun r => _ @ ap (b x1 1) (ap (pind A 1) r @ _))
             (law_right_1 _) @ _).
  unfold law_pind_1'.
  cbn in *.
  set (L := law_pind_1 x1 A).
  generalize dependent L.
  refine (
    pind (fun e _ =>

forall L : e = idE,
(ap (b x1 1) (ap (fun e : A x1 1 <~> A x1 1 => e (a x1 1)) L))^ @
ap (b x1 1)
  (ap (equiv e)
     (ap (fun e : A x1 1 <~> A x1 1 => inverseE' e (a x1 1))
        L)^ @ homot_isrinv_inverseE e (a x1 1)) = 1

    ) (law_pind_1 x1 A)^ _
  ).
  intro L.
  cbn.
  Admitted. (* Will probably beta reduce to the right thing. *)

(* Missing
     * finish law_pap_1
     * law_assoc
     * law_inverse_left
     * law_left_1
*)


(***** Path in sigma continued. *************************************)


(* Missing
     * pap
     * law_pap_1
     * law_assoc
     * law_inverse_left
     * law_left_1
*)
