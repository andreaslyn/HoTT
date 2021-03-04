
Set Primitive Projections.
Unset Elimination Schemes.


(***** Function type ************************************************)


Notation id := (fun x => x).

Notation "g 'o' f" :=
  (fun x => g (f x)) (at level 40, left associativity).


(***** Path type former *********************************************)


Declare Scope Path_scope.
Open Scope Path_scope.

Cumulative Inductive Path {A : Type} (a : A) : A -> Type
  := refl : Path a a.

Notation "x = y" := (Path x y) : type_scope.

Notation "f ~ g" :=
  (forall x, f x = g x) (at level 70, no associativity) : type_scope.

Scheme Path_ind := Elimination for Path Sort Type.
Scheme Path_rect := Elimination for Path Sort Type.
Scheme Path_rec := Elimination for Path Sort Type.

Arguments Path_ind {A} {a} P _ {_} p.
Arguments Path_rect {A} {a} P _ {_} p.
Arguments Path_rec {A} {a} P _ {_} p.


(***** Path structure ***********************************************)


Arguments refl {A a} , {A} a.

Notation "1" := refl : Path_scope.


Lemma inverse {A : Type} {a1 a2 : A} (p : a1 = a2) : a2 = a1.
Proof.
  induction p.
  exact 1.
Defined.

Notation "p ^" := (inverse p) (at level 3, format "p '^'") : Path_scope.


Lemma concat {A : Type} {a1 a2 a3 : A} (p : a1 = a2) : a2 = a3 -> a1 = a3.
Proof.
  induction p.
  exact id.
Defined.

Notation "p @ q" := (concat p q) (at level 20) : Path_scope.


Lemma pap {A : Type} {a1 a2 : A} {B : Type}
  (f : forall (x : A), a1 = x -> B) (p : a1 = a2)
  : f a1 1 = f a2 p.
Proof.
  induction p.
  exact 1.
Defined.

Definition ap {A : Type} {a1 a2 : A} {B : Type} (f : A -> B)
  : a1 = a2 -> f a1 = f a2
  := pap (fun x _ => f x).

Definition tr {A : Type} (B : A -> Type)
  {a1 a2 : A} (p : a1 = a2) (b : B a1) : B a2
  := Path_ind (fun a _ => B a) b p.


(***** Sig type *****************************************************)


Declare Scope Sig_scope.
Open Scope Sig_scope.

Cumulative Record Sig (A : Type) (B : A -> Type) : Type := mkSig
  { pr1 : A;  pr2 : B pr1 }.

Arguments Sig {A}.
Arguments mkSig {A B}.
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

Notation "( a ; b )" := (mkSig a b) : Sig_scope.

Notation "u .1" := (pr1 u) (at level 3, format "u '.1'").
Notation "u .2" := (pr2 u) (at level 3, format "u '.2'").


(***** Equivalence **************************************************)


Definition IsRetr {A B} (f : A -> B) : Type
  := {g : B -> A | f o g ~ id}.

Definition IsSect {A B} (f : A -> B) : Type
  := {h : B -> A | h o f ~ id}.

Definition IsEqi {A B} (f : A -> B) : Type
  := {_ : IsSect f | IsRetr f}.

Definition Eqi (A B : Type) := {f : A -> B | IsEqi f}.

Notation "A <~> B" :=
  (Eqi A B) (at level 70, no associativity) : type_scope.

Definition eqi {A B} (f : A <~> B) : A -> B := f.1.

Coercion eqi : Eqi >-> Funclass.

Definition issect_eqi {A B} (f : A <~> B) : IsSect f
  := f.2.1.

Definition retr_eqi {A B} (f : A <~> B) : B -> A
  := (issect_eqi f).1.

Definition homot_issect_eqi {A B} (f : A <~> B)
  : retr_eqi f o f ~ id
  := (issect_eqi f).2.

Definition isretr_eqi {A B} (f : A <~> B) : IsRetr f
  := f.2.2.

Definition sect_eqi {A B} (f : A <~> B) : B -> A
  := (isretr_eqi f).1.

Definition homot_isretr_eqi {A B} (f : A <~> B)
  : f o sect_eqi f ~ id
  := (isretr_eqi f).2.

Definition homot_sect_inveqi {A B} 
  : forall (f : A <~> B), f o sect_eqi f ~ id
  := homot_isretr_eqi.

Definition issect_inveqi {A B} (f : A <~> B) : IsSect (sect_eqi f)
  := (eqi f; homot_sect_inveqi f).

Definition homot_retr_inveqi {A B} (f : A <~> B)
  : sect_eqi f o f ~ id
  := fun x =>
      (homot_issect_eqi f (sect_eqi f (f x)))^
      @ ap (retr_eqi f) (homot_isretr_eqi f (f x))
      @ homot_issect_eqi f x.

Definition isretr_inveqi {A B} (f : A <~> B) : IsRetr (sect_eqi f)
  := (eqi f; homot_retr_inveqi f).

Definition inveqi {A B} (f : A <~> B) : B <~> A
  := (sect_eqi f; (issect_inveqi f; isretr_inveqi f)).

Notation "f ^-1" := (inveqi f) (at level 3, format "f '^-1'").

Definition iseqi_ideqi {A : Type} : @IsEqi A A id :=
  ((id; fun x => 1); (id; fun x => 1)).

Definition ideqi {A:Type} : A <~> A
  := (id; iseqi_ideqi).

Arguments ideqi {A} , A.

Lemma iseqi_comeqi {A B C} (g : B <~> C) (f : A <~> B) : IsEqi (g o f).
Proof.
  split.
  - refine (retr_eqi f o retr_eqi g; fun x => _).
    exact (ap (retr_eqi f) ((issect_eqi g).2 _) @ (issect_eqi f).2 x).
  - refine (sect_eqi f o sect_eqi g; (fun y => _)).
    exact (ap g ((isretr_eqi f).2 _) @ (isretr_eqi g).2 y).
Defined.

Definition comeqi {A B C} (g : B <~> C) (f : A <~> B) : A <~> C
  := (g o f; iseqi_comeqi g f).

Notation "g 'oE' f" :=
  (comeqi g f) (at level 40, left associativity) : Sig_scope.


(***** Univalence ***************************************************)


Definition coe' {A B : Type} (p : A = B) : A -> B
  := tr (fun X => A -> X) p id.

Definition iseqi_coe {A B : Type} (p : A = B)
  : IsEqi (coe' p)
  := Path_ind (fun X p => IsEqi (coe' p)) ideqi.2 p.

Definition coe {A B : Type} (p : A = B) : A <~> B
  := (coe' p; iseqi_coe p).

Axiom iseqi_path_to_eqi : forall (A B : Type), IsEqi (@coe A B).

Definition ua {A B : Type} : (A <~> B) <~> (A = B).
Proof.
  simple refine (_; _).
  - exact (@coe A B; iseqi_path_to_eqi A B)^-1.
  - exact (inveqi _).2.
Defined.

Lemma pua (A B : Type) : (A <~> B) = (A = B).
Proof.
  apply ua.
  exact ua.
Defined.


(***** Funext *******************************************************)


Definition path_to_homot {A : Type} {B : A -> Type}
  {f g : forall a, B a} (p : f = g) : f ~ g
  := tr (fun h => f ~ h) p (fun a => 1).

Axiom iseqi_path_to_homot :
  forall {A : Type} {B : A -> Type} (f g : forall a, B a),
  IsEqi (@path_to_homot A B f g).

Definition funext {A : Type} {B : A -> Type} {f g : forall a, B a}
  : (f ~ g) <~> (f = g).
Proof.
  simple refine (_; _).
  - exact (@path_to_homot A B f g; @iseqi_path_to_homot A B f g)^-1.
  - exact (inveqi _).2.
Defined.

Definition fap {A : Type} {B : A -> Type} {f g : forall a, B a}
  : (f = g) <~> (f ~ g)
  := funext^-1.

Lemma pfunext {A : Type} {B : A -> Type} (f g : forall a, B a)
  : (f ~ g) = (f = g).
Proof.
  apply ua.
  exact funext.
Defined.


(***** Sigext *******************************************************)


Definition SigPath {A : Type} {B : A -> Type} (u v : {a | B a}) : Type
  := {p : u.1 = v.1 | tr B p u.2 = v.2}.

Notation "u !! v" := (SigPath u v) (at level 70, no associativity) : type_scope.

Definition path_to_sig_path {A : Type} {B : A -> Type}
  {u v : {a | B a}} (p : u = v)
  : u !! v
  := tr (SigPath u) p (1; 1).

Definition sigext' {A : Type} {B : A -> Type}
  {u v : {a | B a}} (p : u !! v)
  : u = v.
Proof.
  destruct p as [p q].
  destruct u as [u1 u2].
  destruct v as [v1 v2].
  cbn in p. induction p.
  cbn in q. induction q.
  exact 1.
Defined.

Lemma isretr_path_to_sig_path {A : Type} {B : A -> Type}
  {u v : {a | B a}} (p : u !! v)
  : path_to_sig_path (sigext' p) = p.
Proof.
  destruct p as [p q].
  destruct u as [u1 u2].
  destruct v as [v1 v2].
  cbn in p. induction p.
  cbn in q. induction q.
  exact 1.
Defined.

Lemma issect_path_to_sig_path {A : Type} {B : A -> Type}
  {u v : {a | B a}} (p : u = v)
  : sigext' (path_to_sig_path p) = p.
Proof.
  induction p.
  exact 1.
Defined.

Definition iseqi_path_to_sig_path {A : Type} {B : A -> Type}
  {u v : {a | B a}}
  : IsEqi (@path_to_sig_path A B u v)
  := ((sigext'; issect_path_to_sig_path);
      (sigext'; isretr_path_to_sig_path)).

Definition sigext {A : Type} {B : A -> Type} {u v : {a | B a}}
  : (u !! v) <~> (u = v).
Proof.
  simple refine (_; _).
  - exact (@path_to_sig_path A B u v; @iseqi_path_to_sig_path A B u v)^-1.
  - exact (inveqi _).2.
Defined.

Definition ppair {A : Type} {B : A -> Type} {u v : {a | B a}}
  : (u = v) <~> (u !! v)
  := sigext^-1.

Definition ppr1 {A : Type} {B : A -> Type} {u v : {a | B a}} (p : u = v)
  : u.1 = v.1
  := (ppair p).1.

Definition ppr2 {A : Type} {B : A -> Type} {u v : {a | B a}} (p : u = v)
  : tr B (ppr1 p) u.2 = v.2
  := (ppair p).2.

Lemma psigext {A : Type} {B : A -> Type} (u v : {a | B a})
  : (u !! v) = (u = v).
Proof.
  apply ua.
  exact sigext.
Defined.


Definition test {X : Type} {x1 x2 : X} (p : x1 = x2)
  : pap (fun x r =>
      some_equiv (Path_ind (fun y s => forall a : A x r y s, B x r y s a)
                           (c x r) (q x r) (a0 x r)) p)
where some_equiv : forall x r y s a, B x r y s a <~> C.

  some_equiv x1 1 (Path_ind ... x1 1 ...) = some_equiv x2 p (Path_ind ... x2 p ...)
  iff
  some_equiv' (Path_ind ... x1 1 ...) = Path_ind ... x2 p ...

