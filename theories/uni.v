
Set Primitive Projections.
Unset Elimination Schemes.

Axiom BETA : forall {A B}, B -> A.

(***** Definitional equality ****************************************)

Inductive Eq {A:Type} (a : A) : A -> Type
  := eqrefl : Eq a a.

Scheme Eq_ind := Elimination for Eq Sort Type.
Scheme Eq_rect := Elimination for Eq Sort Type.
Scheme Eq_rec := Elimination for Eq Sort Type.

Arguments eqrefl {A a} , {A} a.

Notation "x = y" := (Eq x y) : type_scope.

(***** Base types ***************************************************)

Notation id := (fun x => x).

Notation "g 'o' f" :=
  (fun x => g (f x)) (at level 40, left associativity).


Declare Scope Sig_scope.
Open Scope Sig_scope.

Record Sig (A : Type) (B : A -> Type) : Type :=
  { pr1 : A ; pr2 : B pr1 }.

Arguments Sig {A}.
Arguments Build_Sig {A B}.
Arguments pr1 {A B}.
Arguments pr2 {A B}.

Scheme Sig_ind := Elimination for Sig Sort Type.
Scheme Sig_rect := Elimination for Sig Sort Type.
Scheme Sig_rec := Elimination for Sig Sort Type.

Arguments Sig_ind {A B}.
Arguments Sig_rect {A B}.
Arguments Sig_rec {A B}.

Notation "{ x : A  |  P }" := (Sig (fun x : A => P)) : type_scope.
Notation "{ x  |  P }" := (Sig (fun x => P)) : type_scope.

Notation "s .1" := (pr1 s) (at level 3, format "s '.1'").
Notation "s .2" := (pr2 s) (at level 3, format "s '.2'").
Notation "( a ; b )" := {| pr1 := a ; pr2 :=  b |} : Sig_scope.


(***** Path type former *********************************************)

Declare Scope Path_scope.
Open Scope Path_scope.

Axiom Path@{i j k} :
  forall {A : Type@{i}} {B : Type@{j}}, A -> B -> Type@{k}.

Notation "a ~ b" := (Path a b) (at level 70, no associativity) : type_scope.

Axiom refl : forall {A : Type} (a : A), a ~ a.

Arguments refl {A a} , {A} a.

Notation "1" := refl : Path_scope.

Notation "f ~~ g" :=
  (forall x, f x ~ g x) (at level 70, no associativity) : type_scope.


(***** Equivalence **************************************************)


Definition IsRetr {A B} (f : A -> B) : Type
  := {g : B -> A | f o g ~~ id}.

Definition IsSect {A B} (f : A -> B) : Type
  := {h : B -> A | h o f ~~ id}.

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
  : retr_eqi f o f ~~ id
  := (issect_eqi f).2.

Definition isretr_eqi {A B} (f : A <~> B) : IsRetr f
  := f.2.2.

Definition sect_eqi {A B} (f : A <~> B) : B -> A
  := (isretr_eqi f).1.

Definition homot_isretr_eqi {A B} (f : A <~> B)
  : f o sect_eqi f ~~ id
  := (isretr_eqi f).2.

Definition iseqi_ideqi {A : Type} : @IsEqi A A id :=
  ((id; fun x => 1); (id; fun x => 1)).

Definition ideqi {A:Type} : A <~> A
  := (id; iseqi_ideqi).

Arguments ideqi {A} , A.


(***** Path rules ***************************************************)


(* Type path introduction rules. *)

Axiom type_path : forall {A B : Type}, A <~> B -> A ~ B.

Axiom type_path_2 :
  forall {A B : Type} (e e' : A <~> B) (e2 : e ~ e'),
  type_path e ~ type_path e'.

Axiom type_path_3 :
  forall {A B : Type} (e e' : A <~> B)
  {e2 e2' : e ~ e'} (e3 : e2 ~ e2'),
  type_path_2 e e' e2 ~ type_path_2 e e' e2'.

Axiom type_path_4 :
  forall {A B : Type} (e e' : A <~> B)
         {e2 e2' : e ~ e'} {e3 e3' : e2 ~ e2'} (e4 : e3 ~ e3'),
  type_path_3 e e' e3 ~ type_path_3 e e' e3'.

(* Type path elimination rule. *)

Axiom coe : forall {A B : Type}, A ~ B -> A <~> B.

Axiom coe_2 :
  forall {A B : Type} {e e' : A ~ B},
  e ~ e' -> coe e ~ coe e'.

Axiom coe_3 :
  forall {A B : Type} {e e' : A ~ B} {e2 e2' : e ~ e'},
  e2 ~ e2' -> coe_2 e2 ~ coe_2 e2'.

Axiom coe_4 :
  forall {A B : Type} {e e' : A ~ B}
         {e2 e2' : e ~ e'} {e3 e3' : e2 ~ e2'},
  e3 ~ e3' -> coe_3 e3 ~ coe_3 e3'.

(* Type path beta rule. *)

Axiom beta_coe : forall {A B : Type} (f : A <~> B), coe (type_path f) = f.

Axiom beta_coe_2 :
  forall {A B : Type} (e e' : A ~ B) (e2 : coe e ~ coe e'),
  coe_2 (type_path_2 (coe e) (coe e') e2) = BETA e2.

Axiom beta_coe_3 :
  forall {A B : Type} (e e' : A ~ B)
         {e2 e2' : coe e ~ coe e'} (e3 : e2 ~ e2'),
  coe_3 (type_path_3 (coe e) (coe e') e3) = BETA e3.

Axiom beta_coe_4 :
  forall {A B : Type} (e e' : A ~ B)
         {e2 e2' : coe e ~ coe e'} {e3 e3' : e2 ~ e2'} (e4 : e3 ~ e3'),
  coe_4 (type_path_4 (coe e) (coe e') e4) = BETA e4.

(* Type path reflexivity. *)

Definition refl_type (A : Type) : A ~ A := type_path ideqi.

Definition refl_type_2 {A B} (e : A <~> B) : type_path e ~ type_path e
  := type_path_2 e e 1.

Definition refl_type_3 {A B} {e e' : A <~> B} (e2 : e ~ e')
  : type_path_2 e e' e2 ~ type_path_2 e e' e2
  := type_path_3 e e' 1.

Definition refl_type_4 {A B} {e e' : A <~> B} {e2 e2' : e ~ e'}
  (e3 : e2 ~ e2')
  : type_path_3 e e' e3 ~ type_path_3 e e' e3
  := type_path_4 e e' 1.

(* Type path reflexivity maps to identity. *)

Definition beta_coe_id (A : Type)
  : coe (refl_type A) = ideqi
  := beta_coe ideqi.

Definition beta_coe_id_2 {A : Type} (e : A ~ A)
  : coe_2 (refl_type_2 (coe e)) = BETA 1
  := beta_coe_2 e e 1.

Definition beta_coe_id_3 {A : Type} (e e' : A ~ A) (e2 : coe e ~ coe e')
  : coe_3 (refl_type_3 e2) = BETA 1
  := beta_coe_3 e e' 1.

Definition beta_coe_id_4 {A : Type} (e e' : A ~ A)
  {e2 e2' : coe e ~ coe e'} (e3 : e2 ~ e2')
  : coe_4 (refl_type_4 e3) = BETA 1
  := beta_coe_4 e e' 1.

(* Function path introduction rules. *)

Axiom fun_path :
  forall {A : Type} {B : A -> Type} {f g : forall a, B a}
         (h : forall (x y : A) (p : x ~ y), f x ~ g y),
  f ~ g.

Axiom fun_path_2 :
  forall {A : Type} {B : A -> Type} {f g : forall a, B a}
         {h h' : forall (x y : A) (p : x ~ y), f x ~ g y}
         (h2 : h ~ h'),
  fun_path h ~ fun_path h'.

Axiom fun_path_3 :
  forall {A : Type} {B : A -> Type} {f g : forall a, B a}
         {h h' : forall (x y : A) (p : x ~ y), f x ~ g y}
         {h2 h2' : h ~ h'} (h3 : h2 ~ h2'),
  fun_path_2 h2 ~ fun_path_2 h2'.

Axiom fun_path_4 :
  forall {A : Type} {B : A -> Type} {f g : forall a, B a}
         {h h' : forall (x y : A) (p : x ~ y), f x ~ g y}
         {h2 h2' : h ~ h'} {h3 h3' : h2 ~ h2'}
         (h4 : h3 ~ h3'),
  fun_path_3 h3 ~ fun_path_3 h3'.

(* Function path elimination rules. *)

Axiom pointwise :
  forall {A : Type} {B : A -> Type} {f g : forall a, B a},
  f ~ g -> forall (x y : A) (p : x ~ y), f x ~ g y.

Axiom pointwise_2 :
  forall {A : Type} {B : A -> Type} {f g : forall a, B a}
         {h h' : f ~ g},
  h ~ h' -> @pointwise A B f g h ~ @pointwise A B f g h'.

Axiom pointwise_3 :
  forall {A : Type} {B : A -> Type} {f g : forall a, B a}
         {h h' : f ~ g} {h2 h2' : h ~ h'},
  h2 ~ h2' -> pointwise_2 h2 ~ pointwise_2 h2'.

Axiom pointwise_4 :
  forall {A : Type} {B : A -> Type} {f g : forall a, B a}
         {h h' : f ~ g} {h2 h2' : h ~ h'}
         {h3 h3' : h2 ~ h2'},
  h3 ~ h3' -> pointwise_3 h3 ~ pointwise_3 h3'.

(* Function path beta rules. *)

Axiom beta_pointwise :
  forall {A : Type} {B : A -> Type} {f g : forall a, B a}
         (h : forall (x y : A) (p : x ~ y), f x ~ g y),
  @pointwise A B f g (fun_path h) = h.

Axiom beta_pointwise_2 :
  forall {A : Type} {B : A -> Type} {f g : forall a, B a}
         {h h' : f ~ g} (h2 : pointwise h ~ pointwise h'),
  pointwise_2 (fun_path_2 h2) = BETA h2.

Axiom beta_pointwise_3 :
  forall {A : Type} {B : A -> Type} {f g : forall a, B a}
         {h h' : f ~ g} {h2 h2' : pointwise h ~ pointwise h'}
         (h3 : h2 ~ h2'),
  pointwise_3 (fun_path_3 h3) = BETA h3.

Axiom beta_pointwise_4 :
  forall {A : Type} {B : A -> Type} {f g : forall a, B a}
         {h h' : f ~ g} {h2 h2' : pointwise h ~ pointwise h'}
         {h3 h3' : h2 ~ h2'} (h4 : h3 ~ h3'),
  pointwise_4 (fun_path_4 h4) = BETA h4.

(* Type path reflexivity. *)

Definition refl_fun {A : Type} {B : A -> Type} (f : forall a, B a)
  : f ~ f.
apply fun_path. intros.
Admitted.


(* Sig path introduction rules. *)

Axiom sig_path :
  forall {A : Type} {B : A -> Type} (u v : {a | B a})
         (p : u.1 ~ v.1) (q : u.2 ~ v.2),
  u ~ v.

Axiom sig_path_2 :
  forall {A : Type} {B : A -> Type} (u v : {a | B a})
         {p p' : u.1 ~ v.1} {q q' : u.2 ~ v.2}
         (p2 : p ~ p') (q2 : q ~ q'),
  sig_path u v p q ~ sig_path u v p' q'.

Axiom sig_path_3 :
  forall {A : Type} {B : A -> Type} (u v : {a | B a})
         {p p' : u.1 ~ v.1} {q q' : u.2 ~ v.2}
         {p2 p2' : p ~ p'} {q2 q2' : q ~ q'}
         (p3 : p2 ~ p2') (q3 : q2 ~ q2'),
  sig_path_2 u v p2 q2 ~ sig_path_2 u v p2' q2'.

Axiom sig_path_4 :
  forall {A : Type} {B : A -> Type} (u v : {a | B a})
         {p p' : u.1 ~ v.1} {q q' : u.2 ~ v.2}
         {p2 p2' : p ~ p'} {q2 q2' : q ~ q'}
         {p3 p3' : p2 ~ p2'} {q3 q3' : q2 ~ q2'}
         (p4 : p3 ~ p3') (q4 : q3 ~ q3'),
  sig_path_3 u v p3 q3 ~ sig_path_3 u v p3' q3'.

(* Sig path elimination rules 1. *)

Axiom ppr1 :
  forall {A : Type} {B : A -> Type} {u v : {a | B a}},
  u ~ v -> u.1 ~ v.1.

Axiom ppr1_2 :
  forall {A : Type} {B : A -> Type} {u v : {a | B a}} {p p' : u ~ v},
  p ~ p' -> ppr1 p ~ ppr1 p'.

Axiom ppr1_3 :
  forall {A : Type} {B : A -> Type} {u v : {a | B a}}
         {p p' : u ~ v} {p2 p2' : p ~ p'},
  p2 ~ p2' -> ppr1_2 p2 ~ ppr1_2 p2'.

Axiom ppr1_4 :
  forall {A : Type} {B : A -> Type} {u v : {a | B a}}
         {p p' : u ~ v} {p2 p2' : p ~ p'}
         {p3 p3' : p2 ~ p2'},
  p3 ~ p3' -> ppr1_3 p3 ~ ppr1_3 p3'.

(* Sig path elimination rules 2. *)

Axiom ppr2 :
  forall {A : Type} {B : A -> Type} {u v : {a | B a}},
  u ~ v -> u.2 ~ v.2.

Axiom ppr2_2 :
  forall {A : Type} {B : A -> Type} {u v : {a | B a}} {p p' : u ~ v},
  p ~ p' -> ppr2 p ~ ppr2 p'.

Axiom ppr2_3 :
  forall {A : Type} {B : A -> Type} {u v : {a | B a}}
         {p p' : u ~ v} {p2 p2' : p ~ p'},
  p2 ~ p2' -> ppr2_2 p2 ~ ppr2_2 p2'.

Axiom ppr2_4 :
  forall {A : Type} {B : A -> Type} {u v : {a | B a}}
         {p p' : u ~ v} {p2 p2' : p ~ p'}
         {p3 p3' : p2 ~ p2'},
  p3 ~ p3' -> ppr2_3 p3 ~ ppr2_3 p3'.

(* Sig path beta rules 1. *)

Axiom beta_ppr1 :
  forall {A : Type} {B : A -> Type} (u v : {a | B a})
         (p : u.1 ~ v.1) (q : u.2 ~ v.2),
  ppr1 (sig_path u v p q) = p.

Axiom beta_ppr1_2 :
  forall {A : Type} {B : A -> Type} {u v : {a | B a}} (p p' : u ~ v)
         (p2 : ppr1 p ~ ppr1 p') (q2 : ppr2 p ~ ppr2 p'),
  ppr1_2 (sig_path_2 u v p2 q2) = BETA p2.

Axiom beta_ppr1_3 :
  forall {A : Type} {B : A -> Type} {u v : {a | B a}}
         {p p' : u ~ v} {p2 : p ~ p'}
         (p3 : ppr1_2 p2 ~ ppr1_2 p2) (q3 : ppr2_2 p2 ~ ppr2_2 p2),
  ppr1_3 (sig_path_3 u v p3 q3) = BETA p3.

Axiom beta_ppr1_4 :
  forall {A : Type} {B : A -> Type} {u v : {a | B a}}
         {p p' : u ~ v} {p2 p2' : p ~ p'}
         {p3 p3' : p2 ~ p2'}
         (p4 : ppr1_3 p3 ~ ppr1_3 p3') (q4 : ppr2_3 p3 ~ ppr2_3 p3'),
  ppr1_4 (sig_path_4 u v p4 q4) = BETA p4.

(* Sig path beta rules 2. *)

Axiom beta_ppr2 :
  forall {A : Type} {B : A -> Type} (u v : {a | B a})
         (p : u.1 ~ v.1) (q : u.2 ~ v.2),
  ppr2 (sig_path u v p q) = q.

Axiom beta_ppr2_2 :
  forall {A : Type} {B : A -> Type} {u v : {a | B a}} (p p' : u ~ v)
         (p2 : ppr1 p ~ ppr1 p') (q2 : ppr2 p ~ ppr2 p'),
  ppr2_2 (sig_path_2 u v p2 q2) = BETA q2.

Axiom beta_ppr2_3 :
  forall {A : Type} {B : A -> Type} {u v : {a | B a}}
         {p p' : u ~ v} {p2 : p ~ p'}
         {p3 : ppr1_2 p2 ~ ppr1_2 p2} {q3 : ppr2_2 p2 ~ ppr2_2 p2},
  ppr2_3 (sig_path_3 u v p3 q3) = BETA q3.

Axiom beta_ppr2_4 :
  forall {A : Type} {B : A -> Type} {u v : {a | B a}}
         {p p' : u ~ v} {p2 p2' : p ~ p'}
         {p3 p3' : p2 ~ p2'}
         (p4 : ppr1_3 p3 ~ ppr1_3 p3') (q4 : ppr2_3 p3 ~ ppr2_3 p3'),
  ppr2_4 (sig_path_4 u v p4 q4) = BETA q4.

(* Sig path reflexivity. *)

Definition refl_sig {A : Type} {B : A -> Type} (u : {a | B a})
  : u ~ u
  := sig_path u u 1 1.

(* NOTE The sig beta rules map identity to identity. *)


(***** Various ******************************************************)


(* NOTE missing path induction principle *)

Definition tr {A : Type} {x y : A} (P : A -> Type) (c : P x) (p : x ~ y) : P y
  := coe (pointwise 1 x y p) c.

Definition naive_funext {A : Type} {B : A -> Type} {f g : forall a, B a}
  (h : forall a, f a ~ g a) : f ~ g
  := fun_path (fun x y p => tr (fun y => f x ~ g y) (h x) p).