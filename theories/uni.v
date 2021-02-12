
Set Primitive Projections.
Unset Elimination Schemes.


(***** Base types ***************************************************)


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


Declare Scope Id_scope.
Open Scope Id_scope.

Inductive Id {A:Type} (x : A) : A -> Type
  := refl : Id x x.

Scheme Id_ind := Elimination for Id Sort Type.
Scheme Id_rect := Elimination for Id Sort Type.
Scheme Id_rec := Elimination for Id Sort Type.

Arguments Id_ind {A} {x} P c {y} : rename.
Arguments Id_rect {A} {x} P c {y} : rename.
Arguments Id_rec {A} {x} P c {y} : rename.

Arguments refl {A x} , {A} x.

Notation "x = y" := (Id x y) : type_scope.
Notation "1" := refl : Id_scope.


Notation "f == g" :=
  (forall x, f x = g x) (at level 70, no associativity) : type_scope.

Notation id := (fun x => x).

Notation "g 'o' f" :=
  (fun x => g (f x)) (at level 40, left associativity) : fun_scope.

Open Scope fun_scope.


Definition ap {A B} {x y : A} (f : A -> B) (p : x = y) : f x = f y
  := Id_ind (fun y _ => f x = f y) refl p.

Definition concat {A} {x y z : A} (p : x = y) : y = z -> x = z
  := Id_ind (fun y _ => y = z -> x = z) id p.

Definition inverse {A} {x y : A} (p : x = y) : y = x
  := Id_ind (fun y _ => y = x) refl p.

Notation "p @ q" := (concat p q) (at level 20) : Id_scope.

Notation "p ^" := (inverse p) (at level 3, format "p '^'").


(***** Equivalence **************************************************)


Definition IsRetr {A B} (f : A -> B) : Type
  := {g : B -> A | f o g == id}.

Definition IsSect {A B} (f : A -> B) : Type
  := {h : B -> A | h o f == id}.

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
  : retr_eqi f o f == id
  := (issect_eqi f).2.

Definition isretr_eqi {A B} (f : A <~> B) : IsRetr f
  := f.2.2.

Definition sect_eqi {A B} (f : A <~> B) : B -> A
  := (isretr_eqi f).1.

Definition homot_isretr_eqi {A B} (f : A <~> B)
  : f o sect_eqi f == id
  := (isretr_eqi f).2.

Definition homot_sect_inveqi {A B} 
  : forall (f : A <~> B), f o sect_eqi f == id
  := homot_isretr_eqi.

Definition issect_inveqi {A B} (f : A <~> B) : IsSect (sect_eqi f)
  := (eqi f; homot_sect_inveqi f).

Definition homot_retr_inveqi {A B} (f : A <~> B)
  : sect_eqi f o f == id
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
    exact (ap (fun b => retr_eqi f b) ((issect_eqi g).2 _)
           @ (issect_eqi f).2 x).
  - refine (sect_eqi f o sect_eqi g; (fun y => _)).
    exact (ap (fun b => eqi g b) ((isretr_eqi f).2 _)
           @ (isretr_eqi g).2 y).
Defined.

Definition comeqi {A B C} (g : B <~> C) (f : A <~> B) : A <~> C
  := (g o f; iseqi_comeqi g f).

Notation "g 'oE' f" :=
  (comeqi g f) (at level 40, left associativity) : Sig_scope.


(***** Path *********************************************************)


Axiom Path@{i j k} :
  forall {A : Type@{i}} {B : Type@{j}}, A -> B -> Type@{k}.

Notation "x ~ y" :=
  (Path x y) (at level 70, no associativity) : type_scope.


(* For each of the below introduction rules we will show that
   there is an identity inhabitant: *)

Axiom idpath : forall {A : Type} (a : A), a ~ a.

Arguments idpath {A a} , {A} a.

(* We will moreover show that the elimination rules map
   identity to identity *)


(* Type path introduction rule. *)

Axiom type_path : forall {A B : Type}, A <~> B -> A ~ B.

(* Type path elimination rule. *)

Axiom coe : forall {A B : Type}, A ~ B -> A <~> B.

(* Type path beta rule. *)

Axiom beta_coe : forall {A B : Type} (f : A <~> B), coe (type_path f) = f.

(* Type path reflexivity. *)

Definition idpath_type (A : Type) : A ~ A := type_path ideqi.

(* Type path reflexivity maps to identity. *)

Definition beta_coe_id (A : Type)
  : coe (idpath_type A) = ideqi
  := beta_coe _.

(* Function path introduction rule. *)

Axiom fun_path :
  forall {A1 A2 : Type} {B1 : A1 -> Type} {B2 : A2 -> Type}
         {f : forall a, B1 a} {g : forall a, B2 a}
         (h : forall (x : A1) (y : A2) (p : x ~ y), f x ~ g y),
         f ~ g.

(* Function path elimination rule. *)

Axiom pointwise :
  forall {A1 A2 : Type} {B1 : A1 -> Type} {B2 : A2 -> Type}
         {f : forall a, B1 a} {g : forall a, B2 a},
  f ~ g -> forall {x : A1} {y : A2} (p : x ~ y), f x ~ g y.

(* Function path beta rule. *)

Axiom beta_pointwise :
  forall {A1 A2 : Type} {B1 : A1 -> Type} {B2 : A2 -> Type}
         {f : forall a, B1 a} {g : forall a, B2 a}
         (h : forall (x : A1) (y : A2) (p : x ~ y), f x ~ g y),
  @pointwise A1 A2 B1 B2 f g (fun_path h) = h.

(* Type path reflexivity. *)

Definition idpath_fun {A : Type} {B : A -> Type} (f : forall a, B a)
  : f ~ f.
apply fun_path. intros.
Admitted. (* TODO *)


(* Sig path introduction rule. *)

Axiom sig_path :
  forall {A1 A2 : Type} {B1 : A1 -> Type} {B2 : A2 -> Type}
         (u : {a1 | B1 a1}) (v : {a2 | B2 a2})
         (p : u.1 ~ v.1) (q : u.2 ~ v.2),
  u ~ v.

(* Sig path elimination rule 1. *)

Axiom ppr1 :
  forall {A1 A2 : Type} {B1 : A1 -> Type} {B2 : A2 -> Type}
         {u : {a1 | B1 a1}} {v : {a2 | B2 a2}},
  u ~ v -> u.1 ~ v.1.

(* Sig path elimination rule 2. *)

Axiom ppr2 :
  forall {A1 A2 : Type} {B1 : A1 -> Type} {B2 : A2 -> Type}
         {u : {a1 | B1 a1}} {v : {a2 | B2 a2}},
  u ~ v -> u.2 ~ v.2.

(* Sig path beta rule 1. *)

Axiom beta_ppr1 :
  forall {A1 A2 : Type} {B1 : A1 -> Type} {B2 : A2 -> Type}
         (u : {a1 | B1 a1}) (v : {a2 | B2 a2})
         (p : u.1 ~ v.1) (q : u.2 ~ v.2),
  ppr1 (sig_path u v p q) = p.

(* Sig path beta rule 2. *)

Axiom beta_ppr2 :
  forall {A1 A2 : Type} {B1 : A1 -> Type} {B2 : A2 -> Type}
         (u : {a1 | B1 a1}) (v : {a2 | B2 a2})
         (p : u.1 ~ v.1) (q : u.2 ~ v.2),
  ppr2 (sig_path u v p q) = q.

(* Sig path reflexivity. *)

Definition idpath_sig {A : Type} {B : A -> Type} (u : {a | B a})
  : u ~ u
  := sig_path u u idpath idpath.

(* NOTE The sig beta rules map identity to identity. *)


(* Id path introduction rule. *)

Axiom id_path :
  forall {A : Type} {B : Type} {a1 a2 : A} {b1 b2 : B}
         (i : a1 = a2) (j : b1 = b2)
         (p : a1 ~ b1) (q : a2 ~ b2),
  i ~ j.

(* Id path elimination rule 1. *)

Axiom upper_id :
  forall {A : Type} {B : Type} {a1 a2 : A} {b1 b2 : B}
         {i : a1 = a2} {j : b1 = b2},
  i ~ j -> a1 ~ b1.

(* Id path elimination rule 2. *)

Axiom lower_id :
  forall {A : Type} {B : Type} {a1 a2 : A} {b1 b2 : B}
         {i : a1 = a2} {j : b1 = b2},
  i ~ j -> a2 ~ b2.

(* Id path beta rule 1. *)

Axiom beta_upper_id :
  forall {A : Type} {B : Type} {a1 a2 : A} {b1 b2 : B}
         (i : a1 = a2) (j : b1 = b2)
         (p : a1 ~ b1) (q : a2 ~ b2),
  upper_id (id_path i j p q) = p.

(* Id path beta rule 2. *)

Axiom beta_lower_id :
  forall {A : Type} {B : Type} {a1 a2 : A} {b1 b2 : B}
         (i : a1 = a2) (j : b1 = b2)
         (p : a1 ~ b1) (q : a2 ~ b2),
  lower_id (id_path i j p q) = q.

(* Id path reflexivity. *)

Definition idpath_id {A : Type} {x y : A} (i : x = y)
  : i ~ i
  := id_path i i idpath idpath.

(* NOTE The Id beta rules map identity to identity. *)


(* Path path introduction rule. *)

Axiom path_path :
  forall {A1 A2 : Type} {B1 B2 : Type}
         {a1 : A1} {a2 : A2} {b1 : B1} {b2 : B2}
         (p : a1 ~ a2) (q : b1 ~ b2)
         (r : a1 ~ b1) (s : a2 ~ b2),
  p ~ q.

(* Path path elimination rule 1. *)

Axiom upper_path :
  forall {A1 A2 : Type} {B1 B2 : Type}
         {a1 : A1} {a2 : A2} {b1 : B1} {b2 : B2}
         {p : a1 ~ a2} {q : b1 ~ b2},
  p ~ q -> a1 ~ b1.

(* Path path elimination rule 2. *)

Axiom lower_path :
  forall {A1 A2 : Type} {B1 B2 : Type}
         {a1 : A1} {a2 : A2} {b1 : B1} {b2 : B2}
         {p : a1 ~ a2} {q : b1 ~ b2},
  p ~ q -> a2 ~ b2.

(* Path path beta rule 1. *)

Axiom beta_upper_path :
  forall {A1 A2 : Type} {B1 B2 : Type}
         {a1 : A1} {a2 : A2} {b1 : B1} {b2 : B2}
         (p : a1 ~ a2) (q : b1 ~ b2)
         (r : a1 ~ b1) (s : a2 ~ b2),
  upper_path (path_path p q r s) = r.

(* Path path beta rule 2. *)

Axiom beta_lower_path :
  forall {A1 A2 : Type} {B1 B2 : Type}
         {a1 : A1} {a2 : A2} {b1 : B1} {b2 : B2}
         (p : a1 ~ a2) (q : b1 ~ b2)
         (r : a1 ~ b1) (s : a2 ~ b2),
  lower_path (path_path p q r s) = s.

(* Path path reflexivity. *)

Definition idpath_path {A B : Type} {a : A} {b : B} (p : a ~ b)
  : p ~ p
  := path_path p p idpath idpath.

(* NOTE The Path beta rules map identity to identity. *)


(***** Various ******************************************************)


(* At this point we can define transport (assuming reflexivity): *)
Lemma tr {A : Type} {x y : A} (P : A -> Type) (c : P x) (p : x ~ y) : P y.
Proof.
  assert (P ~ P) as q by admit. (* reflexivity *)
  exact (coe (pointwise q p) c).
Admitted.

(* So Path implies Id: *)
Definition path_to_id {A : Type} {x y : A} (p : x ~ y) : x = y
  := tr (fun y => x = y) refl p.

(* Any therefore we have funext: *)
Theorem funext {A : Type} {B : A -> Type} {f g : forall a, B a}
  (h : forall a, f a = g a) : f = g.
Proof.
  apply path_to_id.
  apply fun_path.
  intros x y p.
  apply path_to_id in p.
  induction p.
  induction (h x).
  (* reflexivity *)
Admitted.

