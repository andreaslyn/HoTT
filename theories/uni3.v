
Set Primitive Projections.
Unset Elimination Schemes.

(***** Judgmental equality ******************************************)

Inductive Eq {A : Type} (a : A) : A -> Type
  := eqrefl : Eq a a.

Scheme Eq_ind := Elimination for Eq Sort Type.
Scheme Eq_rect := Elimination for Eq Sort Type.
Scheme Eq_rec := Elimination for Eq Sort Type.

Arguments eqrefl {A a} , {A} a.

Notation "x === y" :=
  (Eq x y) (at level 90, no associativity) : type_scope.

(***** Function type ************************************************)


Notation id := (fun x => x).

Notation "g 'o' f" :=
  (fun x => g (f x)) (at level 40, left associativity).


(***** Sig type *****************************************************)


Declare Scope Sig_scope.
Open Scope Sig_scope.

Record Sig (A : Type) (B : A -> Type) : Type := mkSig
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


(***** Path type former *********************************************)


Declare Scope Path_scope.
Open Scope Path_scope.

Inductive Path {A : Type} : A -> A -> Type
  := refl : forall (a : A), Path a a.

Notation "x = y" := (Path x y) : type_scope.

Notation "f ~ g" :=
  (forall x, f x = g x) (at level 70, no associativity) : type_scope.

Scheme Path_ind := Elimination for Path Sort Type.
Scheme Path_rect := Elimination for Path Sort Type.
Scheme Path_rec := Elimination for Path Sort Type.

Arguments Path_ind {A} P _ {_} {_} p.
Arguments Path_rect {A} P _ {_} {_} p.
Arguments Path_rec {A} P _ {_} {_} p.


(***** Path structure ***********************************************)


Arguments refl {A a} , {A} a.

Notation "1" := refl : Path_scope.


Lemma inverse {A : Type} {a1 a2 : A} (p : a1 = a2) : a2 = a1.
Proof.
  induction p.
  exact 1.
Defined.

Notation "p ^" := (inverse p) (at level 3, format "p '^'") : Path_scope.


Lemma concat {A : Type} {a1 a2 a3 : A} (p : a1 = a2) (q : a2 = a3) : a1 = a3.
Proof.
  induction p.
  induction q.
  exact 1.
Defined.

Notation "p @ q" := (concat p q) (at level 20) : Path_scope.


Lemma ap {A B : Type} {a1 a2 : A} (f : forall (x : A), a1 = x -> B)
  (p : a1 = a2) : f a1 1 = f a2 p.
Proof.
  induction p.
  exact 1.
Defined.


Lemma law_assoc {A : Type} {a1 a2 a3 a4 : A}
  (pa1 : a1 = a2) (pa2 : a2 = a3) (pa3 : a3 = a4)
  : pa1 @ (pa2 @ pa3) = (pa1 @ pa2) @ pa3.
Proof.
  induction pa1.
  induction pa2.
  induction pa3.
  exact 1.
Defined.

Lemma law_inverse_left {A : Type} {a1 a2 : A} (pa : a1 = a2)
  : pa^ @ pa = 1.
Proof.
  induction pa.
  exact 1.
Defined.

Lemma law_refl_left {A : Type} {a1 a2 : A} (pa : a1 = a2)
  : 1 @ pa = pa.
Proof.
  induction pa.
  exact 1.
Defined.

Lemma law_ap_const {A B : Type} {a1 a2 : A} (b : B) (p : a1 = a2)
  : ap (fun _ _ => b) p = 1.
Proof.
  induction p.
  exact 1.
Defined.

Lemma law_ap_inverse {A B : Type} {a1 a2 : A}
  (f : A -> B) (p : a1 = a2)
  : ap (fun a _ => f a) p^ = (ap (fun a _ => f a) p)^.
Proof.
  induction p.
  exact 1.
Defined.

Lemma law_ap_concat {A B : Type} {a1 a2 a3 : A} (f : A -> B)
  (p : a1 = a2) (q : a2 = a3)
  : ap (fun a _ => f a) (p @ q)
    = ap (fun a _ => f a) p @ ap (fun a _ => f a) q.
Proof.
  induction p.
  induction q.
  exact 1.
Defined.


(***** Derived laws *************************************************)


Definition law_inverse_right {A : Type} {a1 a2 : A} (pa : a1 = a2)
  : pa @ pa^ = 1.
Proof.
  refine (ap (fun q _ => q @ pa^) (law_refl_left pa)^ @ _).
  refine (ap (fun q _ => q @ pa @ pa^) (law_inverse_left pa^)^ @ _).
  refine (ap (fun q _ => q @ pa^) (law_assoc pa^^ pa^ pa)^ @ _).
  refine (ap (fun q _ => pa^^ @ q @ pa^) (law_inverse_left pa) @ _).
  refine ((law_assoc pa^^ 1 pa^)^ @ _).
  refine (ap (fun q _ => pa^^ @ q) (law_refl_left pa^) @ _).
  exact (law_inverse_left pa^).
Defined.

Definition law_refl_right {A : Type} {a1 a2 : A} (pa : a1 = a2)
  : pa @ 1 = pa.
Proof.
  refine (ap (fun q _ => pa @ q) (law_inverse_left pa)^ @ _).
  refine ((law_assoc pa pa^ pa) @ _).
  refine (ap (fun q _ => q @ pa) (law_inverse_right pa) @ _).
  exact (law_refl_left pa).
Defined.

Definition law_inverse_inverse {A : Type} {a1 a2 : A} (p : a1 = a2)
  : p^^ = p.
Proof.
  refine ((law_refl_right p^^)^ @ _).
  refine (ap (fun q _ => p^^ @ q) (law_inverse_left p)^ @ _).
  refine ((law_assoc p^^ p^ p) @ _).
  refine (ap (fun q _ => q @ p) (law_inverse_left p^) @ _).
  exact (law_refl_left p).
Defined.


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
      @ ap (fun y _ => retr_eqi f y) (homot_isretr_eqi f (f x))
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
    exact (ap (fun b _ => retr_eqi f b) ((issect_eqi g).2 _)
           @ (issect_eqi f).2 x).
  - refine (sect_eqi f o sect_eqi g; (fun y => _)).
    exact (ap (fun b _ => eqi g b) ((isretr_eqi f).2 _)
           @ (isretr_eqi g).2 y).
Defined.

Definition comeqi {A B C} (g : B <~> C) (f : A <~> B) : A <~> C
  := (g o f; iseqi_comeqi g f).

Notation "g 'oE' f" :=
  (comeqi g f) (at level 40, left associativity) : Sig_scope.


(***** Path of type *************************************************)


Definition Path_Type (A B : Type) : Type := A <~> B.

Axiom Path_is_Path_Type :
  forall (A B : Type),
  (A = B) === Path_Type A B.

Definition coe {A B : Type} (p : A = B) : A <~> B.
Admitted. (* They are judgmentally equal. *)

Definition refl_Path_Type (A : Type) : Path_Type A A
  := ideqi.

Definition inverse_Path_Type {A B : Type} (p : Path_Type A B)
  : Path_Type B A
  := p^-1.

Definition concat_Path_Type {A B C : Type}
  (p : Path_Type A B) (q : Path_Type B C)
  : Path_Type A C
  := q oE p.

(* TODO Need path of equiv for the laws. *)

(* The following laws for coe hold because of judgmentally equal: *)

Definition coe_refl (A : Type)
  : coe (refl A) = ideqi.
Admitted.

Definition coe_refl' {A : Type} (a : A)
  : coe (refl A) a = a
  := ap (fun e _ => eqi e a) (coe_refl A).

Definition law_coe_inverse {A B : Type} (p : A = B)
  : coe p^ = (coe p)^-1.
Admitted.

Definition law_coe_inverse' {A B : Type} (p : A = B) (b : B)
  : coe p^ b = (coe p)^-1 b
  := ap (fun e _ => eqi e b) (law_coe_inverse p).

Definition law_coe_concat {A B C : Type} (p : A = B) (q : B = C)
  : coe (p @ q) = coe q oE coe p.
Admitted.

Definition law_coe_concat' {A B C : Type} (p : A = B) (q : B = C) (a : A)
  : coe (p @ q) a = coe q (coe p a)
  := ap (fun e _ => eqi e a) (law_coe_concat p q).


Definition pind {A : Type} {a1 a2 : A}
  (B : forall x : A, a1 = x -> Type) (p : a1 = a2)
  : B a1 1 <~> B a2 p
  := coe (ap B p).

Definition beta_ind {A : Type} {a : A} (B : forall x : A, a = x -> Type)
  : pind B 1 = ideqi.
Admitted.

Definition beta_ind' {A : Type} {a : A}
  (B : forall x : A, a = x -> Type) (b : B a 1)
  : pind B 1 b = b
  := ap (fun e _ => eqi e b) (beta_ind B).

Definition apD  {A : Type} {a1 a2 : A} (B : forall x : A, a1 = x -> Type)
  (f : forall (x : A) (r : a1 = x), B x r) (p : a1 = a2)
  : pind B p (f a1 1) = f a2 p
  :=  (ap (fun i _ => pind B p (sect_eqi i (f a1 1))) (beta_ind B))^
      @ ap (fun y q => pind B p (inveqi (pind B q) (f y q))) p
      @ homot_isretr_eqi (pind B p) (f a2 p).
  (* The first path is a beta rule. *)


(***** Path of Sig **************************************************)


Definition Path_Sig {A : Type} {B : A -> Type} (u v : {a | B a})
  : Type
  := {p : u.1 = v.1 | pind (fun x _ => B x) p u.2 = v.2}.

Axiom Path_is_Path_Sig :
  forall {A : Type} {B : A -> Type} (u v : {a | B a}),
  (u = v) === Path_Sig u v.

Definition ppr1 :
  forall {A : Type} {B : A -> Type} {u v : {a | B a}},
  u = v -> u.1 = v.1.
Admitted. (* This is just first projection. *)

Definition ppr2 :
  forall {A : Type} {B : A -> Type} {u v : {a | B a}} (p : u = v),
  pind (fun x _ => B x) (ppr1 p) u.2 = v.2.
Admitted. (* This is just second projection. *)

Definition refl_Path_Sig {A : Type} {B : A -> Type} (u : {a | B a})
  : Path_Sig u u
  := (1; beta_ind' (fun a _ => B a) u.2).

Definition inverse_Path_Sig {A : Type} {B : A -> Type} {u v : {a | B a}}
  (p : Path_Sig u v)
  : Path_Sig v u.
Proof.
  refine (p.1^; _).
  refine (ap (fun x _ => coe x v.2) (law_ap_inverse B p.1) @ _).
  refine (law_coe_inverse' (ap (fun a _ => B a) p.1) v.2 @ _).
  refine (ap (fun x _ => (coe (ap (fun a _ => B a) p.1))^-1 x) p.2^ @ _).
  exact (homot_retr_inveqi (coe (ap (fun a _ => B a) p.1)) u.2).
Defined.

Definition compose_Path_Sig {A : Type} {B : A -> Type} {u v w : {a | B a}}
  (p : Path_Sig u v) (q : Path_Sig v w)
  : Path_Sig u w.
Proof.
  refine (p.1 @ q.1; _).
  refine (ap (fun x _ => coe x u.2) (law_ap_concat B p.1 q.1) @ _).
  refine (law_coe_concat' (ap (fun a _ => B a) p.1)
                          (ap (fun a _ => B a) q.1) u.2 @ _).
  refine (ap (fun x _ => pind (fun a _ => B a) q.1 x) p.2 @ _).
  exact q.2.
Defined.

Definition law_assoc_compose_Path_Sig {A : Type} {B : A -> Type}
  {u v w z : {a | B a}}
  (p : Path_Sig u v) (q : Path_Sig v w) (r : Path_Sig w z)
  : compose_Path_Sig p (compose_Path_Sig q r)
    = compose_Path_Sig (compose_Path_Sig p q) r.
Proof.
  unfold compose_Path_Sig.
  cbn.
Admitted.

Definition Path_Fun {A : Type} {B : A -> Type} (f g : forall a, B a)
  : Type
  := forall (a1 : A) (a2 : A) (pa : a1 = a2),
     tr B pa (f a1) = g a2.

Axiom Path_is_Path_Fun :
  forall {A : Type} {B : A -> Type} (f g : forall a, B a),
  (f = g) === Path_Fun f g.

Definition app :
  forall {A : Type} {B : A -> Type} {f g : forall a, B a},
  f = g ->
  forall (a1 : A) (a2 : A) (pa : a1 = a2),
  tr B pa (f a1) = g a2.
Admitted. (* They are judgmentally equal. *)
