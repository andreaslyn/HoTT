
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

Definition path_coe_refl (A : Type)
  : coe (refl A) = ideqi.
Admitted.

Definition path_coe_refl' {A : Type} (a : A)
  : coe (refl A) a = a
  := ap (fun e => eqi e a) (path_coe_refl A).

Definition path_coe_inverse {A B : Type} (p : A = B)
  : coe p^ = (coe p)^-1.
Admitted.

Definition path_coe_inverse' {A B : Type} (p : A = B) (b : B)
  : coe p^ b = (coe p)^-1 b
  := ap (fun e => eqi e b) (path_coe_inverse p).

Definition path_coe_concat {A B C : Type} (p : A = B) (q : B = C)
  : coe (p @ q) = coe q oE coe p.
Admitted.

Definition path_coe_concat' {A B C : Type} (p : A = B) (q : B = C) (a : A)
  : coe (p @ q) a = coe q (coe p a)
  := ap (fun e => eqi e a) (path_coe_concat p q).


Definition pind {A : Type} {a1 a2 : A}
  (B : forall x, a1 = x -> Type) (p : a1 = a2)
  : B a1 1 <~> B a2 p
  := coe (pap B p).

Definition beta_pind {A : Type} {a : A} (B : forall x, a = x -> Type)
  : pind B (refl a) = ideqi.
Admitted.

Definition beta_pind' {A : Type} {a : A}
  (B : forall x, a = x -> Type) (b : B a 1)
  : pind B 1 b = b
  := ap (fun e => eqi e b) (beta_pind B).

Definition tr {A : Type} {a1 a2 : A} (B : A -> Type) (p : a1 = a2)
  : B a1 <~> B a2
  := pind (fun x _ => B x) p.

Definition beta_tr {A : Type} {a : A} (B : A -> Type)
  : tr B (refl a) = ideqi
  := beta_pind (fun x _ => B x).

Definition beta_tr' {A : Type} {a : A} (B : A -> Type) (b : B a)
  : tr B 1 b = b
  := beta_pind' (fun x _ => B x) b.

Definition papD  {A : Type} {a1 a2 : A} (B : forall x : A, a1 = x -> Type)
  (f : forall (x : A) (r : a1 = x), B x r) (p : a1 = a2)
  : pind B p (f a1 1) = f a2 p
  := (ap (fun i => pind B p (sect_eqi i (f a1 1))) (beta_pind B))^
     @ pap (fun x q => pind B p (inveqi (pind B q) (f x q))) p
     @ homot_isretr_eqi (pind B p) (f a2 p).
  (* The first path is a beta rule. *)

Definition apD  {A : Type} {a1 a2 : A} (B : A -> Type)
  (f : forall a, B a) (p : a1 = a2)
  : tr B p (f a1) = f a2
  := papD (fun x _ => B x) (fun x _ => f x) p.

Definition path_ap_inverse {A B : Type} {a1 a2 : A}
  (f : A -> B) (p : a1 = a2)
  : ap f p^ = (ap f p)^
  := (papD (fun x _ => f x = f a1) (fun x p => ap f p^) p)^
      @ papD (fun x _ => f x = f a1) (fun x p => (ap f p)^) p.

Definition path_ap_concat {A B : Type} {a1 a2 a3 : A} (f : A -> B)
  (p : a1 = a2) (q : a2 = a3)
  : ap f (p @ q) = ap f p @ ap f q.
Proof.
  refine ((papD (fun x _ => f a1 = f x) (fun x q => ap f (p @ q)) q)^ @ _).
  refine (_ @ papD (fun x _ => f a1 = f x) (fun x q => ap f p @ ap f q) q).
  refine (ap (pind (fun x _ => f a1 = f x) q) _).
  refine ((papD (fun x _ => f a1 = f x) (fun x p => ap f (p @ 1)) p)^ @ _).
  exact (papD (fun x _ => f a1 = f x) (fun x p => ap f p @ ap f 1) p).
Defined.


(***** Path of Sig **************************************************)


Definition Path_Sig {A : Type} {B : A -> Type} (u v : {a | B a})
  : Type
  := {p : u.1 = v.1 | tr B p u.2 = v.2}.

Axiom Path_is_Path_Sig :
  forall {A : Type} {B : A -> Type} (u v : {a | B a}),
  (u = v) === Path_Sig u v.

Definition psig {A : Type} {B : A -> Type} (u v : {a | B a})
  : Path_Sig u v -> u = v.
Admitted. (* The identity function. *)

Definition ppr1 :
  forall {A : Type} {B : A -> Type} {u v : {a | B a}},
  u = v -> u.1 = v.1.
Admitted. (* This is just first projection. *)

Definition ppr2 :
  forall {A : Type} {B : A -> Type} {u v : {a | B a}} (p : u = v),
  tr B (ppr1 p) u.2 = v.2.
Admitted. (* This is just second projection. *)

Definition refl_Path_Sig {A : Type} {B : A -> Type} (u : {a | B a})
  : Path_Sig u u
  := (1; beta_tr' B u.2).


(****** Sig continued ***********************************************)


Definition path_inv_tr_tr {A : Type} (B : A -> Type)
  {a1 a2 : A} (p : a1 = a2) (b : B a1) :
  tr B p^ (tr B p b) = b.
Proof.
  refine (ap (fun q => coe q _) (path_ap_inverse _ _) @ _).
  refine (path_coe_inverse' _ _ @ _).
  exact (homot_retr_inveqi _ _).
Defined.

Definition path_tr_inv_tr {A : Type} (B : A -> Type)
  {a1 a2 : A} (p : a1 = a2) (b : B a2) :
  tr B p (tr B p^ b) = b.
Proof.
(*
  assert (p = p^^) by admit.
  refine (ap (fun r => tr B r (tr B p^ b)) X @ _).
  apply path_inv_tr_tr.
*)
  refine (ap (fun q => _ (coe q _)) (path_ap_inverse _ _) @ _).
  refine (ap (fun x => _ x) (path_coe_inverse' _ _) @ _).
  exact (homot_sect_inveqi _ _).
Defined.

Lemma eqi_sig {A A' : Type} (B : A -> Type) (B' : A' -> Type)
  (eA : A <~> A') (eB : forall a a', eA a = a' -> B a <~> B' a')
  : {a | B a} <~> {a' | B' a'}.
Proof.
  simple refine (_; _).
  - intro u.
    pose (eB (sect_eqi eA (eA u.1)) (eA u.1)
             (homot_sect_inveqi eA (eA u.1))) as V.
    exact (eA u.1; V (tr B (homot_retr_inveqi _ _)^ u.2)).
  - simple refine (_; _).
    + simple refine (_; _).
      * intro v.
        exact (eA^-1 v.1; (eB _ v.1 (homot_sect_inveqi _ _))^-1 v.2).
      * intro u.
        apply psig.
        simple refine (_; _).
        -- exact (homot_retr_inveqi _ _).
        -- refine (ap (tr B _) (homot_retr_inveqi _ _) @ _).
           exact (path_tr_inv_tr B _ _).
    + cbn. simple refine (_; _).
      * intro v.
        refine (eA^-1 v.1; _).
        apply (tr B (homot_retr_inveqi eA (sect_eqi eA v.1))).
        simple refine ((eB _ _ _)^-1 _).
        -- exact (eA (eA^-1 v.1)).
        -- exact (homot_sect_inveqi _ _).
        -- exact (tr B' (homot_sect_inveqi _ _)^ v.2).
      * cbn.
        intro v.
        apply psig.
        simple refine (_; _).
        -- refine (homot_sect_inveqi _ _).
        -- refine (ap (fun x => _ (eB _ _ _ x)) (path_inv_tr_tr B _ _) @ _).
           refine (ap (tr B' _) (homot_sect_inveqi _ _) @ _).
           exact (path_tr_inv_tr B' _ _).
Defined.

Definition ap_sig {X : Type} {x1 x2 : X} (px : x1 = x2)
  (A : X -> Type) (B : forall x, A x -> Type)
  {a1 : A x1} {a2 : A x2} (pa : tr A px a1 = a2)
  {b1 : B x1 a1} {b2 : B x2 a2}
  (pb : tr (B x2) pa (pind (fun x p => B x (tr A p a1)) px (tr (B x1) (beta_tr' A _)^ b1)) = b2)
  : tr (fun x => {a | B x a}) px (a1; b1) = (a2; b2).
Proof.
  apply psig.
  unfold Path_Sig.
  cbn.
  simple refine (_; _).
  - (* The transport should reduce, so pa applies. *) admit.
  - cbn.
    (* The transport should reduce, so pb applies. *)
Admitted.

(* The general version should also work, but is problematic
   because of missing beta rules.
Definition ap_sig {X : Type} {x1 x2 : X} (px : x1 = x2)
  (A : forall x : X, x1 = x -> Type)
  {a1 : A x1 1} {a2 : A x2 px} (pa : pind A px a1 = a2)
  (B : forall x r, forall a : A x r, pind A r a1 = a -> Type)
  {b1 : B x1 1 a1 (beta_pind' A a1)} {b2 : B x2 px a2 pa}
  (pb : pind (B x2 px) pa
          (pind (fun x p => B x p (pind A p a1) 1) px
            (pind (B x1 1) (beta_pind' A _)^ b1)) = b2)
  : ...
*)

Definition inverse_Path_Sig {A : Type} {B : A -> Type} {u v : {a | B a}}
  (p : Path_Sig u v)
  : Path_Sig v u.
Proof.
  refine (p.1^; _).
  refine (ap (fun x => coe x v.2) (path_ap_inverse B p.1) @ _).
  refine (path_coe_inverse' (ap B p.1) v.2 @ _).
  refine (ap (fun x => (coe (ap B p.1))^-1 x) p.2^ @ _).
  exact (homot_retr_inveqi (coe (ap B p.1)) u.2).
Defined.

Definition compose_Path_Sig {A : Type} {B : A -> Type} {u v w : {a | B a}}
  (p : Path_Sig u v) (q : Path_Sig v w)
  : Path_Sig u w.
Proof.
  refine (p.1 @ q.1; _).
  refine (ap (fun x => coe x u.2) (path_ap_concat B p.1 q.1) @ _).
  refine (path_coe_concat' (ap B p.1) (ap B q.1) u.2 @ _).
  refine (ap (fun x => tr B q.1 x) p.2 @ _).
  exact q.2.
Defined.


(***** Function *****************************************************)


Definition Path_Fun {A : Type} {B : A -> Type} (f g : forall a, B a)
  : Type
  := forall (a1 : A) (a2 : A) (pa : a1 = a2),
     tr B pa (f a1) = g a2.

Axiom Path_is_Path_Fun :
  forall {A : Type} {B : A -> Type} (f g : forall a, B a),
  (f = g) === Path_Fun f g.

Definition pfun {A : Type} {B : A -> Type} (f g : forall a, B a)
  : Path_Fun f g -> f = g.
Admitted. (* The identity function. *)

Definition funext {A : Type} {B : A -> Type}
  (f g : forall a, B a) (h : f ~ g)
  : f = g.
Proof.
  apply pfun.
  intros a1 a2 p.
  exact (apD B f p @ h a2).
Defined.

Definition app :
  forall {A : Type} {B : A -> Type} {f g : forall a, B a},
  f = g ->
  forall (a1 : A) (a2 : A) (pa : a1 = a2),
  tr B pa (f a1) = g a2.
Admitted. (* They are judgmentally equal. *)

Lemma eqi_fun {A A' : Type} (B : A -> Type) (B' : A' -> Type)
  (eA : A <~> A') (eB : forall a a', eA a = a' -> B a <~> B' a')
  : (forall a, B a) <~> (forall a', B' a').
Proof.
  simple refine (_; _).
  - intros f a'.
    exact (eB (eA^-1 a') a' (homot_sect_inveqi eA a') (f (eA^-1 a'))).
  - cbn.
    simple refine (_; _).
    + simple refine (_; _).
      * intros g a.
        pose ((eB (eA^-1 (eA a)) (eA a)
                (homot_sect_inveqi eA (eA a)))^-1 (g (eA a))) as G.
        exact (tr B (homot_retr_inveqi eA a) G).
      * intro f.
        apply funext.
        intro a.
        refine (ap (fun x => tr B (homot_retr_inveqi eA a) x)
                   (homot_retr_inveqi (eB _ _ _) _) @ _).
        exact (apD B f (homot_retr_inveqi eA a)).
    + simple refine (_; _).
      * intros g a. exact ((eB a (eA a) 1)^-1 (g (eA a))).
      * intro g.
        apply funext.
        intro a'.
        refine (
          (papD (fun a' _ => B' a')
            (fun x r =>
              eB (sect_eqi eA a') x r
                ((eB (sect_eqi eA a') (eA (sect_eqi eA a')) 1)^-1
                    (g (eA (sect_eqi eA a'))))) _)^ @ _).
        refine (
          ap (fun x => pind (fun a' _ => B' a') (homot_sect_inveqi eA a') x)
             (homot_sect_inveqi _ _) @ _).
        exact (papD (fun a' _ => B' a') (fun a' _ => g a') _).
Defined.
