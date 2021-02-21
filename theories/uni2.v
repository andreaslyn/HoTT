
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

Axiom BETA : forall {A B}, A -> B.

(***** Function type ************************************************)


Notation id := (fun x => x).

Notation "g 'o' f" :=
  (fun x => g (f x)) (at level 40, left associativity).


(***** Sig type *****************************************************)


Declare Scope Sig_scope.
Open Scope Sig_scope.

Variant Sig (A : Type) (B : A -> Type) : Type
  := mkSig : forall a, B a -> Sig A B.

Arguments Sig {A}.
Arguments mkSig {A B}.

Scheme Sig_ind := Elimination for Sig Sort Type.
Scheme Sig_rect := Elimination for Sig Sort Type.
Scheme Sig_rec := Elimination for Sig Sort Type.

Arguments Sig_ind {A B}.
Arguments Sig_rect {A B}.
Arguments Sig_rec {A B}.

Notation "{ x  |  P }" := (Sig (fun x => P)) : type_scope.
Notation "{ x : A  |  P }" := (Sig (fun x : A => P)) : type_scope.

Notation "( a ; b )" := (mkSig a b) : Sig_scope.

Definition pr1 {A : Type} {B : A -> Type} : {a | B a} -> A
  := Sig_ind (fun _ => A) (fun a _ => a).

Notation "u .1" := (pr1 u) (at level 3, format "u '.1'").

Definition pr2 {A : Type} {B : A -> Type} : forall u : {a | B a}, B u.1
  := Sig_ind (fun u => B u.1) (fun _ b => b).

Notation "u .2" := (pr2 u) (at level 3, format "u '.2'").

(***** Path type former *********************************************)

Declare Scope Path_scope.
Open Scope Path_scope.

Axiom Path : forall {A : Type}, A -> A -> Type.

Notation "x = y" := (Path x y) : type_scope.

Notation "f == g" :=
  (forall x, f x = g x) (at level 70, no associativity) : type_scope.

Axiom PathD :
  forall {A : Type} (B : A -> Type) {a1 a2 : A},
  a1 = a2 -> B a1 -> B a2 -> Type.

Axiom beta_nondep :
  forall {A B : Type} {a1 a2 : A} (p : a1 = a2) (b1 b2 : B),
  PathD (fun _ => B) p b1 b2 === (b1 = b2).

(* The beta_nondep also holds for sigma paths, it can eliminate
   all paths that are not dependent. *)


(***** Preliminary path introduction and elimination rules **********)


Axiom path_sig :
  forall {A : Type} {B : A -> Type} (u1 u2 : {a | B a})
         (p : u1.1 = u2.1) (q : PathD B p u1.2 u2.2),
  u1 = u2.

Axiom ppr1 :
  forall {A : Type} {B : A -> Type} (u1 u2 : {a | B a}),
  u1 = u2 -> u1.1 = u2.1.

Axiom beta_ppr1 :
  forall {A : Type} {B : A -> Type} (u1 u2 : {a | B a})
         (p : u1.1 = u2.1) (q : PathD B p u1.2 u2.2),
  ppr1 u1 u2 (path_sig u1 u2 p q) === p.

Axiom ppr2 :
  forall {A : Type} {B : A -> Type} (u1 u2 : {a | B a})
         (p : u1 = u2),
  PathD B (ppr1 u1 u2 p) u1.2 u2.2.

Axiom beta_ppr2 :
  forall {A : Type} {B : A -> Type} (u1 u2 : {a | B a})
         (p : u1.1 = u2.1) (q : PathD B p u1.2 u2.2),
  ppr2 u1 u2 (path_sig u1 u2 p q) === BETA q.

Axiom pathD_sig :
  forall {X : Type} {A : X -> Type} {B : forall x, A x -> Type}
         {x1 x2 : X} {px : x1 = x2}
         (u1 : {a1 : A x1 | B x1 a1}) (u2 : {a2 : A x2 | B x2 a2})
         (p : PathD A px u1.1 u2.1)
         (q : PathD (fun d => B d.1 d.2)
                (path_sig (x1; u1.1) (x2; u2.1) px p) u1.2 u2.2),
  PathD (fun x => {a : A x | B x a}) px u1 u2.

Axiom ppr1D :
  forall {X : Type} {A : X -> Type} {B : forall x, A x -> Type}
         {x1 x2 : X} {px : x1 = x2}
         (u1 : {a1 : A x1 | B x1 a1}) (u2 : {a2 : A x2 | B x2 a2}),
  PathD (fun x => {a : A x | B x a}) px u1 u2 ->
  PathD A px u1.1 u2.1.

Axiom beta_ppr1D :
  forall {X : Type} {A : X -> Type} {B : forall x, A x -> Type}
         {x1 x2 : X} {px : x1 = x2}
         (u1 : {a1 : A x1 | B x1 a1}) (u2 : {a2 : A x2 | B x2 a2})
         (p : PathD A px u1.1 u2.1)
         (q : PathD (fun d => B d.1 d.2)
                (path_sig (x1; u1.1) (x2; u2.1) px p) u1.2 u2.2),
  ppr1D u1 u2 (pathD_sig u1 u2 p q) === p.

Axiom ppr2D :
  forall {X : Type} {A : X -> Type} {B : forall x, A x -> Type}
         {x1 x2 : X} {px : x1 = x2}
         (u1 : {a1 : A x1 | B x1 a1}) (u2 : {a2 : A x2 | B x2 a2})
         (p : PathD (fun x => {a : A x | B x a}) px u1 u2),
  PathD (fun d => B d.1 d.2)
    (path_sig (x1; u1.1) (x2; u2.1) px (ppr1D u1 u2 p)) u1.2 u2.2.

Axiom beta_ppr2D :
  forall {X : Type} {A : X -> Type} {B : forall x, A x -> Type}
         {x1 x2 : X} {px : x1 = x2}
         (u1 : {a1 : A x1 | B x1 a1}) (u2 : {a2 : A x2 | B x2 a2})
         (p : PathD A px u1.1 u2.1)
         (q : PathD (fun d => B d.1 d.2)
                (path_sig (x1; u1.1) (x2; u2.1) px p) u1.2 u2.2),
  ppr2D u1 u2 (pathD_sig u1 u2 p q) === BETA q.

Axiom path_fun :
  forall {A : Type} {B : A -> Type} (f1 f2 : forall a, B a)
         (h : forall (a1 : A) (a2 : A) (pa : a1 = a2),
              PathD B pa (f1 a1) (f2 a2)),
  f1 = f2.

Axiom app :
  forall {A : Type} {B : A -> Type} (f1 f2 : forall a, B a),
  f1 = f2 ->
  forall (a1 : A) (a2 : A) (pa : a1 = a2),
  PathD B pa (f1 a1) (f2 a2).

Axiom beta_app :
  forall {A : Type} {B : A -> Type} (f1 f2 : forall a, B a)
         (h : forall (a1 : A) (a2 : A) (pa : a1 = a2),
              PathD B pa (f1 a1) (f2 a2)),
  app f1 f2 (path_fun f1 f2 h) === h.

Axiom pathD_fun :
  forall {X : Type} {A : X -> Type} {B : forall x, A x -> Type}
         {x1 x2 : X} {px : x1 = x2}
         (f1 : forall (a1 : A x1), B x1 a1) (f2 : forall (a2 : A x2), B x2 a2)
         (h : forall (a1 : A x1) (a2 : A x2) (pa : PathD A px a1 a2),
              PathD (fun d => B d.1 d.2)
                (path_sig (x1; a1) (x2; a2) px pa) (f1 a1) (f2 a2)),
  PathD (fun x => forall (a : A x), B x a) px f1 f2.

Axiom appD :
  forall {X : Type} {A : X -> Type} {B : forall x, A x -> Type}
         {x1 x2 : X} {px : x1 = x2}
         (f1 : forall (a1 : A x1), B x1 a1) (f2 : forall (a2 : A x2), B x2 a2),
  PathD (fun x => forall (a : A x), B x a) px f1 f2 ->
  forall (a1 : A x1) (a2 : A x2) (pa : PathD A px a1 a2),
  PathD (fun d => B d.1 d.2) (path_sig (x1; a1) (x2; a2) px pa) (f1 a1) (f2 a2).

Axiom beta_appD :
  forall {X : Type} {A : X -> Type} {B : forall x, A x -> Type}
         {x1 x2 : X} {px : x1 = x2}
         (f1 : forall (a1 : A x1), B x1 a1) (f2 : forall (a2 : A x2), B x2 a2)
         (h : forall (a1 : A x1) (a2 : A x2) (pa : PathD A px a1 a2),
              PathD (fun d => B d.1 d.2)
                (path_sig (x1; a1) (x2; a2) px pa) (f1 a1) (f2 a2)),
  appD f1 f2 (pathD_fun f1 f2 h) === h.


(***** Path groupoid structure **************************************)


Axiom refl : forall {A : Type} (a : A), a = a.

Arguments refl {A a} , {A} a.

Axiom reflD :
  forall {A : Type} (B : A -> Type) {a : A} (b : B a), PathD B refl b b.


Axiom inverse : forall {A : Type} {a1 a2 : A}, a1 = a2 -> a2 = a1.

Axiom inverseD :
  forall {A : Type} (B : A -> Type) {a1 a2 : A} {pa : a1 = a2}
         {b1 : B a1} {b2 : B a2},
  PathD B pa b1 b2 -> PathD B (inverse pa) b2 b1.


Axiom concat :
  forall {A : Type} {a1 a2 a3 : A},
  a1 = a2 -> a2 = a3 -> a1 = a3.

Axiom concatD :
  forall {A : Type} (B : A -> Type) {a1 a2 a3 : A}
         {pa1 : a1 = a2} {pa2 : a2 = a3}
         {b1 : B a1} {b2 : B a2} {b3 : B a3},
  PathD B pa1 b1 b2 -> PathD B pa2 b2 b3 ->
  PathD B (concat pa1 pa2) b1 b3.


Axiom law_assoc :
  forall {A : Type} {a1 a2 a3 a4 : A}
         (pa1 : a1 = a2) (pa2 : a2 = a3) (pa3 : a3 = a4),
  concat (concat pa1 pa2) pa3 = concat pa1 (concat pa2 pa3).

Axiom lawD_assoc :
  forall {A : Type} (B : A -> Type) {a1 a2 a3 a4 : A}
         {pa1 : a1 = a2} {pa2 : a2 = a3} {pa3 : a3 = a4}
         {b1 : B a1} {b2 : B a2} {b3 : B a3} {b4 : B a4}
         (pb1 : PathD B pa1 b1 b2) {pb2 : PathD B pa2 b2 b3}
         {pb3 : PathD B pa3 b3 b4},
  PathD (fun pa => PathD B pa b1 b4) (law_assoc pa1 pa2 pa3)
    (concatD B (concatD B pb1 pb2) pb3) (concatD B pb1 (concatD B pb2 pb3)).


Axiom law_inverse_left :
  forall {A : Type} {a1 a2 : A} (pa : a1 = a2),
  concat (inverse pa) pa = refl.

Axiom lawD_inverse_left :
  forall {A : Type} (B : A -> Type) {a1 a2 : A} {pa : a1 = a2}
         {b1 : B a1} {b2 : B a2} (pb : PathD B pa b1 b2),
  PathD (fun pa => PathD B pa b2 b2) (law_inverse_left pa)
    (concatD B (inverseD B pb) pb) (reflD B b2).


Axiom law_refl_left :
  forall {A : Type} {a1 a2 : A} (pa : a1 = a2),
  concat (refl a1) pa = pa.

Axiom lawD_refl_left :
  forall {A : Type} (B : A -> Type) {a1 a2 : A} {pa : a1 = a2}
         {b1 : B a1} {b2 : B a2} (pb : PathD B pa b1 b2),
  PathD (fun pa => PathD B pa b1 b2) (law_refl_left pa)
    (concatD B (reflD B b1) pb) pb.


Notation "p @ q" := (concat p q) (at level 20) : Path_scope.

Notation "p ^" := (inverse p) (at level 3, format "p '^'") : Path_scope.

Definition ap {A B : Type} {a1 a2 : A} (f : A -> B) (p : a1 = a2)
  : f a1 = f a2
  := BETA (app f f refl a1 a2 p).


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
  ((id; fun x => refl); (id; fun x => refl)).

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


(***** Type path intro/elim rules ***********************************)


Axiom path_type : forall {A B : Type}, A <~> B -> A = B.

(* There is no pathD_type, since paths of types are nondependent. *)

Axiom coe : forall {A B : Type}, A = B -> A <~> B.

Axiom beta_coq :
  forall {A B : Type} (e : A <~> B), coe (path_type e) = e.


(***** Higher path intro/elim rules *********************************)


Axiom path_sig_2 :
  forall {A A' : Type} {B : A -> Type} {B' : A' -> Type}
         (u1 : {a | B a}) (u1' : {a' | B' a'})
         (u2 : {a | B a}) (u2' : {a' | B' a'})
         {p : u1.1 = u2.1} {p' : u1'.1 = u2'.1}
         (pp : PathD (equivof (u1.1 = u2.1) (u1'.1 = u2'.1)) p = p')
         (q : PathD B p u1.2 u2.2)
         (q' : PathD B' p' u1'.2 u2'.2),
  path_sig u1 u2 p q = path_sig u1' u2' p' q'.
