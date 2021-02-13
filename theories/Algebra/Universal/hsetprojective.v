Require Import
  HoTT.Basics
  HoTT.Types
  HoTT.HSet
  HoTT.Truncations
  HoTT.HIT.quotient.

Class IsHSetProjective (A : Type) :=
  is_hsetprojective :
    forall (B : A -> Type), (forall x, IsHSet (B x)) ->
    (forall x, merely (B x)) -> merely (forall x, B x).

Global Instance hsetprojectivesigma `{Funext} {A : Type} {B : A -> Type}
  (chA : IsHSetProjective A) (chB : forall a : A, IsHSetProjective (B a))
  : IsHSetProjective {a : A | B a}.
Proof.
  intros C sC f.
  set (f' := fun a => chB a (fun b => C (a; b)) _ (fun b => f (a; b))).
  specialize (chA (fun a => forall b, C (a; b)) _ f').
  strip_truncations.
  apply tr.
  intros [a b].
  apply chA.
Qed.

Definition IsHSetChoosable (A : Type) :=
    forall (B : A -> Type), (forall x, IsHSet (B x)) ->
    forall (P : forall x : A, B x -> Type),
    (forall x (y : B x), IsHProp (P x y)) ->
    (forall x, hexists (fun a : B x => P x a)) ->
    hexists (fun g : (forall x, B x) => forall x, P x (g x)).

Lemma hsetchoosable_to_hsetprojective (A : Type)
  : IsHSetChoosable A -> IsHSetProjective A.
Proof.
  intros ch B sB f.
  specialize (ch B _ (fun _ _ => Unit) _
                (fun a => Trunc_rec (fun b => tr (b; tt)) (f a))).
  strip_truncations.
  apply tr.
  apply ch.
Qed.

Lemma hsetprojectiveto_hsetchoosable (A : Type)
  : IsHSetProjective A -> IsHSetChoosable A.
Proof.
  intros pr B sB P isP f.
  specialize (pr (fun a => {b : B a | P a b}) _ f).
  strip_truncations.
  apply tr.
  exists (fun a => (pr a).1).
  apply pr.
Qed.

Global Instance isequiv_hsetprojective_hsetchoosable `{Funext} (A : Type)
  : IsEquiv (hsetprojectiveto_hsetchoosable A).
Proof.
  srapply isequiv_adjointify.
  - apply hsetchoosable_to_hsetprojective.
  - intro x. apply @path_ishprop. apply trunc_forall.
  - intro x. apply @path_ishprop. apply trunc_forall.
Qed.

Definition equiv_hsetprojective_hsetchoosable `{Univalence} (A : Type)
  : IsHSetProjective A <~> IsHSetChoosable A
  := Build_Equiv _ _ (hsetprojectiveto_hsetchoosable A) _.

Definition IsQuotientChoosable (A : Type) :=
  forall (B : A -> Type), (forall x, IsHSet (B x)) ->
  forall (R : forall x, Relation (B x))
         (pR : forall x, is_mere_relation (B x) (R x)),
         (forall x, Reflexive (R x)) ->
         (forall x, Symmetric (R x)) ->
         (forall x, Transitive (R x)) ->
  forall (f : forall x : A, quotient (R x)),
  hexists (fun g : (forall x : A, B x) =>
                   forall x, class_of (R x) (g x) = f x).

Module quotient_choosable_to_hsetchoosable_module.
Section quotient_choosable_to_hsetchoosable_section.
  Context `{Univalence}
    {A : Type} {B : A -> Type} `{!forall x, IsHSet (B x)}
    (P : forall x, B x -> Type) `{!forall x (a : B x), IsHProp (P x a)}.

  Definition R (x : A) (a : B x) (b : B x) : Type
    := P x a <~> P x b.

  Global Instance reflexive_r : forall x, Reflexive (R x).
  Proof.
    intros x a. apply equiv_idmap.
  Qed.

  Global Instance symmetric_r : forall x, Symmetric (R x).
  Proof.
    intros x a b p. apply (equiv_inverse p).
  Qed.

  Global Instance transitive_r : forall x, Transitive (R x).
  Proof.
    intros x a b c p q. apply (equiv_compose q p).
  Qed.

  Lemma hprop_choose_cod (x : A)
    : IsHProp {a : quotient (R x) | forall b, in_class (R x) a b <~> P x b}.
  Proof.
    apply ishprop_sigma_disjoint.
    refine (quotient_ind_prop _ _ _).
    intro a.
    refine (quotient_ind_prop _ _ _).
    intros b f g.
    apply related_classes_eq.
    apply (f b)^-1.
    apply g.
    apply reflexive_r.
  Qed.

  Definition prechoose (i : forall x, hexists (P x)) (x : A)
    : {a : quotient (R x) | forall b : B x, in_class (R x) a b <~> P x b}.
  Proof.
    pose proof (hprop_choose_cod x).
    specialize (i x).
    strip_truncations.
    destruct i as [a h].
    exists (class_of _ a).
    intro b.
    apply equiv_iff_hprop.
    - intro f. exact (f h).
    - intro p. by apply equiv_iff_hprop.
  Defined.

  Definition choose (i : forall x, hexists (P x)) (x : A)
    : quotient (R x)
    := (prechoose i x).1.

End quotient_choosable_to_hsetchoosable_section.
End quotient_choosable_to_hsetchoosable_module.

Module quotient_choosable_to_hsetchoosable.
Section quotient_choosable_to_hsetchoosable_section.
  Context `{Univalence} (A : Type) (qch : IsQuotientChoosable A).

  Import quotient_choosable_to_hsetchoosable_module.

  Lemma choosable : IsHSetChoosable A.
  Proof.
    intros B sB P pP i.
    pose proof (qch B _ (R P) _ _ _ _ (choose P i)) as c.
    strip_truncations.
    apply tr.
    destruct c as [g p].
    exists g.
    intro x.
    specialize (p x).
    generalize dependent p.
    unfold choose. (* to avoid Coq retyping anomaly. *)
    refine (Trunc_ind (fun a => _ = (Trunc_ind _ _ a).1 -> P x (g x)) _ (i x)).
    intros [a h] p.
    apply classes_eq_related in p; try exact _.
    by apply p^-1.
  Defined.
End quotient_choosable_to_hsetchoosable_section.
End quotient_choosable_to_hsetchoosable.

Lemma quotient_choosable_to_hsetchoosable `{Univalence} (A : Type)
  : IsQuotientChoosable A -> IsHSetChoosable A.
Proof.
  apply quotient_choosable_to_hsetchoosable.choosable.
Defined.

Lemma hsetchoosable_to_quotient_choosable (A : Type)
  : IsHSetChoosable A -> IsQuotientChoosable A.
Proof.
  intros ch B sY R pR Rl Sm Tn f.
  set (P := fun x (a : B x) => class_of (R x) a = f x).
  apply (ch B _ P _).
  intro x.
  refine (quotient_ind_prop _
            (fun c => hexists (fun a => class_of (R x) a = c)) _ (f x)).
  intro y.
  apply tr.
  by exists y.
Defined.

Global Instance isequiv_hsetchoosable_to_quotient_choosable `{Univalence} (A : Type)
  : IsEquiv (hsetchoosable_to_quotient_choosable A).
Proof.
  srapply isequiv_adjointify.
  - apply quotient_choosable_to_hsetchoosable.
  - intro x. apply path_ishprop.
  - intro x. apply @path_ishprop. apply trunc_forall.
Qed.

Definition equiv_hsetchoosable_quotient_choosable `{Univalence} (A : Type)
  : IsHSetChoosable A <~> IsQuotientChoosable A
  := Build_Equiv _ _ (hsetchoosable_to_quotient_choosable A) _.

Definition equiv_hsetprojective_quotient_choosable `{Univalence} (A : Type)
  : IsHSetProjective A <~> IsQuotientChoosable A
  := equiv_compose
      (equiv_hsetchoosable_quotient_choosable A)
      (equiv_hsetprojective_hsetchoosable A).

Lemma pointwise_related_classes_eq `{Univalence} {I : Type} {X : I -> Type}
  (R : forall i, Relation (X i)) `{!forall i, is_mere_relation (X i) (R i)}
  (f g : forall i, X i) (r : forall i, R i (f i) (g i))
  : (fun i => class_of (R i) (f i)) = (fun i => class_of (R i) (g i)).
Proof.
  funext s.
  by apply related_classes_eq.
Defined.

Definition hprop_cod_choice_quotient_ind_pre `{Univalence}
  {I : Type} {X : I -> Type}
  (R : forall i, Relation (X i))
  `{!forall i, is_mere_relation (X i) (R i)}
  `{Rl : forall i, Reflexive (R i)}
  `{Sm : forall i, Symmetric (R i)}
  `{Tn : forall i, Transitive (R i)}
  (P : (forall i, quotient (R i)) -> Type) `{!forall f, IsHSet (P f)}
  (a : forall (f : forall i, X i), P (fun i => class_of (R i) (f i)))
  (f : forall i, quotient (R i))
  : IsHProp
      {b : P f
       | merely (exists (f' : forall i, X i)
                        (q : f = fun i => class_of (R i) (f' i)),
                 forall (g : forall i, X i) (r : forall i, R i (f' i) (g i)),
                 pointwise_related_classes_eq R f' g r # q # b = a g)}.
Proof.
  apply ishprop_sigma_disjoint.
  intros x y h1 h2.
  strip_truncations.
  destruct h1 as [f1 [q1 p1]].
  destruct h2 as [f2 [q2 p2]].
  specialize (p1 f1 (fun i => Rl i (f1 i))).
  set (rR := fun i =>
    classes_eq_related (R i) _ _ (ap (fun h => h i) q2^ @ ap (fun h => h i) q1)).
  specialize (p2 f1 rR).
  do 2 apply moveL_transport_V in p1.
  do 2 apply moveL_transport_V in p2.
  refine (p1 @ _ @ p2^).
  apply moveR_transport_p.
  rewrite inv_V.
  rewrite <- transport_pp.
  apply moveR_transport_p.
  rewrite inv_V.
  rewrite <- transport_pp.
  rewrite <- transport_pp.
  set (pa := (pointwise_related_classes_eq R f2 f1 rR)^
             @ ((q2^ @ q1)
             @ pointwise_related_classes_eq R f1 f1 _)).
  by induction (hset_path2 idpath pa).
Qed.

Lemma choice_fun_quotient_ind_pre `{Univalence}
  {I : Type} `{!IsHSetProjective I}
  {X : I -> Type} `{!forall i, IsHSet (X i)}
  (R : forall i, Relation (X i))
  `{!forall i, is_mere_relation (X i) (R i)}
  `{!forall i, Reflexive (R i)}
  `{!forall i, Symmetric (R i)}
  `{!forall i, Transitive (R i)}
  (P : (forall i, quotient (R i)) -> Type) `{!forall f, IsHSet (P f)}
  (a : forall (f : forall i, X i), P (fun i => class_of (R i) (f i)))
  (E : forall (f g : forall i, X i) (r : forall i, R i (f i) (g i)),
       pointwise_related_classes_eq R f g r # a f = a g)
  (f : forall i, quotient (R i))
  : {b : P f |
      merely (exists (f' : forall i, X i)
                     (q : f = fun i => class_of (R i) (f' i)),
              forall (g : forall i, X i) (r : forall i, R i (f' i) (g i)),
              pointwise_related_classes_eq R f' g r # q # b = a g)}.
Proof.
  pose proof (hprop_cod_choice_quotient_ind_pre R P a f).
  pose proof (equiv_hsetprojective_quotient_choosable I _ X _ R _ _ _ _ f) as g.
  strip_truncations.
  destruct g as [g p].
  apply path_forall in p.
  refine (transport (fun f => {_ : P f | merely {_ | {_ : f = _ | _}}}) p _).
  exists (a g).
  apply tr.
  exists g.
  exists idpath.
  apply E.
Defined.

Lemma choice_fun_quotient_ind `{Univalence} {I : Type} `{!IsHSetProjective I}
  {X : I -> Type} `{!forall i, IsHSet (X i)}
  (R : forall i, Relation (X i))
  `{!forall i, is_mere_relation (X i) (R i)}
  `{!forall i, Reflexive (R i)}
  `{!forall i, Symmetric (R i)}
  `{!forall i, Transitive (R i)}
  (P : (forall i, quotient (R i)) -> Type) `{!forall f, IsHSet (P f)}
  (a : forall (f : forall i, X i), P (fun i => class_of (R i) (f i)))
  (E : forall (f g : forall i, X i) (r : forall i, R i (f i) (g i)),
       pointwise_related_classes_eq R f g r # a f = a g)
  (f : forall i, quotient (R i))
  : P f.
Proof.
  exact (choice_fun_quotient_ind_pre R P a E f).1.
Defined.

Lemma choice_fun_quotient_ind_prop `{Univalence}
  {I : Type} `{!IsHSetProjective I}
  {X : I -> Type} `{!forall i, IsHSet (X i)}
  (R : forall i, Relation (X i))
  `{!forall i, is_mere_relation (X i) (R i)}
  `{!forall i, Reflexive (R i)}
  `{!forall i, Symmetric (R i)}
  `{!forall i, Transitive (R i)}
  (P : (forall i, quotient (R i)) -> Type) `{!forall f, IsHProp (P f)}
  (a : forall (f : forall i, X i), P (fun i => class_of (R i) (f i)))
  (f : forall i, quotient (R i))
  : P f.
Proof.
  refine (choice_fun_quotient_ind R P a _ f). intros. apply path_ishprop.
Defined.

Definition choice_fun_quotient_rec
  `{Univalence} {I : Type} `{!IsHSetProjective I}
  {X : I -> Type} `{!forall i, IsHSet (X i)}
  (R : forall i, Relation (X i))
  `{!forall i, is_mere_relation (X i) (R i)}
  `{!forall i, Reflexive (R i)}
  `{!forall i, Symmetric (R i)}
  `{!forall i, Transitive (R i)}
  {B : Type} `{!IsHSet B}
  (a : (forall i, X i) -> B)
  (E : forall (f g : forall i, X i),
       (forall i, R i (f i) (g i)) -> a f = a g)
  (f : forall i, quotient (R i))
  : B
  := choice_fun_quotient_ind R (fun _ => B) a
      (fun f g r => transport_const _ _ @ E f g r) f.

(* TODO Move this to the right place *)
Lemma path_pr1_transport {A : Type} {B : A -> Type} (C : forall a, B a -> Type)
  {x y : A} (p : x = y) (u : {b : B x | C x b})
  : (transport (fun a => {b : B a | C a b}) p u).1 = transport B p u.1.
Proof.
  by path_induction.
Qed.

Lemma choice_fun_quotient_ind_compute `{Univalence}
  {I : Type} `{!IsHSetProjective I} {X : I -> Type} `{!forall i, IsHSet (X i)}
  (R : forall i, Relation (X i))
  `{!forall i, is_mere_relation (X i) (R i)}
  `{!forall i, Reflexive (R i)}
  `{!forall i, Symmetric (R i)}
  `{!forall i, Transitive (R i)}
  (P : (forall i, quotient (R i)) -> Type) `{!forall f, IsHSet (P f)}
  (a : forall (f : forall i, X i), P (fun i => class_of (R i) (f i)))
  (E : forall (f g : forall i, X i) (r : forall i, R i (f i) (g i)),
       pointwise_related_classes_eq R f g r # a f = a g)
  (f : forall i, X i)
  : choice_fun_quotient_ind R P a E (fun i => class_of (R i) (f i))
    = a f.
Proof.
  refine (Trunc_ind (fun a => (_ a).1 = _) _ _).
  cbn.
  intros [g p].
  rewrite path_pr1_transport.
  cbn.
  set (p' := fun x => classes_eq_related (R x) _ _ (p x)).
  assert (p = (fun s : I => related_classes_eq (R s) (p' s))) as pE.
  - funext x. apply hset_path2.
  - rewrite pE. apply E.
Qed.

Lemma choice_fun_quotient_rec_compute
  `{Univalence} {I : Type} `{!IsHSetProjective I}
  {X : I -> Type} `{!forall i, IsHSet (X i)}
  (R : forall i, Relation (X i))
  `{!forall i, is_mere_relation (X i) (R i)}
  `{!forall i, Reflexive (R i)}
  `{!forall i, Symmetric (R i)}
  `{!forall i, Transitive (R i)}
  {B : Type} `{!IsHSet B}
  (a : (forall i, X i) -> B)
  (E : forall (f g : forall i, X i),
       (forall i, R i (f i) (g i)) -> a f = a g)
  (f : forall i, X i)
  : choice_fun_quotient_rec R a E (fun i => class_of (R i) (f i)) = a f.
Proof.
  apply (choice_fun_quotient_ind_compute R (fun _ => B)).
Qed.

Lemma apD_path_helper `{Funext} {A : Type} {B : A -> Type} {x y : A} (p : x = y)
  (f g : forall a, B a) (h : f == g)
  : apD f p = ap (transport B p) (h x) @ apD g p @ (h y)^.
Proof.
  induction p.
  rewrite ap_idmap.
  rewrite concat_p1.
  by rewrite concat_pV.
Qed.