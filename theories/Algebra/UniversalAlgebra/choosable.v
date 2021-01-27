Require Import
  HoTT.Basics
  HoTT.Types
  HoTT.Truncations
  HoTT.HIT.quotient
  HoTT.Algebra.UniversalAlgebra.equiv_class_quotient.

(* TODO connect with IsProjective, IsProjective'. *)

Class IsChoosable (X : Type) :=
  is_choosable :
    forall (Y : X -> Type), (forall x, IsHSet (Y x)) ->
    forall (P : forall x : X, Y x -> Type),
    (forall x (y : Y x), IsHProp (P x y)) ->
    (forall x, hexists (fun a : Y x => P x a)) ->
    hexists (fun g : (forall x, Y x) => forall x, P x (g x)).

Definition IsQuotientChoosable (X : Type) :=
  forall (Y : X -> Type), (forall x, IsHSet (Y x)) ->
  forall (R : forall x, Relation (Y x))
         (pR : forall x, is_mere_relation (Y x) (R x)),
         (forall x, Reflexive (R x)) ->
         (forall x, Symmetric (R x)) ->
         (forall x, Transitive (R x)) ->
  forall (f : forall x : X, quotient (R x)),
  hexists (fun g : (forall x : X, Y x) =>
                   forall x, class_of (R x) (g x) = f x).

Module quotient_choosable_to_choosable_module.
Section quotient_choosable_to_choosable_section.
  Context `{Univalence}
    {X : Type} {A : X -> Type} `{!forall x, IsHSet (A x)}
    (P : forall x, A x -> Type) `{!forall x (a : A x), IsHProp (P x a)}.

  Definition R (x : X) (a : A x) (b : A x) : Type
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

  Lemma r_merely (i : forall x, hexists (P x))
    : forall x, hexists (fun a : A x => forall b : A x, R x a b <~> P x b).
  Proof.
    intro x.
    specialize (i x).
    strip_truncations.
    apply tr.
    destruct i as [a h].
    exists a.
    intro b.
    apply equiv_iff_hprop.
    - intro f. exact (f h).
    - intro p. by apply equiv_iff_hprop.
  Qed.

  Definition induced_map (i : forall x, hexists (P x)) (x : X)
    : equiv_class_quotient (R x)
    := (fun a => BuildhProp (P x a); r_merely i x).

End quotient_choosable_to_choosable_section.
End quotient_choosable_to_choosable_module.

Module quotient_choosable_to_choosable.
Section quotient_choosable_to_choosable_section.
  Context `{Univalence} (X : Type) (qch : IsQuotientChoosable X).

  Import quotient_choosable_to_choosable_module.

  Lemma choosable : IsChoosable X.
  Proof.
    intros Y sY P pP i.
    set (m' :=
      fun x =>
        (equiv_quotient_to_equiv_class_quotient _)^-1 (induced_map P i x)).
    pose proof (qch Y _ (R P) _ _ _ _ m') as c.
    strip_truncations.
    apply tr.
    destruct c as [g p].
    exists g.
    intro x.
    set (q := ap (equiv_quotient_to_equiv_class_quotient _) (p x)
              @ eisretr (equiv_quotient_to_equiv_class_quotient _) _).
    set (q' := ap (fun f => trunctype_type (f (g x))) q..1).
    cbn in q'.
    by induction q'.
  Qed.
End quotient_choosable_to_choosable_section.
End quotient_choosable_to_choosable.

Lemma quotient_choosable_to_choosable `{Univalence} (X : Type)
  : IsQuotientChoosable X -> IsChoosable X.
Proof.
  apply quotient_choosable_to_choosable.choosable.
Qed.

Lemma choosable_to_quotient_choosable (X : Type)
  : IsChoosable X -> IsQuotientChoosable X.
Proof.
  intros ch Y sY R pR Rl Sm Tn f.
  set (P := fun x (a : Y x) => class_of (R x) a = f x).
  apply (ch Y _ P _).
  intro x.
  refine (quotient_ind_prop _
            (fun c => hexists (fun a => class_of (R x) a = c)) _ (f x)).
  intro y.
  apply tr.
  by exists y.
Qed.
