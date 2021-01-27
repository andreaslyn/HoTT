Require Import
  HoTT.Basics
  HoTT.Types
  HoTT.Truncations
  HoTT.TruncType
  HoTT.HSet
  HoTT.HIT.quotient.

Section equiv_class_quotient.
  Context `{Univalence}
    {A : Type} (R : Relation A) `{!is_mere_relation A R}
    `{!Reflexive R} `{!Symmetric R}  `{!Transitive R}.

  Definition equiv_class_quotient :=
    {P : A -> hProp | merely (exists a, forall b, R a b <~> P b)}.

  Definition equiv_class_of (a : A) : equiv_class_quotient
    := ((fun b => BuildhProp (R a b)); tr (a; fun b => equiv_idmap)).

  Lemma related_equiv_classes_eq
    : forall x y : A, R x y -> equiv_class_of x = equiv_class_of y.
  Proof.
    intros x y h.
    apply path_sigma_hprop.
    funext b.
    apply path_iff_hprop; cbn; intro.
    + by transitivity x.
    + by transitivity y.
  Qed.

  Definition quotient_to_equiv_class_quotient
    : quotient R -> equiv_class_quotient
    := quotient_rec R equiv_class_of related_equiv_classes_eq.

  Global Instance surjection_quotient_to_equiv_class_quotient
    : IsSurjection quotient_to_equiv_class_quotient.
  Proof.
    apply BuildIsSurjection.
    intros [P e].
    strip_truncations.
    apply tr.
    destruct e as [a e].
    exists (class_of R a).
    apply path_sigma_hprop.
    funext b.
    apply path_hprop.
    apply e.
  Qed.

  Global Instance embedding_quotient_to_equiv_class_quotient
    : IsEmbedding quotient_to_equiv_class_quotient.
  Proof.
    apply isembedding_isinj_hset.
    refine (quotient_ind_prop _ _ _).
    intro x.
    refine (quotient_ind_prop _ _ _).
    intro y.
    intro p.
    apply related_classes_eq.
    symmetry.
    set (p' := ap (fun f => trunctype_type (f x)) p..1).
    cbn in p'.
    by induction p'.
  Qed.

  Global Instance isequiv_quotient_to_equiv_class_quotient
    : IsEquiv quotient_to_equiv_class_quotient.
  Proof.
    apply isequiv_surj_emb.
    - apply surjection_quotient_to_equiv_class_quotient.
    - apply embedding_quotient_to_equiv_class_quotient.
  Qed.

  Definition equiv_quotient_to_equiv_class_quotient
    : quotient R <~> equiv_class_quotient
    := Build_Equiv _ _ quotient_to_equiv_class_quotient _.
End equiv_class_quotient.
