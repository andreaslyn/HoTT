(*
(** This file defines the kernel of a homomorphism [cong_ker], the
    image of a homomorphism [in_image_hom], and it proves the first
    isomorphism theorem [isomorphic_first_isomorphism]. The first
    identification theorem [id_first_isomorphism] follows. *)

Require Import
  HoTT.Types.Forall
  HoTT.Types.Sigma
  HoTT.Types.Universe
  HoTT.HSet
  HoTT.HIT.quotient
  HoTT.Classes.interfaces.canonical_names
  HoTT.Algebra.Universal.isomorphic
  HoTT.Algebra.Universal.subalgebra
  HoTT.Algebra.Universal.quotient_algebra
  HoTT.Algebra.Universal.hsetprojective.

Import
  algebra_notations
  quotient_algebra_notations
  subalgebra_notations
  isomorphic_notations.

(** The following section defines the kernel of a homomorphism
    [cong_ker], and shows that it is a congruence.*)

Section cong_ker.
  Context
    `{Funext} {σ : Signature} {A B : Algebra σ}
    (f : ∀ s, A s → B s) {IsH : IsHomomorphism f}.

  Definition cong_ker (s : Sort σ) : Relation (A s)
    := λ (x y : A s), f s x = f s y.

  Global Instance equiv_rel_ker (s : Sort σ) : EquivRel (cong_ker s).
  Proof.
    repeat constructor.
    - intros x y. exact inverse.
    - intros x y z. exact concat.
  Qed.

  Global Instance ops_compatible_ker : OpsCompatible A cong_ker.
  Proof.
    intros u a b R.
    refine (IsH _ _ @ ap _ _ @ (IsH _ _)^).
    funext i.
    apply R.
  Qed.

  Global Instance is_congruence_ker : IsCongruence A cong_ker
    := Build_IsCongruence A cong_ker.

End cong_ker.

(** The next section defines an "in image predicate", [in_image_hom].
    It gives rise to the homomorphic image of a homomorphism. *)

Section in_image_hom.
  Context
    `{Funext} {σ : Signature} {A B : Algebra σ}
    (f : ∀ s, A s → B s) {IsH : IsHomomorphism f}
    `{!∀ u, IsHSetProjective (Arity (σ u))}.

  Definition in_image_hom (s : Sort σ) (y : B s) : hProp
    := merely (hfiber (f s) y).

  Lemma closed_under_op_in_image_hom
    {w : SymbolType σ} `{!IsHSetProjective (Arity w)}
    (α : Operation A w) (β : Operation B w) (P : OpPreserving f α β)
    : ClosedUnderOp B in_image_hom β.
  Proof.
    intros b a.
    pose proof (is_hsetprojective _ _ a) as a'.
    strip_truncations.
    apply tr.
    exists ((α (λ i, (a' i).1))).
    induction (P (λ i, (a' i).1))^.
    f_ap.
    funext i.
    apply a'.
  Qed.

  Lemma is_closed_under_ops_in_image_hom
    : IsClosedUnderOps B in_image_hom.
  Proof.
    intro u. eapply closed_under_op_in_image_hom, IsH.
  Qed.

  Global Instance is_subalgebra_predicate_in_image_hom
    : IsSubalgebraPredicate B in_image_hom
    := Build_IsSubalgebraPredicate is_closed_under_ops_in_image_hom.

End in_image_hom.

(** The folowing section proves the first isomorphism theorem,
    [isomorphic_first_isomorphism] and the first identification
    theorem [id_first_isomorphism]. *)

Section first_isomorphism.
  Context
    `{Univalence} {σ} {A B : Algebra σ}
    (f : ∀ s, A s → B s) {IsH : IsHomomorphism f}
    `{!∀ u, IsHSetProjective (Arity (σ u))}.

(** The homomorphism [def_first_isomorphism] is informally given by

    <<
      def_first_isomorphism s (class_of _ x) := f s x.
    >>
*)

  Definition def_first_isomorphism (s : Sort σ)
    : (A / cong_ker f) s → (B & in_image_hom f) s.
  Proof.
    refine (quotient_rec (cong_ker f s) (λ x, (f s x; tr (x; idpath))) _).
    intros x y p.
    now apply path_sigma_hprop.
  Defined.

  Lemma oppreserving_first_isomorphism
    {w : SymbolType σ} `{!IsHSetProjective (Arity w)}
    (α : Operation A w)
    (β : Operation B w)
    (γ : Operation (A / cong_ker f) w)
    (C : ClosedUnderOp B (in_image_hom f) β)
    (P : OpPreserving f α β)
    (G : ∀ a, γ (λ i, class_of _ (a i)) = class_of _ (α a))
    : OpPreserving def_first_isomorphism γ
        (op_subalgebra B (in_image_hom f) β C).
  Proof.
    refine (choice_fun_quotient_ind_prop (λ i, cong_ker f (sorts_dom _ i)) _ _).
    cbn in *.
    intro a.
    induction (G a)^.
    apply path_sigma_hprop.
    apply P.
  Qed.

(* Leave [is_homomorphism_first_isomorphism] opaque because
   [IsHomomorphism] is an hprop when [B] is a set algebra. *)

  Global Instance is_homomorphism_first_isomorphism
    : IsHomomorphism def_first_isomorphism.
  Proof.
    intro u. apply (oppreserving_first_isomorphism (u^^A)).
    - apply IsH.
    - apply compute_op_quotient.
  Qed.

  Definition hom_first_isomorphism
    : Homomorphism (A / cong_ker f) (B & in_image_hom f)
    := Build_Homomorphism def_first_isomorphism.

  Global Instance embedding_first_isomorphism (s : Sort σ)
    : IsEmbedding (hom_first_isomorphism s).
  Proof.
    apply isembedding_isinj_hset.
    refine (quotient_ind_prop (cong_ker f s) _ _). intro x.
    refine (quotient_ind_prop (cong_ker f s) _ _). intros y p.
    apply related_classes_eq.
    exact (p..1).
  Qed.

  Global Instance surjection_first_isomorphism (s : Sort σ)
    : IsSurjection (hom_first_isomorphism s).
  Proof.
    apply BuildIsSurjection.
    intros [x M].
    refine (Trunc_rec _ M). intros [y Y].
    apply tr.
    exists (class_of _ y).
    now apply path_sigma_hprop.
  Qed.

  Global Instance is_isomorphism_first_isomorphism
    : IsIsomorphism hom_first_isomorphism.
  Proof.
    intro s. apply isequiv_surj_emb; exact _.
  Qed.

  Theorem isomorphic_first_isomorphism
    : A / cong_ker f ≅ B & in_image_hom f.
  Proof.
    exact (Build_Isomorphic def_first_isomorphism).
  Defined.

(* The first identification theorem [id_first_isomorphism] is an
   h-prop, so we can leave it opaque. *)

  Corollary id_first_isomorphism : A / cong_ker f = B & in_image_hom f.
  Proof.
    exact (id_isomorphic isomorphic_first_isomorphism).
  Qed.
End first_isomorphism.

(** The next section gives a specialization of the first isomorphism
    theorem, where the homomorphism is surjective. *)

Section first_isomorphism_surjection.
  Context
    `{Univalence} {σ} {A B : Algebra σ}
    (f : ∀ s, A s → B s) `{!IsHomomorphism f} {S : ∀ s, IsSurjection (f s)}
    `{!∀ u, IsHSetProjective (Arity (σ u))}.

  Global Instance is_isomorphism_inc_first_isomorphism_surjection
    : IsIsomorphism (hom_inc_subalgebra B (in_image_hom f)).
  Proof.
    apply is_isomorphism_inc_improper_subalgebra. apply S.
  Qed.

(** The homomorphism [hom_first_isomorphism_surjection] is the
    composition of two isomorphisms, so it is an isomorphism. *)

  Definition hom_first_isomorphism_surjection
    : Homomorphism (A / cong_ker f) B
    := hom_compose
          (hom_inc_subalgebra B (in_image_hom f))
          (hom_first_isomorphism f).

  Theorem isomorphic_first_isomorphism_surjection : A / cong_ker f ≅ B.
  Proof.
    exact (Build_Isomorphic hom_first_isomorphism_surjection).
  Defined.

  Corollary id_first_isomorphism_surjection : (A / cong_ker f) = B.
  Proof.
    exact (id_isomorphic isomorphic_first_isomorphism_surjection).
  Qed.
End first_isomorphism_surjection.

(** The next section specializes the first isomorphism theorem to the
    case where the homomorphism is injective. It proves that an
    injective homomorphism is an isomorphism between its domain
    and its image. *)

Section first_isomorphism_inj.
  Context
    `{Univalence} {σ} {A B : Algebra σ}
    (f : ∀ s, A s → B s) `{!IsHomomorphism f} (inj : ∀ s, isinj (f s))
    `{!∀ u, IsHSetProjective (Arity (σ u))}.

  Global Instance is_isomorphism_quotient_first_isomorphism_inj
    : IsIsomorphism (hom_quotient (cong_ker f)).
  Proof.
    apply is_isomorphism_quotient. intros s x y p. apply inj, p.
  Qed.

(** The homomorphism [hom_first_isomorphism_inj] is the
    composition of two isomorphisms, so it is an isomorphism. *)

  Definition hom_first_isomorphism_inj
    : Homomorphism A (B & in_image_hom f)
    := hom_compose
          (hom_first_isomorphism f)
          (hom_quotient (cong_ker f)).

  Definition isomorphic_first_isomorphism_inj : A ≅ B & in_image_hom f
    := Build_Isomorphic hom_first_isomorphism_inj.

  Definition id_first_isomorphism_inj : A = B & in_image_hom f
    := id_isomorphic isomorphic_first_isomorphism_inj.

End first_isomorphism_inj.
*)