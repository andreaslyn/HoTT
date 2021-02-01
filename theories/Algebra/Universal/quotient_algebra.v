Require Export HoTT.Algebra.Universal.congruence.

Require Import
  HoTT.Basics
  HoTT.Types
  HoTT.HProp
  HoTT.HSet
  HoTT.HIT.quotient
  HoTT.Truncations
  HoTT.Classes.interfaces.canonical_names
  HoTT.Algebra.Universal.hsetprojective
  HoTT.Algebra.Universal.homomorphism
  HoTT.Algebra.Universal.algebraic_theory.

Import algebra_notations.

Section quotient_algebra.
  Context
    `{Univalence} {σ : Signature} `{!∀ u, IsHSetProjective (Arity (σ u))}
    (A : Algebra σ) (Φ : ∀ s, Relation (A s)) `{!IsCongruence A Φ}.

(** The quotient algebra carriers is the family of set-quotients
    induced by [Φ]. *)

  Definition carriers_quotient_algebra : Carriers σ
    := λ s, quotient (Φ s).

  Lemma well_def_op_quotient_algebra
    {w : SymbolType σ} `{!IsHSetProjective (Arity w)}
    (α : Operation A w) (C : OpCompatible A Φ α)
    (a b : DomOperation A w) (r : ∀ i, Φ (sorts_dom w i) (a i) (b i))
    : class_of (Φ (sort_cod w)) (α a) = class_of (Φ (sort_cod w)) (α b).
  Proof.
    apply related_classes_eq. apply C. exact r.
  Qed.

  Definition op_quotient_algebra
    {w : SymbolType σ} `{!IsHSetProjective (Arity w)}
    (α : Operation A w) (C : OpCompatible A Φ α)
  : Operation carriers_quotient_algebra w
  := choice_fun_quotient_rec _ (λ a, class_of _ (α a))
      (well_def_op_quotient_algebra α C).

  Definition ops_quotient_algebra (u : Symbol σ)
    : Operation carriers_quotient_algebra (σ u)
    := op_quotient_algebra (u^^A) (ops_compatible_cong A Φ u).

(** Definition of quotient algebra. See Lemma [compute_op_quotient]
    below for the computation rule of quotient algebra operations. *)

  Definition QuotientAlgebra : Algebra σ
    := Build_Algebra carriers_quotient_algebra ops_quotient_algebra.

End quotient_algebra.

Module quotient_algebra_notations.
  Global Notation "A / Φ" := (QuotientAlgebra A Φ)
                             (at level 40, left associativity)
                             : Algebra_scope.
End quotient_algebra_notations.

Import quotient_algebra_notations.

(** The following lemma gives the computation rule for the quotient
    algebra operations. It says that for
    [(a1, a2, ..., an) : A s1 * A s2 * ... * A sn],
    <<
      β (class_of _ a1, class_of _ a2, ..., class_of _ an)
      = class_of _ (α (a1, a2, ..., an))
    >>
    where [α] is the uncurried [u^^A] operation and [β] is the
    uncurried [u^^QuotientAlgebra] operation. *)

Lemma compute_op_quotient
  `{Univalence} {σ : Signature} `{!∀ u, IsHSetProjective (Arity (σ u))}
  (A : Algebra σ) (Φ : ∀ s, Relation (A s)) `{!IsCongruence A Φ}
  (u : Symbol σ) (a : DomOperation A (σ u))
  : (u^^(A/Φ)) (λ i, class_of (Φ (sorts_dom (σ u) i)) (a i))
    = class_of (Φ (sort_cod (σ u))) ((u^^A) a).
Proof.
  apply (choice_fun_quotient_rec_compute _
          (λ x, class_of (Φ (sort_cod (σ u))) ((u^^A) x))).
Qed.

(** The next section shows that A/Φ = A/Ψ whenever
    [Φ s x y <-> Ψ s x y] for all [s], [x], [y]. *)

Section path_quotient_algebra.
  Context `{Univalence} {σ : Signature}
    `{!∀ u, IsHSetProjective (Arity (σ u))} (A : Algebra σ)
    (Φ : ∀ s, Relation (A s)) {CΦ : IsCongruence A Φ}
    (Ψ : ∀ s, Relation (A s)) {CΨ : IsCongruence A Ψ}.

  Lemma path_quotient_algebra (p : Φ = Ψ) : A/Φ = A/Ψ.
  Proof.
    by destruct p, (path_ishprop CΦ CΨ).
  Defined.

  Lemma path_quotient_algebra_iff
    (R : ∀ s x y, Φ s x y <-> Ψ s x y)
    : A/Φ = A/Ψ.
  Proof.
    apply path_quotient_algebra.
    funext s x y.
    refine (path_universe_uncurried _).
    apply equiv_iff_hprop; apply R.
  Defined.
End path_quotient_algebra.

(** The following section defines the quotient homomorphism
    [hom_quotient : Homomorphism A (A/Φ)]. *)

Section hom_quotient.
  Context
    `{Univalence} {σ : Signature} `{!∀ u, IsHSetProjective (Arity (σ u))}
    {A : Algebra σ} (Φ : ∀ s, Relation (A s)) `{!IsCongruence A Φ}.

  Definition def_hom_quotient : ∀ (s : Sort σ), A s → (A/Φ) s :=
    λ s x, class_of (Φ s) x.

  Lemma oppreserving_quotient {w : SymbolType σ}
    (α : Operation A w) (β : Operation (A/Φ) w)
    (c : ∀ a, β (λ i, class_of _ (a i)) = class_of _ (α a))
    : OpPreserving def_hom_quotient α β.
  Proof.
    intro a. symmetry. apply c.
  Qed.

  Global Instance is_homomorphism_quotient
    : IsHomomorphism def_hom_quotient.
  Proof.
    intro u. apply oppreserving_quotient, compute_op_quotient.
  Qed.

  Definition hom_quotient : Homomorphism A (A/Φ)
    := Build_Homomorphism def_hom_quotient.

  Global Instance surjection_quotient
    : ∀ s, IsSurjection (hom_quotient s).
  Proof.
    intro s. apply quotient_surjective.
  Qed.
End hom_quotient.

Section path_map_term_algebra_quotient.
  Context
    `{Univalence} {σ : Signature} `{!∀ u, IsHSetProjective (Arity (σ u))}
    (A : Algebra σ) (Φ : ∀ s, Relation (A s)) `{!IsCongruence A Φ}
    (C : Carriers σ) `{∀ s, IsHSet (C s)} (f : ∀ s, C s → A s).

  Lemma path_map_term_algebra_quotient (t : Sort σ)
    (x : TermAlgebra C t)
    : map_term_algebra (A/Φ) (λ s, hom_quotient Φ s o f s) t x
      = hom_quotient Φ t (map_term_algebra A f t x).
  Proof.
    induction x.
    - reflexivity.
    - refine (ap _ _ @ compute_op_quotient A Φ u _). funext i. apply X.
  Qed.
End path_map_term_algebra_quotient.

Section AlgebraicTheoryQuotient.
  Context
    `{Univalence} {σ : Signature} `{!∀ u, IsHSetProjective (Arity (σ u))}
    (A : Algebra σ) (Φ : ∀ s, Relation (A s)) `{!IsCongruence A Φ}
    (I : Type) (e : Equations σ I) {E : IsAlgebraicTheory A e}
    `{!IsHSetProjective (Sort σ)}
    `{!∀ s i, IsHSetProjective (context_equation (e i) s)}.

  Global Instance equational_theory_quotient : IsAlgebraicTheory (A/Φ) e.
  Proof.
    intros i a.
    assert (hexists (λ a', a = λ s x, class_of _ (a' s x))) as pa.
    - pose proof (equiv_hsetprojective_quotient_choosable
                    {s | context_equation (e i) s} _ (λ u, A u.1) _
                    (λ u, Φ u.1) _ _ _ _ (fun u => a u.1 u.2)) as ch.
      strip_truncations.
      destruct ch as [g G].
      apply tr.
      exists (λ s x, g (s; x)).
      funext s x.
      symmetry.
      exact (G (s; x)).
    - strip_truncations.
      destruct pa as [a' pa].
      induction pa^.
      exact (path_map_term_algebra_quotient A Φ _ a' _ _
             @ ap _ (E i a')
             @ (path_map_term_algebra_quotient A Φ _ a' _ _)^).
  Qed.

  Definition AlgebraicTheoryQuotient : AlgebraicTheory σ
    := Build_AlgebraicTheory (A/Φ) e.

End AlgebraicTheoryQuotient.

(** If [Φ s x y] implies [x = y], then homomorphism [hom_quotient Φ]
    is an isomorphism. *)

Global Instance is_isomorphism_quotient `{Univalence}
  {σ : Signature}  `{!∀ u, IsHSetProjective (Arity (σ u))}
  {A : Algebra σ} (Φ : ∀ s, Relation (A s))
  `{!IsCongruence A Φ} (P : ∀ s x y, Φ s x y → x = y)
  : IsIsomorphism (hom_quotient Φ).
Proof.
  intro s.
  apply isequiv_surj_emb; [exact _ |].
  apply isembedding_isinj_hset.
  intros x y p.
  by apply P, (classes_eq_related (Φ s)).
Qed.

(** This section develops the universal mapping property
    [ump_quotient_algebra] of the quotient algebra. *)

Section ump_quotient_algebra.
  Context
    `{Univalence} {σ : Signature}  `{!∀ u, IsHSetProjective (Arity (σ u))}
    {A B : Algebra σ} (Φ : ∀ s, Relation (A s)) `{!IsCongruence A Φ}.

(** In the nested section below we show that if [f : Homomorphism A B]
    maps elements related by [Φ] to equal elements, there is a
    [Homomorphism (A/Φ) B] out of the quotient algebra satisfying
    [compute_quotient_algebra_mapout] below. *)

  Section quotient_algebra_mapout.
    Context
      (f : Homomorphism A B)
      (R : ∀ s (x y : A s), Φ s x y → f s x = f s y).

    Definition def_hom_quotient_algebra_mapout
      : ∀ (s : Sort σ), (A/Φ) s → B s
      := λ s, (quotient_ump (Φ s) (BuildhSet (B s)))^-1 (f s; R s).

    Lemma oppreserving_quotient_algebra_mapout
      {w : SymbolType σ} `{!IsHSetProjective (Arity w)}
      (α : Operation A w) (β : Operation B w) (α' : Operation (A/Φ) w)
      (c : ∀ a, α' (λ i, class_of _ (a i)) = class_of _ (α a))
      (P : OpPreserving f α β)
      : OpPreserving def_hom_quotient_algebra_mapout α' β.
    Proof.
      intro a.
      pose proof (equiv_hsetprojective_quotient_choosable (Arity w) _
                    (λ i, A (sorts_dom w i)) _
                    (λ i, Φ (sorts_dom w i)) _ _ _ _ a) as ch.
      strip_truncations.
      destruct ch as [g p].
      apply path_forall in p.
      induction p.
      rewrite c.
      apply P.
    Qed.

    Global Instance is_homomorphism_quotient_algebra_mapout
      : IsHomomorphism def_hom_quotient_algebra_mapout.
    Proof.
      intro u.
      eapply oppreserving_quotient_algebra_mapout.
      - apply compute_op_quotient.
      - apply f.
    Qed.

    Definition hom_quotient_algebra_mapout
      : Homomorphism (A/Φ) B
      := Build_Homomorphism def_hom_quotient_algebra_mapout.

(** The computation rule for [hom_quotient_algebra_mapout] is
    <<
      hom_quotient_algebra_mapout s (class_of (Φ s) x) = f s x.
    >>
*)

    Lemma compute_quotient_algebra_mapout
      : ∀ (s : Sort σ) (x : A s),
        hom_quotient_algebra_mapout s (class_of (Φ s) x) = f s x.
    Proof.
      reflexivity.
    Defined.

  End quotient_algebra_mapout.

  Definition hom_quotient_algebra_mapin (g : Homomorphism (A/Φ) B)
    : Homomorphism A B
    := hom_compose g (hom_quotient Φ).

  Lemma ump_quotient_algebra_lr :
    {f : Homomorphism A B | ∀ s (x y : A s), Φ s x y → f s x = f s y}
    → Homomorphism (A/Φ) B.
  Proof.
    intros [f P]. exists (hom_quotient_algebra_mapout f P). exact _.
  Defined.

  Lemma ump_quotient_algebra_rl :
    Homomorphism (A/Φ) B →
    {f : Homomorphism A B | ∀ s (x y : A s), Φ s x y → f s x = f s y}.
  Proof.
    intro g.
    exists (hom_quotient_algebra_mapin g).
    intros s x y E.
    exact (transport (λ z, g s (class_of (Φ s) x) = g s z)
            (related_classes_eq (Φ s) E) idpath).
  Defined.

(** The universal mapping property of the quotient algebra. For each
    homomorphism [f : Homomorphism A B], mapping elements related by
    [Φ] to equal elements, there is a unique homomorphism
    [g : Homomorphism (A/Φ) B] satisfying
    <<
      f = hom_compose g (hom_quotient Φ).
    >>
*)

  Lemma ump_quotient_algebra
    : {f : Homomorphism A B | ∀ s (x y : A s), Φ s x y → f s x = f s y}
     <~>
      Homomorphism (A/Φ) B.
  Proof.
    apply (equiv_adjointify
             ump_quotient_algebra_lr ump_quotient_algebra_rl).
    - intro G.
      apply path_homomorphism.
      funext s.
      exact (eissect (quotient_ump (Φ s) _) (G s)).
    - intro F.
      apply path_sigma_hprop.
      by apply path_homomorphism.
  Defined.
End ump_quotient_algebra.
