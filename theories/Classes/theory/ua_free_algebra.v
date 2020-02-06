Require Export HoTT.Classes.interfaces.ua_equational_theory.

Require Import
  HoTT.Basics.Equivalences
  HoTT.Basics.PathGroupoids
  HoTT.Types.Prod
  HoTT.Types.Sigma
  HoTT.Types.Universe
  HoTT.HIT.Truncations
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.interfaces.ua_congruence
  HoTT.Classes.theory.ua_isomorphic.

Import algebra_notations isomorphic_notations.

Definition param_map_term_algebra {σ} {C : Carriers σ} (A : Algebra σ)
  (f : ∀ t, C t → A t) (P : ∀ (s : Sort σ), A s → Type)
  (F : ∀ t c, P t (f t c))
  (os : ∀ (u : Symbol σ)
          (a : DomOperation A (σ u)),
        (∀ X, P _ (a X)) → P _ ((u^^A) a))
  (s : Sort σ) (E : CarriersTermAlgebra C s)
  : P s (map_term_algebra A f s E)
  := CarriersTermAlgebra_ind C
       (fun s T => P s (map_term_algebra A f s T)) F
       (fun u a r => os u (λ X, map_term_algebra A f _ (a X)) r) s E.

Example param_map_term_algebra_is_generalization {σ} {C : Carriers σ}
  (A : Algebra σ) (f : ∀ t, C t → A t)
  : param_map_term_algebra A f (fun s _ => A s) f (fun u _ => u^^A)
    = map_term_algebra A f.
Proof.
  reflexivity.
Defined.

Module Export CarriersFreeAlgebra.

  Private Inductive CarriersFreeAlgebra {σ} (C : Carriers σ)
    {I : Type} (e : SyntacticEquations σ I)
    : Carriers σ :=
    | var_free_algebra : ∀ s, C s → CarriersFreeAlgebra C e s
    | ops_free_algebra : ∀ (u : Symbol σ),
        DomOperation (CarriersFreeAlgebra C e) (σ u) →
        CodOperation (CarriersFreeAlgebra C e) (σ u).

Section PathsCarriersFreeAlgebra.
  Context {σ} (C : Carriers σ) {I : Type} (e : SyntacticEquations σ I).

  Axiom hset_free_algebra : ∀ s, IsHSet (CarriersFreeAlgebra C e s).

  Global Existing Instance hset_free_algebra.

  Definition FreeAlgebra : Algebra σ :=
    BuildAlgebra (CarriersFreeAlgebra C e) (ops_free_algebra C e).

  Axiom equations_free_algebra
    : ∀ (i : I) (f : ∀ t, context_syntactic_equation (e i) t →
                          CarriersFreeAlgebra C e t),
      map_term_algebra FreeAlgebra f _ (left_syntactic_equation (e i))
      = map_term_algebra FreeAlgebra f _ (right_syntactic_equation (e i))
      :> CarriersFreeAlgebra C e (sort_syntactic_equation (e i)).

  Fixpoint CarriersFreeAlgebra_ind
    (P : ∀ (s : Sort σ), CarriersFreeAlgebra C e s → Type)
    `{∀ (s : Sort σ) (F : CarriersFreeAlgebra C e s), IsHSet (P s F)}
    (vs : ∀ s (v : C s), P s (var_free_algebra C e s v))
    (os : ∀ (u : Symbol σ)
            (a : DomOperation (CarriersFreeAlgebra C e) (σ u)),
            (∀ X, P (sorts_dom (σ u) X) (a X)) →
            P (sort_cod (σ u)) (ops_free_algebra C e u a))
    (ps : ∀ (i : I)
            (f : ∀ t, context_syntactic_equation (e i) t →
                      CarriersFreeAlgebra C e t)
            (F : ∀ t c, P t (f t c)),
      equations_free_algebra i f #
        param_map_term_algebra FreeAlgebra f P F os
          (sort_syntactic_equation (e i)) (left_syntactic_equation (e i))
      = param_map_term_algebra FreeAlgebra f P F os
          (sort_syntactic_equation (e i)) (right_syntactic_equation (e i)))
    (s : Sort σ)
    (T : CarriersFreeAlgebra C e s)
    : P s T
    := match T with
       | var_free_algebra s v =>
          vs s v
       | ops_free_algebra u a =>
          os u a (fun X => CarriersFreeAlgebra_ind P vs os ps
                             (sorts_dom (σ u) X) (a X))
       end.

End PathsCarriersFreeAlgebra.
End CarriersFreeAlgebra.

Section CarriersFreeAlgebra_rec.
  Context {σ} (C : Carriers σ) {I : Type} (e : SyntacticEquations σ I).

  Definition CarriersFreeAlgebra_rec
    (P : Sort σ → Type)
    `{∀ (s : Sort σ), IsHSet (P s)}
    (vs : ∀ s, C s → P s)
    (os : ∀ (u : Symbol σ),
            DomOperation (CarriersFreeAlgebra C e) (σ u) →
            (∀ X, P (sorts_dom (σ u) X)) →
            P (sort_cod (σ u)))
    (ps : ∀ (i : I)
            (f : ∀ t, context_syntactic_equation (e i) t →
                      CarriersFreeAlgebra C e t)
            (F : ∀ t, context_syntactic_equation (e i) t → P t),
          param_map_term_algebra (FreeAlgebra C e) f (fun s _ => P s) F os
            (sort_syntactic_equation (e i)) (left_syntactic_equation (e i))
          = param_map_term_algebra (FreeAlgebra C e) f (fun s _ => P s) F os
              (sort_syntactic_equation (e i)) (right_syntactic_equation (e i)))
    (s : Sort σ)
    (T : CarriersFreeAlgebra C e s)
    : P s
    := CarriersFreeAlgebra_ind C e (fun s _ => P s) vs os
        (fun i f F => transport_const _ _ @ ps i f F) s T.

End CarriersFreeAlgebra_rec.

Section EquationalTheoryFreeAlgebra.
  Context `{Funext} {σ} (C : Carriers σ)
    {I : Type} (e : SyntacticEquations σ I).

  Global Instance is_equational_theory_free_algebra
    : IsEquationalTheory (FreeAlgebra C e) e.
  Proof.
    intros i f. apply equations_free_algebra.
  Defined.

  Definition EquationalTheoryFreeAlgebra : EquationalTheory σ
    := BuildEquationalTheory (FreeAlgebra C e) e.

End EquationalTheoryFreeAlgebra.

Section hom_free_algebra.
  Context `{Funext} {σ : Signature} (C : Carriers σ)
    {I : Type} (e : SyntacticEquations σ I)
    (A : Algebra σ) `{!IsEquationalTheory A e} (f : ∀ s, C s → A s).

  Definition map_free_algebra : ∀ s, FreeAlgebra C e s → A s
    := CarriersFreeAlgebra_rec C e A f (fun u _ r => (u^^A) r)
        (fun i _ F => equational_theory_laws i F).

  Global Instance is_homomorphism_map_free_algebra
    : IsHomomorphism map_free_algebra.
  Proof.
    intros u a.
    reflexivity.
  Defined.

  Definition hom_free_algebra : Homomorphism (FreeAlgebra C e) A
    := BuildHomomorphism map_free_algebra.

  Definition inv_hom_free_algebra (f : Homomorphism (FreeAlgebra C e) A)
    : ∀ s, C s → A s
    := λ s x, f s (var_free_algebra C e s x).

End hom_free_algebra.

Section ump_free_algebra.
  Context
    `{Funext} {σ} (C : Carriers σ) `{∀ s, IsHSet (C s)} (A : Algebra σ)
    {I : Type} (e : SyntacticEquations σ I) `{!IsEquationalTheory A e}.

  Lemma sect_inv_hom_free_algebra' (f : Homomorphism (FreeAlgebra C e) A)
    : ∀ (s : Sort σ) (a : FreeAlgebra C e s),
      hom_free_algebra C e A (inv_hom_free_algebra C e A f) s a = f s a.
  Proof.
    srefine (CarriersFreeAlgebra_ind C e
        (fun s a => hom_free_algebra C e A
                      (inv_hom_free_algebra C e A f) s a = f s a) _ _ _).
    - reflexivity.
    - cbn; intros. refine (_ @ (is_homomorphism_hom f u a)^).
      f_ap. funext Y. apply X.
    - intros. apply path_ishprop.
  Defined.

  Lemma sect_inv_hom_free_algebra
    : Sect (inv_hom_free_algebra C e A) (hom_free_algebra C e A).
  Proof.
    intro f.
    apply path_homomorphism.
    funext s a.
    apply sect_inv_hom_free_algebra'.
  Defined.

  Lemma sect_hom_free_algebra
    : Sect (hom_free_algebra C e A) (inv_hom_free_algebra C e A).
  Proof.
    intro f. by funext s a.
  Defined.

  Global Instance isequiv_hom_free_algebra
    : IsEquiv (hom_free_algebra C e A).
  Proof.
    serapply isequiv_adjointify.
    - apply inv_hom_free_algebra.
    - apply sect_inv_hom_free_algebra.
    - apply sect_hom_free_algebra.
  Defined.

  Theorem ump_free_algebra
    : (∀ s, C s → A s) <~> Homomorphism (FreeAlgebra C e) A.
  Proof.
    exact (BuildEquiv _ _ (hom_free_algebra C e A) _).
  Defined.
End ump_free_algebra.

Section term_algebra_is_free.
  Context `{Funext}.

  Definition trivial_equations (σ : Signature)
    : SyntacticEquations σ Empty
    := Empty_ind (fun _ => SyntacticEquation σ).

  Global Instance is_equational_theory_equations_term_algebra {σ}
    (A : Algebra σ)
    : IsEquationalTheory A (trivial_equations σ).
  Proof.
    intro e. elim e.
  Defined.

  Definition term_algebra_to_free_algebra {σ}
    (C : Carriers σ) `{∀ s, IsHSet (C s)}
    (s : Sort σ) (T : TermAlgebra C s)
    : FreeAlgebra C (trivial_equations σ) s
    := CarriersTermAlgebra_rec C
        (FreeAlgebra C (trivial_equations σ))
        (var_free_algebra C (trivial_equations σ))
        (fun u a r => ops_free_algebra C (trivial_equations σ) u r) s T.

  Definition free_algebra_to_term_algebra {σ}
    (C : Carriers σ) `{∀ s, IsHSet (C s)}
    (s : Sort σ) (T : FreeAlgebra C (trivial_equations σ) s)
    : TermAlgebra C s
    := CarriersFreeAlgebra_rec C (trivial_equations σ)
        (TermAlgebra C)
        (var_term_algebra C)
        (fun u a r => ops_term_algebra C u r) (Empty_ind _) s T.

  Global Instance is_homomorphism_term_algebra_to_free_algebra
    {σ} (C : Carriers σ) `{∀ s, IsHSet (C s)}
    : IsHomomorphism (term_algebra_to_free_algebra C).
  Proof.
    intros u a. reflexivity.
  Qed.

  Definition hom_term_algebra_to_free_algebra
    {σ} (C : Carriers σ) `{∀ s, IsHSet (C s)}
    : Homomorphism
        (TermAlgebra C)
        (FreeAlgebra C (trivial_equations σ))
    := BuildHomomorphism (term_algebra_to_free_algebra C).

  Global Instance is_isomorphism_term_algebra_to_free_algebra
    {σ} (C : Carriers σ) `{∀ s, IsHSet (C s)}
    : IsIsomorphism (term_algebra_to_free_algebra C).
  Proof.
    intros s.
    refine (isequiv_adjointify
      (term_algebra_to_free_algebra C s)
      (free_algebra_to_term_algebra C s) _ _); generalize dependent s.
    - refine (CarriersFreeAlgebra_ind C (trivial_equations σ)
                (fun s T => _ (_ T) = T) (fun _ _ => idpath) _ (Empty_ind _)).
      intros u a r. cbn. f_ap. funext X. apply r.
    - refine (CarriersTermAlgebra_ind C
                (fun s T => _ (_ T) = T) (fun _ _ => idpath) _).
      intros u a r. cbn. f_ap. funext X. apply r.
  Qed.

  Lemma isomorphic_term_algebra_free_algebra
    {σ} (C : Carriers σ) `{∀ s, IsHSet (C s)}
    : TermAlgebra C ≅ FreeAlgebra C (trivial_equations σ).
  Proof.
    exact (BuildIsomorphic (hom_term_algebra_to_free_algebra C)).
  Defined.
End term_algebra_is_free.
