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
  HoTT.Classes.theory.ua_homomorphism.

Import algebra_notations.

Section hom_term_algebra.
  Context
    `{Funext}
    {σ : Signature}
    {X : Carriers σ}
    `{∀ s, IsHSet (X s)}
    {A : Algebra σ}
    (f : ∀ s, X s → A s).

  Global Instance is_homomorphism_map_term_algebra
    : @IsHomomorphism σ (TermAlgebra X) A (map_term_algebra A f).
  Proof.
    intros u a.
    reflexivity.
  Defined.

  Definition hom_term_algebra : Homomorphism (TermAlgebra X) A
    := @BuildHomomorphism σ (TermAlgebra X) A (map_term_algebra A f) _.

  Definition inv_hom_term_algebra (f : Homomorphism (TermAlgebra X) A)
    : ∀ s, X s → A s
    := λ s x, f s (var_term_algebra X s x).

End hom_term_algebra.

Section ump_term_algebra.
  Context `{Funext}
    {σ : Signature}
    (X : Carriers σ)
    `{∀ s, IsHSet (X s)}
    (A : Algebra σ).

  Lemma sect_inv_hom_term_algebra' (f : Homomorphism (TermAlgebra X) A)
    {s : Sort σ} (a : TermAlgebra X s)
    : hom_term_algebra (inv_hom_term_algebra f) s a = f s a.
  Proof.
    induction a; cbn in *.
    - reflexivity.
    - refine (_ @ (is_homomorphism_hom f u c)^).
      f_ap.
      funext I.
      apply X0.
  Defined.

  Lemma sect_inv_hom_term_algebra
    : Sect (@inv_hom_term_algebra _ σ X _ A) (@hom_term_algebra _ σ X _ A).
  Proof.
    intro f.
    apply path_homomorphism.
    funext s a.
    apply sect_inv_hom_term_algebra'.
  Defined.

  Lemma sect_hom_term_algebra
    : Sect (@hom_term_algebra _ σ X _ A) (@inv_hom_term_algebra _ σ X _ A).
  Proof.
    intro f. by funext s a.
  Defined.

  Global Instance isequiv_hom_term_algebra
    : IsEquiv (@hom_term_algebra _ σ X _ A).
  Proof.
    serapply isequiv_adjointify.
    - exact inv_hom_term_algebra.
    - apply sect_inv_hom_term_algebra.
    - apply sect_hom_term_algebra.
  Defined.

  Theorem ump_term_algebra
    : (∀ s, X s → A s) <~> Homomorphism (TermAlgebra X) A.
  Proof.
    exact (BuildEquiv _ _ (@hom_term_algebra _ σ X _ A) _).
  Defined.
End ump_term_algebra.

Module CarriersFreeAlgebra.

  Private Inductive CarriersFreeAlgebra `{Funext} {σ} (C : Carriers σ)
    {I : Type} (e : SyntacticEquations σ I)
    : Carriers σ :=
    | var_free_algebra : ∀ s, C s → CarriersFreeAlgebra C e s
    | ops_free_algebra : ∀ (u : Symbol σ),
        DomOperation (CarriersFreeAlgebra C e) (σ u) →
        CodOperation (CarriersFreeAlgebra C e) (σ u).

Section PathsCarriersFreeAlgebra.
  Context `{Funext} {σ} (C : Carriers σ)
    {I : Type} (e : SyntacticEquations σ I).

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

(* TODO: Make definition for:
CarriersTermAlgebra_ind (context_syntactic_equation (e i))
          (fun s T => P s (map_term_algebra FreeAlgebra f _ T)) F
          (fun u a r => os u _ r) _ (left_syntactic_equation (e i))
Then use definition in CarriersFreeAlgebra_ind and test.
*)

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
        CarriersTermAlgebra_ind (context_syntactic_equation (e i))
          (fun s T => P s (map_term_algebra FreeAlgebra f _ T)) F
          (fun u a r => os u _ r) _ (left_syntactic_equation (e i))
      = CarriersTermAlgebra_ind (context_syntactic_equation (e i))
          (fun s T => P s (map_term_algebra FreeAlgebra f _ T)) F
          (fun u a r => os u _ r) _ (right_syntactic_equation (e i)))
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

  Lemma test
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
        CarriersTermAlgebra_ind (context_syntactic_equation (e i))
          (fun s T => P s (map_term_algebra FreeAlgebra f _ T)) F
          (fun u a r => os u _ r) _ (left_syntactic_equation (e i))
      = CarriersTermAlgebra_ind (context_syntactic_equation (e i))
          (fun s T => P s (map_term_algebra FreeAlgebra f _ T)) F
          (fun u a r => os u _ r) _ (right_syntactic_equation (e i)))
    (i : I)
    (f : ∀ t, context_syntactic_equation (e i) t → CarriersFreeAlgebra C e t)
    (E : CarriersTermAlgebra (context_syntactic_equation (e i))
          (sort_syntactic_equation (e i)))
    : CarriersFreeAlgebra_ind P vs os ps (sort_syntactic_equation (e i))
         (map_term_algebra FreeAlgebra f (sort_syntactic_equation (e i)) E)
      = CarriersTermAlgebra_ind (context_syntactic_equation (e i))
         (λ s T, P s (map_term_algebra FreeAlgebra f s T))
         (λ t (c : context_syntactic_equation (e i) t),
            CarriersFreeAlgebra_ind P vs os ps t (f t c))
         (λ u
          (a : ∀ X, CarriersTermAlgebra _ (sorts_dom (σ u) X))
          (r : ∀ X, P (sorts_dom (σ u) X)
               (map_term_algebra FreeAlgebra f (sorts_dom (σ u) X) (a X))),
          os u
            (λ X, map_term_algebra FreeAlgebra f (sorts_dom (σ u) X) (a X)) r)
         (sort_syntactic_equation (e i)) E.
  Proof.
    induction E.
    - cbn; intros. reflexivity.
    - cbn; intros. f_ap. funext Y. apply X.
  Defined.

  Lemma compute_CarriersFreeAlgebra_ind_equations : ∀
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
        CarriersTermAlgebra_ind (context_syntactic_equation (e i))
          (fun s T => P s (map_term_algebra FreeAlgebra f _ T)) F
          (fun u a r => os u _ r) _ (left_syntactic_equation (e i))
      = CarriersTermAlgebra_ind (context_syntactic_equation (e i))
          (fun s T => P s (map_term_algebra FreeAlgebra f _ T)) F
          (fun u a r => os u _ r) _ (right_syntactic_equation (e i)))
    (i : I)
    (f : ∀ t, context_syntactic_equation (e i) t → CarriersFreeAlgebra C e t),
    apD (CarriersFreeAlgebra_ind P vs os ps _) (equations_free_algebra i f)
    = apD (CarriersFreeAlgebra_ind P vs os ps _) (equations_free_algebra i f).
    intros.
pose (apD (CarriersFreeAlgebra_ind P vs os ps _) (equations_free_algebra i f))
  as D.
(*
     : transport (P (sort_syntactic_equation (e i)))
         (equations_free_algebra i f)
         (CarriersFreeAlgebra_ind P vs os ps (sort_syntactic_equation (e i))
            (map_term_algebra FreeAlgebra f (sort_syntactic_equation (e i))
               (left_syntactic_equation (e i)))) =
       CarriersFreeAlgebra_ind P vs os ps (sort_syntactic_equation (e i))
         (map_term_algebra FreeAlgebra f (sort_syntactic_equation (e i))
            (right_syntactic_equation (e i)))
*)
Check ps i f (fun t c => CarriersFreeAlgebra_ind P vs os ps t (f t c)).
(*
     : transport (P (sort_syntactic_equation (e i)))
         (equations_free_algebra i f)
         (CarriersTermAlgebra_ind (context_syntactic_equation (e i))
            (λ (s : Sort σ)
             (T : CarriersTermAlgebra (context_syntactic_equation (e i)) s),
             P s (map_term_algebra FreeAlgebra f s T))
            (λ (t : Sort σ) (c : context_syntactic_equation (e i) t),
             CarriersFreeAlgebra_ind P vs os ps t (f t c))
            (λ (u : Symbol σ)
             (a : forall X : Arity (σ u),
                  CarriersTermAlgebra (context_syntactic_equation (e i))
                    (sorts_dom (σ u) X))
             (r : forall X : Arity (σ u),
                  P (sorts_dom (σ u) X)
                    (map_term_algebra FreeAlgebra f (sorts_dom (σ u) X) (a X))),
             os u
               (λ X : Arity (σ u),
                map_term_algebra FreeAlgebra f (sorts_dom (σ u) X) (a X)) r)
            (sort_syntactic_equation (e i)) (left_syntactic_equation (e i))) =
       CarriersTermAlgebra_ind (context_syntactic_equation (e i))
         (λ (s : Sort σ)
          (T : CarriersTermAlgebra (context_syntactic_equation (e i)) s),
          P s (map_term_algebra FreeAlgebra f s T))
         (λ (t : Sort σ) (c : context_syntactic_equation (e i) t),
          CarriersFreeAlgebra_ind P vs os ps t (f t c))
         (λ (u : Symbol σ)
          (a : forall X : Arity (σ u),
               CarriersTermAlgebra (context_syntactic_equation (e i))
                 (sorts_dom (σ u) X))
          (r : forall X : Arity (σ u),
               P (sorts_dom (σ u) X)
                 (map_term_algebra FreeAlgebra f (sorts_dom (σ u) X) (a X))),
          os u
            (λ X : Arity (σ u),
             map_term_algebra FreeAlgebra f (sorts_dom (σ u) X) (a X)) r)
         (sort_syntactic_equation (e i)) (right_syntactic_equation (e i))
*)

End PathsCarriersFreeAlgebra.
End CarriersFreeAlgebra.

Import CarriersFreeAlgebra.

Section CarriersFreeAlgebra_rec.
  Context `{Funext} {σ} (C : Carriers σ)
    {I : Type} (e : SyntacticEquations σ I).

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
      CarriersTermAlgebra_rec (context_syntactic_equation (e i)) P F
        (fun u a r =>
          os u (λ X, map_term_algebra (FreeAlgebra C e) f _ (a X)) r)
        (sort_syntactic_equation (e i))
        (left_syntactic_equation (e i))
      = CarriersTermAlgebra_rec (context_syntactic_equation (e i)) P F
          (fun u a r =>
            os u (λ X, map_term_algebra (FreeAlgebra C e) f _ (a X)) r)
          (sort_syntactic_equation (e i))
          (right_syntactic_equation (e i)))
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
    intros i f.
    apply equations_free_algebra.
  Defined.

  Definition EquationalTheoryFreeAlgebra : EquationalTheory σ
    := BuildEquationalTheory (FreeAlgebra C e) e.

End EquationalTheoryFreeAlgebra.

Section hom_free_algebra.
  Context `{Funext} {σ : Signature} {C : Carriers σ}
    {I : Type} (e : SyntacticEquations σ I)
    {A : Algebra σ} `{!IsEquationalTheory A e} (f : ∀ s, C s → A s).

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
      hom_free_algebra e (inv_hom_free_algebra e f) s a = f s a.
  Proof.
    srefine (CarriersFreeAlgebra_ind C e (fun s a => hom_free_algebra e (inv_hom_free_algebra e f) s a = f s a) _ _ _).
    - reflexivity.
    - cbn; intros. refine (_ @ (is_homomorphism_hom f u a)^).
      f_ap.
      funext Y.
      apply X.
    - intros. apply path_ishprop.
  Defined.

  Lemma sect_inv_hom_free_algebra
    : Sect (@inv_hom_free_algebra _ σ C _ e A) (@hom_free_algebra _ σ C _ e A _).
  Proof.
    intro f.
    apply path_homomorphism.
    funext s a.
    apply sect_inv_hom_free_algebra'.
  Defined.

  Lemma sect_hom_free_algebra
    : Sect (@hom_free_algebra _ σ C _ e A _) (@inv_hom_free_algebra _ σ C _ e A).
  Proof.
    intro f. by funext s a.
  Defined.

  Global Instance isequiv_hom_free_algebra
    : IsEquiv (@hom_free_algebra _ σ C _ e A _).
  Proof.
    serapply isequiv_adjointify.
    - apply inv_hom_free_algebra.
    - apply sect_inv_hom_free_algebra.
    - apply sect_hom_free_algebra.
  Defined.

  Theorem ump_free_algebra
    : (∀ s, C s → A s) <~> Homomorphism (FreeAlgebra C e) A.
  Proof.
    exact (BuildEquiv _ _ (@hom_free_algebra _ σ C _ e A _) _).
  Defined.
End ump_free_algebra.
