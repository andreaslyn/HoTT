Require Export HoTT.Classes.interfaces.ua_equational_theory.

Require Import
  HoTT.Basics.Equivalences
  HoTT.Types.Prod
  HoTT.HIT.Truncations
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.interfaces.ua_congruence
  HoTT.Classes.theory.ua_homomorphism
  HoTT.Classes.theory.ua_quotient_algebra.

Import algebra_notations ne_list.notations quotient_algebra_notations.

Close Scope mc_scope.
Open Scope list_scope.

Section hom_term_algebra.
  Context
    {σ : Signature}
    {X : Carriers σ}
    {A : Algebra σ}
    (f : ∀ s, X s → A s).

  Lemma oppreserving_map_term_algebra
    {w : SymbolType σ}
    (α : Operation A w)
    (β : ProdTermAlgebra X (dom_symboltype w)
         → TermAlgebra X (cod_symboltype w))
    (p : ∀ a, map_term_algebra f _ (β a)
              = ap_operation α (map_prod_term_algebra f a))
    : OpPreserving (map_term_algebra f)
        (operation_prod_term_algebra X β) α.
  Proof.
    induction w.
    - apply p.
    - intro x. apply IHw. intro a. apply p.
  Defined.

  Global Instance is_homomorphism_map_term_algebra
    : IsHomomorphism (map_term_algebra f).
  Proof.
    intro u. by apply oppreserving_map_term_algebra.
  Defined.

  Definition hom_term_algebra : Homomorphism (TermAlgebra X) A
    := BuildHomomorphism (map_term_algebra f).

End hom_term_algebra.

Section compose_map_term_algebra.
  Context `{Funext}
    {σ} {X Y : Carriers σ} {A : Algebra σ}
    (g : ∀ s, X s → A s) (f : ∀ s, Y s → TermAlgebra X s).

  Fixpoint path_compose_map_term_algebra {s : Sort σ} (x : TermAlgebra Y s)
    : map_term_algebra g s (map_term_algebra f s x)
      = map_term_algebra (λ (t : Sort σ) (y : Y t), map_term_algebra g t (f t y)) s x
    := match x with
       | var_term_algebra _ _ => idpath
       | op_term_algebra u p =>
        path_homomorphism_ap_operation (map_term_algebra g) u (map_prod_term_algebra f p)
        @ ap (ap_operation (u^^A)) (path_compose_prod_term_algebra p)
       end
  with path_compose_prod_term_algebra {w : list (Sort σ)} (p : ProdTermAlgebra Y w)
    : map_family_prod (map_term_algebra g) (map_prod_term_algebra f p)
      = map_prod_term_algebra (λ t y, map_term_algebra g t (f t y)) p
    := match p with
       | nil_prod_term_algebra => idpath
       | cons_prod_term_algebra s w a p =>
          path_prod' (path_compose_map_term_algebra a) (path_compose_prod_term_algebra p)
       end.
End compose_map_term_algebra.

Definition inv_hom_term_algebra {σ : Signature} {X : Carriers σ} {A : Algebra σ}
  (f : Homomorphism (TermAlgebra X) A) : ∀ s, X s → A s
  := λ s x, f s (var_term_algebra X x).

Section ump_term_algebra.
  Context `{Funext}
    {σ : Signature}
    (X : Carriers σ)
    (A : Algebra σ) `{IsHSetAlgebra A}.

  Fixpoint sect_inv_hom_term_algebra' (f : Homomorphism (TermAlgebra X) A)
    {s : Sort σ} (a : TermAlgebra X s)
    : hom_term_algebra (inv_hom_term_algebra f) s a = f s a
    := match a with
       | var_term_algebra s x => idpath
       | op_term_algebra u p =>
          transport (λ z, _ = f _ z)
            (compute_ap_operation_term_algebra X u p)
            (transport (λ q, ap_operation (u^^A) q = f _ _)
              (sect_inv_prod_hom_term_algebra' f p)^
              (path_homomorphism_ap_operation f u (family_prod_prod_term_algebra p))^)
       end
    with sect_inv_prod_hom_term_algebra' (f : Homomorphism (TermAlgebra X) A)
      {w : list (Sort σ)} (p : ProdTermAlgebra X w)
      : map_prod_term_algebra (inv_hom_term_algebra f) p
        = map_family_prod f (family_prod_prod_term_algebra p)
      := match p with
         | nil_prod_term_algebra => idpath
         | cons_prod_term_algebra s w a p =>
            path_prod' (sect_inv_hom_term_algebra' f a) (sect_inv_prod_hom_term_algebra' f p)
         end.

  Lemma sect_inv_hom_term_algebra
    : Sect (@inv_hom_term_algebra σ X A) (@hom_term_algebra σ X A).
  Proof.
    intro f.
    apply path_hset_homomorphism.
    funext s a.
    apply sect_inv_hom_term_algebra'.
  Defined.

  Lemma sect_hom_term_algebra
    : Sect (@hom_term_algebra σ X A) (@inv_hom_term_algebra σ X A).
  Proof.
    intro f. by funext s a.
  Defined.

  Global Instance isequiv_hom_term_algebra : IsEquiv (@hom_term_algebra σ X A).
  Proof.
    serapply isequiv_adjointify.
    - exact inv_hom_term_algebra.
    - apply sect_inv_hom_term_algebra.
    - apply sect_hom_term_algebra.
  Defined.

  Theorem ump_term_algebra
    : (∀ s, X s → A s) <~> Homomorphism (TermAlgebra X) A.
  Proof.
    exact (BuildEquiv _ _ (@hom_term_algebra σ X A) _).
  Defined.
End ump_term_algebra.

Inductive RelFreeEquations' {σ : Signature} (A : Algebra σ)
  {I : Type} (e : SyntacticEquations σ I) : ∀ s, A s → A s → Type :=
  | rel_free_equations :
      ∀ (i:I) (j : ∀ t, vars_syntactic_equation (e i) t → A t),
        RelFreeEquations' A e
          (sort_syntactic_equation (e i))
          (hom_term_algebra j _ (left_syntactic_equation (e i)))
          (hom_term_algebra j _ (right_syntactic_equation (e i)))
  | reflexive_rel_free_equations :
      ∀ s (x : A s), RelFreeEquations' A e s x x
  | symmetric_rel_free_equations :
      ∀ s (x y : A s), RelFreeEquations' A e s x y → RelFreeEquations' A e s y x
  | transitive_rel_free_equations :
      ∀ s (x y z : A s),
      RelFreeEquations' A e s x y →
      RelFreeEquations' A e s y z →
      RelFreeEquations' A e s x z
  | congruence_rel_free_equations :
      ∀ (u : Symbol σ) (a b : FamilyProd A (dom_symboltype (σ u))),
      for_all_2_family_prod_inductive A A (RelFreeEquations' A e) a b →
      RelFreeEquations' A e _ (ap_operation (u^^A) a) (ap_operation (u^^A) b).

Definition RelFreeEquations {σ} (A : Algebra σ) {I : Type}
  (e : SyntacticEquations σ I) (s : Sort σ) (x y : A s)
  : hProp
  := BuildhProp (Trunc -1 (RelFreeEquations' A e s x y)).

Lemma equiv_rel_rel_free_equations {σ} (A : Algebra σ)
  {I : Type} (e : SyntacticEquations σ I) (s : Sort σ)
  : EquivRel (RelFreeEquations A e s).
Proof.
  constructor.
  - intro x. apply tr. constructor.
  - intros x y g.
    strip_truncations.
    apply tr.
    constructor.
    assumption.
  - intros x y z g h.
    strip_truncations.
    apply tr.
    apply (transitive_rel_free_equations A e s x y z); assumption.
Defined.

Lemma ops_compatible_rev_free_equations `{Funext} {σ} (A : Algebra σ)
  {I : Type} (e : SyntacticEquations σ I)
  : OpsCompatible A (λ (s : Sort σ) (x y : A s), RelFreeEquations A e s x y).
Proof.
  intros u a b h.
  apply (Trunc_rec_for_all_2_family_prod A A (RelFreeEquations' A e) _ a b).
  - assumption.
  - intro h'.
    apply tr.
    apply congruence_rel_free_equations.
    apply for_all_2_family_prod_inductive_for_all_2_family_prod.
    assumption.
Defined.

Global Instance is_congruence_rel_free_equations `{Funext}
  {σ} (A : Algebra σ) {I : Type} (e : SyntacticEquations σ I)
  : IsCongruence A (RelFreeEquations A e).
Proof.
  constructor.
  - intros; exact _.
  - apply equiv_rel_rel_free_equations.
  - apply ops_compatible_rev_free_equations.
Defined.

Definition FreeAlgebra `{Funext} {σ} (X : Carriers σ)
  {I : Type} (e : SyntacticEquations σ I)
  := TermAlgebra X / RelFreeEquations (TermAlgebra X) e.

Lemma respect_rel_free_equations_hom_term_algebra {σ : Signature}
  {I : Type} (e : SyntacticEquations σ I)
  {X : Carriers σ} {A : Algebra σ} `{IsHSetAlgebra A} `{!IsEquationalTheory A e}
  (f : ∀ s, X s → A s)
  : ∀ s (x y : TermAlgebra X s), RelFreeEquations (TermAlgebra X) e s x y →
    hom_term_algebra f s x = hom_term_algebra f s y.
Proof.
  intros s x y r.
  strip_truncations.
  induction r.
  - cbn in *.
    pose proof equational_theory_laws as E.
    rewrite path_compose_map_term_algebra.
    rewrite path_compose_map_term_algebra.
    apply E.
  - reflexivity.
  - now symmetry.
  - now transitivity (hom_term_algebra f s y).
  - rewrite path_homomorphism_ap_operation; [| exact _].
    rewrite path_homomorphism_ap_operation; [| exact _].
    admit. (* Follows from induction hypothesis!
              Need to change RelFreeEquations' *)
Admitted.

(* Use quotient UMP to obtain a map Homomorphism (FreeAlgebra X e) A. *)

Definition hom_free_algebra `{Funext} {σ} (X : Carriers σ)
  {I : Type} (e : SyntacticEquations σ I)
  {A : Algebra σ} (f : ∀ s, X s → A s)
  : Homomorphism (FreeAlgebra X e) A
  := ...
