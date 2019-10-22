Require Export HoTT.Classes.interfaces.ua_equational_theory.

Require Import
  HoTT.Basics.Equivalences
  HoTT.Types.Prod
  HoTT.Types.Sigma
  HoTT.Types.Universe
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

  Definition inv_hom_term_algebra (f : Homomorphism (TermAlgebra X) A)
    : ∀ s, X s → A s
    := λ s x, f s (var_term_algebra X x).

End hom_term_algebra.

Section compose_map_term_algebra.
  Context `{Funext}
    {σ} {X Y : Carriers σ} {A : Algebra σ}
    (g : ∀ s, X s → A s) (f : ∀ s, Y s → TermAlgebra X s).

  Fixpoint path_compose_map_term_algebra {s : Sort σ} (x : TermAlgebra Y s)
    : map_term_algebra g s (map_term_algebra f s x)
      = map_term_algebra (λ t y, map_term_algebra g t (f t y)) s x
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
      ForAllRelFreeEquations' A e _ a b →
      RelFreeEquations' A e _ (ap_operation (u^^A) a) (ap_operation (u^^A) b)
with ForAllRelFreeEquations' {σ : Signature} (A : Algebra σ)
  {I : Type} (e : SyntacticEquations σ I)
  : ∀ w, FamilyProd A w → FamilyProd A w → Type :=
  | nil_for_all_rel_free_equations :
      ForAllRelFreeEquations' A e nil tt tt
  | cons_for_all_rel_free_equations :
      ∀ s (x y : A s) w a b,
      RelFreeEquations' A e s x y →
      ForAllRelFreeEquations' A e w a b →
      ForAllRelFreeEquations' A e (s :: w) (x, a) (y, b).

Global Arguments ForAllRelFreeEquations' {σ} A {I} e {w}.
Global Arguments cons_for_all_rel_free_equations {σ} A {I} e {s} x y {w a b}.

(** Conversion from [for_all_2_family_prod] to [ForAllRelFreeEquations]. *)

Fixpoint for_all_rel_equations_for_all_2_family_prod {σ} (A : Algebra σ)
  {I : Type} (e : SyntacticEquations σ I) {w : list (Sort σ)}
  : ∀ (a b : FamilyProd A w),
      for_all_2_family_prod A A (RelFreeEquations' A e) a b
      → ForAllRelFreeEquations' A e a b
  := match w with
     | nil => λ 'tt 'tt _, nil_for_all_rel_free_equations A e
     | s :: w' => λ '(x,a) '(y,b) '(r,h),
        cons_for_all_rel_free_equations A e x y r
          (for_all_rel_equations_for_all_2_family_prod A e a b h)
     end.

(** Conversion from [ForAllRelFreeEquations'] to [for_all_2_family_prod]. *)

Fixpoint for_all_2_family_prod_for_all_rel_free_equations {σ} (A : Algebra σ)
  {I : Type} (e : SyntacticEquations σ I) {w : list (Sort σ)}
  (a b : FamilyProd A w) (h : ForAllRelFreeEquations' A e a b)
  : for_all_2_family_prod A A (RelFreeEquations' A e) a b
  := match h with
     | nil_for_all_rel_free_equations => Logic.I
     | cons_for_all_rel_free_equations s x y w' a' b' r h' =>
        (r, for_all_2_family_prod_for_all_rel_free_equations A e a' b' h')
     end.

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
    apply for_all_rel_equations_for_all_2_family_prod.
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

Section respect_rel_free_equations_hom_term_algebra.
  Context {σ : Signature} {X : Carriers σ} {A : Algebra σ}
  {I : Type} (e : SyntacticEquations σ I) `{!IsEquationalTheory A e}
  (f : ∀ s, X s → A s).

  Fixpoint respect_rel_free_equations_hom_term_algebra' (s : Sort σ)
    (x y : TermAlgebra X s) (r : RelFreeEquations' (TermAlgebra X) e s x y)
    : hom_term_algebra f s x = hom_term_algebra f s y :=
    match r with
    | rel_free_equations i j =>
        path_compose_map_term_algebra f j _
        @ ltac:(apply equational_theory_laws)
        @ (path_compose_map_term_algebra f j _)^
    | reflexive_rel_free_equations s x => idpath
    | symmetric_rel_free_equations s x y r' =>
        (respect_rel_free_equations_hom_term_algebra' _ x y r')^
    | transitive_rel_free_equations s x z y r' r'' =>
        respect_rel_free_equations_hom_term_algebra' _ x z r'
        @ respect_rel_free_equations_hom_term_algebra' _ z y r''
    | congruence_rel_free_equations u a b R =>
        path_homomorphism_ap_operation (hom_term_algebra f) u a
        @ ap (ap_operation (u^^A))
             (respect_for_all_rel_free_equations_hom_term_algebra' a b R)
        @ (path_homomorphism_ap_operation (hom_term_algebra f) u b)^
    end
  with respect_for_all_rel_free_equations_hom_term_algebra' {w}
    (a b : FamilyProd (TermAlgebra X) w)
    (R : ForAllRelFreeEquations' (TermAlgebra X) e a b)
    : map_family_prod (hom_term_algebra f) a
      = map_family_prod (hom_term_algebra f) b :=
    match R with
    | nil_for_all_rel_free_equations => idpath
    | cons_for_all_rel_free_equations s x y w' a' b' r R' =>
        path_prod'
          (respect_rel_free_equations_hom_term_algebra' _ x y r)
          (respect_for_all_rel_free_equations_hom_term_algebra' a' b' R')
    end.

  Lemma respect_rel_free_equations_hom_term_algebra `{IsHSetAlgebra A}
    (s : Sort σ) (x y : TermAlgebra X s)
    (r : RelFreeEquations (TermAlgebra X) e s x y)
    : hom_term_algebra f s x = hom_term_algebra f s y.
  Proof.
    strip_truncations.
    exact (respect_rel_free_equations_hom_term_algebra' s x y r).
  Defined.
End respect_rel_free_equations_hom_term_algebra.

Section ump_free_algebra.
  Context
    `{Univalence} {σ : Signature}
    {X : Carriers σ} (A : Algebra σ) `{IsHSetAlgebra A}
    {I : Type} (e : SyntacticEquations σ I) `{!IsEquationalTheory A e}.

  Definition map_term_algebra_respect (f : ∀ s, X s → A s)
    : {f : Homomorphism (TermAlgebra X) A
      | ∀ s x y, RelFreeEquations (TermAlgebra X) e s x y → f s x = f s y}
    := (hom_term_algebra f; respect_rel_free_equations_hom_term_algebra e f).

  Definition inv_map_term_algebra_respect
    (F : {f : Homomorphism (TermAlgebra X) A
         | ∀ s x y, RelFreeEquations (TermAlgebra X) e s x y → f s x = f s y})
    : ∀ s, X s → A s
    := inv_hom_term_algebra F.1.

  Lemma sect_map_term_algebra_respect
    : Sect map_term_algebra_respect inv_map_term_algebra_respect.
  Proof.
    apply sect_hom_term_algebra.
  Defined.

  Lemma sect_inv_map_term_algebra_respect
    : Sect inv_map_term_algebra_respect map_term_algebra_respect.
  Proof.
    intros [f F].
    apply path_sigma_hprop.
    now apply sect_inv_hom_term_algebra.
  Defined.

  Lemma equiv_respect_rel_free_equations_hom_term_algebra
    : (∀ s, X s → A s)
        <~>
      {f : Homomorphism (TermAlgebra X) A
         | ∀ s x y, RelFreeEquations (TermAlgebra X) e s x y → f s x = f s y}.
  Proof.
    serapply equiv_adjointify.
    - exact map_term_algebra_respect.
    - exact inv_map_term_algebra_respect.
    - exact sect_inv_map_term_algebra_respect.
    - exact sect_map_term_algebra_respect.
  Defined.

  Theorem ump_free_algebra
    : (∀ s, X s → A s) <~> Homomorphism (FreeAlgebra X e) A.
  Proof.
    exact (equiv_compose (ump_quotient_algebra _) equiv_respect_rel_free_equations_hom_term_algebra).
  Defined.

End ump_free_algebra.
