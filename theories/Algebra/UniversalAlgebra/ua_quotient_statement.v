Require Import
  HoTT.Algebra.UniversalAlgebra.ua_homomorphism
  HoTT.Algebra.UniversalAlgebra.ua_congruence.

Definition QuotientAlgebraStatement : Type :=
  ∀ σ (A : Algebra σ) (Φ : ∀ s, Relation (A s)) (isC : IsCongruence A Φ),
  ∃ (Q : Algebra σ) (q : Homomorphism A Q),
  ∀ (B : Algebra σ),
  ∃ (e : Homomorphism Q B <~> {f : Homomorphism A B | HomCompatible Φ f}),
  ∀ (h : Homomorphism Q B), (e h).1 = hom_compose h q.
