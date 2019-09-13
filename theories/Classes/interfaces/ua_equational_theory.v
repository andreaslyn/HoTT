Require Import HoTT.Classes.interfaces.ua_algebra.

Import ne_list.notations algebra_notations.

Inductive SyntacticTerm {σ : Signature} : SymbolType σ → Type :=
  | syntactic_op : ∀ (u : Symbol σ), SyntacticTerm (σ u)
  | syntactic_var : ∀ (s : Sort σ), nat → SyntacticTerm [:s:]
  | syntactic_app : ∀ (s : Sort σ) (w : SymbolType σ),
                 SyntacticTerm (s ::: w) → SyntacticTerm [:s:] → SyntacticTerm w.

Arguments syntactic_app {σ s w}.

Definition SyntacticEquation (σ : Signature)
  := ∃ (w : SymbolType σ), SyntacticTerm w * SyntacticTerm w.

Definition SyntacticEquations (σ : Signature) (I : Type)
  := I -> SyntacticEquation σ.

Fixpoint SemanticTerm {σ : Signature} (A : Algebra σ)
  (x : ∀ (s : Sort σ), nat -> A s) {w : SymbolType σ} (a : SyntacticTerm w)
  : Operation A w
  := match a with
     | syntactic_op u => u^^A
     | syntactic_var s n => x s n
     | syntactic_app s w g b => SemanticTerm A x g (SemanticTerm A x b)
     end.

Definition SemanticEquation {σ : Signature} (A : Algebra σ) (e : SyntacticEquation σ)
  := match e with
     | (w; (a, b)) =>
         ∀ (x : ∀ s, nat -> A s), SemanticTerm A x a = SemanticTerm A x b
     end.

Definition SemanticEquations {σ : Signature} (A : Algebra σ)
  {I : Type} (e : SyntacticEquations σ I)
  := ∀ (i:I), SemanticEquation A (e i).

Class IsEquationalTheory {σ : Signature} (A : Algebra σ)
  {I : Type} (e : SyntacticEquations σ I)
  := equational_theory_laws : SemanticEquations A e.

Record AlgebraicTheory (σ : Signature) :=
  { algebraic_theory_algebra : Algebra σ
  ; algebraic_theory_index : Type
  ; algebraic_theory_syntax : SyntacticEquations σ algebraic_theory_index
  ; algebraic_theory_is_equational
      : IsEquationalTheory algebraic_theory_algebra algebraic_theory_syntax }.

Global Coercion algebraic_theory_algebra : AlgebraicTheory >-> Algebra.

Global Existing Instance algebraic_theory_is_equational.
