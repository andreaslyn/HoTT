Require Export HoTT.Classes.interfaces.ua_algebra.

Import ne_list.notations algebra_notations.

Inductive CarriersTermAlgebra {σ} (X : Carriers σ) : Carriers σ :=
  | var_term_algebra : ∀ s, X s → CarriersTermAlgebra X s
  | op_term_algebra : ∀ (u : Symbol σ),
      ProdTermAlgebra X (dom_symboltype (σ u)) →
      CarriersTermAlgebra X (cod_symboltype (σ u))
with ProdTermAlgebra {σ} (X : Carriers σ) : list (Sort σ) → Type :=
  | nil_prod_term_algebra : ProdTermAlgebra X nil
  | cons_prod_term_algebra : ∀ s w,
      CarriersTermAlgebra X s → ProdTermAlgebra X w → ProdTermAlgebra X (s :: w).

Arguments var_term_algebra {σ} X {s}.
Arguments op_term_algebra {σ} X {u}.

Arguments cons_prod_term_algebra {σ} X {s w}.

Fixpoint operation_prod_term_algebra {σ} (X : Carriers σ) {w : SymbolType σ}
  : (ProdTermAlgebra X (dom_symboltype w) → CarriersTermAlgebra X (cod_symboltype w))
    → Operation (CarriersTermAlgebra X) w
  := match w with
     | [:s:] => λ α, α (nil_prod_term_algebra X)
     | s ::: w' => λ α x, 
        operation_prod_term_algebra X (λ p, α (cons_prod_term_algebra X x p))
     end.

Definition operations_term_algebra {σ : Signature} (X : Carriers σ) (u : Symbol σ)
  : Operation (CarriersTermAlgebra X) (σ u)
  := operation_prod_term_algebra X (op_term_algebra X).

Definition TermAlgebra {σ : Signature} (X : Carriers σ) : Algebra σ
  := BuildAlgebra (CarriersTermAlgebra X) (operations_term_algebra X).

Fixpoint family_prod_prod_term_algebra  {σ} {X : Carriers σ}
  {w : list (Sort σ)} (p : ProdTermAlgebra X w)
  : FamilyProd (TermAlgebra X) w
  := match p with
     | nil_prod_term_algebra => tt
     | cons_prod_term_algebra s w' a p' =>
        (a, family_prod_prod_term_algebra p')
     end.

Lemma path_prod_term_algebra {σ} (X : Carriers σ) {w : list (Sort σ)}
  (p : ProdTermAlgebra X w)
  : list_rect (λ w, ProdTermAlgebra X w → Type)
      (λ p, p = nil_prod_term_algebra X)
      (λ s w' _ p, ∃ x p', p = cons_prod_term_algebra X x p')
      w p.
Proof. destruct p.
  - cbn. reflexivity.
  - cbn. exists c, p. reflexivity.
Defined.

Lemma path_nil_prod_term_algebra {σ} (X : Carriers σ)
  (p : ProdTermAlgebra X nil) : p = nil_prod_term_algebra X.
Proof.
  apply (path_prod_term_algebra X p).
Defined.

Lemma path_cons_prod_term_algebra {σ} (X : Carriers σ)
  {s : Sort σ} {w : list (Sort σ)} (p : ProdTermAlgebra X (s :: w))
  : ∃ x q, p = cons_prod_term_algebra X x q.
Proof.
  apply (path_prod_term_algebra X p).
Defined.

Lemma compute_ap_operation_term_algebra' {σ} (X : Carriers σ)
  {w : SymbolType σ} (p : ProdTermAlgebra X (dom_symboltype w))
  (β : ProdTermAlgebra X (dom_symboltype w) → TermAlgebra X (cod_symboltype w))
  : ap_operation (operation_prod_term_algebra X β) (family_prod_prod_term_algebra p)
    = β p.
Proof.
  induction w; cbn.
  - by destruct (path_nil_prod_term_algebra X p).
  - destruct (path_cons_prod_term_algebra X p) as [x [p' q]].
    destruct q^.
    apply IHw.
Defined.

Lemma compute_ap_operation_term_algebra {σ} (X : Carriers σ) (u : Symbol σ)
  (p : ProdTermAlgebra X (dom_symboltype (σ u)))
  : ap_operation (u ^^ TermAlgebra X) (family_prod_prod_term_algebra p)
    = op_term_algebra X p.
Proof.
  apply compute_ap_operation_term_algebra'.
Defined.

Definition SyntacticEquation (σ : Signature)
  := {N : Carriers σ | {s : Sort σ | TermAlgebra N s * TermAlgebra N s}}.

Definition vars_syntactic_equation {σ} (e : SyntacticEquation σ)
  : Carriers σ
  := e.1.

Definition sort_syntactic_equation {σ} (e : SyntacticEquation σ)
  : Sort σ
  := e.2.1.

Definition left_syntactic_equation {σ} (e : SyntacticEquation σ)
  : TermAlgebra (vars_syntactic_equation e) (sort_syntactic_equation e)
  := fst e.2.2.

Definition right_syntactic_equation {σ} (e : SyntacticEquation σ)
  : TermAlgebra (vars_syntactic_equation e) (sort_syntactic_equation e)
  := snd e.2.2.

Definition SyntacticEquations (σ : Signature) (I : Type)
  := I -> SyntacticEquation σ.

Fixpoint map_term_algebra {σ} {X : Carriers σ} {A : Algebra σ}
  (f : ∀ s, X s → A s) (s : Sort σ) (a : TermAlgebra X s) : A s
  := match a with
     | var_term_algebra s x => f s x
     | op_term_algebra u p => ap_operation (u^^A) (map_prod_term_algebra f p)
     end
with map_prod_term_algebra {σ} {X : Carriers σ} {A : Algebra σ}
  (f : ∀ s, X s → A s) {w : list (Sort σ)} (p : ProdTermAlgebra X w)
  : FamilyProd A w
  := match p with
     | nil_prod_term_algebra => tt
     | cons_prod_term_algebra s w x p =>
        (map_term_algebra f s x, map_prod_term_algebra f p)
     end.

Definition SemanticEquation {σ : Signature} (A : Algebra σ) (e : SyntacticEquation σ)
  := match e with
     | (N; (t; (a, b))) =>
         ∀ (f : ∀ s, N s -> A s), map_term_algebra f t a = map_term_algebra f t b
     end.

Definition SemanticEquations {σ : Signature} (A : Algebra σ)
  {I : Type} (e : SyntacticEquations σ I)
  := ∀ (i:I), SemanticEquation A (e i).

Class IsEquationalTheory {σ : Signature} (A : Algebra σ)
  {I : Type} (e : SyntacticEquations σ I)
  := equational_theory_laws : SemanticEquations A e.

Record EquationalTheory (σ : Signature) :=
  { algebra_equational_theory : Algebra σ
  ; index_equational_theory : Type
  ; syntax_equational_theory : SyntacticEquations σ index_equational_theory
  ; is_equational_equational_theory
      : IsEquationalTheory algebra_equational_theory syntax_equational_theory }.

Global Coercion algebra_equational_theory : EquationalTheory >-> Algebra.

Global Existing Instance is_equational_equational_theory.
