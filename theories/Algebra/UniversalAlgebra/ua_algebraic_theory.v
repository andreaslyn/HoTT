Require Export HoTT.Algebra.UniversalAlgebra.ua_algebra.

Require Import
  HoTT.Types.Empty
  HoTT.HSet.

Unset Elimination Schemes.

Import algebra_notations.

Inductive CarriersTermAlgebra {σ} (C : Carriers σ) : Carriers σ :=
  | var_term_algebra : ∀ s, C s → CarriersTermAlgebra C s
  | ops_term_algebra : ∀ (u : Symbol σ),
      DomOperation (CarriersTermAlgebra C) (σ u) →
      CodOperation (CarriersTermAlgebra C) (σ u).

Arguments var_term_algebra {σ} {C} {s}.
Arguments ops_term_algebra {σ} {C} {u}.

Scheme CarriersTermAlgebra_ind := Elimination for CarriersTermAlgebra Sort Type.
Arguments CarriersTermAlgebra_ind {σ}.

Definition CarriersTermAlgebra_rect {σ} := @CarriersTermAlgebra_ind σ.

Definition CarriersTermAlgebra_rec {σ : Signature} (C : Carriers σ)
  (P : Sort σ → Type) (vs : ∀ (s : Sort σ), C s → P s)
  (os : ∀ (u : Symbol σ)
          (c : DomOperation (CarriersTermAlgebra C) (σ u)),
        (∀ X : Arity (σ u), P (sorts_dom (σ u) X)) →
        P (sort_cod (σ u)))
  (s : Sort σ) (T : CarriersTermAlgebra C s)
  : P s
  := CarriersTermAlgebra_ind C (fun s _ => P s) vs os s T.

Fixpoint equal_carriers_term_algebra {σ} {C : Carriers σ} {s1 s2 : Sort σ}
  (S : CarriersTermAlgebra C s1) (T : CarriersTermAlgebra C s2) : Type
  := match S, T with
     | var_term_algebra s1 c1, var_term_algebra s2 c2 =>
        {p : s1 = s2 | p # c1 = c2}
     | ops_term_algebra u1 d1, ops_term_algebra u2 d2 =>
        {p : u1 = u2 |
          ∀ X : Arity (σ u1),
          equal_carriers_term_algebra
            (d1 X) (d2 (transport (fun v => Arity (σ v)) p X)) }
     | _, _ => Empty
     end.

Section hset_carriers_term_algebra.
  Context `{Funext} {σ} (C : Carriers σ) `{∀ s, IsHSet (C s)}.

  Definition reflexive_equal_carriers_term_algebra (s : Sort σ)
    : Reflexive (@equal_carriers_term_algebra σ C s s).
  Proof.
    intro S. induction S.
    - by exists idpath.
    - exact (idpath; X).
  Defined.

  Lemma reflexive_equal_carriers_term_algebra_path (s : Sort σ)
    {S T : CarriersTermAlgebra C s} (p : S = T)
    : equal_carriers_term_algebra S T.
  Proof.
    induction p. apply reflexive_equal_carriers_term_algebra.
  Defined.

  Definition is_mere_relation_equal_carriers_term_algebra (s : Sort σ)
    : is_mere_relation (CarriersTermAlgebra C s) equal_carriers_term_algebra.
  Proof.
    intros S.
    induction S; intros []; try exact hprop_Empty.
    - apply Sigma.ishprop_sigma_disjoint. intros. apply hset_path2.
    - apply @Sigma.ishprop_sigma_disjoint.
      + intro p. induction p. apply Forall.trunc_forall.
      + intros. apply hset_path2.
  Defined.

  Lemma path_equal_carriers_term_algebra' {s1 s2 : Sort σ}
    (S : CarriersTermAlgebra C s1) (T : CarriersTermAlgebra C s2)
    (e : equal_carriers_term_algebra S T)
    : ∃ p : s1 = s2, p # S = T.
  Proof.
    generalize dependent s2.
    induction S; intros s2 [] e; (solve [elim e] || destruct e as [p e]).
    - exists p. by induction p, e.
    - induction p. exists idpath. cbn. f_ap. funext a.
      destruct (X a _ (c0 a) (e a)) as [p q].
      by induction (hset_path2 idpath p).
  Defined.

  Lemma path_equal_carriers_term_algebra (s : Sort σ)
    (S T : CarriersTermAlgebra C s)
    (e : equal_carriers_term_algebra S T)
    : S = T.
  Proof.
    destruct (path_equal_carriers_term_algebra' S T e) as [p q].
    by induction (hset_path2 idpath p).
  Defined.

  Global Instance hset_carriers_term_algebra (s : Sort σ)
    : IsHSet (CarriersTermAlgebra C s).
  Proof.
    apply (@ishset_hrel_subpaths _ equal_carriers_term_algebra).
    - apply reflexive_equal_carriers_term_algebra.
    - apply is_mere_relation_equal_carriers_term_algebra; exact _.
    - apply path_equal_carriers_term_algebra.
  Defined.
End hset_carriers_term_algebra.

Lemma isinj_var_term_algebra  {σ} {C : Carriers σ} {s} (x y : C s)
  : var_term_algebra x = var_term_algebra y -> x = y.
Proof.
  intro p.
  apply reflexive_equal_carriers_term_algebra_path in p.
  destruct p as [p1 p2].
  About hset_path2.
  by destruct (hset_path2 p1 idpath)^.
Qed.

Lemma isinj_ops_term_algebra `{Funext} {σ} {C : Carriers σ} {u}
  (a b : DomOperation (CarriersTermAlgebra C) (σ u))
  : ops_term_algebra a = ops_term_algebra b -> a = b.
Proof.
  intro p.
  apply reflexive_equal_carriers_term_algebra_path in p.
  destruct p as [p1 p2].
  destruct (hset_path2 p1 idpath)^.
  funext i.
  apply path_equal_carriers_term_algebra.
  apply p2.
Qed.

Definition map_term_algebra {σ} {C : Carriers σ} (A : Algebra σ)
  (f : ∀ s, C s → A s) (s : Sort σ) (T : CarriersTermAlgebra C s)
  : A s
  := CarriersTermAlgebra_rec C A f (fun u _ r => (u^^A) r) s T.

Definition TermAlgebra `{Funext} {σ} (C : Carriers σ) `{∀ s, IsHSet (C s)}
  : Algebra σ
  := Build_Algebra (CarriersTermAlgebra C) (@ops_term_algebra _ C).

Record Equation {σ : Signature} : Type :=
  Build_Equation
  { context_equation : Carriers σ
  ; hset_context_equation : ∀ s, IsHSet (context_equation s)
  ; sort_equation : Sort σ
  ; left_equation : CarriersTermAlgebra context_equation sort_equation
  ; right_equation : CarriersTermAlgebra context_equation sort_equation }.

Global Arguments Equation : clear implicits.

Global Arguments Build_Equation {σ}
  context_equation {hset_context_equation}.

Global Existing Instance hset_context_equation.

Definition Equations (σ : Signature) (I : Type)
  := I -> Equation σ.

Section InterpEquations.
  Context {σ} (A : Algebra σ).

  Definition InterpEquation (e : Equation σ) : Type
    := ∀ (f : ∀ s, context_equation e s -> A s),
       map_term_algebra A f (sort_equation e) (left_equation e)
       = map_term_algebra A f (sort_equation e) (right_equation e).

  Definition InterpEquations {I : Type} (e : Equations σ I)
    := ∀ (i:I), InterpEquation (e i).

End InterpEquations.

Class IsAlgebraicTheory {σ : Signature}
  (A : Algebra σ) {I : Type} (e : Equations σ I)
  := algebraic_theory_laws : InterpEquations A e.

Record AlgebraicTheory (σ : Signature) :=
  Build_AlgebraicTheory
  { algebra_algebraic_theory : Algebra σ
  ; index_algebraic_theory : Type
  ; equations_algebraic_theory : Equations σ index_algebraic_theory
  ; is_algebraic_algebraic_theory
      : IsAlgebraicTheory algebra_algebraic_theory equations_algebraic_theory }.

Arguments Build_AlgebraicTheory {σ} algebra_algebraic_theory
  {index_algebraic_theory} equations_algebraic_theory {is_algebraic_algebraic_theory}.

Global Coercion algebra_algebraic_theory : AlgebraicTheory >-> Algebra.

Global Existing Instance is_algebraic_algebraic_theory.
