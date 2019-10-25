Require Import
  HoTT.Basics.Equivalences
  HoTT.Types.Bool
  HoTT.Types.Forall
  HoTT.Types.Sigma
  HoTT.Types.Prod
  HoTT.Classes.interfaces.ua_equational_theory
  HoTT.Classes.theory.ua_homomorphism.

Import algebra_notations ne_list.notations.

(** The following section defines product algebra [ProdAlgebra].
    Section [bin_prod_algebra] specialises the definition to
    binary product algebra. *)

Section prod_algebra.
  Context `{Funext} {σ : Signature} (I : Type) (A : I → Algebra σ).

  Definition carriers_prod_algebra : Carriers σ
    := λ (s : Sort σ), ∀ (i:I), A i s.

  Fixpoint op_prod_algebra (w : SymbolType σ)
      : (∀ i, Operation (A i) w) →
        Operation carriers_prod_algebra w :=
    match w return (∀ i, Operation (A i) w) →
                    Operation carriers_prod_algebra w
    with
    | [:_:] => idmap
    | _ ::: g => λ f p, op_prod_algebra g (λ i, f i (p i))
    end.

  Definition ops_prod_algebra (u : Symbol σ)
    : Operation carriers_prod_algebra (σ u)
    := op_prod_algebra (σ u) (λ (i:I), u ^^ A i).

  Definition ProdAlgebra : Algebra σ
    := BuildAlgebra carriers_prod_algebra ops_prod_algebra.

  Global Instance trunc_prod_algebra {n : trunc_index}
    `{!∀ i, IsTruncAlgebra n (A i)}
    : IsTruncAlgebra n ProdAlgebra.
  Proof.
    intro s. exact _.
  Qed.
End prod_algebra.

Section path_ap_operation_prod_algebra.
  Context  {σ} (I : Type) (A : I → Algebra σ).

  Lemma path_ap_operation_op_prod_algebra {w : SymbolType σ}
    (α : ∀ i, Operation (A i) w)
    (a : FamilyProd (ProdAlgebra I A) (dom_symboltype w)) (i : I)
    : ap_operation (op_prod_algebra I A w α) a i
      = ap_operation (α i)
          (map_family_prod (λ s (p : ProdAlgebra I A s), p i) a).
  Proof.
    induction w.
    - reflexivity.
    - apply IHw.
  Defined.

  Lemma path_ap_operation_prod_algebra (u : Symbol σ)
    (a : FamilyProd (ProdAlgebra I A) (dom_symboltype (σ u))) (i : I)
    : ap_operation (u ^^ ProdAlgebra I A) a i
      = ap_operation (u ^^ A i)
          (map_family_prod (λ s (p : ProdAlgebra I A s), p i) a).
  Proof.
    apply (path_ap_operation_op_prod_algebra (λ i, u ^^ A i)).
  Defined.
End path_ap_operation_prod_algebra.

Section path_map_term_algebra_prod_algebra.
  Context
    {σ} (I : Type) (A : I → Algebra σ) (X : Carriers σ)
    (f : forall s : Sort σ, X s → ProdAlgebra I A s).

  Fixpoint path_map_term_algebra_prod_algebra (s : Sort σ)
    (x : TermAlgebra X s) (i : I)
    : map_term_algebra f s x i
      = map_term_algebra (λ s n, f s n i) s x
    := match x with
       | var_term_algebra s x => idpath
       | op_term_algebra u p =>
          path_ap_operation_prod_algebra I A u _ i
          @ ap (ap_operation _) (path_map_prod_term_algebra_prod_algebra p i)
       end
  with path_map_prod_term_algebra_prod_algebra {w : list (Sort σ)}
    (p : ProdTermAlgebra X w) (i : I)
    : map_family_prod (λ s (p : ProdAlgebra I A s), p i) (map_prod_term_algebra f p)
      = map_prod_term_algebra (λ s n, f s n i) p
    := match p with
       | nil_prod_term_algebra => idpath
       | cons_prod_term_algebra s w x p =>
          path_prod'
            (path_map_term_algebra_prod_algebra s x i)
            (path_map_prod_term_algebra_prod_algebra p i)
       end.
End path_map_term_algebra_prod_algebra.

Section equational_theory_prod_algebra.
  Context `{Funext} {σ : Signature} (I : Type) (A : I → Algebra σ)
          (J : Type) (e : SyntacticEquations σ J)
          `{∀ i, IsEquationalTheory (A i) e}.

  Global Instance equational_theory_prod_algebra
    : IsEquationalTheory (ProdAlgebra I A) e.
  Proof.
    intros j a.
    funext i.
    set (IsE := _ : IsEquationalTheory (A i) e).
    set (E := equational_theory_laws j).
    clearbody E.
    destruct (e j) as [N [s [x y]]].
    exact (path_map_term_algebra_prod_algebra I A N _ _ _ i
           @ E _
           @ (path_map_term_algebra_prod_algebra I A N _ _ _ i)^).
  Defined.
End equational_theory_prod_algebra.

(** The next section defines the product projection homomorphisms. *)

Section hom_proj_prod_algebra.
  Context `{Funext} {σ : Signature} (I : Type) (A : I → Algebra σ).

  Definition def_proj_prod_algebra (i:I) (s : Sort σ) (c : ProdAlgebra I A s)
    : A i s
    := c i.

  Lemma oppreserving_proj_prod_algebra {w : SymbolType σ}
    (i : I) (v : ∀ i : I, Operation (A i) w) (α : Operation (A i) w)
    (P : v i = α)
    : OpPreserving (def_proj_prod_algebra i)
        (op_prod_algebra I A w v) α.
  Proof.
    induction w.
    - exact P.
    - intro p. apply (IHw (λ i, v i (p i)) (α (p i))). f_ap.
  Defined.

  Global Instance is_homomorphism_proj_prod_algebra (i:I)
    : IsHomomorphism (def_proj_prod_algebra i).
  Proof.
    intro u.
    by apply oppreserving_proj_prod_algebra.
  Defined.

  Definition hom_proj_prod_algebra (i : I)
    : Homomorphism (ProdAlgebra I A) (A i)
    := BuildHomomorphism (def_proj_prod_algebra i).

End hom_proj_prod_algebra.

(** The product algebra univarsal mapping property [ump_prod_algebra]. *)

Section ump_prod_algebra.
  Context
    `{Funext}
    {σ : Signature}
    (I : Type)
    (A : I → Algebra σ)
    (C : Algebra σ).

  Definition hom_prod_algebra_mapout
    (f : Homomorphism C (ProdAlgebra I A)) (i:I)
    : Homomorphism C (A i)
    := hom_compose (hom_proj_prod_algebra I A i) f.

  Definition def_prod_algebra_mapin (f : ∀ (i:I) s, C s → A i s)
    : ∀ (s : Sort σ) , C s → ProdAlgebra I A s
    := λ (s : Sort σ) (x : C s) (i : I), f i s x.

  Lemma oppreserving_prod_algebra_mapin {w : SymbolType σ}
    (f : ∀ (i:I) s, C s → A i s)
    (α : ∀ (i:I), Operation (A i) w) (β : Operation C w)
    (P : ∀ (i:I), OpPreserving (f i) β (α i))
    : OpPreserving (def_prod_algebra_mapin f) β
        (op_prod_algebra I A w (λ i, α i)).
  Proof.
    induction w.
    - funext i. apply P.
    - intro x. apply IHw. intro i. apply P.
  Defined.

  Global Instance is_homomorphism_prod_algebra_mapin
    (f : ∀ (i:I), Homomorphism C (A i))
    : IsHomomorphism (def_prod_algebra_mapin f).
  Proof.
    intro u.
    apply oppreserving_prod_algebra_mapin.
    intro i.
    apply f.
  Defined.

  Definition hom_prod_algebra_mapin (f : ∀ i, Homomorphism C (A i))
    : Homomorphism C (ProdAlgebra I A)
    := BuildHomomorphism (def_prod_algebra_mapin f).

  (** Given a family of homomorphisms [h : ∀ (i:I), Homomorphism C (A i)]
      there is a unique homomorphism [f : Homomorphism C (ProdAlgebra I A)]
      such that [h i = hom_compose (pr i) f], where

      <<
        pr i = hom_proj_prod_algebra I A i
      >>

      is the ith projection homomorphism. *)

 Lemma ump_prod_algebra `{!∀ i, IsHSetAlgebra (A i)}
   : (∀ (i:I), Homomorphism C (A i)) <~> Homomorphism C (ProdAlgebra I A).
  Proof.
    apply (equiv_adjointify hom_prod_algebra_mapin hom_prod_algebra_mapout).
    - intro f. by apply path_hset_homomorphism.
    - intro f. funext i. by apply path_hset_homomorphism.
  Defined.
End ump_prod_algebra.

(** Binary product algebra. *)

Section bin_prod_algebra.
  Context `{Funext} {σ : Signature} (A B : Algebra σ).

  Definition bin_prod_algebras (b:Bool) : Algebra σ
    := if b then B else A.

  Global Instance trunc_bin_prod_algebras {n : trunc_index}
    `{!IsTruncAlgebra n A} `{!IsTruncAlgebra n B}
    : ∀ (b:Bool), IsTruncAlgebra n (bin_prod_algebras b).
  Proof.
    intros []; exact _.
  Qed.

  Definition BinProdAlgebra : Algebra σ :=
    ProdAlgebra Bool bin_prod_algebras.

  Definition fst_prod_algebra : Homomorphism BinProdAlgebra A
    := hom_proj_prod_algebra Bool bin_prod_algebras false.

  Definition snd_prod_algebra : Homomorphism BinProdAlgebra B
    := hom_proj_prod_algebra Bool bin_prod_algebras true.
End bin_prod_algebra.

Module prod_algebra_notations.

  Global Notation "A × B" := (BinProdAlgebra A B)
                             (at level 40, left associativity)
                             : Algebra_scope.

End prod_algebra_notations.

Import prod_algebra_notations.

(** Specialisation of the product algebra univarsal mapping property
    to binary product. *)

Section ump_bin_prod_algebra.
  Context
    `{Funext}
    {σ : Signature}
    (A B C : Algebra σ)
    `{!IsHSetAlgebra A} `{!IsHSetAlgebra B}.

 Lemma ump_bin_prod_algebra
   : Homomorphism C A * Homomorphism C B <~> Homomorphism C (A × B).
  Proof.
    set (k := λ (b:Bool), Homomorphism C (bin_prod_algebras A B b)).
    exact (equiv_compose
            (ump_prod_algebra Bool (bin_prod_algebras A B) C)
            (equiv_bool_forall_prod k)^-1).
  Defined.
End ump_bin_prod_algebra.
