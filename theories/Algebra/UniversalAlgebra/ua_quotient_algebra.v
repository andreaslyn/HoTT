(*
Require Export HoTT.Classes.interfaces.ua_congruence.

Require Import
  HoTT.Basics
  HoTT.Types
  HoTT.HProp
  HoTT.HSet
  HoTT.HProp
  HoTT.HIT.quotient
  HoTT.Truncations
  HoTT.UnivalenceImpliesFunext
  HoTT.Classes.implementations.list
  HoTT.Classes.interfaces.canonical_names
  HoTT.Classes.theory.ua_homomorphism.

Import algebra_notations.

Local Unset Elimination Schemes.

Section quotient_algebra.
  Context `{Funext} {σ : Signature} (A : Algebra σ)
    (Φ : ∀ s, relation (A s)) `{!IsCongruence A Φ}.

  Definition carriers_quotient_algebra (s : Sort σ) : Type
    := quotient (Φ s).

  Definition quotient_class_of (s : Sort σ) (x : A s)
    : carriers_quotient_algebra s
    := class_of (Φ s) x.

  Definition equations_quotient_algebra
    (i : {u : Symbol σ | DomOperation A (σ u)})
    : SyntacticEquation σ :=
    {| context_syntactic_equation := carriers_quotient_algebra
     ; hset_vars_syntactic_equation := _
     ; sort_syntactic_equation := sort_cod (σ i.1)
     ; left_syntactic_equation :=
        (i.1 ^^ TermAlgebra carriers_quotient_algebra)
          (fun X => var_term_algebra carriers_quotient_algebra _
            (quotient_class_of _ (i.2 X)))
     ; right_syntactic_equation :=
        var_term_algebra carriers_quotient_algebra
          (sort_cod (σ i.1)) (quotient_class_of _ ((i.1^^A) i.2))
    |}.

  Definition QuotientAlgebra : Algebra σ :=
    FreeAlgebra carriers_quotient_algebra equations_quotient_algebra.

End quotient_algebra.

Module quotient_algebra_notations.
  Global Notation "A / Φ" := (QuotientAlgebra A Φ)
                             (at level 40, left associativity)
                             : Algebra_scope.

  Global Notation "Φ '.[' x ]" :=
    (var_free_algebra (carriers_quotient_algebra _ Φ)
      (equations_quotient_algebra _ Φ) _ (class_of _ x))
    (at level 3, format "Φ '.[' x ]").
End quotient_algebra_notations.

Import quotient_algebra_notations.

For any algebra A and congruence Φ : ∀ s, relation (A s).
There is a quotient algebra A/Φ, such that
[a] = [a'] iff Φ a a' and
op(u)(fun x => [z x]) = [op(u)(z)], where z : (∀ X : Arity (σ u), A (sorts_dom (σ u) X))

Show that (∀ x:X, Trunc (Y x)) → Trunc(∀ x:X, Y x).

Need Φ a a' := True. Everything is related.
Then A/Φ = Trunc A.
Need op(z) : ∀ x:X, Y x

Lemma compute_op_quotient `{Funext} {σ} (A : Algebra σ)
  (Φ : ∀ s, relation (A s)) `{!IsCongruence A Φ}
  (u : Symbol σ) (a : DomOperation A (σ u))
  : (u ^^ A/Φ) (λ I, Φ.[a I]) = Φ.[(u^^A) a].
Proof.
  cbn.
  apply (@equations_free_algebra _ σ (carriers_quotient_algebra A Φ)
          {u : Symbol σ | DomOperation A (σ u)}
          (equations_quotient_algebra A Φ)
          (u; a)).
Defined.

(** The following section defines the quotient homomorphism
    [hom_quotient : Homomorphism A (A/Φ)]. *)

Section hom_quotient.
  Context `{Funext} {σ} (A : Algebra σ)
    (Φ : ∀ s, relation (A s)) `{!IsCongruence A Φ}.

  Definition def_hom_quotient : ∀ (s : Sort σ), A s → (A/Φ) s :=
    λ s x, Φ.[x].

  Global Instance is_homomorphism_quotient
    : IsHomomorphism def_hom_quotient.
  Proof.
    intros u a. symmetry. apply compute_op_quotient.
  Defined.

  Definition hom_quotient : Homomorphism A (A/Φ)
    := Build_Homomorphism def_hom_quotient.

  Global Instance surjection_quotient `{Funext}
    : ∀ s, IsSurjection
            (var_free_algebra
              (carriers_quotient_algebra A Φ)
              (equations_quotient_algebra A Φ) s).
  Proof.
    intro s. apply Build_IsSurjection. generalize dependent s.
    srefine (CarriersFreeAlgebra_ind (carriers_quotient_algebra A Φ) (equations_quotient_algebra A Φ) (fun s Q => merely (hfiber _ Q)) _ _ _).
    - intros s Q. apply tr. by exists Q.
    - cbn. intros u a h.
      unfold hfiber in *.
      apply tr.
      unshelve esplit.
      + assert (
    forall X : Arity (σ u),
    Trunc (-1)
      (∃ x : carriers_quotient_algebra A Φ (sorts_dom (σ u) X),
       var_free_algebra (carriers_quotient_algebra A Φ)
         (equations_quotient_algebra A Φ) (sorts_dom (σ u) X) x = 
       a X) →
      (∃ x : carriers_quotient_algebra A Φ (sorts_dom (σ u) X),
       var_free_algebra (carriers_quotient_algebra A Φ)
         (equations_quotient_algebra A Φ) (sorts_dom (σ u) X) x = 
       a X)
      ).
      * admit.
      * pose (fun I => X I (h I)) as h'.
    - intros. apply path_ishprop.
  Qed.
End hom_quotient.

















(* OLD: *)

Module carriers_quotient_algebra.

  Private Inductive carriers_quotient_algebra {σ : Signature}
    (A : Algebra σ) (Φ : ∀ s, relation (A s)) : Carriers σ :=
  | class_quotient_algebra :
      ∀ {s : Sort σ}, A s → carriers_quotient_algebra A Φ s
  | ops_quotient_algebra : ∀ (u : Symbol σ),
      DomOperation (carriers_quotient_algebra A Φ) (σ u) →
      CodOperation (carriers_quotient_algebra A Φ) (σ u).

Section context_carriers_quotient_algebra.
  Context {σ : Signature} (A : Algebra σ) (Φ : ∀ s, relation (A s)).

  Local Notation "Ψ '.[' x ]" := (class_quotient_algebra _ Ψ x) (at level 3, format "Ψ '.[' x ]").

  Axiom path_class_quotient_algebra
  : ∀ {s} (x y : A s), Φ s x y → Φ.[x] = Φ.[y].

  Axiom path_ops_quotient_algebra
    : ∀ (u : Symbol σ) (a : DomOperation A (σ u)),
      ops_quotient_algebra A Φ u (λ I, Φ.[a I]) = Φ.[(u^^A) a].

  Axiom hset_quotient_algebra
    : ∀ (s : Sort σ), IsHSet (carriers_quotient_algebra A Φ s).

  Fixpoint carriers_quotient_algebra_ind
    (P : ∀ (s : Sort σ), carriers_quotient_algebra A Φ s -> Type)
    `{∀ (s : Sort σ) (Q : carriers_quotient_algebra A Φ s), IsHSet (P s Q)}
    (cas : ∀ (s : Sort σ) (x : A s), P s Φ.[x])
    (pcas : ∀ (s : Sort σ) (x y : A s) (R : Φ s x y),
            path_class_quotient_algebra x y R # cas s x = cas s y)
    (ops : ∀ (u : Symbol σ)
             (a : DomOperation (carriers_quotient_algebra A Φ) (σ u))
             (aP : ∀ I, P (sorts_dom (σ u) I) (a I)),
           P (sort_cod (σ u)) (ops_quotient_algebra A Φ u a))
    (pops : ∀ (u : Symbol σ) (a : DomOperation A (σ u))
              (aP : ∀ I, P (sorts_dom (σ u) I) Φ.[a I]),
            path_ops_quotient_algebra u a # ops u (λ I, Φ.[a I]) aP
            = cas (sort_cod (σ u)) ((u^^A) a))
    (s : Sort σ) (Q : carriers_quotient_algebra A Φ s)
    : P s Q
    := match Q with
       | class_quotient_algebra s x =>
          cas s x
       | ops_quotient_algebra u a =>
          ops u a (λ I, carriers_quotient_algebra_ind P cas pcas
                          ops pops (sorts_dom (σ u) I) (a I))
       end.

  Axiom compute_path_carriers_quotient :
    ∀ (P : ∀ (s : Sort σ), carriers_quotient_algebra A Φ s -> Type)
    `{∀ (s : Sort σ) (Q : carriers_quotient_algebra A Φ s), IsHSet (P s Q)}
    (cas : ∀ (s : Sort σ) (x : A s), P s Φ.[x])
    (pcas : ∀ (s : Sort σ) (x y : A s) (R : Φ s x y),
            path_class_quotient_algebra x y R # cas s x = cas s y)
    (ops : ∀ (u : Symbol σ)
             (a : DomOperation (carriers_quotient_algebra A Φ) (σ u))
             (aP : ∀ I, P (sorts_dom (σ u) I) (a I)),
           P (sort_cod (σ u)) (ops_quotient_algebra A Φ u a))
    (pops : ∀ (u : Symbol σ) (a : DomOperation A (σ u))
              (aP : ∀ I, P (sorts_dom (σ u) I) Φ.[a I]),
            path_ops_quotient_algebra u a # ops u (λ I, Φ.[a I]) aP
            = cas (sort_cod (σ u)) ((u^^A) a))
    (s : Sort σ) (x y : A s) (R : Φ s x y),
    apD (carriers_quotient_algebra_ind P cas pcas ops pops s)
        (path_class_quotient_algebra x y R)
    = pcas s x y R.

  Axiom compute_path_operations_quotient :
    ∀ (P : ∀ (s : Sort σ), carriers_quotient_algebra A Φ s -> Type)
    `{∀ (s : Sort σ) (Q : carriers_quotient_algebra A Φ s), IsHSet (P s Q)}
    (cas : ∀ (s : Sort σ) (x : A s), P s Φ.[x])
    (pcas : ∀ (s : Sort σ) (x y : A s) (R : Φ s x y),
            path_class_quotient_algebra x y R # cas s x = cas s y)
    (ops : ∀ (u : Symbol σ)
             (a : DomOperation (carriers_quotient_algebra A Φ) (σ u))
             (aP : ∀ I, P (sorts_dom (σ u) I) (a I)),
           P (sort_cod (σ u)) (ops_quotient_algebra A Φ u a))
    (pops : ∀ (u : Symbol σ) (a : DomOperation A (σ u))
              (aP : ∀ I, P (sorts_dom (σ u) I) Φ.[a I]),
            path_ops_quotient_algebra u a # ops u (λ I, Φ.[a I]) aP
            = cas (sort_cod (σ u)) ((u^^A) a))
    (u : Symbol σ) (a : DomOperation A (σ u)),
    apD (carriers_quotient_algebra_ind P cas pcas ops pops (sort_cod (σ u)))
        (path_ops_quotient_algebra u a)
    = pops u a (λ I, cas (sorts_dom (σ u) I) (a I)).

End context_carriers_quotient_algebra.
End carriers_quotient_algebra.

Import carriers_quotient_algebra.

Global Existing Instance hset_quotient_algebra.

Definition QuotientAlgebra {σ : Signature} (A : Algebra σ)
  (Φ : ∀ s, relation (A s)) `{!IsCongruence A Φ}
  : Algebra σ
  := Build_Algebra (carriers_quotient_algebra A Φ) (ops_quotient_algebra A Φ).

Module quotient_algebra_notations.
  Global Notation "A / Φ" := (QuotientAlgebra A Φ)
                             (at level 40, left associativity)
                             : Algebra_scope.

  Global Notation "Ψ '.[' x ]" := (class_quotient_algebra _ Ψ x) (at level 3, format "Ψ '.[' x ]").
End quotient_algebra_notations.

Import quotient_algebra_notations.

Lemma compute_op_quotient {σ} (A : Algebra σ) (Φ : ∀ s, relation (A s))
  `{!IsCongruence A Φ} (u : Symbol σ) (a : DomOperation A (σ u))
  : (u ^^ A/Φ) (λ I, Φ.[a I]) = Φ.[(u^^A) a].
Proof.
  apply path_ops_quotient_algebra.
Defined.

(** The next section shows that A/Φ = A/Ψ whenever
    [Φ s x y <-> Ψ s x y] for all [s], [x], [y]. *)

Section path_quotient_algebra_iff.
  Context `{Univalence}
    {σ : Signature} (A : Algebra σ)
    (Φ : ∀ s, Relation (A s)) {CΦ : IsCongruence A Φ}
    (Ψ : ∀ s, Relation (A s)) {CΨ : IsCongruence A Ψ}.

  Lemma path_quotient_algebra_cong (p : Φ = Ψ) : A/Φ = A/Ψ.
  Proof.
    by destruct p.
  Defined.

  Lemma path_quotient_algebra_iff (R : ∀ s x y, Φ s x y <-> Ψ s x y)
    : A/Φ = A/Ψ.
  Proof.
    apply path_quotient_algebra_cong.
    funext s x y.
    refine (path_universe_uncurried _).
    apply equiv_iff_hprop; apply R.
  Defined.
End path_quotient_algebra_iff.

(** The following section defines the quotient homomorphism
    [hom_quotient : Homomorphism A (A/Φ)]. *)

Section hom_quotient.
  Context
    {σ} (A : Algebra σ) (Φ : ∀ s, relation (A s)) `{!IsCongruence A Φ}.

  Definition def_hom_quotient : ∀ (s : Sort σ), A s → (A/Φ) s :=
    λ s x, Φ.[x].

  Global Instance is_homomorphism_quotient
    : IsHomomorphism def_hom_quotient.
  Proof.
    intros u a. symmetry. apply compute_op_quotient.
  Defined.

  Definition hom_quotient : Homomorphism A (A/Φ)
    := Build_Homomorphism def_hom_quotient.

  Global Instance surjection_quotient `{Funext} (P : ∀ s x y, Φ s x y → x = y)
    : ∀ s, IsSurjection (hom_quotient s).
  Proof.
    intro s. apply Build_IsSurjection. generalize dependent s.
    srefine (carriers_quotient_algebra_ind A Φ (fun s Q => merely (hfiber (hom_quotient s) Q)) _ _ _ _).
    - intros. apply tr. by exists x.
    - intros. cbn. apply path_ishprop.
    - intros. cbn in *.
      unfold def_hom_quotient in *.
      unfold hfiber in *.
      assert (
(∀ I : Arity (σ u),
     Trunc (-1) (∃ x : A (sorts_dom (σ u) I), Φ.[x] = a I)) →
∀ I : Arity (σ u),
     ∃ x : A (sorts_dom (σ u) I), Φ.[x] = a I
).
  + intros.
    specialize (X I).
    notypeclasses refine (@Trunc_rec _ _ _ _ idmap X).
    apply hprop_allpath.
    intros [x p] [y q].
    apply path_sigma_hprop.
    cbn.
    apply P.
    pose (p @ q^) as r.
      apply tr.
      exists ((u^^A) (fun I => (aP' I).1)).
      transparent assert (HH : (a = (fun I => Φ.[(aP' I).1]))).
      + funext I. symmetry. apply aP'.
      + rewrite HH.
        symmetry.
        apply path_ops_quotient_algebra.
    - intros. cbn. apply path_ishprop.
  Qed.
End hom_quotient.

(** If [Φ s x y] implies [x = y], then homomorphism [hom_quotient Φ]
    is an isomorphism. *)

Global Instance is_isomorphism_quotient `{Univalence}
  {σ : Signature} {A : Algebra σ} (Φ : ∀ s, Relation (A s))
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
    `{Univalence} {σ} {A B : Algebra σ} `{!IsHSetAlgebra B}
    (Φ : ∀ s, Relation (A s)) `{!IsCongruence A Φ}.

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
      := λ s, (quotient_ump (Φ s) (Build_hSet (B s)))^-1 (f s; R s).

    Lemma oppreserving_quotient_algebra_mapout {w : SymbolType σ}
      (g : Operation (A/Φ) w) (α : Operation A w) (β : Operation B w)
      (G : ComputeOpQuotient A Φ α g) (P : OpPreserving f α β)
      : OpPreserving def_hom_quotient_algebra_mapout g β.
    Proof.
      unfold ComputeOpQuotient in G.
      induction w; cbn in *.
      - destruct (G tt)^. apply P.
      - refine (quotient_ind_prop (Φ t) _ _). intro x.
        apply (IHw (g (class_of (Φ t) x)) (α x) (β (f t x))).
        + intro a. apply (G (x,a)).
        + apply P.
    Defined.

    Global Instance is_homomorphism_quotient_algebra_mapout
      : IsHomomorphism def_hom_quotient_algebra_mapout.
    Proof.
      intro u.
      eapply oppreserving_quotient_algebra_mapout.
      - apply compute_op_quotient.
      - apply f.
    Defined.

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
      apply path_hset_homomorphism.
      funext s.
      exact (eissect (quotient_ump (Φ s) _) (G s)).
    - intro F.
      apply path_sigma_hprop.
      by apply path_hset_homomorphism.
  Defined.
End ump_quotient_algebra.
*)
