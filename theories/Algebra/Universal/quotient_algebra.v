Require Export HoTT.Algebra.Universal.congruence.

Require Import
  HoTT.Basics
  HoTT.Types
  HoTT.HProp
  HoTT.HSet
  HoTT.HProp
  HoTT.Truncations
  HoTT.TruncType
  HoTT.Classes.interfaces.canonical_names
  HoTT.Algebra.Universal.homomorphism
  HoTT.Algebra.Universal.algebraic_theory.

Import algebra_notations.

Module carriers_quotient_algebra.

  Private Inductive carriers_quotient_algebra {σ : Signature}
    (A : Algebra σ) (Φ : ∀ s, Relation (A s)) : Carriers σ :=
  | class_quotient_algebra :
      ∀ {s : Sort σ}, A s → carriers_quotient_algebra A Φ s
  | ops_quotient_algebra : ∀ (u : Symbol σ),
      DomOperation (carriers_quotient_algebra A Φ) (σ u) →
      CodOperation (carriers_quotient_algebra A Φ) (σ u).

Section context_carriers_quotient_algebra.
  Context {σ : Signature} (A : Algebra σ) (Φ : ∀ s, Relation (A s)).

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
    (pops : ∀ (u : Symbol σ) (a : DomOperation A (σ u)),
            path_ops_quotient_algebra u a
              # ops u (λ I, Φ.[a I]) (λ I, cas (sorts_dom (σ u) I) (a I))
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

End context_carriers_quotient_algebra.
End carriers_quotient_algebra.

Import carriers_quotient_algebra.

Global Existing Instance hset_quotient_algebra.

Definition QuotientAlgebra {σ : Signature} (A : Algebra σ)
  (Φ : ∀ s, Relation (A s)) `{!IsCongruence A Φ}
  : Algebra σ
  := Build_Algebra (carriers_quotient_algebra A Φ) (ops_quotient_algebra A Φ).

Module quotient_algebra_notations.
  Global Notation "A / Φ" := (QuotientAlgebra A Φ)
                             (at level 40, left associativity)
                             : Algebra_scope.

  Global Notation "Ψ '.[' x ]" := (class_quotient_algebra _ Ψ x) (at level 3, format "Ψ '.[' x ]").
End quotient_algebra_notations.

Import quotient_algebra_notations.

Lemma compute_op_quotient {σ} (A : Algebra σ) (Φ : ∀ s, Relation (A s))
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

Definition in_class_quotient_algebra `{Univalence} {σ} {A : Algebra σ}
  {Φ : ∀ s, Relation (A s)} `{!IsCongruence A Φ} {s : Sort σ}
  (x : A s) (a : (A/Φ) s)
  : hProp.
srefine(carriers_quotient_algebra_ind A Φ (λ s X, A s -> hProp)
      _
      _
      _
      _
      s
      a
      x); clear a x s.
  - intros s x y. exact (BuildhProp (Φ s x y)).
  - abstract(intros s x y r;
    cbn; rewrite transport_const;
    funext z;
    apply path_iff_hprop; cbn; [
    intro q; by transitivity x | intro q; by transitivity y]).
  - cbn. intros u a h x.
    srefine (BuildhProp _).
    + exact (merely (exists b : DomOperation A (σ u),
                     {_ : Φ _ x ((u^^A) b) | ∀ I, h I (b I)})).
    + exact _.
  - abstract (cbn; intros u a;
    rewrite transport_const;
    funext x;
    apply path_iff_hprop; cbn;
    [
      intro e;
      strip_truncations;
      destruct e as [b [p r]];
      symmetry;
      transitivity ((u ^^ A) b); [assumption|];
      apply ops_compatible_cong; [exact _|];
      intro X;
      symmetry;
      apply r
    |
      intro r;
      apply tr;
      exists a;
      srefine (_; _); [ by symmetry | cbn; intro I; reflexivity]
    ]).
Defined.

Definition path_in_class_quotient_algebra `{Univalence} {σ} (A : Algebra σ)
  (Φ : ∀ s, Relation (A s)) `{!IsCongruence A Φ} (s : Sort σ)
  (x : A s) (a : (A/Φ) s) (C : in_class_quotient_algebra x a)
  : Φ.[x] = a.
Proof.
  generalize dependent C.
  generalize dependent x.
  generalize dependent s.
  srefine(carriers_quotient_algebra_ind A Φ
        (λ s a, ∀ x : A s, in_class_quotient_algebra x a → Φ.[x] = a)
        _
        _
        _
        _).
  - intros s x y r. apply path_class_quotient_algebra.
    cbn in r. symmetry. apply r.
  - intros. apply path_ishprop.
  - intros u a h x r.
    simpl in r.
    strip_truncations.
    destruct r as [b [p r]].
    cbn in h.
    assert (∀ I, Φ.[b I] = a I) as h0.
    + intro I.
      apply h.
      specialize (r I).
      exact r.
    + apply path_forall in h0.
      rewrite <- h0.
      rewrite path_ops_quotient_algebra.
      apply path_class_quotient_algebra.
      assumption.
  - intros. apply path_ishprop.
Qed.

Lemma simpl_in_class_quotient_algebra `{Univalence} {σ} (A : Algebra σ)
  (Φ : ∀ s, Relation (A s)) `{!IsCongruence A Φ} (s : Sort σ)
  (x y : A s)
  : trunctype_type (in_class_quotient_algebra x Φ.[y]) = Φ s y x.
Proof.
  reflexivity.
Qed.

Lemma related_path_quotient_algebra `{Univalence} {σ} {A : Algebra σ}
  (Φ : ∀ s, Relation (A s)) `{!IsCongruence A Φ} {s : Sort σ}
  {x y : A s} (p : Φ.[x] = Φ.[y])
  : Φ s x y.
Proof.
  pattern (Φ s x y).
  eapply transport.
  - apply simpl_in_class_quotient_algebra.
  - pattern (class_quotient_algebra A Φ x). apply (transport _ p^).
    cbn.
    reflexivity.
Qed.

(** The following section defines the quotient homomorphism
    [hom_quotient : Homomorphism A (A/Φ)]. *)

Section hom_quotient.
  Context
    `{Funext} {σ} {A : Algebra σ}
    (Φ : ∀ s, Relation (A s)) `{!IsCongruence A Φ}.

  Definition def_hom_quotient : ∀ (s : Sort σ), A s → (A/Φ) s :=
    λ s x, Φ.[x].

  Global Instance is_homomorphism_quotient
    : IsHomomorphism def_hom_quotient.
  Proof.
    intros u a. symmetry. apply compute_op_quotient.
  Defined.

  Definition hom_quotient : Homomorphism A (A/Φ)
    := Build_Homomorphism def_hom_quotient.

  Lemma isepi_quotient {B : Algebra σ} (f g : Homomorphism (A/Φ) B)
    (p : hom_compose f hom_quotient = hom_compose g hom_quotient)
    : f = g.
  Proof.
    apply path_homomorphism.
    funext s x.
    generalize dependent s.
    srefine (carriers_quotient_algebra_ind A Φ (fun s Q => f s Q = g s Q) _ _ _ _).
    - intros; cbn in *.
      apply (ap (λ h, def_hom h s x) p).
    - intros. cbn. apply hset_path2.
    - intros; cbn in *.
      rewrite is_homomorphism_hom.
      rewrite is_homomorphism_hom.
      f_ap.
      funext i.
      apply aP.
    - cbn in *. intros. apply hset_path2.
  Qed.
End hom_quotient.

(** This section develops the universal mapping property
    [ump_quotient_algebra] of the quotient algebra. *)

Section ump_quotient_algebra.
  Context
    `{Univalence} {σ} {A B : Algebra σ}
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
      : ∀ (s : Sort σ), (A/Φ) s → B s.
    Proof.
      srefine (carriers_quotient_algebra_ind A Φ
                (λ s _, B s) _ _ _ _).
      - cbn. intros s x. exact (f s x).
      - cbn. intros s x y r.
        rewrite transport_const.
        by apply R.
      - cbn. intros u a x.
        apply (u^^B).
        exact x.
      - cbn. intros u a.
        rewrite transport_const.
        symmetry.
        apply is_homomorphism_hom.
    Defined.

    Global Instance is_homomorphism_quotient_algebra_mapout
      : IsHomomorphism def_hom_quotient_algebra_mapout.
    Proof.
      easy.
    Qed.

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
        hom_quotient_algebra_mapout s Φ.[x] = f s x.
    Proof.
      reflexivity.
    Qed.

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
    cbn.
    exact (transport (λ z, g s Φ.[x] = g s z)
            (path_class_quotient_algebra A Φ _ _ E) idpath).
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
    - intro g.
      apply path_homomorphism.
      funext s a.
      generalize dependent s.
      srefine (carriers_quotient_algebra_ind A Φ
                (λ s a, ump_quotient_algebra_lr (_ g) s a = g s a) _ _ _ _).
      + cbn. intros s x. reflexivity.
      + intros. apply hset_path2.
      + cbn. intros u a h.
        rewrite is_homomorphism_hom.
        f_ap.
        funext I.
        apply h.
      + intros. apply hset_path2.
    - intro F.
      apply path_sigma_hprop.
      by apply path_homomorphism.
  Defined.
End ump_quotient_algebra.

(** If [Φ s x y] implies [x = y], then homomorphism [hom_quotient Φ]
    is an isomorphism. *)

Global Instance is_isomorphism_quotient `{Univalence}
  {σ : Signature} {A : Algebra σ} (Φ : ∀ s, Relation (A s))
  `{!IsCongruence A Φ} (P : ∀ s x y, Φ s x y → x = y)
  : IsIsomorphism (hom_quotient Φ).
Proof.
  intro s.
  srefine (isequiv_adjointify _ _ _ _).
  - generalize dependent s.
    srefine (carriers_quotient_algebra_ind A Φ (λ s _, A s) _ _ _ _).
    + intros s x. exact x.
    + intros. cbn. rewrite transport_const. apply P. exact R.
    + cbn. intros u x h. apply (u^^A). exact h.
    + intros. cbn. rewrite transport_const. reflexivity.
  - cbn.
    intro x.
    cbn.
    generalize dependent s.
    srefine (carriers_quotient_algebra_ind A Φ _ _ _ _ _).
    + cbn. intros s x. reflexivity.
    + intros. apply hset_path2.
    + cbn. intros u a h.
      rewrite is_homomorphism_quotient.
      f_ap.
      funext I.
      apply h.
    + intros. apply hset_path2.
  - reflexivity.
Qed.

(*
Lemma choice_fun_quotient_algebra_ind_pre `{Univalence}
  {σ} {A : Algebra σ} (Φ : ∀ s, Relation (A s)) `{!IsCongruence A Φ}
  {I : Type} `{!IsHSetProjective I}
  {X : I -> Type} `{!forall i, IsHSet (X i)}
  (R : forall i, Relation (X i))
  `{!forall i, is_mere_relation (X i) (R i)}
  `{!forall i, Reflexive (R i)}
  `{!forall i, Symmetric (R i)}
  `{!forall i, Transitive (R i)}
  (P : (forall i, quotient (R i)) -> Type) `{!forall f, IsHSet (P f)}
  (a : forall (f : forall i, X i), P (fun i => class_of (R i) (f i)))
  (E : forall (f g : forall i, X i) (r : forall i, R i (f i) (g i)),
       pointwise_related_classes_eq R f g r # a f = a g)
  (f : forall i, quotient (R i))
  : {b : P f |
      merely (exists (f' : forall i, X i)
                     (q : f = fun i => class_of (R i) (f' i)),
              forall (g : forall i, X i) (r : forall i, R i (f' i) (g i)),
              pointwise_related_classes_eq R f' g r # q # b = a g)}.
Proof.
  pose proof (hprop_cod_choice_quotient_ind_pre R P a f).
  pose proof (equiv_hsetprojective_quotient_choosable I _ X _ R _ _ _ _ f) as g.
  strip_truncations.
  destruct g as [g p].
  apply path_forall in p.
  refine (transport (fun f => {_ : P f | merely {_ | {_ : f = _ | _}}}) p _).
  exists (a g).
  apply tr.
  exists g.
  exists idpath.
  apply E.
Defined.
*)

Section AlgebraicTheoryQuotient.
  Context
    `{Univalence} {σ : Signature}
    (A : Algebra σ) (Φ : ∀ s, Relation (A s)) `{!IsCongruence A Φ}
    (I : Type) (e : Equations σ I) {E : IsAlgebraicTheory A e}.

  Global Instance equational_theory_quotient : IsAlgebraicTheory (A/Φ) e.
  Proof.
    intros i a.
    cbn in *.
    specialize (E i).
    unfold InterpEquation in E.
    destruct (e i) as [C h s L R].
    simpl in *.
    induction L; [induction R |].
    - cbn in *.
      set (a1 := a s c).
      set (a0 := a s c0).
      clearbody a0.
      clearbody a1.
      clear a.
      generalize dependent E.
      clear E.
      generalize dependent c.
      generalize dependent c0.
      generalize dependent s.
      srefine(carriers_quotient_algebra_ind A Φ _ _ _ _ _).
      + intros s x. cbn in *. intro a0.
        generalize dependent x.
        generalize dependent s.
        srefine(carriers_quotient_algebra_ind A Φ _ _ _ _ _).
        * cbn in *. intros s x y c0 c E.
          exact (E )
  Qed.

  Definition AlgebraicTheoryQuotient : AlgebraicTheory σ
    := Build_AlgebraicTheory (A/Φ) e.

End AlgebraicTheoryQuotient.
