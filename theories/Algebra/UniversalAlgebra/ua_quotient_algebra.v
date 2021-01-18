(*
Require Export HoTT.Algebra.UniversalAlgebra.ua_congruence.

Require Import
  HoTT.Basics
  HoTT.Types
  HoTT.HProp
  HoTT.HSet
  HoTT.HProp
  HoTT.HIT.quotient
  HoTT.Truncations
  HoTT.TruncType
  HoTT.Classes.implementations.list
  HoTT.Classes.interfaces.canonical_names
  HoTT.Algebra.UniversalAlgebra.ua_homomorphism.

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

(** The following section defines the quotient homomorphism
    [hom_quotient : Homomorphism A (A/Φ)]. *)

Section hom_quotient.
  Context
    `{Funext} {σ} (A : Algebra σ)
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

(*
  Definition Choice : Type :=
    (∀ (X : Type) (P : X -> Type), (∀ x, merely (P x)) -> merely (∀ x, P x)).

  Global Instance surjection_quotient (choice : Choice)
    : ∀ s, IsSurjection (hom_quotient s).
  Proof.
    intro s. apply BuildIsSurjection. generalize dependent s.
    srefine (carriers_quotient_algebra_ind A Φ (fun s Q => merely (hfiber (hom_quotient s) Q)) _ _ _ _).
    - intros. apply tr. by exists x.
    - intros. cbn. apply path_ishprop.
    - intros. cbn in *.
      unfold def_hom_quotient in *.
      unfold hfiber in *.
      pose (u ^^ A) as op.
      unfold Operation in op.
      apply choice in aP.
      strip_truncations.
      apply tr.
      srefine (_ ; _).
      + apply op. intro X. apply aP.
      + cbn in *.
        set (aP' := λ x, (aP x).2).
        cbn in *.
        apply path_forall in aP'.
        rewrite <- aP'.
        symmetry.
        apply path_ops_quotient_algebra.
    - cbn in *. intros. apply path_ishprop.
    Qed.
*)
End hom_quotient.

(*
Definition in_class_quotient_algebra
  `{Univalence} {σ : Signature} {A : Algebra σ}
  (Φ : ∀ s, Relation (A s)) `{!IsCongruence A Φ}
  : ∀ {s : Sort σ}, (A/Φ) s -> A s -> hProp.
Proof.
  srefine (carriers_quotient_algebra_ind A Φ (λ s Q, A s -> hProp) _ _ _ _).
  - cbn. intros s x y. exact (BuildhProp (Φ s x y)).
  - cbn. intros. rewrite transport_const. funext a.
    apply path_iff_hprop.
    + cbn. intros.
      pose proof (equiv_rel_cong A Φ).
      Print EquivRel.
      About EquivRel_Transitive.
      pose (@EquivRel_Transitive (A s) (Φ s) (X0 s)).
      unfold Transitive in t.
      apply (t y x a).
      * symmetry. exact R.
      * exact X.
    + cbn. intros.
      pose proof (equiv_rel_cong A Φ).
      pose (@EquivRel_Transitive (A s) (Φ s) (X0 s)).
      unfold Transitive in t.
      apply (t x y a).
      * exact R.
      * exact X.
  - cbn. intros u a x y.
    exact (BuildhProp (Φ (sort_cod (σ u))
            (ops_quotient_algebra A Φ u a) y)).
  - admit.
  (* Somehow need a simpler induction principle.
     It should be possible to ommit the cases
     for the quotient operations when assuming choice. *)
Admitted.
*)

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
        induction path_class_quotient_algebra.
        cbn.
        by apply R.
      - cbn. intros u a x. (* HMM *)
      - cbn. intros u a aP.
        induction path_ops_quotient_algebra.
        cbn.
        rewrite is_homomorphism_hom.
        f_ap.

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

(* TODO Prove this from the universal property. *)
(** If [Φ s x y] implies [x = y], then homomorphism [hom_quotient Φ]
    is an isomorphism. *)

Global Instance is_isomorphism_quotient `{Univalence}
  (choice : Choice)
  {σ : Signature} {A : Algebra σ} (Φ : ∀ s, Relation (A s))
  `{!IsCongruence A Φ} (P : ∀ s x y, Φ s x y → x = y)
  : IsIsomorphism (hom_quotient A Φ).
Proof.
  intro s.
  apply isequiv_surj_emb; [apply surjection_quotient; exact choice |].
  apply isembedding_isinj_hset.
  intros x y p.
  apply P.
  unfold hom_quotient in *.
  cbn in *.
  unfold def_hom_quotient in *.
  pattern (Φ s x y).
  eapply transport.
  - apply in_class_pr.
  - pattern (Φ.[x]). apply (transport _ (p^)).
    pose proof (equiv_rel_cong A Φ).
    pose ((@EquivRel_Reflexive (A s) (Φ s) (X s))).
    apply r. (* This shoud work when in_class_quotient_algebra computes. *)
Qed.
*)
