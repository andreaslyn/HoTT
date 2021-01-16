Require Import
  HoTT.HIT.quotient
  HoTT.Classes.interfaces.canonical_names
  HoTT.Algebra.UniversalAlgebra.ua_quotient_statement
  HoTT.Algebra.UniversalAlgebra.ua_isomorphic
  HoTT.Algebra.UniversalAlgebra.ua_congruence
  HoTT.Algebra.UniversalAlgebra.ua_free_algebra.

Unset Elimination Schemes.

Import isomorphic_notations.

Section TermCongruenceExtension.
  Context
    {σ} {C : Carriers σ} `{!∀ s, IsHSet (C s)} (R : ∀ s, Relation (C s))
    `{!∀ s, EquivRel (R s)} `{∀ s, is_mere_relation (C s) (R s)}.

  Fixpoint TermCongruenceExtension' s1 s2
    (S : CarriersTermAlgebra C s1) (T : CarriersTermAlgebra C s2)
    : Type
    := match S, T with
       | var_term_algebra s1 x, var_term_algebra s2 y =>
          {p : s1 = s2 | R s2 (p # x) y}
       | ops_term_algebra u1 a, ops_term_algebra u2 b =>
          { p : u1 = u2 |
            ∀ i, TermCongruenceExtension' _ _
                  (a i) (b (transport (fun v => Arity (σ v)) p i))}
       | _, _ => Empty
       end.

  Definition TermCongruenceExtension s (S T : CarriersTermAlgebra C s)
  : Type 
  := TermCongruenceExtension' s s S T.

  Lemma hprop_term_congruence_extension' `{Funext} s1 s2
    (S : CarriersTermAlgebra C s1) (T : CarriersTermAlgebra C s2)
    : IsHProp (TermCongruenceExtension' s1 s2 S T).
  Proof.
    generalize dependent s2.
    induction S; intros s2 T; destruct T.
    - exact _.
    - exact _.
    - exact _.
    - cbn in *.
      apply @trunc_sigma.
      + exact _.
      + intros.
        apply @trunc_forall.
        * exact _.
        * intros. induction a.
        cbn in *.
        apply X.
  Qed.

  Global Instance hprop_term_congruence_extension
    `{Funext} s (S T : CarriersTermAlgebra C s)
    : IsHProp (TermCongruenceExtension s S T).
  Proof.
    apply hprop_term_congruence_extension'.
  Qed.

  Lemma reflexive_term_congruence_extension' (s : Sort σ)
    (S : CarriersTermAlgebra C s)
    : TermCongruenceExtension s S S.
  Proof.
    induction S.
    - by exists idpath.
    - cbn in *. exists idpath.
      intros i. cbn in *.
      apply X.
  Qed.

  Lemma symmetric_term_congruence_extension' (s1 s2 : Sort σ)
    (S : CarriersTermAlgebra C s1) (T : CarriersTermAlgebra C s2)
    (h : TermCongruenceExtension' s1 s2 S T)
    : TermCongruenceExtension' s2 s1 T S.
  Proof.
    generalize dependent s2.
    induction S; intros s2 [] h.
    - cbn in *. destruct h as [p1 p2].
      induction p1.
      exists idpath.
      by symmetry.
    - elim h.
    - elim h.
    - cbn in *.
      destruct h as [p f].
      induction p.
      exists idpath.
      cbn in *.
      intro i.
      apply X.
      apply f.
    Qed.

  Lemma transitive_term_congruence_extension' (s1 s2 s3 : Sort σ)
    (S1 : CarriersTermAlgebra C s1)
    (S2 : CarriersTermAlgebra C s2)
    (S3 : CarriersTermAlgebra C s3)
    (T1 : TermCongruenceExtension' s1 s2 S1 S2)
    (T2 : TermCongruenceExtension' s2 s3 S2 S3)
    : TermCongruenceExtension' s1 s3 S1 S3.
  Proof.
    generalize dependent s3.
    generalize dependent s2.
    induction S1; intros s2 [] h2 s3 [] h3.
    - cbn in *. destruct h2 as [p2 P2], h3 as [p3 P3].
      exists (p2 @ p3).
      rewrite transport_pp.
      induction p2, p3.
      cbn in *.
      by transitivity c0.
    - cbn in *. elim h3.
    - cbn in *. elim h3.
    - cbn in *. elim h2.
    - cbn in *. elim h2.
    - cbn in *. elim h2.
    - cbn in *. elim h3.
    - cbn in *. destruct h2 as [p2 P2], h3 as [p3 P3].
      exists (p2 @ p3).
      intro i.
      cbn in *.
      induction p2.
      apply (X i _ (c0 i)).
      + apply P2.
      + cbn in *.
        rewrite concat_1p.
        apply P3.
  Qed.

  Global Instance equivrel_term_congruence_extension (s : Sort σ)
    : EquivRel (@TermCongruenceExtension s).
  Proof.
    constructor.
    - intro. apply reflexive_term_congruence_extension'.
    - intros x y a. by apply symmetric_term_congruence_extension'.
    - intros x y z T1 T2.
      by apply (transitive_term_congruence_extension' s s s _ _ _ T1 T2).
  Qed.

  Global Instance is_term_congruence_extension `{Funext}
    : IsCongruence (TermAlgebra C) TermCongruenceExtension.
  Proof.
    constructor.
    - intros. exact _.
    - intros. exact _.
    - intros u a b c.
      exists idpath.
      intro i.
      apply c.
  Qed.
End TermCongruenceExtension.

Module quotient_to_choice.
Section assume_quotient.
  Hypothesis (QStmt : QuotientAlgebraStatement).

Section quotient.
    Context
      {σ} {A : Algebra σ}
      (Φ : ∀ s, Relation (A s)) `{!IsCongruence A Φ}.
  
  Definition Quot : Algebra σ := (QStmt _ _ Φ _).1.

  Definition quot : Homomorphism A Quot := (QStmt _ _ Φ _).2.1.

  Definition equiv_quot {B : Algebra σ}
    : Homomorphism Quot B <~> {f : Homomorphism A B | HomCompatible Φ f}
    := ((QStmt _ _ Φ _).2.2 B).1.

  Definition path_equiv_quot {B : Algebra σ} (h : Homomorphism Quot B)
    : (equiv_quot h).1 = hom_compose h quot
    := ((QStmt _ _ Φ _).2.2 B).2 h.

  Lemma compatible_quot {s} {x y : A s} (r : Φ s x y)
    : quot s x = quot s y.
  Proof.
    pose (path_equiv_quot (hom_id Quot)).
    set (p' := ap (λ f, def_hom f s) p).
    cbn in p'.
    set (px := ap (λ f, f x) p').
    cbn in px.
    refine (px^ @ _).
    set (py := ap (λ f, f y) p').
    cbn in py.
    refine (_ @ py).
    by apply (equiv_quot (hom_id Quot)).2.
  Qed.
End quotient.

Section equiv_quotient_term_algebra.
  Context
    `{Funext} {σ} {C : Carriers σ} `{!∀ s, IsHSet (C s)}
    (R : ∀ s, Relation (C s))
    `{!∀ s, EquivRel (R s)} `{∀ s, is_mere_relation (C s) (R s)}.

  Definition R' : ∀ s, Relation (TermAlgebra C s)
    := (TermCongruenceExtension R).

  Local Notation QuotR := (Quot R').

  Local Notation TermR := (TermAlgebra (λ s, quotient (R s))).

  Lemma map_term_algebra_is_compatible (s1 s2 : Sort σ) (p : s1 = s2)
    (S : CarriersTermAlgebra C s1)
    (T : CarriersTermAlgebra C s2)
    (E : TermCongruenceExtension' R s1 s2 S T)
    : map_term_algebra TermR
        (λ s (x : C s), var_term_algebra (class_of (R s) x)) s2 (p # S) =
      map_term_algebra TermR
        (λ s (x : C s), var_term_algebra (class_of (R s) x)) s2 T.
  Proof.
    generalize dependent s2.
    induction S; intros s2 p T E; cbn in *.
    - destruct T.
      + destruct E as [p' E].
        induction p'. cbn in *.
        induction (HSet.hset_path2 idpath p).
        cbn in *.
        by induction (@related_classes_eq (C s) (R s) _ c c0).
      + elim E.
    - destruct T.
      + elim E.
      + destruct E as [p' E].
        induction p'. cbn in *.
        induction (HSet.hset_path2 idpath p).
        cbn in *.
        assert (
(λ X0 : Arity (σ u),
   CarriersTermAlgebra_ind C
     (λ (s : Sort σ) (_ : CarriersTermAlgebra C s),
      CarriersTermAlgebra (λ s0 : Sort σ, quotient (R s0)) s)
     (λ (s : Sort σ) (x : C s), var_term_algebra (class_of (R s) x))
     (λ (u0 : Symbol σ)
      (_ : forall X1 : Arity (σ u0),
           CarriersTermAlgebra C (sorts_dom (σ u0) X1))
      (r : forall X1 : Arity (σ u0),
           CarriersTermAlgebra (λ s : Sort σ, quotient (R s))
             (sorts_dom (σ u0) X1)), ops_term_algebra r) 
     (sorts_dom (σ u) X0) (c X0))
=
(λ X0 : Arity (σ u),
   CarriersTermAlgebra_ind C
     (λ (s : Sort σ) (_ : CarriersTermAlgebra C s),
      CarriersTermAlgebra (λ s0 : Sort σ, quotient (R s0)) s)
     (λ (s : Sort σ) (x : C s), var_term_algebra (class_of (R s) x))
     (λ (u0 : Symbol σ)
      (_ : forall X1 : Arity (σ u0),
           CarriersTermAlgebra C (sorts_dom (σ u0) X1))
      (r : forall X1 : Arity (σ u0),
           CarriersTermAlgebra (λ s : Sort σ, quotient (R s))
             (sorts_dom (σ u0) X1)), ops_term_algebra r) 
     (sorts_dom (σ u) X0) (c0 X0))
        ).
        * funext i.
          apply (X i (sorts_dom (σ u) i) idpath).
          apply E.
        * by destruct X0.
  Qed.

  Definition quot_to_term : Homomorphism QuotR TermR.
  Proof.
    apply ((equiv_quot R')^-1).
    srefine (_; _).
    - exact (hom_term_algebra TermR (λ s, var_term_algebra o class_of (R s))).
    - cbn in *.
      intros s' S T h.
      by apply (map_term_algebra_is_compatible s' s' idpath).
  Defined.

  Definition term_to_quot : Homomorphism TermR QuotR.
  Proof.
    apply (ump_term_algebra (λ s, quotient (R s)) QuotR).
    intros s.
    srefine (quotient_rec (R s) _ _).
    - intro x. apply quot. apply var_term_algebra. exact x.
    - intros x y h. cbn in *.
      apply compatible_quot.
      exists idpath. apply h.
  Defined.

  Lemma f_id_on_terms (D : Carriers σ) `{∀ s, IsHSet (D s)}
    (f : Homomorphism (TermAlgebra D) (TermAlgebra D))
    (idT : ∀ s (x : D s), f s (var_term_algebra x) = var_term_algebra x)
    : ∀ s (x : TermAlgebra D s), f s x = x.
  Proof.
    (* This should be a lemma in term algebrta file. *)
    assert (∀ (f : Homomorphism (TermAlgebra D) (TermAlgebra D)),
            ump_term_algebra D
              (TermAlgebra D) (λ s, f s o var_term_algebra) = f).
    - intro f'.
      apply path_homomorphism.
      funext s x.
      cbn in *.
      induction x.
      + reflexivity.
      + cbn in *.
        rewrite is_homomorphism_hom.
        cbn.
        f_ap.
        funext i.
        apply X.
    - assert (
        ump_term_algebra D (TermAlgebra D) (λ s, f s o var_term_algebra)
        = ump_term_algebra D (TermAlgebra D) (λ s, hom_id (TermAlgebra D) s o var_term_algebra)).
      + f_ap. funext s x. apply idT.
      + intros s x.
        set (pf := X f).
        set (pi := X (hom_id (TermAlgebra D))).
        set (p := pf^ @ X0 @ pi).
        apply (ap (λ f, def_hom f s x) p).
  Qed.

  Lemma equiv_quot_id
    : (equiv_quot R' (hom_id QuotR)).1 = quot R'.
  Proof.
    rewrite path_equiv_quot.
    apply path_homomorphism.
    by funext s x.
  Qed.

  Lemma equiv_quot_compose_var0 (s : Sort σ) (x : C s)
    : quot_to_term s (quot R' s (var_term_algebra x))
      = var_term_algebra (class_of (R s) x).
  Proof.
    set (p := ap (λ g, def_hom g s) (path_equiv_quot R' quot_to_term)).
    cbn in p.
    set (p' := ap (λ g, g (var_term_algebra x)) p).
    cbn in p'.
    rewrite <- p'.
    unfold quot_to_term.
    rewrite (eisretr (equiv_quot R')).
    reflexivity.
  Qed.

  Lemma equiv_quot_compose_var (s : Sort σ) (x : C s)
    : hom_compose term_to_quot
        (hom_compose quot_to_term (quot R')) s (var_term_algebra x)
      = quot R' s (var_term_algebra x).
  Proof.
    cbn.
    rewrite equiv_quot_compose_var0.
    cbn.
    reflexivity.
  Qed.

  Lemma equiv_quot_compose
    : hom_compose term_to_quot (hom_compose quot_to_term (quot R')) = quot R'.
  Proof.
    assert (ump_term_algebra C QuotR (λ s, quot R' s o var_term_algebra)
            = quot R') by apply compute_ump_term_algebra.
    assert (ump_term_algebra C QuotR (λ s,
              hom_compose term_to_quot (hom_compose quot_to_term (quot R')) s
                o var_term_algebra)
            = hom_compose term_to_quot (hom_compose quot_to_term (quot R')))
      by apply compute_ump_term_algebra.
    assert (ump_term_algebra C QuotR (λ s,
              hom_compose term_to_quot (hom_compose quot_to_term (quot R')) s
                o var_term_algebra)
            = quot R').
    - refine (_ @ X).
      apply moveR_equiv_M.
      rewrite eissect.
      funext s x.
      apply equiv_quot_compose_var.
    - exact (X0^ @ X1).
  Qed.

  Lemma last_sect_helper''
    : (equiv_quot R' (hom_id QuotR)).1
      = hom_compose term_to_quot (hom_compose quot_to_term (quot R')).
  Proof.
    refine (_ @ equiv_quot_compose^).
    apply equiv_quot_id.
  Qed.

  Lemma last_sect_helper'
    : (equiv_quot R' (hom_id QuotR)).1
      = hom_compose (hom_compose term_to_quot quot_to_term) (quot R').
  Proof.
    refine (last_sect_helper'' @ _).
    apply path_homomorphism.
    funext s x.
    reflexivity.
  Qed.

  Lemma last_sect_helper
    : equiv_quot R' (hom_id QuotR)
      = equiv_quot R' (hom_compose term_to_quot quot_to_term).
  Proof.
    apply path_sigma_hprop.
    refine (_ @ (path_equiv_quot R' _)^).
    apply last_sect_helper'.
  Qed.

  Lemma last_sect
    : hom_id QuotR = hom_compose term_to_quot quot_to_term.
  Proof.
    apply (equiv_inj (equiv_quot R')).
    apply last_sect_helper.
  Qed.

  Global Instance is_isomorphism_quot_to_term
    : IsIsomorphism quot_to_term.
  Proof.
    intro s.
    srapply isequiv_adjointify.
    - apply term_to_quot.
    - intro x.
      apply (f_id_on_terms _ (hom_compose quot_to_term term_to_quot)).
      cbn in *.
      intros s'.
      refine (quotient_ind_prop _ _ _).
      intro x'.
      cbn.
      set (p := ap (λ g, def_hom g s') (path_equiv_quot R' quot_to_term)).
      cbn in p.
      set (p' := ap (λ g, g (var_term_algebra x')) p).
      cbn in p'.
      rewrite <- p'.
      unfold quot_to_term.
      rewrite (eisretr (equiv_quot R')).
      reflexivity.
    - intro x.
      pose (ap (λ f, def_hom f s x) last_sect) as sh.
      cbn in sh.
      symmetry.
      apply sh.
  Qed.

  Lemma isomorphic_quot_term : QuotR ≅ TermR.
  Proof.
    exact (Build_Isomorphic quot_to_term).
  Defined.
End equiv_quotient_term_algebra.

End assume_quotient.
End quotient_to_choice.

(*
Need to assume quotient algebra UMP.

Equivalence R : Relation(X), is_mere_relation R.

*)
