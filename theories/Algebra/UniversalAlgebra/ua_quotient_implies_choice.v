Require Import
  HoTT.HSet
  HoTT.TruncType
  HoTT.HIT.quotient
  HoTT.HIT.epi
  HoTT.Classes.interfaces.canonical_names
  HoTT.Algebra.UniversalAlgebra.ua_quotient_statement
  HoTT.Algebra.UniversalAlgebra.ua_isomorphic
  HoTT.Algebra.UniversalAlgebra.ua_congruence
  HoTT.Algebra.UniversalAlgebra.ua_algebraic_theory
  HoTT.Algebra.UniversalAlgebra.choosable.

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

  Definition issurjection_quot
    : ∀ s (y : Quot s), merely (hfiber (quot s) y)
    := (QStmt _ _ Φ _).2.2.1.

  Definition equiv_quot {B : Algebra σ}
    : Homomorphism Quot B <~> {f : Homomorphism A B | HomCompatible Φ f}
    := ((QStmt _ _ Φ _).2.2.2 B).1.

  Definition path_equiv_quot {B : Algebra σ} (h : Homomorphism Quot B)
    : (equiv_quot h).1 = hom_compose h quot
    := ((QStmt _ _ Φ _).2.2.2 B).2 h.

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

  Lemma isepi_quot `{Funext} {C : Algebra σ} (f g : Homomorphism Quot C)
    : hom_compose f quot = hom_compose g quot -> f = g.
  Proof.
    intro p.
    rewrite <- path_equiv_quot in p.
    rewrite <- path_equiv_quot in p.
    apply (equiv_inj equiv_quot).
    by apply path_sigma_hprop.
  Qed.
End quotient.

Section equiv_quotient_term_algebra.
  Context
    `{Funext} {σ} {C : Carriers σ} `{!∀ s, IsHSet (C s)}
    (R : ∀ s, Relation (C s))
    `{!∀ s, EquivRel (R s)} `{∀ s, is_mere_relation (C s) (R s)}.

  Definition Ext : ∀ s, Relation (TermAlgebra C s)
    := (TermCongruenceExtension R).

  Definition QuotR := Quot Ext.

  Definition TermR := TermAlgebra (λ s, quotient (R s)).

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
        induction (hset_path2 idpath p).
        cbn in *.
        by induction (@related_classes_eq (C s) (R s) _ c c0).
      + elim E.
    - destruct T.
      + elim E.
      + destruct E as [p' E].
        induction p'. cbn in *.
        induction (hset_path2 idpath p).
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
    apply ((equiv_quot Ext)^-1).
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
    : (equiv_quot Ext (hom_id QuotR)).1 = quot Ext.
  Proof.
    rewrite path_equiv_quot.
    apply path_homomorphism.
    by funext s x.
  Qed.

  Lemma equiv_quot_compose_var0 (s : Sort σ) (x : C s)
    : quot_to_term s (quot Ext s (var_term_algebra x))
      = var_term_algebra (class_of (R s) x).
  Proof.
    set (p := ap (λ g, def_hom g s) (path_equiv_quot Ext quot_to_term)).
    cbn in p.
    set (p' := ap (λ g, g (var_term_algebra x)) p).
    cbn in p'.
    rewrite <- p'.
    unfold quot_to_term.
    rewrite (eisretr (equiv_quot Ext)).
    reflexivity.
  Qed.

  Lemma equiv_quot_compose_var (s : Sort σ) (x : C s)
    : hom_compose term_to_quot
        (hom_compose quot_to_term (quot Ext)) s (var_term_algebra x)
      = quot Ext s (var_term_algebra x).
  Proof.
    cbn.
    rewrite equiv_quot_compose_var0.
    cbn.
    reflexivity.
  Qed.

  Lemma equiv_quot_compose
    : hom_compose term_to_quot (hom_compose quot_to_term (quot Ext)) = quot Ext.
  Proof.
    assert (ump_term_algebra C QuotR (λ s, quot Ext s o var_term_algebra)
            = quot Ext) by apply compute_ump_term_algebra.
    assert (ump_term_algebra C QuotR (λ s,
              hom_compose term_to_quot (hom_compose quot_to_term (quot Ext)) s
                o var_term_algebra)
            = hom_compose term_to_quot (hom_compose quot_to_term (quot Ext)))
      by apply compute_ump_term_algebra.
    assert (ump_term_algebra C QuotR (λ s,
              hom_compose term_to_quot (hom_compose quot_to_term (quot Ext)) s
                o var_term_algebra)
            = quot Ext).
    - refine (_ @ X).
      apply moveR_equiv_M.
      rewrite eissect.
      funext s x.
      apply equiv_quot_compose_var.
    - exact (X0^ @ X1).
  Qed.

  Lemma last_sect_helper''
    : (equiv_quot Ext (hom_id QuotR)).1
      = hom_compose term_to_quot (hom_compose quot_to_term (quot Ext)).
  Proof.
    refine (_ @ equiv_quot_compose^).
    apply equiv_quot_id.
  Qed.

  Lemma last_sect_helper'
    : (equiv_quot Ext (hom_id QuotR)).1
      = hom_compose (hom_compose term_to_quot quot_to_term) (quot Ext).
  Proof.
    refine (last_sect_helper'' @ _).
    apply path_homomorphism.
    funext s x.
    reflexivity.
  Qed.

  Lemma last_sect_helper
    : equiv_quot Ext (hom_id QuotR)
      = equiv_quot Ext (hom_compose term_to_quot quot_to_term).
  Proof.
    apply path_sigma_hprop.
    refine (_ @ (path_equiv_quot Ext _)^).
    apply last_sect_helper'.
  Qed.

  Lemma last_sect
    : hom_id QuotR = hom_compose term_to_quot quot_to_term.
  Proof.
    apply (equiv_inj (equiv_quot Ext)).
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
      set (p := ap (λ g, def_hom g s') (path_equiv_quot Ext quot_to_term)).
      cbn in p.
      set (p' := ap (λ g, g (var_term_algebra x')) p).
      cbn in p'.
      rewrite <- p'.
      unfold quot_to_term.
      rewrite (eisretr (equiv_quot Ext)).
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

Section is_quotient_term.
  Context
    `{Funext} {σ} {C : Carriers σ} `{!∀ s, IsHSet (C s)}
    (R : ∀ s, Relation (C s))
    `{!∀ s, EquivRel (R s)} `{∀ s, is_mere_relation (C s) (R s)}.

  Definition termR : Homomorphism (TermAlgebra C) (TermR R)
    := hom_compose (quot_to_term R) (quot (Ext R)).

  Lemma equiv_termR {B : Algebra σ}
    : Homomorphism (TermR R) B
      <~> {f : Homomorphism (TermAlgebra C) B | HomCompatible (Ext R) f}.
  Proof.
    srefine (HoTT.Basics.Equivalences.equiv_compose (equiv_quot (Ext R)) _).
    - intro h. exact (hom_compose h (quot_to_term R)).
    - srapply isequiv_adjointify.
      + intro h. exact (hom_compose h (hom_inv (quot_to_term R))).
      + cbn. intro h. Search hom_inv.
        apply path_homomorphism.
        funext s x.
        cbn.
        by rewrite eissect.
      + cbn. intro h.
        apply path_homomorphism.
        funext s x.
        cbn.
        by rewrite eisretr.
  Defined.
  
  Lemma path_equiv_termR {B : Algebra σ} (h : Homomorphism (TermR R) B)
    : (equiv_termR h).1 = hom_compose h termR.
  Proof.
    apply path_homomorphism.
    funext s x.
    cbn.
    rewrite path_equiv_quot.
    cbn.
    reflexivity.
  Qed.

  Lemma compatible_termR {s} {x y : TermAlgebra C s} (r : Ext R s x y)
    : termR s x = termR s y.
  Proof.
    cbn.
    apply (equiv_inj (quot_to_term R s)^-1).
    rewrite eissect.
    rewrite eissect.
    by apply compatible_quot.
  Qed.

  Definition ker' {A : Algebra σ} (f : Homomorphism A (TermR R))
    (s1 s2 : Sort σ) (x : A s1) (y : A s2)
    := equal_carriers_term_algebra (f s1 x) (f s2 y).

  Lemma ker_to_ext' `{Univalence} {s1 s2}
    {x : TermAlgebra C s1} {y : TermAlgebra C s2} (h : ker' termR s1 s2 x y)
    : TermCongruenceExtension' R s1 s2 x y.
  Proof.
    generalize dependent s2.
    induction x; intros s2 y.
    - destruct y.
      + intro h. cbn in *.
        rewrite equiv_quot_compose_var0 in h.
        rewrite equiv_quot_compose_var0 in h.
        cbn in h.
        destruct h as [p h].
        induction p. exists idpath. unfold ker' in h.
        by apply (classes_eq_related (R s)).
      + cbn in *. intro h.
        rewrite is_homomorphism_hom in h.
        rewrite is_homomorphism_hom in h.
        rewrite equiv_quot_compose_var0 in h.
        elim h.
    - destruct y.
      + cbn in *. intro h.
        unfold ker' in h.
        cbn in h.
        rewrite is_homomorphism_hom in h.
        rewrite is_homomorphism_hom in h.
        rewrite equiv_quot_compose_var0 in h.
        elim h.
      + cbn in *. intro h.
        unfold ker' in h.
        cbn in h.
        rewrite is_homomorphism_hom in h.
        rewrite is_homomorphism_hom in h.
        rewrite is_homomorphism_hom in h.
        rewrite is_homomorphism_hom in h.
        cbn in h.
        destruct h as [p h].
        induction p.
        exists idpath.
        cbn in *.
        intro i.
        apply X.
        apply h.
  Qed.

  Definition ker {A : Algebra σ} (f : Homomorphism A (TermR R))
    (s : Sort σ) (x : A s) (y : A s)
    := f s x = f s y.

  Lemma ker_to_ext `{Univalence} {s}
    {x y : TermAlgebra C s} (h : ker termR s x y)
    : Ext R s x y.
  Proof.
    apply ker_to_ext'.
    unfold ker'.
    apply reflexive_equal_carriers_term_algebra_path.
    apply h.
  Qed.

  Lemma equiv_ker_ext `{Univalence} {s} (x y : TermAlgebra C s)
    : ker termR s x y <~> Ext R s x y.
  Proof.
    apply equiv_iff_hprop.
    - intros. by apply ker_to_ext.
    - intros. by apply compatible_termR.
  Qed.

  Lemma path_ker_ext `{Univalence} {s} (x y : TermAlgebra C s)
    : ker termR s x y = Ext R s x y.
  Proof.
    srapply path_universe.
    - apply equiv_ker_ext.
    - exact _.
  Qed.

  Lemma isepi_termR {B : Algebra σ}
    (f g : Homomorphism (TermR R) B)
    : hom_compose f termR = hom_compose g termR -> f = g.
  Proof.
    intro p.
    rewrite <- path_equiv_termR in p.
    rewrite <- path_equiv_termR in p.
    apply (equiv_inj equiv_termR).
    by apply path_sigma_hprop.
  Qed.

  Lemma issurjection_termR
    : ∀ s (y : TermR R s), merely (hfiber (termR s) y).
  Proof.
    intros s y.
    pose (issurjection_quot (Ext R) s ((quot_to_term R s)^-1 y)) as S.
    clearbody S.
    strip_truncations.
    apply tr.
    destruct S as [t T].
    exists t.
    cbn.
    apply (equiv_inj (quot_to_term R s)^-1).
    by rewrite eissect.
  Qed.
End is_quotient_term.

Section choose_representatives.
  Lemma isop' `{Funext} {σ} {C : Carriers σ} `{!∀ s, IsHSet (C s)}
    (R : ∀ s, Relation (C s)) `{!∀ s, is_mere_relation (C s) (R s)}
    `{!∀ s, EquivRel (R s)} (s : Sort σ) (T : TermAlgebra C s)
    (u : Symbol σ) (a : DomOperation (TermAlgebra (λ s, quotient (R s))) (σ u))
    (p : equal_carriers_term_algebra (termR R s T) (ops_term_algebra a))
    : ∃ (f : DomOperation (TermAlgebra C) (σ u)),
        equal_carriers_term_algebra T (ops_term_algebra f).
  Proof.
    generalize dependent u.
    induction T.
    - intros. cbn in *.
      rewrite equiv_quot_compose_var0 in p.
      elim p.
    - intros.
      rewrite is_homomorphism_hom in p.
      cbn in p.
      destruct p as [p P].
      induction p.
      exists c.
      apply reflexive_equal_carriers_term_algebra_path.
      reflexivity.
  Qed.

  Lemma isop `{Funext} {σ} {C : Carriers σ} `{!∀ s, IsHSet (C s)}
    (R : ∀ s, Relation (C s)) `{!∀ s, is_mere_relation (C s) (R s)}
    `{!∀ s, EquivRel (R s)} (u : Symbol σ) (T : TermAlgebra C (sort_cod (σ u)))
    (a : DomOperation (TermAlgebra (λ s, quotient (R s))) (σ u))
    (p : termR R (sort_cod (σ u)) T = ops_term_algebra a)
    : ∃ (f : DomOperation (TermAlgebra C) (σ u)),
        T = ops_term_algebra f.
  Proof.
    apply reflexive_equal_carriers_term_algebra_path in p.
    srefine (_ ; _).
    - apply (isop' R (sort_cod (σ u)) T u a p).
    - cbn.
      apply path_equal_carriers_term_algebra.
      apply (isop' R (sort_cod (σ u)) T u a p).
  Qed.

  Lemma isvar' `{Funext} {σ} {C : Carriers σ} `{!∀ s, IsHSet (C s)}
    (R : ∀ s, Relation (C s)) `{!∀ s, is_mere_relation (C s) (R s)}
    `{!∀ s, EquivRel (R s)}
    (s1 s2 : Sort σ) (T : TermAlgebra C s1) (t : quotient (R s2))
    (p : equal_carriers_term_algebra (termR R s1 T) (var_term_algebra t))
    : ∃ y : C s1, T = var_term_algebra y.
  Proof.
    generalize dependent s2.
    induction T.
    - intros. exists c. reflexivity.
    - intros. rewrite is_homomorphism_hom in p. elim p.
  Defined.

  Lemma isvar_fun' `{Funext} {σ} {X} {C : Carriers σ} `{!∀ s, IsHSet (C s)}
    (R : ∀ s, Relation (C s)) `{!∀ s, is_mere_relation (C s) (R s)}
    `{!∀ s, EquivRel (R s)}
    (s1 s2 : Sort σ) (T : X -> TermAlgebra C s1) (t : X -> quotient (R s2))
    (p : ∀ x : X,
          equal_carriers_term_algebra (termR R s1 (T x))
          (var_term_algebra (t x)))
    : ∃ f : X -> C s1,
      ∀ x : X, T x = var_term_algebra (f x).
  Proof.
    srefine (_ ; _).
    - intro x. apply (isvar' R s1 s2 (T x) (t x) (p x)).
    - intro x.
      destruct ((isvar' R s1 s2 (T x) (t x) (p x))) as [y p'].
      cbn in *.
      exact p'.
  Defined.

  Lemma isvar_fun `{Funext} {σ} {X} {C : Carriers σ} `{!∀ s, IsHSet (C s)}
    (R : ∀ s, Relation (C s)) `{!∀ s, is_mere_relation (C s) (R s)}
    `{!∀ s, EquivRel (R s)}
    (s : Sort σ) (T : X -> TermAlgebra C s) (t : X -> quotient (R s))
    (p : ∀ x : X, termR R s (T x) = var_term_algebra (t x))
    : ∃ f : X -> C s,
      ∀ x : X, T x = var_term_algebra (f x).
  Proof.
    set (p' := λ x, reflexive_equal_carriers_term_algebra_path (λ s, quotient (R s)) s (p x)).
    exact (isvar_fun' R s s T t p').
  Defined.

  Theorem choice1 `{Univalence} {X Y : Type} `{!IsHSet Y}
    (R : Relation Y) `{!is_mere_relation Y R} `{!EquivRel R}
    : ∀ g' : X -> quotient R,
      merely (∃ g : X -> Y, ∀ x, class_of R (g x) = g' x).
  Proof.
    intro g'.
    set (σ := Build_Signature Unit Unit
                (λ _ : Unit, Build_SymbolTypeTo X (λ _, tt) tt) _ _).
    set (f' := @var_term_algebra σ (λ _, quotient R) tt o g').
    set (op' := @ops_term_algebra σ (λ _, quotient R) tt f').
    pose (@issurjection_termR _ σ (λ _, Y) _ (λ _, R) _ _ tt op') as S.
    clearbody S.
    strip_truncations.
    apply tr.
    destruct S as [t T].
    unfold op' in T.
    destruct (@isop _ σ (λ _, Y) _ (λ _, R) _ _ tt t f' T) as [g p].
    induction p^.
    unfold f' in T.
    cbn in g.
    rewrite (is_homomorphism_hom (termR (λ _ : Sort σ, R))) in T.
    cbn in T.
    unfold f' in T.
    pose (@isinj_ops_term_algebra _ σ (λ _, quotient R) tt) as ii0.
    set (T' := ii0 (λ X : X,
       @quot_to_term _ σ (λ _, Y) _ (λ _ : Unit, R) _ _ tt (quot (@Ext  _ σ (λ _, Y) _ (λ _ : Unit, R)) tt (g X))) f' T).
    set (T'' := λ x, ap (λ f, f x) T').
    set (S := @isvar_fun _ σ X (λ _, Y) _ (λ _, R) _ _ tt g g' T'').
    destruct S as [g0 gp].
    exists g0.
    intro x.
    cbn in *.
    unfold f' in *.
    specialize (T'' x).
    rewrite (gp x) in T''.
    rewrite equiv_quot_compose_var0 in T''.
    cbn in T''.
    by apply isinj_var_term_algebra in T''.
  Qed.

  Lemma isvar_funD' `{Funext} {σ} {X} {C : Carriers σ} `{!∀ s, IsHSet (C s)}
    (R : ∀ s, Relation (C s)) `{!∀ s, is_mere_relation (C s) (R s)}
    `{!∀ s, EquivRel (R s)} (k : X -> Sort σ)
    (T : ∀ x : X, TermAlgebra C (k x))
    (t : ∀ x : X, quotient (R (k x)))
    (p : ∀ x : X,
          equal_carriers_term_algebra (termR R (k x) (T x))
          (var_term_algebra (t x)))
    : ∃ f : ∀ x : X, C (k x),
      ∀ x : X, T x = var_term_algebra (f x).
  Proof.
    srefine (_ ; _).
    - intro x. apply (isvar' R (k x) (k x) (T x) (t x) (p x)).
    - intro x.
      destruct ((isvar' R (k x) (k x) (T x) (t x) (p x))) as [y p'].
      cbn in *.
      exact p'.
  Defined.

  Lemma isvar_funD `{Funext} {σ} {X} {C : Carriers σ} `{!∀ s, IsHSet (C s)}
    (R : ∀ s, Relation (C s)) `{!∀ s, is_mere_relation (C s) (R s)}
    `{!∀ s, EquivRel (R s)} (k : X -> Sort σ)
    (T : ∀ x : X, TermAlgebra C (k x)) (t : ∀ x, quotient (R (k x)))
    (p : ∀ x : X, termR R (k x) (T x) = var_term_algebra (t x))
    : ∃ f : ∀ x : X, C (k x),
      ∀ x : X, T x = var_term_algebra (f x).
  Proof.
    set (p' := λ x, reflexive_equal_carriers_term_algebra_path (λ s, quotient (R s)) (k x) (p x)).
    exact (isvar_funD' R k T t p').
  Defined.

  Theorem choose_sum `{Univalence} {X : Type} `{!IsHSet X} {Y : X + Unit -> Type}
    `{!∀ x, IsHSet (Y x)} (R : ∀ x, Relation (Y x))
    `{!∀ x, is_mere_relation (Y x) (R x)} `{!∀ x, EquivRel (R x)}
    : ∀ g' : ∀ x : X, quotient (R (inl x)),
      merely (∃ g : (∀ x : X, Y (inl x)), ∀ x, class_of (R (inl x)) (g x) = g' x).
  Proof.
    intro g'.
    set (σ := Build_Signature (X + Unit) Unit
                (λ _ : Unit, Build_SymbolTypeTo X inl (inr tt)) _ _).
    set (f' := λ x, @var_term_algebra σ (λ x, quotient (R x)) (inl x) (g' x)).
    set (op' := @ops_term_algebra σ (λ x, quotient (R x)) tt f').
    pose (@issurjection_termR _ σ Y _ R _ _ (inr tt) op') as S.
    clearbody S.
    strip_truncations.
    apply tr.
    destruct S as [t T].
    unfold op' in T.
    destruct (@isop _ σ Y _ R _ _ tt t f' T) as [g p].
    induction p^.
    unfold f' in T.
    cbn in g.
    rewrite (is_homomorphism_hom (@termR _ σ Y _ R _ _)) in T.
    cbn in T.
    unfold f' in T.
    pose (@isinj_ops_term_algebra _ σ (λ x, quotient (R x)) tt) as ii0.
    set (T' := ii0 (λ x : X,
       @quot_to_term _ σ Y _ R _ _ (inl x) (quot (@Ext  _ σ Y _ R) (inl x) (g x))) f' T).
    set (T'' := λ x, ap (λ f, f x) T').
    set (S := @isvar_funD _ σ X Y _ R _ _ inl g g' T'').
    destruct S as [g0 gp].
    exists g0.
    intro x.
    cbn in *.
    unfold f' in *.
    specialize (T'' x).
    rewrite (gp x) in T''.
    rewrite equiv_quot_compose_var0 in T''.
    cbn in T''.
    by apply isinj_var_term_algebra in T''.
  Qed.

  Definition IncFam {X} (Y : X -> Type) (x' : X + Unit) : Type
    := match x' with
       | inl x => Y x
       | inr tt => Unit
       end.

  Global Instance ishset_inc_fam {X} (Y : X -> Type) `{!∀ x, IsHSet (Y x)}
    (x' : X + Unit)
    : IsHSet (IncFam Y x').
  Proof.
    destruct x'.
    - exact _.
    - destruct u. exact _.
  Defined.

  Definition IncRel {X} {Y : X -> Type} (R : ∀ x, Relation (Y x))
    : ∀ x' : X + Unit, Relation (IncFam Y x')
    := λ x',
       match x' as x' return Relation (IncFam Y x') with
       | inl x => R x
       | inr tt => λ _ _, Unit
       end.

  Global Instance equivrel_inc_rel {X : Type} {Y : X -> Type}
    (R : ∀ x, Relation (Y x)) `{!∀ x, EquivRel (R x)}
    : ∀ x', EquivRel (IncRel R x').
  Proof.
    intros []; constructor.
    - apply H.
    - apply H.
    - apply H.
    - destruct u. constructor.
    - destruct u. constructor.
    - destruct u. constructor.
  Defined.

  Global Instance is_mere_relation_inc_rel {X : Type} {Y : X -> Type}
    (R : ∀ x, Relation (Y x)) `{!∀ x, is_mere_relation (Y x) (R x)}
    : ∀ x', is_mere_relation (IncFam Y x') (IncRel R x').
  Proof.
    intros [].
    - exact _.
    - destruct u. exact _.
  Defined.

  Theorem choose `{Univalence} (X : Type) `{!IsHSet X} (Y : X -> Type)
    `{!∀ x, IsHSet (Y x)} (R : ∀ x, Relation (Y x))
    `{!∀ x, is_mere_relation (Y x) (R x)} `{!∀ x, EquivRel (R x)}
    : ∀ g' : ∀ x : X, quotient (R x),
      merely (∃ g : (∀ x : X, Y x), ∀ x, class_of (R x) (g x) = g' x).
  Proof.
    About choose_sum.
    intro g'.
    exact (@choose_sum _ X _ (IncFam Y) _ (IncRel R) _ _ g').
  Qed.
End choose_representatives.

Section axiom_of_choice.
  Context `{Univalence}
    {X : Type} `{!IsHSet X} {A : X → Type} `{!∀ x, IsHSet (A x)}
    (P : ∀ x : X, A x → Type) `{!∀ x (a : A x), IsHProp (P x a)}.

  Corollary axiom_of_choice
    : (∀ (x : X), merely (∃ a : A x, P x a)) →
      merely (∃ g : (∀ x, A x), ∀ x, P x (g x)).
  Proof.
    intro i.
    apply quotient_choosable_to_choosable; try exact _.
    - intros Y sY R pR Rf Sm Tn f.
      assert (∀ x, EquivRel (R x)) as eR.
      + intro x. constructor; exact _.
      + apply (choose X Y R).
    - exact i.
  Qed.
End axiom_of_choice.

End assume_quotient.
End quotient_to_choice.
