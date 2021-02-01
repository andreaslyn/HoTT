(* This file shows that if the quotient algebra always exists,
   then we can derive the axiom of choice. So constructively,
   we cannot generally define the quotient algebra. *)

Require Import
  HoTT.HSet
  HoTT.TruncType
  HoTT.HIT.quotient
  HoTT.HIT.epi
  HoTT.Classes.interfaces.canonical_names
  HoTT.Algebra.Universal.quotient_statement
  HoTT.Algebra.Universal.isomorphic
  HoTT.Algebra.Universal.congruence
  HoTT.Algebra.Universal.algebraic_theory
  HoTT.Algebra.Universal.hsetprojective.

Unset Elimination Schemes.

Import isomorphic_notations.

(* Any equivalence relations [R : ∀ s, Relation (C s)], [C : Carriers σ],
   can be extended to a congruence on the term algabra
   [∀ s, Relation (CarriersTermAlgebra C s)]. *)

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
    induction S; intros s2 T; destruct T; exact _.
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
    - exists idpath. intros i. apply X.
  Qed.

  Lemma symmetric_term_congruence_extension' (s1 s2 : Sort σ)
    (S : CarriersTermAlgebra C s1) (T : CarriersTermAlgebra C s2)
    (h : TermCongruenceExtension' s1 s2 S T)
    : TermCongruenceExtension' s2 s1 T S.
  Proof.
    generalize dependent s2.
    induction S; intros s2 [] h.
    - destruct h as [p1 p2].
      induction p1.
      exists idpath.
      by symmetry.
    - elim h.
    - elim h.
    - destruct h as [p f].
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
    - destruct h2 as [p2 P2], h3 as [p3 P3].
      exists (p2 @ p3).
      rewrite transport_pp.
      induction p2, p3.
      by transitivity c0.
    - elim h3.
    - elim h3.
    - elim h2.
    - elim h2.
    - elim h2.
    - elim h3.
    - destruct h2 as [p2 P2], h3 as [p3 P3].
      exists (p2 @ p3).
      intro i.
      induction p2.
      apply (X i _ (c0 i)).
      + apply P2.
      + rewrite concat_1p. apply P3.
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

(* For the rest of the file we assume the [QuotientAlgebraStatement]. *)

Section assume_quotient.
  Hypothesis (QStmt : QuotientAlgebraStatement).

Section quotient.
    Context
      {σ} {A : Algebra σ} (Φ : ∀ s, Relation (A s)) `{!IsCongruence A Φ}.
  
  (* The quotient A/Φ *)
  Definition Quot : Algebra σ := (QStmt _ _ Φ _).1.

  (* The quotient map A → A/Φ *)
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
    set (px := ap (λ f, f x) p').
    refine (px^ @ _).
    set (py := ap (λ f, f y) p').
    refine (_ @ py).
    by apply (equiv_quot (hom_id Quot)).2.
  Qed.
End quotient.

(* Let [R : ∀ s, Relation (C s)] be equivalence relations, for [C : Carriers σ].
   The following section shows that there is an isomprphism between
   the quotient algebra of the term algebra and the term algebra of
   the set-quotient,

   <<
    TermAlgebra C / Ext R  ≅  TermAlgebra (λ s, C s / R)
   >>

   where [Ext R] is the extension of R from section [TermCongruenceExtension].
*)

Section isomorphic_quot_term.
  Context
    `{Funext} {σ} {C : Carriers σ} `{!∀ s, IsHSet (C s)}
    (R : ∀ s, Relation (C s))
    `{!∀ s, EquivRel (R s)} `{∀ s, is_mere_relation (C s) (R s)}.

  Definition Ext : ∀ s, Relation (TermAlgebra C s)
    := (TermCongruenceExtension R).

  Definition QuotT := Quot Ext.

  Definition TermQ := TermAlgebra (λ s, quotient (R s)).

  Lemma map_term_algebra_is_compatible (s1 s2 : Sort σ) (p : s1 = s2)
    (S : CarriersTermAlgebra C s1)
    (T : CarriersTermAlgebra C s2)
    (E : TermCongruenceExtension' R s1 s2 S T)
    : map_term_algebra TermQ
        (λ s (x : C s), var_term_algebra (class_of (R s) x)) s2 (p # S) =
      map_term_algebra TermQ
        (λ s (x : C s), var_term_algebra (class_of (R s) x)) s2 T.
  Proof.
    generalize dependent s2.
    induction S; intros s2 p T E.
    - destruct T.
      + destruct E as [p' E].
        induction p'.
        cbn.
        induction (hset_path2 idpath p).
        by induction (@related_classes_eq (C s) (R s) _ c c0).
      + elim E.
    - destruct T.
      + elim E.
      + destruct E as [p' E].
        induction p'.
        induction (hset_path2 idpath p).
        cbn.
        f_ap.
        funext i.
        apply (X i (sorts_dom (σ u) i) idpath).
        apply E.
  Qed.

  Definition quot_to_term : Homomorphism QuotT TermQ.
  Proof.
    apply ((equiv_quot Ext)^-1).
    srefine (_; _).
    - exact (hom_term_algebra TermQ (λ s, var_term_algebra o class_of (R s))).
    - intros s' S T h. by apply (map_term_algebra_is_compatible s' s' idpath).
  Defined.

  Definition term_to_quot : Homomorphism TermQ QuotT.
  Proof.
    apply (ump_term_algebra (λ s, quotient (R s)) QuotT).
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
    assert (
      ump_term_algebra D (TermAlgebra D) (λ s, f s o var_term_algebra)
      = ump_term_algebra D (TermAlgebra D)
          (λ s, hom_id (TermAlgebra D) s o var_term_algebra)) as p.
    - f_ap. funext s x. apply idT.
    - intros s x.
      set (pf := path_ump_term_algebra_var _ _ f).
      set (pi := path_ump_term_algebra_var _ _ (hom_id (TermAlgebra D))).
      apply (ap (λ f, def_hom f s x) (pf^ @ p @ pi)).
  Qed.

  Lemma equiv_quot_id
    : (equiv_quot Ext (hom_id QuotT)).1 = quot Ext.
  Proof.
    rewrite path_equiv_quot.
    apply path_homomorphism.
    by funext s x.
  Qed.

  Lemma path_termQ_var (s : Sort σ) (x : C s)
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

  Lemma path_termQ_compose_var (s : Sort σ) (x : C s)
    : hom_compose term_to_quot
        (hom_compose quot_to_term (quot Ext)) s (var_term_algebra x)
      = quot Ext s (var_term_algebra x).
  Proof.
    cbn.
    by rewrite path_termQ_var.
  Qed.

  Lemma equiv_quot_compose
    : hom_compose term_to_quot (hom_compose quot_to_term (quot Ext)) = quot Ext.
  Proof.
    refine ((path_ump_term_algebra_var _ _ _)^
            @ _ @ path_ump_term_algebra_var _ _ _).
    apply moveR_equiv_M.
    rewrite eissect.
    funext s x.
    apply path_termQ_compose_var.
  Qed.

  Lemma sect_term_to_quot
    : hom_id QuotT = hom_compose term_to_quot quot_to_term.
  Proof.
    apply (equiv_inj (equiv_quot Ext)).
    apply path_sigma_hprop.
    refine (_ @ _ @ (path_equiv_quot Ext _)^).
    - refine (_ @ equiv_quot_compose^).
      apply equiv_quot_id.
    - apply path_homomorphism.
      funext s x.
      reflexivity.
  Qed.

  Global Instance is_isomorphism_quot_to_term
    : IsIsomorphism quot_to_term.
  Proof.
    intro s.
    srapply isequiv_adjointify.
    - apply term_to_quot.
    - intro x.
      apply (f_id_on_terms _ (hom_compose quot_to_term term_to_quot)).
      intros s'.
      refine (quotient_ind_prop _ _ _).
      intro x'.
      cbn.
      set (p := ap (λ g, def_hom g s') (path_equiv_quot Ext quot_to_term)).
      set (p' := ap (λ g, g (var_term_algebra x')) p).
      cbn in p'.
      rewrite <- p'.
      by rewrite (eisretr (equiv_quot Ext)).
    - intro x.
      pose (ap (λ f, def_hom f s x) sect_term_to_quot) as sh.
      symmetry.
      apply sh.
  Qed.

  Lemma isomorphic_quot_term : QuotT ≅ TermQ.
  Proof.
    exact (Build_Isomorphic quot_to_term).
  Defined.
End isomorphic_quot_term.

(* Due to the isomorphism in the above section,
   the term algebra of the set-quotient and the same universal
   property as the quotient of the term algebra. This is the contents
   of the following section. *)

Section is_quotient_term.
  Context
    `{Funext} {σ} {C : Carriers σ} `{!∀ s, IsHSet (C s)}
    (R : ∀ s, Relation (C s))
    `{!∀ s, EquivRel (R s)} `{∀ s, is_mere_relation (C s) (R s)}.

  (* The "quotient map". *)

  Definition termQ : Homomorphism (TermAlgebra C) (TermQ R)
    := hom_compose (quot_to_term R) (quot (Ext R)).

  Lemma equiv_termQ {B : Algebra σ}
    : Homomorphism (TermQ R) B
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
  
  Lemma path_equiv_termQ {B : Algebra σ} (h : Homomorphism (TermQ R) B)
    : (equiv_termQ h).1 = hom_compose h termQ.
  Proof.
    apply path_homomorphism.
    funext s x.
    cbn.
    rewrite path_equiv_quot.
    cbn.
    reflexivity.
  Qed.

  Lemma issurjection_termQ
    : ∀ s (y : TermQ R s), merely (hfiber (termQ s) y).
  Proof.
    intros s y.
    pose proof (issurjection_quot (Ext R) s ((quot_to_term R s)^-1 y)) as S.
    strip_truncations.
    apply tr.
    destruct S as [t T].
    exists t.
    cbn.
    apply (equiv_inj (quot_to_term R s)^-1).
    by rewrite eissect.
  Qed.
End is_quotient_term.

(* Now we can choose representatives from equivalence classes,
   as shown in the next section. *)

Section choose_representatives.
  Lemma cop_op_to_dom_op' `{Funext} {σ} {C : Carriers σ} `{!∀ s, IsHSet (C s)}
    (R : ∀ s, Relation (C s)) `{!∀ s, is_mere_relation (C s) (R s)}
    `{!∀ s, EquivRel (R s)} (s : Sort σ) (T : TermAlgebra C s)
    (u : Symbol σ) (a : DomOperation (TermAlgebra (λ s, quotient (R s))) (σ u))
    (p : equal_carriers_term_algebra (termQ R s T) (ops_term_algebra a))
    : ∃ (f : DomOperation (TermAlgebra C) (σ u)),
        equal_carriers_term_algebra T (ops_term_algebra f).
  Proof.
    generalize dependent u.
    induction T.
    - intros. cbn in *.
      rewrite path_termQ_var in p.
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

  Lemma cop_op_to_dom_op `{Funext} {σ} {C : Carriers σ} `{!∀ s, IsHSet (C s)}
    (R : ∀ s, Relation (C s)) `{!∀ s, is_mere_relation (C s) (R s)}
    `{!∀ s, EquivRel (R s)} (u : Symbol σ) (T : TermAlgebra C (sort_cod (σ u)))
    (a : DomOperation (TermAlgebra (λ s, quotient (R s))) (σ u))
    (p : termQ R (sort_cod (σ u)) T = ops_term_algebra a)
    : ∃ (f : DomOperation (TermAlgebra C) (σ u)),
        T = ops_term_algebra f.
  Proof.
    apply reflexive_equal_carriers_term_algebra_path in p.
    srefine (_ ; _).
    - apply (cop_op_to_dom_op' R (sort_cod (σ u)) T u a p).
    - apply path_equal_carriers_term_algebra.
      apply (cop_op_to_dom_op' R (sort_cod (σ u)) T u a p).
  Qed.

  Lemma cod_var_to_dom_var' `{Funext} {σ} {C : Carriers σ} `{!∀ s, IsHSet (C s)}
    (R : ∀ s, Relation (C s)) `{!∀ s, is_mere_relation (C s) (R s)}
    `{!∀ s, EquivRel (R s)}
    (s1 s2 : Sort σ) (T : TermAlgebra C s1) (t : quotient (R s2))
    (p : equal_carriers_term_algebra (termQ R s1 T) (var_term_algebra t))
    : ∃ y : C s1, T = var_term_algebra y.
  Proof.
    generalize dependent s2.
    induction T.
    - intros. exists c. reflexivity.
    - intros. rewrite is_homomorphism_hom in p. elim p.
  Defined.

  Lemma fun_cod_var_to_fun_dom_var' `{Funext} {σ} {X}
    {C : Carriers σ} `{!∀ s, IsHSet (C s)}
    (R : ∀ s, Relation (C s)) `{!∀ s, is_mere_relation (C s) (R s)}
    `{!∀ s, EquivRel (R s)} (k : X -> Sort σ)
    (T : ∀ x : X, TermAlgebra C (k x))
    (t : ∀ x : X, quotient (R (k x)))
    (p : ∀ x : X,
          equal_carriers_term_algebra (termQ R (k x) (T x))
          (var_term_algebra (t x)))
    : ∃ f : ∀ x : X, C (k x),
      ∀ x : X, T x = var_term_algebra (f x).
  Proof.
    srefine (_ ; _).
    - intro x. apply (cod_var_to_dom_var' R (k x) (k x) (T x) (t x) (p x)).
    - intro x.
      destruct ((cod_var_to_dom_var' R (k x) (k x) (T x) (t x) (p x))) as [y p'].
      exact p'.
  Defined.

  Lemma fun_cod_var_to_fun_dom_var `{Funext} {σ} {X}
    {C : Carriers σ} `{!∀ s, IsHSet (C s)}
    (R : ∀ s, Relation (C s)) `{!∀ s, is_mere_relation (C s) (R s)}
    `{!∀ s, EquivRel (R s)} (k : X -> Sort σ)
    (T : ∀ x : X, TermAlgebra C (k x)) (t : ∀ x, quotient (R (k x)))
    (p : ∀ x : X, termQ R (k x) (T x) = var_term_algebra (t x))
    : ∃ f : ∀ x : X, C (k x),
      ∀ x : X, T x = var_term_algebra (f x).
  Proof.
    set (p' := λ x, reflexive_equal_carriers_term_algebra_path (λ s, quotient (R s)) (k x) (p x)).
    exact (fun_cod_var_to_fun_dom_var' R k T t p').
  Defined.

  Lemma choose_sum `{Univalence} {X : Type} `{!IsHSet X} {Y : X + Unit -> Type}
    `{!∀ x, IsHSet (Y x)} (R : ∀ x, Relation (Y x))
    `{!∀ x, is_mere_relation (Y x) (R x)} `{!∀ x, EquivRel (R x)}
    : ∀ g' : ∀ x : X, quotient (R (inl x)),
      hexists (fun g : (∀ x : X, Y (inl x)) =>
               ∀ x, class_of (R (inl x)) (g x) = g' x).
  Proof.
    intro g'.
    set (σ := Build_Signature (X + Unit) Unit
                (λ _ : Unit, Build_SymbolTypeTo X inl (inr tt)) _ _).
    set (f' := λ x, @var_term_algebra σ (λ x, quotient (R x)) (inl x) (g' x)).
    set (op' := @ops_term_algebra σ (λ x, quotient (R x)) tt f').
    pose proof (@issurjection_termQ _ σ Y _ R _ _ (inr tt) op') as S.
    strip_truncations.
    apply tr.
    destruct S as [t T].
    destruct (@cop_op_to_dom_op _ σ Y _ R _ _ tt t f' T) as [g p].
    induction p^.
    rewrite (is_homomorphism_hom (@termQ _ σ Y _ R _ _)) in T.
    pose (@isinj_ops_term_algebra _ σ (λ x, quotient (R x)) tt) as isi.
    set (T' :=
      isi (λ x, @quot_to_term _ σ Y _ R _ _ (inl x)
                  (quot (@Ext  _ σ Y _ R) (inl x) (g x))) f' T).
    set (T'' := λ x, ap (λ f, f x) T').
    set (S := @fun_cod_var_to_fun_dom_var _ σ X Y _ R _ _ inl g g' T'').
    destruct S as [g0 gp].
    exists g0.
    intro x.
    cbn in T''.
    specialize (T'' x).
    rewrite (gp x) in T''.
    rewrite path_termQ_var in T''.
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

  Theorem choose_representatives `{Univalence}
    (X : Type) `{!IsHSet X} (Y : X -> Type)
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

(* Then we also have the axiom of choice: *)

Section axiom_of_choice.
  Context `{Univalence}
    {A : Type} `{!IsHSet A} {B : A → Type} `{!∀ a, IsHSet (B a)}.

  Corollary axiom_of_choice : (∀ a, merely (B a)) → merely (∀ a, B a).
  Proof.
    intro i.
    apply equiv_hsetprojective_quotient_choosable; try exact _.
    - intros Y sY R pR Rf Sm Tn f.
      assert (∀ x, EquivRel (R x)) as eR.
      + intro x. constructor; exact _.
      + apply (choose_representatives A Y R).
    - exact i.
  Qed.
End axiom_of_choice.

End assume_quotient.
End quotient_to_choice.
