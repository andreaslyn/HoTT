Require Import
  HoTT.Classes.interfaces.canonical_names
  HoTT.Algebra.UniversalAlgebra.ua_quotient_statement
  HoTT.Algebra.UniversalAlgebra.ua_homomorphism
  HoTT.Algebra.UniversalAlgebra.ua_congruence
  HoTT.Algebra.UniversalAlgebra.ua_free_algebra.

Unset Elimination Schemes.

Import algebra_notations.

Section TermCongruenceExtension.
  Context
    {σ} {C : Carriers σ} `{!∀ s, IsHSet (C s)} (R : ∀ s, Relation (C s))
    `{!∀ s, EquivRel (R s)} `{∀ s, is_mere_relation (C s) (R s)}.

  Fixpoint TermCongruenceExtension' s1 s2
    (S : CarriersTermAlgebra C s1) (T : CarriersTermAlgebra C s2)
    : Type
    := match S, T with
       | var_term_algebra s1 x, var_term_algebra s2 y =>
          {p : s1 = s2 | p # x = y}
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
      by rewrite P2.
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

Section equiv_quotient_term_algebra.
  Context
    (QStmt : QuotientAlgebraStatement)
    (X : Type) (R : Relation X) `{!EquivRel R}.

End equiv_quotient_term_algebra.


(*
Need to assume quotient algebra UMP.

Equivalence R : Relation(X), is_mere_relation R.

*)
