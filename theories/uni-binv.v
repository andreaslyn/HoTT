Require Import
  HoTT.Basics
  HoTT.Types
  HoTT.Tactics.

Definition IsBinv {A B} (f : A -> B) :=
  {_ : {g : B -> A | g o f == idmap}
     | {h : B -> A | f o h == idmap} }.

Definition linv_isbinv {A B : Type} {f : A -> B} (S : IsBinv f)
  : B -> A
  := S.1.1.

Definition rinv_isbinv {A B : Type} {f : A -> B} (S : IsBinv f)
  : B -> A
  := S.2.1.

Definition lhomot_isbinv {A B : Type} {f : A -> B} (S : IsBinv f)
  : linv_isbinv S o f == idmap
  := S.1.2.

Lemma lpath_isbinv `{Funext} {A B : Type} {f : A -> B} (S : IsBinv f)
  : linv_isbinv S o f = idmap.
Proof.
  funext a. apply lhomot_isbinv.
Defined.

Definition rhomot_isbinv {A B : Type} {f : A -> B} (S : IsBinv f)
  : f o rinv_isbinv S == idmap
  := S.2.2.

Lemma rpath_isbinv `{Funext} {A B : Type} {f : A -> B} (S : IsBinv f)
  : f o rinv_isbinv S = idmap.
Proof.
  funext a. apply rhomot_isbinv.
Defined.

Lemma homot_rinv_isbinv {A B : Type} {f : A -> B} (S T : IsBinv f)
  : rinv_isbinv S == rinv_isbinv T.
Proof.
  intro b.
  refine ((lhomot_isbinv S (rinv_isbinv S b))^ @ _).
  refine (ap (linv_isbinv S) (rhomot_isbinv S b) @ _).
  refine (ap (linv_isbinv S) (rhomot_isbinv T b)^ @ _).
  exact ((lhomot_isbinv S (rinv_isbinv T b))).
Defined.

Lemma path_rinv_isbinv `{Funext} {A B : Type} {f : A -> B} (S T : IsBinv f)
  : rinv_isbinv S = rinv_isbinv T.
Proof.
  funext b. apply homot_rinv_isbinv.
Defined.

Lemma homot_linv_isbinv {A B : Type} {f : A -> B} (S T : IsBinv f)
  : linv_isbinv S == linv_isbinv T.
Proof.
  intro b.
  refine (ap (linv_isbinv S) (rhomot_isbinv S b)^ @ _).
  refine (lhomot_isbinv S (rinv_isbinv S b) @ _).
  refine ((lhomot_isbinv T (rinv_isbinv S b))^ @ _).
  exact (ap (linv_isbinv T) (rhomot_isbinv S b)).
Defined.

Lemma path_linv_isbinv `{Funext} {A B : Type} {f : A -> B} (S T : IsBinv f)
  : linv_isbinv S = linv_isbinv T.
Proof.
  funext b. apply homot_linv_isbinv.
Defined.

Lemma homot_linv_rinv_isbinv {A B : Type} {f : A -> B} (S : IsBinv f)
  : linv_isbinv S == rinv_isbinv S.
Proof.
  intro b.
  exact (ap (linv_isbinv S) (rhomot_isbinv S b)^
         @ lhomot_isbinv S (rinv_isbinv S b)).
Defined.

Lemma path_linv_rinv_isbinv `{Funext} {A B : Type} {f : A -> B} (S : IsBinv f)
  : linv_isbinv S = rinv_isbinv S.
Proof.
  funext b. apply homot_linv_rinv_isbinv.
Defined.

Lemma ap_composef {A B C D : Type} (g : C -> D) (F : (A -> B) -> C)
  {f1 f2} (h : f1 = f2) :
  ap (fun f : A -> B => g (F f)) h =
  ap g (ap (fun f : A -> B => F f) h).
Proof.
  by path_induction.
Defined.

Lemma hprop_isbinv `{Funext} {A B} (f : A -> B) : IsHProp (IsBinv f).
Proof.
  apply hprop_allpath.
  intros [[g P1] [h1 R1]] [[g2 P2] [h2 R2]].
  set (p := path_linv_isbinv ((g; P1); (h1; R1)) ((g2; P2); (h2; R2))).
  cbn in p; induction p.
  set (p := path_rinv_isbinv ((g; P1); (h1; R1)) ((g; P2); (h2; R2))).
  cbn in p; induction p.
  set (p := path_linv_rinv_isbinv ((g; P1); (h1; R1))).
  cbn in p; induction p.
  pose proof (h1 := (rpath_isbinv ((g; P1); (g; R1)))^).
  pose proof (h2 := (lpath_isbinv ((g; P1); (g; R1)))^).
  srapply path_sigma; cbn in*.
  - srapply path_sigma; cbn in *.
    + funext b.
      exact ((ap (fun i => i (g b)) h2)
              @ P1 (g b) @ (P2 (g b))^
              @ (ap (fun i => i (g b)) h2^)).
    + cbn in *.
      funext b.
      rewrite transport_forall_constant.
      transport_path_forall_hammer.
      rewrite transport_paths_Fl.
      hott_simpl.
      generalize dependent P2.
      generalize dependent P1.
      refine (
        paths_ind
          _
          (fun F R =>
forall P1 P2 : F == idmap,
(((ap (fun i : A -> A => i (F b)) R @ P1 (F b)) @ (P2 (F b))^) @
 ap (fun i : A -> A => i (F b)) R^)^ @ P1 b = 
P2 b
          )
          _
          _
          h2
      ).
      intros.
      hott_simpl.
      rewrite inv_pp.
      rewrite inv_V.
      hott_simpl.
  - rewrite transport_const.
    srapply path_sigma; cbn in *.
    + funext b.
      exact ((ap (fun i => g (i b)) h1)
              @ ap g (R1 b) @ ap g (R2 b)^
              @ (ap (fun i => g (i b)) h1^)).
    + cbn in *.
      funext b.
      rewrite transport_forall_constant.
      transport_path_forall_hammer.
      rewrite transport_paths_Fl.
      rewrite <- ap_V.
      rewrite inv_pp.
      rewrite inv_pp.
      rewrite inv_pp.
      rewrite ap_V.
      hott_simpl.
      rewrite ap_pp.
      rewrite ap_pp.
      rewrite ap_pp.
      rewrite <- ap_compose.
      rewrite <- ap_compose.
      rewrite <- (ap_composef f (fun i : B -> B => g (i b)) h1).
      rewrite ap_V.
      rewrite ap_V.
      rewrite <- (ap_composef f (fun i : B -> B => g (i b)) h1).
      generalize dependent R2.
      generalize dependent R1.
      refine (
        paths_ind _
          (fun F R =>
forall rtg stg : F == idmap,
(((ap (fun f0 : B -> B => F (f0 b)) R @
   ap F (stg b)) @
  (ap F (rtg b))^) @
 (ap (fun f0 : B -> B => F (f0 b)) R)^) @ rtg b = 
stg b
          )
          _
          _
          h1
      ).
      intros.
      hott_simpl.
Defined.
