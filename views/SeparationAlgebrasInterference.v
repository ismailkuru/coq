
Require Import Monoids.
Require Import SetoidClass.
Require Import MySetoids.
Require Import Language Setof.
Require Import Tactics.
Require Import Framework.

Require Import SeparationAlgebras.

Section SAI_Views.
 (* Assume a separation algebra *)
 Context {A} sepop `{SA : SepAlg A sepop}.

 Local Infix "∙" := sepop (at level 50).

 Class IfRel (R : relation A) :=
   {
     Rpo :> PreOrder R;
     Rsmorph :> Proper (equiv ==> equiv ==> iff) R;
     Rdecomp : forall m1 m2 m m',
             lift_val m == m1 ∙ m2 ->
             R m m' ->
               exists m1', exists m2',
                 R m1 m1' /\ R m2 m2' /\
                 lift_val m' == m1' ∙  m2';
     Runit : forall i, i ∈ sa_unit ->
            forall i', R i i' -> i' ∈ sa_unit
     }.

 Context R `{IfRelR : IfRel R}.

 Definition stable (v : Setof (A:=A)) :=
   forall m, m ∈ v ->
        forall m', R m m' ->
            m' ∈ v.

Ltac liftvaldef := repeat
  match goal with
  | [H : context [defined (lift_val ?X)] |- _] => replace (defined (lift_val X)) with True in H by reflexivity
  end.
Ltac saop_tac := match goal with 
  | [ |- _ ∈ saop _ _ _] => eexists; intuition; try reflexivity
  | [H : _ ∈ saop _ _ _ |- _] => destruct H; intuition; try ssubst
  | [H : saop_ _ _ _ _ |- _ ] => destruct H; push
  | [H : saop__ _ _ _ _ |- _] => destruct H; liftvaldef; simpl in *; intuition
end.


  Hint Unfold stable.

 Lemma stable_saop_pres : forall p q,
     stable p -> stable q -> stable (saop sepop p q).
  repeat intro.
  repeat saop_tac.
  assert (lift_val x == x0 ∙ x1).
    split; simpl; intuition.
  destruct (Rdecomp _ _ _ _ H5 H2).
  destruct H8; intuition.
  exists x2; exists x3; intuition; eauto.
  firstorder.
 Qed.

 Record SV :=
   { v :> Setof (A:=A); v_stable : stable v }.

  Definition SV_equiv p q := v p == v q.
  Instance SV_equivalence : Equivalence SV_equiv.
   firstorder.
  Qed.
  Program Instance SV_setoid : Setoid SV.

 Definition isaop (p q : SV) : SV :=
  {|
   v := saop sepop (v p) (v q);
   v_stable := stable_saop_pres _ _ (v_stable p) (v_stable q)
  |}.

 Instance isaop_smorph : Proper (equiv ==> equiv ==> equiv) isaop.
  simpl; cbv [isaop equiv SV_equiv]; do 6 intro; simpl in *.
  apply saop_smorph; intuition.
 Qed.



  Ltac reduce_to lem:= simpl; cbv [isaop SV_equiv]; simpl; intros; apply lem; trivial.

  Lemma isaop_assoc : forall m1 m2 m3, 
     isaop (isaop m1 m2) m3 == isaop m1 (isaop m2 m3).
   reduce_to (saop_assoc (A:=A)).
  Qed.

  Lemma isaop_comm : forall m1 m2, isaop m1 m2 == isaop m2 m1.
   reduce_to (saop_comm (A:=A)).
  Qed.

  Lemma stable_unit : stable sa_unit.
   exact Runit.
  Qed.   

  Definition if_unit : SV := {| v := sa_unit; v_stable := stable_unit |}.

  Lemma isaop_lunit : forall p, isaop if_unit p == p.
   reduce_to (left_unit (A:=A)).
  Qed.

  Lemma isaop_runit : forall p, isaop p if_unit == p.
   reduce_to (right_unit (A:=A)).
  Qed.

  Local Obligation Tactic := auto.

  Hint Resolve isaop_assoc.
  Program Instance isaop_semigroup : SemiGroup isaop.

  Hint Resolve isaop_lunit.
  Hint Resolve isaop_runit.
  Program Instance isaop_monoid : Monoid isaop := {| unit := if_unit |}.

  Hint Resolve isaop_comm.
  Program Instance isaop_commut : Commutative isaop.

  Definition stabof m := mkSetof (fun m' => R m m').
  Lemma stabof_stable m : stable (stabof m).
   repeat intro.
   destruct H; intuition; ssubst.
   exists m'; intuition.
   etransitivity; eauto.
  Qed.

  Definition stabiliser (m : A) : SV :=
   {| v:= stabof m; v_stable:= stabof_stable m |}.

  Instance v_morphism : Proper (equiv ==> equiv) v.
   firstorder.
  Qed.

  Lemma union_stable (P : Setof (A:=SV)) : stable (setof_union (so_map v P)).
   repeat intro.
   repeat destruct H; ssubst.
   exists (v x).
    exists x; intuition.
    eapply v_stable; eauto.
  Qed.

  Definition sunion (P : Setof (A:=SV)) : SV :=
   {| v := setof_union (so_map v P); v_stable := union_stable P |}.

 Lemma isaop_mjoin_dist : forall p P,
   isaop p (sunion P) == sunion (so_map (isaop p) P).
  split; intros.
   repeat destruct H; intuition.
   destruct H2.
   destruct H1.
   intuition; repeat ssubst.
   exists (v (isaop p x2)).
    eexists; split; try reflexivity.
    eexists; split; eauto; reflexivity.

    exists x; intuition.
    eexists; eexists; intuition; eauto.
  
   repeat destruct H.
   repeat ssubst.
   repeat destruct H0; intuition; ssubst.
   exists x1; intuition.
   exists x2; exists x3; intuition.
   exists (v x0); intuition.
   exists x0; intuition.
 Qed.

End SAI_Views.

Existing Instance v_morphism.

Module Type SAISafetyParams
    (Import ats : Atomics)
    (Import st : StateTransformers ats).
  Parameter M : Type.
  Declare Instance M_setoid : Setoid M.
  Parameter sepop : partial_op M.
  Declare Instance separationAlgebra : SepAlg sepop.
  Parameter R : relation M.
  Declare Instance Rif : IfRel sepop R.
  Parameter axioms :
    (SV R) -> Atomic -> (SV R) -> Prop.

  Parameter erase : M -> Setof (A:=State).
  Local Infix "*" := (saop sepop).
  Local Notation "|_ A _|" := (collapse (so_map erase A)).
  Axiom soundAxioms :
    forall p a q, axioms p a q ->
      forall (m : M),
        subsetof (so_map_rel (interp a)
              |_ p * singleton m _|
             (R_morphism:=st_morph (interp a)))
                |_ q * stabiliser sepop R m _|.
End SAISafetyParams.

Module MakeSafetyParams_SAI
    (ats : Atomics)
    (Import st : StateTransformers ats)
    (Import saisp : SAISafetyParams ats st)
      <: (SafetyParams ats st).

  Definition V := (SV R).
  Instance V_setoid : Setoid V := SV_setoid sepop R.
  Definition op : V -> V -> V := isaop sepop R.
  Instance op_monoid : SemiGroup op := isaop_semigroup sepop R.
  Instance op_comm : Commutative op := isaop_commut sepop R.

  Definition erase := fun p : V => collapse (so_map saisp.erase p).

  Instance R_smorph : Proper (equiv ==> equiv ==> iff) R.
    eapply Rsmorph; auto with *.
  Qed.
    
  Instance erase_morphism : Proper (equiv ==> equiv) erase.
   split; intro;
   repeat match goal with
   | [ H: elem _ _ |- _] => destruct H; intuition
   | [ |- elem _ _ ] => eexists; intuition; eauto
   end; rewr trivial.
  Qed.

End MakeSafetyParams_SAI.

Module SAI_Safety
    (ats: Atomics)
    (bs : BasicSyntaxT ats)
    (st : StateTransformers ats)
    (Import saisp : SAISafetyParams ats st).
 Module Import msp := (MakeSafetyParams_SAI ats st saisp).
 Module Export sft := (Safety ats bs st msp).

 Local Infix "*" := op.

 Definition ent : relation V := fun p q => subsetof p q.

 Instance v_entmorph : Proper (ent ==> subsetof) (v R).
  firstorder.
 Qed.

 Instance op_ent_lmorph : Proper
    (ent ==> equiv ==> ent) op.
  repeat intro.
  ssubst.
  destruct H1; eexists; intuition; eauto.
  destruct H1 as [x2 H1]; exists x2.
  destruct H1 as [x3 H1]; exists x3.
  intuition.
 Qed.

 Lemma ent_aimpl : forall p q : V,
    ent p q -> aimpl p q.
  repeat intro.
  destruct H0; intuition; destruct H1.
  eexists; intuition; eauto.
  eexists; intuition; eauto.
  rewr trivial.
 Qed.

 Existing Instance isaop_monoid.

 Hint Resolve ent_aimpl.
 Hint Resolve aimpl_wm_to_aimpl.


 Instance Safe_ent : Proper
   (ent --> eq ==> ent ++> Basics.impl) Safe.
  repeat intro.
  apply Safe_aimpl with x x0 x1;
   unfold Basics.flip in *; intuition;
   apply aimpl_wm_to_aimpl; auto.
 Qed.


 Definition mjoin : Setof (A:=V) -> V := sunion sepop R.
 Lemma op_mjoin_dist : forall (p : V) P,
   p * (mjoin P) == mjoin (so_map (op p) P).
  apply isaop_mjoin_dist.
 Qed.

 Lemma erase_jmorphism : forall P,    
      erase (mjoin P) == setof_union (elem (so_map erase P)).
  split; intros.
   destruct H as [x H]; intuition.
   destruct H0 as [x0 H0]; intuition.
   destruct H as [x1 H].
   ssubst.
   destruct H as [p H]; intuition; ssubst.
   exists (erase p).
    exists p; intuition.
    exists (saisp.erase x0); intuition.
    exists x0; intuition.
   
   repeat destruct H; intuition.
   rewrite H1 in H0.
   repeat destruct H0.
   repeat ssubst.
   exists (saisp.erase x1); intuition.
   exists x1; intuition.
   exists x; intuition.
   exists x; intuition.
 Qed.

  Hint Resolve op_mjoin_dist.
  Hint Resolve erase_jmorphism.

 Lemma Safe_mjoin_disj : forall P c q,
    (forall p, p ∈ P -> Safe p c q) ->
      Safe (mjoin P) c q.
  apply Safe_disj; auto.
 Qed.

 Import bs.

 Lemma Safe_atomic : forall p a q,
   axioms p a q -> Safe p a q.
  intros.
  apply Safe_asat.
  repeat intro.
  repeat destruct H0.
  intuition.
  ssubst.

  cut (a0 ∈ collapse
       (so_map saisp.erase (saop sepop (v R q) (v R (stabiliser sepop R x4))))).
   intuition.
   destruct H3.
   exists x5; intuition.
   destruct H5.
   exists x6; intuition.
   destruct H5.
   exists x7; intuition.
   destruct H5.
   destruct H3.
   exists x8; exists x9.
   intuition.
   destruct H3.
   intuition.
   eapply v_stable; eauto.
   rewr trivial.

   rewrite <- (soundAxioms _ _ _ H x4).
   eexists; split; eauto.
   eexists; split; eauto.
   eexists; split; try reflexivity.
   eexists; split; eauto.
   eexists; eexists; intuition; eauto.
   eexists; split; reflexivity.
 Qed.

End SAI_Safety.
    
