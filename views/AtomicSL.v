Require Import Framework. 
Require Import Tactics. 
Require Import MySetoids.
Require Import Monoids.
Require Import Setof.
Require Import Utf8.
Require Import Language.
Require Import Bool.


Module AtomicSL (Import ats : Language.Atomics)
   (Import bs : Language.BasicSyntaxT ats)
   (Import st : Language.StateTransformers ats)
   (* Take a model of SL as an argument *)
   (Import dcsl : SafetyParams ats st) .

   (* Get Safety proof for the DCSL *)
   Module DCSLSafety := Safety ats bs st dcsl. 

   (* TODO: Fix to make this a module type *)
   Instance dcsl_monoid : Monoid dcsl.op.
   Admitted. 
   (* Assume some axioms for DCSL *)
   Parameter Axioms : dcsl.V -> ats.Atomic -> dcsl.V -> Prop.   

   (* Assume they satisfy asat for DCSL *)
   Axiom dcslaxiomsound : 
 	forall p a q, Axioms p a q 
                     -> DCSLSafety.asat p (st.interp a) q.

   Inductive ASL : V -> V -> bs.Syntax -> V -> Prop
   :=
     | atom : forall (I p q: dcsl.V)(a : Atomic), 
                  Axioms (I * p) a (I * q)
                  -> ASL I p (atom a) q
     | skip : forall (I p : V),
                  ASL I p skip p
     | loop : forall (I p : V) c, 
                  ASL I p c p 
                  -> ASL I p (loop c) p
     | sequence : forall (I p q r : V) c1 c2,
                  ASL I p c1 q 
                  -> ASL I q c2 r 
                  -> ASL I p (sequence c1 c2) r 
     | choice   : forall (I p q : V) c1 c2,
                  ASL I  p c1 q 
                  -> ASL I p c2 q 
                  -> ASL I p (choice c1 c2) q

     | parallel : forall (I p1 q1 p2 q2 : V) c1 c2,
                  ASL I p1 c1 q1 
                  -> ASL I p2 c2 q2 
                  -> ASL I 
                        (p1 * p2)
                        (parallel c1 c2)
                        (q1 * q2) 
     | hide : forall (I I' p q : V) c,
                  ASL I p c q
                  -> ASL (I * I') p c q
     | share : forall (I I' p q : V) c,
                  ASL (I * I') p c q
                  -> ASL I (p * I') c (q * I')
  . 

  Module ASLSafetyParams.
     (* The natural encoding doesn't have a single unit *)
     Inductive V_pre := 
     | def : dcsl.V -> dcsl.V -> V_pre
     | undef. 
     Definition V := V_pre. 

    Definition V_equiv v1 v2:= 
    match v1,v2 with 
    | undef,undef => True
    | def v11 v12, def v21 v22 => v11==v21 /\ v12==v22
    | _,_ => False
    end.
    Ltac destructV := match goal with H: V_pre |- _ => destruct H end.
    Instance veq: Equivalence V_equiv.
    split; repeat intro; repeat destructV; repeat ssubst; firstorder;
    repeat ssubst; reflexivity.
    Qed.
    Program Instance V_pre_setoid : Setoid V_pre.
    Program Instance V_setoid : Setoid V.
    Instance def_morph : Proper (equiv ==> equiv ==> equiv) def.
     firstorder. Qed.

     (* Assume we can decide 
         equality on dcsl propositions *)
Require Import MyClassical. 
     Definition equal_dec (v1 v2 : dcsl.V) := to_bool (v1 == v2).
     Lemma equal_dec_def : 
       forall v1 v2, equal_dec v1 v2 = true <-> v1 == v2.
     unfold equal_dec; intros; rewrite to_bool_defn. reflexivity.
     Qed.

     Definition op v1 v2:= 
       match v1,v2 with 
       | def I1 p1, def I2 p2 => 
          if equal_dec I1 I2 then def I1 (p1 * p2) else undef
       | undef,_ | _,undef => undef
       end. 

    
    Lemma aslop_commut : forall a1 a2, op a1 a2 == op a2 a1 .
    intros; repeat destructV; simpl; repeat autodestruct;
       simpl; repeat rewrite <- not_true_iff_false in *;
       repeat rewrite equal_dec_def in *;
       trivial; try (firstorder; fail).
    rewrite  op_commut. 
    intuition.
    Qed. 

      

    
    Lemma aslop_assoc : 
       forall a1 a2 a3, op (op a1 a2) a3 == op a1 (op a2 a3).
    intros; repeat destructV; 
       repeat (simpl; autodestruct);
       simpl; repeat rewrite <- not_true_iff_false in *;
       repeat rewrite equal_dec_def in *;
    repeat rewrite op_assoc; repeat ssubst; firstorder.
    Qed. 

    Instance opmorph : Proper (equiv ==> equiv ==> equiv) op.
    repeat (trivial; (intro || destructV || simpl in * || autodestruct));
    repeat rewrite <- not_true_iff_false in *;
    repeat rewrite equal_dec_def in *;
    repeat (splitup || ssubst); firstorder.
    Qed.

    Program Instance aslop_zero : Zero op := { zero := undef }.
    Next Obligation. intros; rewrite aslop_commut. firstorder. Qed. 
    Instance aslop_zeros : Zeros op := zeros_zero op.

    Program Instance aslop_many_units : ManyUnits op.
    Next Obligation.
      destructV.
      2: exists undef; split; simpl; trivial.
      2: intros; right; exists undef; rewrite aslop_commut; simpl; intuition.
      exists (def v unit).
      simpl. 
      autodestruct.
      rewrite unit_runit.
      split; try reflexivity.
      intros. destructV.
      2: simpl; left; reflexivity. 
      simpl. autodestruct.
        left; rewrite unit_runit; reflexivity.
        right; intuition. exists undef. split; reflexivity.

      simpl; repeat rewrite <- not_true_iff_false in *;
      repeat rewrite equal_dec_def in *; firstorder. 
    Qed.
              
    Instance op_monoid : SemiGroup op
      :={ 
        op_morphism := opmorph;
        op_assoc := aslop_assoc
      }.

    Instance op_comm : Commutative op := {op_commut := aslop_commut}.
    

    Definition erase  v : (Setof (A:=State)) :=
                  match v with 
                  | undef => emptyset 
                  | def I' P => dcsl.erase (I' * P)
                  end.

    
    Instance erase_morphism : Proper (equiv ==> equiv) erase.
    repeat (intro || destructV);
    simpl in *; intros; repeat splitup; 
      try (firstorder; fail).
    repeat ssubst; reflexivity. 
    Qed.     
  End ASLSafetyParams.
  
  Import ASLSafetyParams.

  Module Import ASLSafety := Safety ats bs st ASLSafetyParams.

  Program Instance ze : ZeroErase .
  Next Obligation. firstorder. Qed. 

  Instance zse : ZerosErase := ze_zse ze.

  Definition hide_fun I' V' := 
     match V' with 
     | def I1 P1  => def (I1 * I') P1
     | undef => undef
     end.

  Definition share_fun I I' V' := 
     match V' with 
     | def I1 P1  => 
	if equal_dec I1 (I * I') then def I (P1* I') else undef
     | undef => undef
     end.

  Lemma soundness_pre : 
     forall I1 p q c (Hrg: ASL I1 p c q), 
         Safe (def I1 p) c (def I1 q). 
  induction 1; subst; eauto.

  (* Axiom case *)
   intros.
   eapply Safe_asat2.
   intros r; destruct r; simpl; repeat autodestruct; simpl;
   repeat rewrite <- op_assoc;
   try eapply dcslaxiomsound; eauto;
    compute; firstorder. 


   (* Parallel case *)
   eapply Safe_para_equiv; eauto;
      simpl; repeat autodestruct; try split; try reflexivity;
      repeat rewrite <- not_true_iff_false in *;
      repeat rewrite equal_dec_def in *;
      match goal with H : not(?I==?I) |- _ 
         => elim H; reflexivity end. 


   (* Hide rule *)
     assert (def (I * I') p == (hide_fun I' (def I p))). 
       firstorder.
     assert (def (I * I') q == (hide_fun I' (def I q))). 
       firstorder.
     rewrite H; rewrite H0. clear H; clear H0. 
     eapply (simulation_rule_fun2 (hide_fun I')); eauto. 
     unfold asat. intros x; destruct x; simpl.
     (* undef cases are trivial*)
     2: simpl; intros; intro; simpl; firstorder.
     (* def case *)
     intros y a Hframe.
      (* frame like case *)
      intro r. 
      destruct r; simpl.
      2: intro; simpl; firstorder.
      autodestruct. 
      2: intro; simpl; firstorder.
      generalize (Hframe (def v (I' * v2))). 
      autodestruct.
      2:  repeat rewrite <- not_true_iff_false in *;
          repeat rewrite equal_dec_def in *;
          elim H0; reflexivity.
      clear H0. 
      simpl.  
      repeat rewrite equal_dec_def in *.
      rewrite <- H. clear H.
      rewrite <- (op_assoc v0).
      rewrite (op_commut v0). 
      repeat rewrite op_assoc. 
      intro Hre; rewrite Hre; clear Hre. 
      destruct y. 
      2: intro; simpl; firstorder. 
      intro; simpl.
      repeat autodestruct; simpl; try contradiction;
      repeat rewrite <- not_true_iff_false in *; 
      repeat rewrite equal_dec_def in *;
      rewrite H in *; clear H.
      2: elim H0; reflexivity. 
      rewrite <- (op_assoc v4). 
      rewrite (op_commut v4).
      repeat rewrite op_assoc. 
      trivial.

    (* Share rule *)
    cut (share_fun I I' (def (I * I') p) == def I (p * I')).
    cut (share_fun I I' (def (I * I') q) == def I (q * I')).
    intro H; rewrite <- H. clear H.
    intro H; rewrite <- H. clear H.
    Focus 2. 
       clear; compute -[equal_dec]; autodestruct.
       split; reflexivity.
       repeat rewrite <- not_true_iff_false in *;
       repeat rewrite equal_dec_def in *;
       elim H; reflexivity.
    Focus 2. 
       clear; compute -[equal_dec]; autodestruct.
       split; reflexivity.
       repeat rewrite <- not_true_iff_false in *;
       repeat rewrite equal_dec_def in *;
       elim H; reflexivity.
    eapply (simulation_rule_fun2 (share_fun I I')); eauto.
    clear Hrg. clear IHHrg. 
    destruct x.
    2: compute; firstorder. 
    simpl. 
    autodestruct. 
    2: compute; firstorder. 
    intros y a Hasat r.
    destruct r. 
    2: compute; firstorder. 
    simpl. 
    autodestruct. 
    2: compute; firstorder.
    repeat rewrite equal_dec_def in *.
    rewrite <- H0 in *. clear H0. 
    rewrite H in *. clear H.
    generalize (Hasat (def (I * I') v2)). clear Hasat. 
    simpl. 
    autodestruct.
    2: repeat rewrite <- not_true_iff_false in *;
       repeat rewrite equal_dec_def in *;
       elim H; reflexivity.
    clear H.
    simpl.
    rewrite op_assoc.
    rewrite (op_commut v0 I').
    rewrite op_assoc.
    intros Hre. rewrite  Hre.
    clear Hre. 
    destruct y. 
    2: compute; firstorder. 
    simpl. 
    autodestruct.
    2: compute; firstorder.
    repeat rewrite equal_dec_def in *; rewrite H.
    clear H.
    simpl.
    autodestruct. 
    2: repeat rewrite <- not_true_iff_false in *;
       repeat rewrite equal_dec_def in *;
       elim H; reflexivity.
    rewrite (op_commut v4 I').
    simpl. 
    repeat rewrite op_assoc. reflexivity.  
  Qed.
End AtomicSL. 
  