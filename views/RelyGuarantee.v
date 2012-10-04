Require Import Framework. 
Require Import Tactics. 
Require Import MySetoids.
Require Import Monoids.
Require Import Setof.
Require Import Utf8.
Require Import Language.
Require Import Classical. 

Module RelyGuarantee (Import ats : Language.Atomics)
   (Import bs : Language.BasicSyntaxT ats)
   (Import st : Language.StateTransformers ats).


   Definition A := Setof (A:= st.State).
   Definition A_pre := st.State -> Prop.
   Instance A_setoid : Setoid A := setof_setoid.

   Definition Rel := Language.ST (A:= st.State).
   Definition Rel_pre := st.State -> st.State -> Prop.
   Definition Rel_eq R1 R2 : Prop := st_trans (A:=st.State) R1 == st_trans R2.
   Instance rel_eq_equiv : Equivalence Rel_eq.
   split. firstorder. firstorder. 
   unfold Rel_eq. repeat intro. ssubst. firstorder. Qed.
   Instance Rel_setoid : Setoid Rel := { equiv:= Rel_eq }.


   Definition stable (R : Rel_pre) (P : A_pre) := 
       forall x y, P x -> R x y -> P y. 

   Definition restrict (R : Rel_pre) (P : A_pre) := 
       fun x y => R x y /\ P x.
   
   Definition contains (R1 R2 : Rel_pre) :=
       forall x y, R1 x y -> R2 x y.

Require Import Coq.Logic.Epsilon.
Require Import Classical. 
   Definition contains_dec (R1 R2 : Rel_pre) : bool := 
   (epsilon (inhabits true) (fun i => contains R1 R2 <-> i=true)).
   Lemma contains_dec_contains: 
      forall R1 R2, contains R1 R2 <-> contains_dec R1 R2 = true. 
   unfold contains_dec. 
   unfold epsilon. 
   intros. 
   destruct (epsilon_statement (fun i : bool => contains R1 R2 ↔ i = true)
       (inhabits true)). simpl.
   generalize (classic (contains R1 R2)).
   intros; casesplit.
   assert (exists x, contains R1 R2 <-> x = true). 
   exists true; intuition. 
   intuition. 
   assert (exists x, contains R1 R2 <-> x = true). 
   exists false; intuition. 
   intuition. 
   Qed.
   Lemma contains_dec_contains_false :
     forall (R1 R2 : Rel_pre), 
     contains_dec R1 R2 = false 
     <-> (exists x, exists y, R1 x y /\ not(R2 x y)). 
    intros.  
    rewrite <- Bool.not_true_iff_false.
    rewrite <- contains_dec_contains.
    split.
    intro H. generalize (not_all_ex_not _ _ H).
    intros [n H2]. generalize (not_all_ex_not _ _ H2).
    intros [m H3]. 
      generalize (not_imply_elim _ _ H3).
      generalize (not_imply_elim2 _ _ H3).
      clear; firstorder.
    firstorder.      
    Qed.



   Definition contains_A (P1 P2: A_pre) : Prop :=
      forall x, P1 x -> P2 x.

   Definition apply (R: Rel_pre) (P : A_pre) : A_pre := 
       fun x => exists y, R y x /\ P y.

   Definition intersect_pre (R1 R2: Rel) :=
      fun x y => R1 x y /\ R2 x y.

   Instance intersect_morph R1 R2 : 
      Proper (equiv ==> equiv ==> iff) (intersect_pre R1 R2).
   destruct R1; destruct R2. unfold intersect_pre. 
   repeat (intro|| ssubst). firstorder. 
   Qed. 

   Definition intersect (R1 R2 : Rel) : Rel := 
      {|st_trans := intersect_pre R1 R2|}.

   Definition union_pre (R1 R2: Rel) :=
      fun x y => R1 x y \/ R2 x y.

   Instance union_morph R1 R2 : 
      Proper (equiv ==> equiv ==> iff) (union_pre R1 R2).
   destruct R1; destruct R2. unfold union_pre. 
   repeat (intro|| ssubst). firstorder. 
   Qed. 

   Definition union (R1 R2 : Rel) : Rel := 
      {|st_trans := union_pre R1 R2|}.

   Definition and_pre (P1 P2: A) :=
      fun x => P1 x /\ P2 x.

   Instance and_morph R1 R2 : 
      Proper (equiv ==> iff) (and_pre R1 R2).
   destruct R1; destruct R2. unfold and_pre. 
   repeat (intro|| ssubst). firstorder. 
   Qed. 

   Definition and (P1 P2: A) := {| elem := and_pre P1 P2 |}.

   Inductive rg : Rel -> Rel -> A -> bs.Syntax -> A -> Prop
   :=
     | atom : forall (R G :Rel) (P : A) a (Q : A), 
                  stable R P
                  -> stable R Q
                  -> contains (restrict (interp a) P) G
                  -> subsetof (so_map_rel (interp a) P 
                        (R_morphism := st_morph (interp a))) Q
                  -> rg R G P (atom a) Q 
     | skip : forall (R G : Rel) (P : A), 
                  stable R P
                  -> rg R G P skip P 
     | loop : forall (R G : Rel) (P : A) c, 
                  stable R P
                  -> rg R G P c P 
                  -> rg R G P (loop c) P 
     | sequence : forall (R G : Rel) (P Q P' : A) c1 c2,
                  stable R P
                  -> stable R P'
                  -> stable R Q
                  -> rg R G P c1 P' 
                  -> rg R G P' c2 Q 
                  -> rg R G P (sequence c1 c2) Q 
     | choice   : forall (R G : Rel) (P Q : A) c1 c2,
                  stable R P
                  -> stable R Q
                  -> rg R G P c1 Q 
                  -> rg R G P c2 Q 
                  -> rg R G P (choice c1 c2) Q 
     | parallel : forall (R1 G1 R2 G2 : Rel) (P1 Q1 P2 Q2 : A) c1 c2,
                  stable R1 P1
                  -> stable R1 Q1
                  -> stable R2 P2
                  -> stable R2 Q2
                  -> contains G1 R2
                  -> contains G2 R1
                  -> rg R1 G1 P1 c1 Q1 
                  -> rg R2 G2 P2 c2 Q2 
                  -> rg (intersect R1 R2) 
                        (union G1 G2) 
                        (and P1 P2)
                        (parallel c1 c2)
                        (and Q1 Q2) 
     | weaken : forall (R1 R2 G1 G2 : Rel) (P : A) c (Q : A),
                  stable R1 P
                  -> stable R1 Q
                  -> rg R1 G1 P c Q 
                  -> rg (intersect R1 R2) (union G1 G2)  P c Q 

   .


  Module RGSafetyParams .
    Definition stab_V := (fun (x : A * Rel * Rel) 
                          => stable (snd (fst x)) (fst (fst x))).
    Definition V_pre := {  x : A * Rel * Rel | stab_V x }.

    Program Instance setoid_sig {A} {_: Setoid A} P : Setoid {x : A | P x}
      := { equiv := fun x y => proj1_sig x == proj1_sig y}.
    Next Obligation.
    split. firstorder. firstorder. 
    intro x; destruct x. 
    intro y; destruct y. 
    intro z; destruct z. simpl. intros; ssubst. trivial. 
    Qed. 

    Instance V_pre_setoid : Setoid V_pre := setoid_sig stab_V. 

    Definition V := option V_pre.

    Program Instance V_setoid : Setoid V. 

    Lemma preserve_stable: 
       forall (R1 R2 : Rel) (P1 P2 : A), 
       stable R1 P1
       -> stable R2 P2 
       -> stable (intersect R1 R2) (and P1 P2).
    destruct R1; destruct R2; destruct P1; destruct P2.
    compute.  firstorder. Qed. 

    Definition op (V1 V2 : V) : V :=
       match V1,V2 with
       | Some (exist (P1,R1,G1) p1), Some (exist (P2,R2,G2) p2) => 
            match contains_dec G1 R2, contains_dec G2 R1 with
            | true, true => 
               Some (exist stab_V (and P1 P2,intersect R1 R2,union G1 G2) 
                             (preserve_stable R1 R2 P1 P2 p1 p2))
            | _,_ => None
            end
       | _,_ => None
       end.

    Ltac local_destruct := 
     repeat
         match goal with 
         | a : V |- _ => destruct a; repeat destructpair; intros
         | a : V_pre |- _ => destruct a; repeat destructpair; intros
         | a : Rel |- _ => destruct a; repeat destructpair; intros
         | a : A |- _ => destruct a; repeat destructpair; intros
         | a : option _ |- _ => destruct a; repeat destructpair; intros
         | a : Setof |- _ => destruct a; intros
         end.
    Ltac local_contains_dec :=
         match goal with 
         |- context C [contains_dec ?x ?y] => case_eq (contains_dec x y); intros
         end.
    Ltac local_foo :=
       intros;
       unfold op; simpl;
       local_destruct;
(*       unfold op; simpl;
       repeat
         match goal with 
         | |- forall a : V, _ => destruct a; repeat destructpair
         end;*)
        compute -[contains_dec];
        repeat local_contains_dec;
        trivial; 
        try rewrite <- contains_dec_contains in *;
        try rewrite contains_dec_contains_false in *;
        intuition; repeat splitup; firstorder.


    Lemma op_none : forall a, op None a == None.
    local_foo. 
    Qed.

    Lemma op_none_2 : forall a, op a None == None.
    local_foo. 
    Qed.

    Lemma  rgop_commut : forall a1 a2, op a1 a2 == op a2 a1 .
    intros; local_destruct; simpl; intuition; 
    repeat local_contains_dec; intuition.
    compute. firstorder. 
    Qed.

    Lemma rgop_assoc : 
       forall a1 a2 a3, op (op a1 a2) a3 == op a1 (op a2 a3).
    local_foo. 
    Qed.

   Program Definition rgunit : V := 
      Some ( {| elem := fun x => True |}, 
             {| st_trans := fun x y => True|},
             {| st_trans := fun x y => False|}).
   Solve All Obligations using firstorder.


   Lemma rgunit_lunit : forall a, op rgunit a == a.
    local_foo.
    Qed.

    Lemma rgunit_runit : forall a, op a rgunit == a.
    local_foo.
    Qed.

    Instance opmorph' : Proper (eq ==> equiv ==> equiv) op.
    repeat intro. subst.
    destruct x0; destruct y0; 
      try reflexivity; try (inversion H0; fail). 
    destruct y. 
    2: simpl; reflexivity.
    destruct v; destruct v0; destruct v1.
    repeat destructpair. 
    simpl in *. 
    repeat (compute [prod_equiv] in H0; simpl in H0).
    repeat (autodestruct; try reflexivity);
    repeat rewrite contains_dec_contains_false in *;
    repeat rewrite <- contains_dec_contains in *.
    simpl. compute -[st_trans elem]. simpl. 
    unfold contains in *.
    unfold Rel_eq in *. 
    repeat split. firstorder.  
    firstorder.
    firstorder.
    firstorder.
    firstorder.
    firstorder.
    firstorder.
    firstorder.
    intuition.
    compute -[st_trans] in H6; simpl in H6.
    right. firstorder.
    intros; casesplit. 
      triv. compute -[st_trans] in H0; simpl in H0. 
      right; firstorder.
    (* Same again *)
    simpl. compute -[st_trans elem]. simpl. 
    unfold contains in *.
    unfold Rel_eq in *. 
    repeat split. firstorder.  
    firstorder.
    firstorder.
    firstorder.
    Qed.

    Instance opmorph : Proper (equiv ==> equiv ==> equiv) op.
    repeat intro. ssubst.  
    rewrite rgop_commut.
    ssubst. eapply rgop_commut. 
    Qed. 

    Instance op_monoid : SemiGroup op
      :={ 
        op_morphism := opmorph;
        op_assoc := rgop_assoc
      }.

    Instance op_monoid_full : Monoid op
      :={ 
        unit := rgunit;
        unit_lunit := rgunit_lunit;
        unit_runit := rgunit_runit
      }.


    Instance op_comm : Commutative op := {op_commut := rgop_commut}.
    
    Infix "*" := op.

    Definition erase : V -> (Setof (A:=State)) :=
         fun V => match V with 
                  | Some (exist (P,_,_) _) => P 
                  | None => emptyset
                  end.
    
    Instance erase_morphism : Proper (equiv ==> equiv) erase.
    intro. unfold erase. local_foo; compute in *.
    firstorder. firstorder.  
    Qed. 
  End RGSafetyParams.

  Module RGSafety := Safety ats bs st RGSafetyParams.

  Import RGSafety.
  Import RGSafetyParams.

  Lemma subset_and :
    forall p q r, 
       subsetof p q 
       -> subsetof p r 
       -> subsetof p (and q r).
  intros; local_destruct.
  compute in *.
  firstorder. 
  Qed. 

  Lemma subset_and_2 :
    forall q r, 
       subsetof (and q r) q .
  intros; local_destruct.
  compute in *.
  firstorder. 
  Qed.

  Lemma subset_so_map_rel :
    forall (R : Rel) p q, subsetof p q ->
    subsetof (so_map_rel R p (R_morphism := st_morph R))
             (so_map_rel R q (R_morphism := st_morph R))
             .
  intros; local_destruct. compute in *. firstorder. 
  Qed.

  Lemma all_stable: forall R G P Q C, rg R G P C Q -> 
      stable R P /\ stable R Q.
  inversion 1; intuition;
   eauto using preserve_stable;
   compute in *;
   firstorder.
  Qed.

   Program Definition rg_g x1 y1 : V := 
      Some ( {| elem := fun x => True |}, 
             {| st_trans := fun x y => True|},
             {| st_trans := fun x y => x1 == x /\ y == y1 |}).
   Next Obligation. firstorder. Qed.
   Next Obligation. firstorder. Qed.
   Next Obligation. repeat intro. repeat ssubst. firstorder. Qed.
   Next Obligation. firstorder. Qed.

   Program Definition rg_r x1 y1 : V := 
      Some ( {| elem := fun x => True |}, 
             {| st_trans := fun x y => not(x1 == x /\ y == y1) |},
             {| st_trans := fun x y => False |}).
   Next Obligation. firstorder. Qed.
   Next Obligation. repeat intro. repeat ssubst. firstorder. Qed.
   Next Obligation. firstorder. Qed.
   Next Obligation. firstorder. Qed.


  Lemma asat_rg_shrink : 
     forall p1 a q1, 
       asat p1 a q1->
    forall  (P : A) (R G : Rel) p (P' : A) (R' G' : Rel) p',
       p1 = (Some (exist stab_V (P,R,G) p)) -> 
       q1 = (Some (exist stab_V (P',R',G') p')) ->
       (exists x, so_map_rel a P (R_morphism:=st_morph a) x) ->  
              (not (exists x, exists y, R x y /\ not (R' x y))).
   intros. 
   intro.
   repeat splitup. subst. 
   red in H.
   generalize (H (rg_g x x0)). 
   assert (erase (Some (exist stab_V (P, R, G) p) * rg_g x x0) == P).
     unfold rg_g.
     unfold op. 
     local_destruct; repeat local_contains_dec; compute. firstorder.
        try rewrite contains_dec_contains_false in *; simpl in *;
        repeat splitup. ssubst. ssubst. firstorder.

        try rewrite contains_dec_contains_false in *; simpl in *;
        firstorder.
        
        rewrite H0.
   assert (Some (exist stab_V (P', R', G') p') * rg_g x x0 = None).
     clear -H5.
     unfold op. local_destruct; compute -[equiv contains_dec]; 
       repeat local_contains_dec; compute -[equiv]; trivial.
        try rewrite <- contains_dec_contains in *.
        compute -[equiv] in *. elim H5. eapply H0. split; reflexivity.  
   rewrite H1.  simpl. firstorder.
  Qed.  
    
  Lemma asat_rg_shrink' : 
     forall p1 a q1, 
       asat p1 a q1->

    forall  (P : A) (R G : Rel) p (P' : A) (R' G' : Rel) p',
       p1 = (Some (exist stab_V (P,R,G) p)) -> 
       q1 = (Some (exist stab_V (P',R',G') p')) ->
       (exists x, so_map_rel a P (R_morphism:=st_morph a) x) ->  
              (not (exists x, exists y, G' x y /\ not (G x y))).
   intros. 
   intro.
   repeat splitup. subst. 
   red in H.
   generalize (H (rg_r x x0)). 
   assert (erase (Some (exist stab_V (P, R, G) p) * rg_r x x0) == P).
     unfold rg_r.
     unfold op. 
     local_destruct; repeat local_contains_dec; compute. firstorder.
        try rewrite contains_dec_contains_false in *; simpl in *; 
          repeat splitup; contradiction.
        simpl in *. 
         try rewrite contains_dec_contains_false in *; simpl in *;
         firstorder.
         elim H4.  intro. splitup; ssubst. ssubst. contradiction. 

        
        rewrite H0.
   assert (Some (exist stab_V (P', R', G') p') * rg_r x x0 = None).
     clear H H0. 
     unfold op. local_destruct; compute -[equiv contains_dec]; 
       repeat local_contains_dec; compute -[equiv]; trivial.
        try rewrite <- contains_dec_contains in *.
        compute -[equiv] in *.
        eelim H. eauto. firstorder.  

 rewrite H1. 
 clear -H4. compute in *. firstorder. 
 Qed.

(* This is the classical combination of the previous two lemma,
   with some work to use a match to make it apply more nicely. *)
  Lemma asat_rg_shrink2 : 
     forall p1 a q1, 
       asat p1 a q1->
          match p1,q1 with
          | (Some (exist (P,R,G) p)),
            (Some (exist (P',R',G') p'))
               => (exists x, so_map_rel a P (R_morphism:=st_morph a) x) ->  
              (contains R R' /\ contains G' G)
          | _,_ => True
          end. 
  intros p1 a q1 Hasat. 
  generalize (asat_rg_shrink p1 a q1 Hasat); intro Hasats1.
  generalize (asat_rg_shrink' p1 a q1 Hasat); intro Hasats2.
  local_destruct; trivial.
  eapply NNPP.
  intro Hor.
  generalize (not_and_or _ _ Hor).
  clear Hor; intro Hor; elim Hor; clear Hor;
  intro Hco.
  (* Rely case *)
  eelim Hasats1.
   reflexivity.
   reflexivity.
   trivial.
  compute in Hco.
  generalize (not_all_ex_not _ _ Hco).
  clear.
  intros [x Hco].
  generalize (not_all_ex_not _ _ Hco).
  clear.
  intros [y Hco].
  exists x; exists y. simpl. 
  generalize (not_imply_elim _ _ Hco).
  generalize (not_imply_elim2 _ _ Hco).
  auto.
  (* Guarantee case *)
  eelim Hasats2.
   reflexivity.
   reflexivity.
   trivial.
  compute in Hco.
  generalize (not_all_ex_not _ _ Hco).
  clear.
  intros [x Hco].
  generalize (not_all_ex_not _ _ Hco).
  clear.
  intros [y Hco].
  exists x; exists y. simpl. 
  generalize (not_imply_elim _ _ Hco).
  generalize (not_imply_elim2 _ _ Hco).
  auto.
  Qed.
 
  Definition sim_fun_pre R2 G2 (Vp : A * Rel * Rel) :=  
     match Vp with 
     | (P, R, G) 
         => (P, (intersect R R2), (union G G2)) 
     end.

  Lemma stab_V_pre : 
    forall R G a,  stab_V a -> stab_V (sim_fun_pre R G a).
  unfold sim_fun_pre. intros; repeat destructpair.
  compute [stab_V] in *. simpl in *.
  unfold stable in *. unfold intersect_pre. firstorder. 
  Qed.

  Definition sim_fun R2 G2 (V1 : V) : V :=  
     match V1 with 
     | Some (exist a p) => 
         Some (exist stab_V (sim_fun_pre R2 G2 a) (stab_V_pre R2 G2 a p))
     | None => None
     end. 


Ltac autodestruct2 := 
  match goal with 
  |  |- context C [if ?foo then _ else _] => 
	match foo with 
        | context D [if _ then _ else _] => fail 1
	| _ => let Heq := fresh in case_eq foo; intro Heq; try rewrite Heq in *; subst        
        end
  |  H : context C [if ?foo then _ else _] |- _ => 
	match foo with 
        | context D [if _ then _ else _] => fail 1
	| _ => let Heq := fresh in case_eq foo; intro Heq; try rewrite Heq in * ; subst
        end
  end.


  Lemma soundness_pre : 
     forall (R G : Rel) (P Q : A) C (Hrg: rg R G P C Q), 
         exists p1, exists p2,
         Safe (Some (exist stab_V (P,R,G) p1)) 
               C (Some (exist stab_V (Q,R,G) p2)).
  intros.

  generalize (all_stable _ _ _ _ _ Hrg). 
  intros [p1 p2]; exists p1; exists p2.   
  induction Hrg;
  match goal with
  | [ |- context [_ ;; _]] => use_foralls
  | _ => idtac end;  
  eauto.

  (* Skip Case *)
  Focus 2.
  assert  (Some (exist stab_V (P, R, G) p1) 
            == Some (exist stab_V (P, R, G) p2)).
  local_foo. 
  rewrite H0.  
  eauto.

  (* Loop Case *)
  Focus 2.  
  assert  (Some (exist stab_V (P, R, G) p1) 
            == Some (exist stab_V (P, R, G) p2)).
  local_foo. 
  rewrite H0.  
  eauto.
  
  (* Atomic case *)
  eapply Safe_asat. unfold asat.
  intro r. 
   (* Case split on whether context combines well *)
   case_eq (Some (exist stab_V (P, R, G) p1) * r); simpl erase.
     (* Well defined case *)
     intro p; repeat destructpair.
     simpl op. 
     destruct r; try congruence.
     destruct v; destruct p. 
      (* Context is Some *)
      repeat destructpair. 
      repeat match goal with 
        | |- context C [contains_dec ?x ?y] => case_eq (contains_dec x y); intros
      end;
      try autodestruct; try congruence;
      simpl erase;
      try rewrite <- contains_dec_contains in *;
      try rewrite contains_dec_contains_false in *.
      inversion H4; clear H4. 
      eapply subset_and.
      (* Standard post *)
        erewrite subset_so_map_rel;
        eauto using subset_and_2.
      (* Preserve view *)
        clear -H1 s H3. destruct P. destruct a1.
        destruct (interp a). destruct r2. simpl in *.
        compute in *.  firstorder.
     (* Not well defined case *)
     intros. red. unfold so_map_rel. simpl. firstorder. 


  (* Parallel case *)
  use_foralls;  eapply Safe_para_equiv; eauto;
  red; simpl; repeat autodestruct; local_foo.


  (* Weakening case *)
  assert ((Some (exist stab_V (P, intersect R1 R2, union G1 G2) p1))
      == sim_fun R2 G2 (Some (exist stab_V (P,R1,G1) H))).
    simpl; reflexivity.
  rewrite H1. 
  assert ((Some (exist stab_V (Q, intersect R1 R2, union G1 G2) p2))
      == sim_fun R2 G2 (Some (exist stab_V (Q,R1,G1) H0))).
    simpl; reflexivity.
  rewrite H2.
  eapply (simulation_rule_fun (sim_fun R2 G2)); eauto.
  
  (* Requirement: f-step  *)
  intros x y a.
  intros Hasat. generalize (asat_rg_shrink2 _ _ _ Hasat). intros Hasat_shrunk. 
  unfold asat in *.
  intros r; generalize (Hasat r); clear Hasat. 
  case_eq (sim_fun R2 G2 x * r).
  (*  = None *)
  2: compute; firstorder.  
  (*  = Some v *)  
  intros v Hop. destruct x; simpl in Hop; try congruence.
  destruct v0. repeat destructpair.
  destruct r;
  simpl in Hop; try congruence.
  destruct v0; repeat destructpair. 
  simpl.

  repeat (autodestruct2; try congruence);
     try rewrite <- contains_dec_contains in *;
     try rewrite contains_dec_contains_false in *.

  (* Other two cases are trivial *)
  2:  unfold contains in *; firstorder.
  2:  unfold contains in *; firstorder.
 
  inversion Hop.  clear Hop.
  destruct y; simpl; trivial. 
  destruct v0. repeat destructpair. simpl. 
  repeat autodestruct; try congruence; trivial;
     try rewrite <- contains_dec_contains in *;
     try rewrite contains_dec_contains_false in *.
  unfold contains; repeat splitup. 
firstorder.
  firstorder. 
  firstorder. 
  firstorder. 
  Qed. 
  

End RelyGuarantee.