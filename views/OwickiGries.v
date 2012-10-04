Require Import Framework. 
Require Import Tactics. 
Require Import MySetoids.
Require Import Monoids.
Require Import Setof.
Require Import Utf8.
Require Import Language.
Require Import Bool.
Require Import MyClassical.

Module OwickiGries (Import ats : Language.Atomics)
   (Import bs : Language.BasicSyntaxT ats)
   (Import st : Language.StateTransformers ats).


   Definition P := Setof (A:= st.State).
   Definition PP := Setof (A := P).
   Program Instance Step_setoid : Setoid (prod P Atomic). 
   Definition AA := Setof (A:= prod P Atomic). 

   Definition and_pre {A} {_ : Setoid A} (P1 P2 : Setof (A:=A)) :=
      fun x => P1 x /\ P2 x.

   Instance and_morph {A} {_ : Setoid A} (P1 P2 : Setof (A:=A))
    :  Proper (equiv ==> iff) (and_pre P1 P2).
   destruct P1; destruct P2. unfold and_pre. 
   repeat (intro|| ssubst). firstorder. 
   Qed. 

   Definition and {A} {_ : Setoid A} 
        (P1 P2 : Setof (A:=A)) := 
          {| elem := and_pre P1 P2; 
             elem_morph := and_morph P1 P2 |}.

   Definition or_pre {A} {_ : Setoid A} (P1 P2 : Setof (A:=A)) :=
      fun x => P1 x \/ P2 x.
   Instance or_morph {A} {_ : Setoid A} (P1 P2 : Setof (A:=A))
    :  Proper (equiv ==> iff) (or_pre P1 P2).
   destruct P1; destruct P2. unfold or_pre. 
   repeat (intro|| ssubst). firstorder. 
   Qed. 

   Definition or {A} {_ : Setoid A} 
        (P1 P2 : Setof (A:=A)) := 
          {| elem := or_pre P1 P2; 
             elem_morph := or_morph P1 P2 |}.

   Definition interfere (Ps : PP) (As : AA) := 
      forall a p q, As (p,a) -> Ps q -> 
           subsetof (so_map_rel (interp a) (and p q) 
              (R_morphism := st_morph (interp a))) q.
         

   Inductive OG : PP -> AA -> P -> bs.Syntax -> P -> Prop
   :=
     | atom : forall (Ps : PP) (As : AA) (p : P) (a : Atomic) (q : P), 
                  Ps p -> Ps q -> As (p,a) -> 
                    subsetof (so_map_rel (interp a) p 
                        (R_morphism := st_morph (interp a))) q
                  -> OG Ps As p (atom a) q
     | skip : forall (Ps : PP) (As : AA) (p : P),  
                  Ps p -> 
                  OG Ps As p skip p
     | loop : forall (Ps : PP) (As : AA) (p : P) c, 
                  OG Ps As p c p 
                  -> OG Ps As p (loop c) p
     | sequence : forall (Ps : PP) (As : AA) (p p' q : P) c1 c2,
                  OG Ps As p c1 p' 
                  -> OG Ps As p' c2 q 
                  -> OG Ps As p (sequence c1 c2) q 
     | choice   : forall (Ps : PP) (As : AA) (p q : P) c1 c2,
                  OG Ps As p c1 q 
                  -> OG Ps As p c2 q 
                  -> OG Ps As p (choice c1 c2) q

     | parallel : forall (Ps1 Ps2 : PP) (As1 As2 : AA)
                           (p1 q1 p2 q2 : P) c1 c2,
                  interfere Ps1 As2
                  -> interfere Ps2 As1
                  -> OG Ps1 As1 p1 c1 q1 
                  -> OG Ps2 As2 p2 c2 q2 
                  -> OG (or Ps1 Ps2)
                        (or As1 As2) 
                        (and p1 p2)
                        (parallel c1 c2)
                        (and q1 q2) 
     | weaken : forall (Ps1 Ps2 : PP) (As1 As2 : AA)
                           (p q: P) c,
                  OG Ps1 As1 p c q 
                  -> OG (or Ps1 Ps2)
                        (or As1 As2) 
                        p c q
  . 

    
   Definition interfere_dec (Ps :PP) (As : AA) : bool := 
     to_bool (interfere Ps As).
   Lemma interfere_defn : 
      forall Ps As, interfere_dec Ps As = true <-> interfere Ps As. 
  unfold interfere_dec; intros; rewrite to_bool_defn; reflexivity.   
  Qed.

  Module OGSafetyParams.
    Definition wf (x : PP * AA * P) : Prop :=
       match x with 
       | (Ps,_,p) => 
           exists Ps',  subsetof Ps' Ps 
              /\ setof_intersection Ps' == p
       end.

    Program Instance setoid_sig {A} {_: Setoid A} P : Setoid {x : A | P x}
      := { equiv := fun x y => proj1_sig x == proj1_sig y}.
    Next Obligation.
    split. firstorder. firstorder. 
    intro x; destruct x. 
    intro y; destruct y. 
    intro z; destruct z. simpl. intros; ssubst. trivial. 
    Qed. 
    Definition V_pre := { x : PP * AA * P| wf x  }.

    Instance V_pre_setoid : Setoid V_pre := setoid_sig wf. 


    Definition V := option V_pre.
    Program Instance V_setoid : Setoid V.

    Lemma wf_pres :
      forall Ps1 As1 p1 Ps2 As2 p2, 
       wf (Ps1,As1,p1)
       -> wf (Ps2,As2,p2)
       -> wf (or Ps1 Ps2,or As1 As2, and p1 p2).
    unfold wf. intros. repeat splitup. 
    exists (or x0 x).
    split. clear -H H0.
    compute -[elem] in *. simpl. firstorder. 
    clear -H2 H3.
    unfold setof_intersection in *.
    simpl in *.  
    unfold setofeq in *. 
    simpl in *.
    unfold setof_preintersection in *.
    unfold and_pre. unfold or_pre. 
    firstorder.
    Qed. 
 
    Definition op (v1 v2 : V) : V := 
    match v1,v2 with
    | Some (exist (Ps1,As1,p1) prf1),
      Some (exist (Ps2,As2,p2) prf2) =>
       if interfere_dec Ps1 As2 && interfere_dec Ps2 As1 then 
            Some (exist wf (or Ps1 Ps2, or As1 As2, and p1 p2) 
                 (wf_pres Ps1 As1 p1 Ps2 As2 p2 prf1 prf2))
       else None
    | _,_ => None
    end.

   Lemma or_assoc {A} `{Setoid A} : forall a1 a2 a3 , 
        setofeq (or (or a1 a2) a3) (or a1 (or a2 a3)).
   destruct a1; destruct a2; destruct a3. 
   compute. intuition. 
   Qed. 
   Lemma and_assoc {A} `{Setoid A} : forall a1 a2 a3, 
        and (and a1 a2) a3 == and a1 (and a2 a3).
   destruct a1; destruct a2; destruct a3. 
   compute. intuition. 
   Qed.

   Lemma op_None : forall a, op a None = None. 
   destruct a.  
     destruct v; repeat destructpair; compute; trivial.
   simpl; trivial.
   Qed.  
   Lemma op_None2 : forall a, op None a = None. 
   simpl; trivial.
   Qed.  
    
   Lemma op_commut : forall a1 a2,  
      op a1 a2 == op a2 a1.
   destruct a1.
   (* None case *)
   2: intros; rewrite op_None; simpl; trivial.
   (* Some case *)
   destruct a2.
   (* None case *) 
   2: intros; rewrite op_None; simpl; trivial.
   destruct v; destruct v0. repeat destructpair.
   simpl . unfold andb. 
   repeat autodestruct; compute -[elem]; trivial.
   simpl. intuition. 
   Qed. 

   Lemma interfere_or :
     forall a b c, 
         (interfere a c /\ interfere b c) 
          <->  interfere (or a b) c .
   intros; destruct a; destruct b; destruct c.
   unfold interfere. simpl. unfold or_pre. 
   simpl. intuition. 
   Qed. 

   Lemma interfere_and :
     forall a c d, 
         (interfere a c /\ interfere a d) 
          <->  interfere a (or c d) .
   intros; destruct a; destruct d; destruct c.
   unfold interfere. simpl;  unfold or_pre. 
   simpl. intuition. 
   Qed. 

   Lemma op_assoc : forall a1 a2 a3, 
        op (op a1 a2) a3 == op a1 (op a2 a3).
   destruct a1; destruct a2; destruct a3; 
     try repeat rewrite op_None; try repeat rewrite op_None2;
       try reflexivity.
   unfold op. 
   destruct v; destruct v0; destruct v1.
   repeat destructpair. 
   simpl. unfold andb. 
   repeat autodestruct; trivial;
   try rewrite <- not_true_iff_false in *;
   try rewrite interfere_defn in *; 
   try rewrite <- interfere_or in *;
   try rewrite <- interfere_and in *;
   intuition. 

   unfold option_equiv. 
   unfold equiv.
   simpl. unfold prod_equiv. simpl. 
   unfold prod_equiv. simpl.
    rewrite and_assoc.
   unfold setofeq. 
   split.
   2: reflexivity.
  (*    Should use: or_assoc.
      Didn't work: Something is specialised wrong here *)
   destruct p; destruct p1; destruct p3; destruct p2; 
      compute; intuition. 
   Qed.

   Program Definition EmptySet {A} {_:Setoid A}: Setof (A:=A)
   := 
       {| elem := fun x => False |}.
   Next Obligation. firstorder. Qed.

   Program Definition UnivSet {A} {_:Setoid A}: Setof (A:=A)
   := 
       {| elem := fun x => True |}.
   Next Obligation. firstorder. Qed.

   Program Definition unit : V:= Some ( EmptySet, EmptySet, UnivSet).
   Next Obligation.
   exists EmptySet.
   split. reflexivity.
   compute. intuition. Qed.

   Lemma interfere_emp_1 :
     forall a, True <-> interfere a EmptySet.
   intros; intuition. 
   compute. intuition.
   Qed.   
   Lemma interfere_emp_2 :
     forall a, True <-> interfere EmptySet a. 
   intros; intuition. 
   compute. intuition.
   Qed.   


   Lemma unit_lunit : forall a, op unit a == a.
   unfold op. unfold unit.
   intro a; destruct a; intuition.
   destruct v; repeat destructpair.   
   unfold andb.  
   simpl. repeat autodestruct;
   try rewrite <- not_true_iff_false in *;
   try rewrite interfere_defn in *; 
   try rewrite <- interfere_emp_1 in *;
   try rewrite <- interfere_emp_2 in *;
   intuition.
   compute. intuition. 
   Qed.

    Lemma unit_runit : forall a, op a unit == a.
    intros; rewrite op_commut.
    eapply unit_lunit. 
    Qed.

   Instance op_monoid : SemiGroup op.
   split. 2: eapply op_assoc. 
   repeat intro. 
   unfold op. 
   destruct x; destruct y; try reflexivity;
   try inversion H. 
   destruct v; destruct v0; repeat destructpair.
   simpl in *. 
   destruct x0; destruct y0; try reflexivity;
   try inversion H0.
   destruct v; destruct v0; repeat destructpair.
   simpl in *.
   unfold andb.  
   repeat (autodestruct; try reflexivity).
   simpl.
   compute [prod_equiv] in *.
   simpl in *. repeat splitup. 
   compute [prod_equiv] in *.
   simpl in *. repeat splitup.
   compute -[elem]. simpl. unfold setofeq in *. 
   repeat split; try intro; try casesplit.
   left; firstorder. 
   right; firstorder. 
   left; firstorder.
   right; firstorder. 
   left; firstorder. 
   right; firstorder. 
   left; firstorder.
   right; firstorder. 
   firstorder. 
   firstorder. 
   firstorder.
   firstorder.
 (* Contradiction cases *) 
   repeat rewrite <- not_true_iff_false in *;
   repeat rewrite interfere_defn in *.
   elim H8.
   generalize H6.  
   compute [prod_equiv] in *. simpl in *. repeat splitup.
   unfold interfere in *.
   automatcher. 
   automatcher. 
   automatcher. 
   rewrite H19. rewrite H9. trivial. 
(* 2 *)
   repeat rewrite <- not_true_iff_false in *;
   repeat rewrite interfere_defn in *.
   elim H7.
   generalize H5.  
   repeat compute [prod_equiv] in *. simpl in *. repeat splitup.
   unfold interfere in *.
   automatcher. 
   automatcher. 
   automatcher. 
   rewrite H17. rewrite H3. trivial. 
(* 3 *)
   repeat rewrite <- not_true_iff_false in *;
   repeat rewrite interfere_defn in *.
   elim H6.
   generalize H8.  
   repeat compute [prod_equiv] in *. simpl in *. repeat splitup.
   unfold interfere in *.
   automatcher. 
   automatcher. 
   automatcher. 
   rewrite H19. rewrite H9. trivial.
(* 4 *)
   repeat rewrite <- not_true_iff_false in *;
   repeat rewrite interfere_defn in *.
   elim H5.
   generalize H6.  
   repeat compute [prod_equiv] in *. simpl in *. repeat splitup.
   unfold interfere in *.
   automatcher. 
   automatcher. 
   automatcher. 
   rewrite H17. rewrite H3. trivial.
   Qed.  

   Instance op_monoid_full : Monoid op := {
     unit := unit;
     unit_runit := unit_runit;
     unit_lunit := unit_lunit
   }.
    
   Instance op_comm : Commutative op.
   split. eapply op_commut.
   Qed. 
  
   Infix "*" := op.

   Definition erase (v : V) : Setof (A:=State)
     := match v with 
        | Some (exist (_,_,p) _) => p  
        | None => emptyset
        end.
   
    Instance erase_morphism :
        Proper (equiv ==> equiv) erase.
    repeat intro.
    unfold erase. 
    destruct x; destruct y;
    try reflexivity; try inversion H.
    destruct v; destruct v0; repeat destructpair.
    simpl in *. 
    rewrite H1. reflexivity. 
    Qed.
  End OGSafetyParams.

  Module OGSafety := Safety ats bs st OGSafetyParams.

  Import OGSafety.
  Import OGSafetyParams.

  Lemma in_wf : 
    forall (Ps : PP) (As : AA) (p : P), Ps p -> wf (Ps,As,p).
  intros. 
  exists (singleton p).
  split. 
  intro; intro. compute -[equiv] in H0.
  splitup. splitup. ssubst. 
  destruct Ps. red.  red in H. 
   
  Focus 2.
  unfold setof_intersection.
  unfold singleton.
  unfold setof_preintersection. simpl.
  unfold setofeq.
  split. simpl. firstorder. 
  simpl.  firstorder. compute in *.  firstorder. 
  Qed.

  Lemma wf_pres2 :
      forall Ps1 As1 p Ps2 As2, 
       wf (Ps1,As1,p)
       -> wf (or Ps1 Ps2,or As1 As2,p).
       unfold wf.
       intros Ps As p q c. 
       automatcher. 
       automatcher; trivial.
       compute -[elem]. simpl. 
       firstorder.
  Qed.

  Definition sim_fun Ps As v := 
     match v with 
     | Some (exist (Ps1,As1,p) prf)
        => Some (exist wf (or Ps1 Ps,or As1 As, p) 
               (wf_pres2 Ps1 As1 p Ps As prf))
     | None => None 
     end.

  Program Definition complement {A} {b : Setoid A} 
     (x : Setof (A:=A)) : (Setof (A:=A)) :=
     {| elem := fun y => not (elem x y) |}.
  Next Obligation.
    split; intros; intro; ssubst; contradiction.
  Qed. 
  Instance complement_proper {A} {b : Setoid A} : 
     Proper (equiv ==> equiv) complement. 
  repeat intro. unfold complement. simpl.   
  split; firstorder.
  Qed. 

  Lemma wf_pre_post : 
     forall (Ps : PP) (As : AA) (p q : P) c 
        (Hog: OG Ps As p c q), 
         wf (Ps,As,p) /\ wf (Ps,As,q).
  generalize in_wf. 
  induction 2; repeat splitup; eauto. 
  split; eapply wf_pres; eauto. 
  split; eapply wf_pres2; eauto. 
  Qed.


  Lemma soundness_pre : 
     forall (Ps : PP) (As : AA) (p q : P) c 
        (Hog: OG Ps As p c q), 
         exists prf1, exists prf2,
         Safe (Some (exist wf (Ps,As,p) prf1)) 
               c (Some (exist wf (Ps,As,q) prf2)).
  intros Ps As p q c HOG.
  generalize (wf_pre_post _ _ _ _ _ HOG).
  intros [prf1 prf2].
    exists prf1; exists prf2.
  induction HOG.

  (* Skip case *)
  Focus 2. 
  assert (Some (exist wf (Ps, As, p) prf1) 
          == Some (exist wf (Ps, As, p) prf2)). firstorder.
  rewrite H0.    
  eapply Safe_skip.

  (* loop case *)
  Focus 2.
  assert (Some (exist wf (Ps, As, p) prf1) 
          == Some (exist wf (Ps, As, p) prf2)). firstorder. 
  rewrite H. eauto.

  (* Seq case *)
  Focus 2.
  generalize (wf_pre_post _ _ _ _ _ HOG1).
  intros [prf3 prf4].
  generalize (IHHOG2 prf4); clear IHHOG2; intro IHHOG2.
  eapply Safe_seq; eauto; eapply IHHOG1.

  (* Choice case *)
  Focus 2. eauto.

  (* Parallel case *)
  Focus 2.
  generalize (wf_pre_post _ _ _ _ _ HOG1).
  generalize (wf_pre_post _ _ _ _ _ HOG2).
  intros; repeat splitup.
  use_foralls. 
  eapply (Safe_para_equiv); eauto;
  simpl; unfold andb;
  repeat autodestruct; 
  simpl; try reflexivity;
  rewrite <- not_true_iff_false in *;
  rewrite interfere_defn in *; intuition.  

  (* Atomic case *) 
  eapply Safe_asat.
  unfold asat.   
  unfold erase.
  intro r. 
  case_eq (Some (exist wf (Ps, As, p) prf1) * r).
  (* Bad pre *)
  Focus 2. 
    unfold subsetof; unfold so_map_rel. 
    intros Ha xx Hb; compute in Hb; firstorder. 
  (* Proper pre. *)
  intros. 
  assert (r <> None).
  intro. subst.
  compute in *. congruence.
  destruct r; try congruence. clear H4.  
  (* r = Some *)
  destruct v0. repeat destructpair. 
  destruct v. repeat destructpair.
  (* Extract verything useful from op defn *)
   unfold op in H3. unfold andb in H3.
   repeat autodestruct; try congruence. 
   rewrite interfere_defn in *. intuition.
   inversion H3. clear H3. subst.
  
  intro; intro.
  (* Weird implicit arguments, not sure why be they are needed *) 
  case_eq (@Some (@sig (PP * AA * P) wf) (@exist (PP * AA * P) wf (Ps, As, q) prf2) *
  @Some V_pre
    (@exist (PP * AA * P) (fun x : PP * AA * P => wf x) (p0, a0, p1) w)).
  (* None case has a contradiction *)
  Focus 2.  
  intro Hcontra.
   unfold op in Hcontra; unfold andb in Hcontra. 
   repeat autodestruct; try congruence. 
   rewrite <- not_true_iff_false in *.
   rewrite interfere_defn in *. intuition.
   rewrite <- not_true_iff_false in *.
   rewrite interfere_defn in *. intuition.
  (* Some case *)
  intros v.
  intros Hop. 
   unfold op in Hop; unfold andb in Hop. 
   repeat autodestruct; try congruence.
   inversion Hop; subst.
  assert (q a1 /\ p1 a1). 
  Focus 2. clear -H8. compute.   firstorder.
  split.
  (* sound for us *)
  clear -H2 H3. compute in *. 
  destruct q. destruct (interp a). destruct p.
  firstorder.    
  (* sound for frame *)
  inversion w.
  splitup.  
  rewrite <- H10 in *.  
  rewrite interfere_defn in *.
  clear -H3 H9 H7 H1 H10.

  (* Lemma to move big intersection out. *)
  Lemma foo : 
    forall a (p : P) (q : Setof  (A := P)) ,
        (forall u, q u -> 
            subsetof (so_map_rel (interp a) (and p u)
                        (R_morphism:=st_morph (interp a))) u)
        -> subsetof (so_map_rel (interp a) 
                                (and p (setof_intersection q))
                        (R_morphism:= st_morph (interp a)))
                    (setof_intersection q).
  unfold so_map_rel. unfold subsetof. simpl.  
  intros. repeat splitup.
  intro. intro. firstorder.  
  Qed.
   

  eapply foo. 
  
  Require Import Classical. 

  intros; eapply H7; eauto.

  clear H7. clear -H10 H3. 
  compute in *. firstorder.
  

  (* Weakening case *)
  (* Rearrange to apply rule *)
  generalize (wf_pre_post _ _ _ _ _ HOG).
  intros [Hwfpre Hwfpost].
  cut (Some (exist wf (or Ps1 Ps2, or As1 As2, p) prf1)
       == (sim_fun Ps2 As2 (Some (exist wf (Ps1, As1, p) Hwfpre)))).
  cut (Some (exist wf (or Ps1 Ps2, or As1 As2, q) prf2)
       == (sim_fun Ps2 As2 (Some (exist wf (Ps1, As1, q) Hwfpost)))).
  2: unfold sim_fun; simpl; reflexivity.
  2: unfold sim_fun; simpl; reflexivity.
  intros Hre Hre2; rewrite Hre; rewrite Hre2; clear Hre Hre2. 
  (* Apply rule *)
  eapply (simulation_rule_fun (sim_fun Ps2 As2)). 
  2: eauto.  clear. 
  (* f-step part *)
  intros x y a. 
  destruct x. 
  2: unfold sim_fun; unfold asat; simpl; intros; 
     intro; simpl; firstorder.
  (* Case split on terminates *)
  destruct y. 
    (* Terminates case *)  
    intros Hasat. generalize Hasat. clear Hasat.
    destruct v; destruct v0; repeat destructpair. 
    automatcher.
    (* Case on frame being invalid *)
    case_eq (op
           (sim_fun Ps2 As2
              (@Some V_pre
                 (@exist (prod (prod PP AA) P)
                    (fun x0 : prod (prod PP AA) P => wf x0)
                    (@pair (prod PP AA) P (@pair PP AA p1 a1) p2) w))) x).
    2: simpl; intros; intro; simpl; clear;  firstorder.
    intros v Hop. destruct v; repeat destructpair.
    destruct x.
    2: simpl in Hop; try congruence. 
    destruct v; repeat destructpair.
    simpl in Hop.
    unfold andb in *; repeat autodestruct; try congruence. 
    rewrite interfere_defn in *. 
    rewrite <- interfere_or in *.
    rewrite <- interfere_and in *.
    repeat splitup.
    inversion Hop. clear Hop. subst.   
    unfold op. 
    unfold andb.
    repeat autodestruct;
    repeat rewrite <- not_true_iff_false in *;
    repeat rewrite interfere_defn in *;
    repeat rewrite <- interfere_or in *;
    repeat rewrite <- interfere_and in *; try contradiction. 
    (* Three cases *)
      (* First case *)
       simpl.
       intros. 
       repeat autodestruct;
       repeat rewrite <- not_true_iff_false in *;
       repeat rewrite interfere_defn in *;
       repeat rewrite <- interfere_or in *;
       repeat rewrite <- interfere_and in *; try contradiction.
       (* Three cases *)
         (* 1 *)
         simpl; trivial.
         (* 2 *)
         intuition.
         (* 3 *)
         intuition. 
     (* Second case *)
       firstorder. 
     (* Third case *)
       firstorder. 
  (* Non-terminating case : I don't think was the best order *)
  automatcher.
  case_eq ((sim_fun Ps2 As2 (Some v) * x));
  destruct v; repeat destructpair.
  Focus 2. 
     intros.  simpl. intro. simpl. firstorder. 
  intros v Hop.
  destruct x. 
  2: simpl in Hop; congruence. 
  destruct v0; destruct v; repeat destructpair.
  simpl.
  unfold sim_fun in *. 
  unfold op in *.
  unfold andb in *. 
  repeat autodestruct;
       repeat rewrite <- not_true_iff_false in *;
       repeat rewrite interfere_defn in *;
       repeat rewrite <- interfere_or in *;
       repeat rewrite <- interfere_and in *; try contradiction;
       intuition; try congruence.
  simpl in *.
  inversion Hop. 
  subst. trivial. 
  Qed.  

End OwickiGries.