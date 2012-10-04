Require Export Relations Basics Morphisms Setoid Equalities SetoidClass.
Require Import Tactics. 
Require Import TypeSystem.
Require Import Monoids. 
Require Import Setof. 
Require Import Framework.
Require Import MySetoids.  
Require Import MyClassical.  
Import TupleStateTransformers.

Section Types.
Variables Th : Locs -> option Types.
Variable v : nat.

Inductive types  : Types -> Prop :=
  | t_null : v=0 -> types Null
  | t_int : types Int 
  | t_nullable1 : forall t, v =0 -> types (Nullable t)
  | t_nullable2 : forall t, ( types t -> types (Nullable t))
  | t_ref : forall t1 t2, 
                Th v = Some t1
                -> Th (S v) = Some t2
                -> types (Ref t1 t2)
  | t_rec : forall t, types (unfold t) -> types (Rec t) 
  . 
End Types.

(* Sanity check *)
Definition list tau := Rec (Nullable (Ref tau (RVar_b 1 (Gt.gt_Sn_O 0)))). 
Lemma null_is_list: forall Th, types Th 0 (list Int).
intros.
eapply t_rec. compute. autodestruct. intro; eapply t_nullable1. trivial.
congruence. 
Qed. 
Lemma cons_is_list: 
  forall Th x, x <> 0 ->
    Th(x) = Some Int 
    -> Th (S x) = Some (list Int)
    -> types Th x (list Int).
intros. 
eapply t_rec. compute. 
eapply t_nullable2. 
eapply t_ref; trivial.
autodestruct; try congruence. trivial. 
Qed.
(* End sanity check: sanity is in check. *)

Instance types_proper : 
  Proper (equiv ==> equiv ==> equiv ==> impl) types.
push.
(* Get into correct form for induction *)
generalize H H1 H0. clear H H1 H0.
generalize y y1 y0. clear y y1 y0.
induction H2. 
(* null *) 
compute. intros; subst.
eapply t_null. intuition. 
(* Int *)
compute. intros; subst.
eapply t_int. intuition.
(* Nullable1 *) 
compute in *. intros; subst.
eapply t_nullable1. intuition.
(* Nullable 2 *)
compute in *. intros; subst.
eapply t_nullable2. intuition.
(* ref *)
compute in *. intros; subst.
eapply t_ref.
 (* fst *)
  use_foralls.
  optionstac; subst; intuition.
 (* snd *)
  generalize (H1 (S y0)).
  intros; optionstac; subst; intuition. 
(* rec *)
intros.
inversion H1. subst.  
eapply t_rec. eapply IHtypes; triv.
Qed.

Definition union : VCon -> VCon -> VCon := 
   fun x y a => match x a with None => y a | _ => x a end. 

Instance union_morph : Proper (equiv ==> equiv ==> equiv) union. 
  repeat intro. 
  unfold union. 
  generalize (H a).
  generalize (H0 a).
  destruct (x a); destruct (y a); trivial;
  compute; intuition. congruence. congruence.
Qed. 

Definition welltyped Ts Th (SH : State ) := 
  match SH with 
  | Some (H,Ss) =>  
     ( forall t (x : Vars), 
          Ts x = Some t
          -> types Th (Ss x) t)
     /\
     ( forall t (x : Locs), 
          Th x = Some t
           -> exists v, H x == Some v /\ types Th v t)
  | None => False
  end
  .

Instance well_typed_proper : 
  Proper (equiv ==> equiv ==> equiv ==> impl) welltyped.
do 9 intro.
destruct x1; destruct y1.
2: inversion H1.
2: inversion H1.
2: compute; trivial.
destruct p; destruct p0.
inversion H1.
compute [fst snd] in *.  clear H1.  
automatcher.
(* Stack part *)
automatcher.
automatcher.
rewrite H0.
generalize (H x2).
intro Heq; compute in Heq.  rewrite Heq.
rewrite H3.  
trivial.
(* Heap part *)
automatcher. 
automatcher.
generalize (H0 x2).
intro Heq; rewrite Heq.
automatcher.
automatcher. 
rewrite  H0.
automatcher.
rewrite (H2 x2). 
trivial.
trivial.
Qed.  

Lemma option_none_eq :
  forall {A}  {b : Setoid A} (x : option A), 
     MySetoids.option_equiv x None <-> x = None.
      intros A b  xx; destruct xx; simpl;
      intuition; try contradiction; try congruence.
Qed.

Module TypeSystemSafetyParams.

  (* Views *)
  Definition V := option VCon. 
  Instance V_setoid : Setoid V := setoid_option VCon setoid_m.

  Definition disjoint_prop (v1 v2 : VCon) : Prop := 
      forall x, v1 x = None \/ v2 x = None.
  Definition disjoint_dec (v1 v2 : VCon) : bool :=
     to_bool (disjoint_prop v1 v2). 
  Lemma disjoint : 
    forall a b, disjoint_dec a b = true
       <-> forall x, a x = None \/ b x = None.
  intros; unfold disjoint_dec; rewrite to_bool_defn; firstorder. 
  Qed.
  Instance disjoint_dec_morph : Proper (equiv ==> equiv ==> eq) disjoint_dec.
  repeat intro. 
  assert (disjoint_dec x x0 = true <-> disjoint_dec y y0 = true).
      repeat rewrite disjoint.
      split; automatcher;
      repeat rewrite <- option_none_eq;
      generalize (H x1);
      generalize (H0 x1);
      intros Hre1 Hre2;
      rewrite Hre1;
      rewrite Hre2; 
      trivial.
  destruct (disjoint_dec x x0);
  destruct (disjoint_dec y y0);
  intuition.
  Qed.

  (* Composition *)
  Definition op v1 v2 :=
    match v1,v2 with 
    | None, _ | _,None => None
    | Some th1, Some th2 => 
       if disjoint_dec th1 th2 then 
          Some (union th1 th2)
       else None
    end.

  Program Instance op_monoid : SemiGroup op.
  Next Obligation. (* op morphism *)
    repeat intro. 
    destruct x; destruct y. 
    2: inversion H. 
    2: inversion H. 
    2: simpl; trivial.  
    destruct x0; destruct y0. 
    2: inversion H0. 
    2: inversion H0. 
    2: simpl; trivial.
    simpl.
    simpl in *. 
    repeat rewrite H.
    repeat rewrite H0. 
    autodestruct; simpl; trivial. 
    repeat rewrite H.
    repeat rewrite H0. 
    reflexivity. 
  Qed. 
  Next Obligation. (* op morphism *)
    repeat (optiondestruct; simpl; trivial). 
    2: autodestruct; simpl; trivial. 
    repeat (autodestruct; simpl; trivial);
    repeat rewrite <- Bool.not_true_iff_false in *;
    repeat rewrite disjoint in *;
    unfold union in *.
    intro x.
    use_foralls.
    repeat casesplit;
    repeat rewrite H3; repeat rewrite H4; repeat rewrite H5; repeat rewrite H6;
    try reflexivity. 
    
    destruct (v1 x); reflexivity.
    destruct (v1 x); reflexivity.
    destruct (v1 x); reflexivity.
    destruct (v1 x); reflexivity.

    
    elim H2. clear H2. intro x; use_foralls.
    clear H H0 H1. 
    destruct (v1 x).
    2: left; trivial. 
    destruct (v0 x); trivial. 

    elim H1. clear H1.
    intro x; use_foralls. 
    destruct (v1 x). 
    repeat casesplit; trivial; try congruence.
    triv. triv. 

    elim H0. intro x; use_foralls. 
    destruct (v1 x); trivial.
    destruct (v x); try triv. 
    destruct (v0 x).
    casesplit; congruence.
    elim H5; intros; try congruence.

    elim H. intros x; use_foralls. 
    destruct (v0 x); try triv.
  Qed. 


  Program Instance op_comm : Commutative op.
  Next Obligation. 
  destruct a1; destruct a2.
  4: reflexivity. 
  3: simpl; trivial.
  2: simpl; trivial.
  simpl. 
  repeat autodestruct;
    repeat rewrite <- Bool.not_true_iff_false in *;
    repeat rewrite disjoint in *.
  4: reflexivity. 
  3: match goal with H : ~ _ |- _ => elim H end;
        intro; use_foralls; intuition.
  2: match goal with H : ~ _ |- _ => elim H end;
        intro; use_foralls; intuition.
  intro. 
  use_foralls. 
  simpl. unfold union. 
  destruct (v a); destruct (v0 a); try reflexivity. 
  casesplit; congruence.
  Qed. 

  Infix "*" := op.

  Program Definition erase (v: V) : (Setof (A:=State)):= 
  {| elem := fun s => 
      match v with 
      | Some Ts =>
         exists Th, welltyped Ts Th s 
      | None => False
      end|}
      .
  Next Obligation.
  intro. intro.
  destruct v. 
  intro. 
  split; automatcher;
  setoid_rewrite H; trivial. 
  firstorder. 
  Qed. 

  Instance erase_morphism : Proper (equiv ==> equiv) erase.
  intro. intro.
  intro Hre. 
  unfold erase. 
  destruct x; destruct y. 
  4: reflexivity.
  3: compute in Hre; firstorder.  
  2: compute in Hre; firstorder.  
  intro; simpl.
  simpl in Hre. 
  assert (v == v0). 
  firstorder. 
  split; automatcher.
  rewrite H; trivial.
  rewrite <- H; trivial.
  Qed.

End TypeSystemSafetyParams.

 
Module Import TypeSystemSafety :=  
   Safety 
     TupleAtoms TupleLang
     TupleStateTransformers
     TypeSystemSafetyParams. 

Import TypeSystemSafetyParams.

Definition tsunit : V := (Some (fun x => None)).
Lemma tsunit_lunit :
    forall a, op tsunit a == a.
  destruct a.
  2: reflexivity.
  unfold tsunit. simpl. autodestruct.
  
    simpl. intro. unfold union. reflexivity.

    repeat rewrite <- Bool.not_true_iff_false in *;
    repeat rewrite disjoint in *.
    elim H; left; trivial. 
Qed.
 
Instance ts_monoid : Monoid op := {unit := tsunit; unit_lunit := tsunit_lunit}.
   intros; rewrite op_commut.
   apply tsunit_lunit. 
Qed.
   

Ltac eq_dec := 
  match goal with 
  | H : context C [if eq_dec ?c ?c then _ else _] |- _ 
    => destruct (eq_dec c c)
  | H : context C [if eq_dec ?c ?d then _ else _] |- _ 
    => let x := fresh in let y := fresh in 
       case_eq (eq_dec c d); intros x y; rewrite y in *
  end.

Ltac destructopt o := 
  let yyy := fresh in let Heq := fresh in   
  case_eq o ; [intros yyy Heq | intros Heq]; rewrite Heq in * .


Lemma types_subtype : 
forall Th v,forall t t', 
 subtype t t' -> types Th v t -> types Th v t'.
inversion 1; subst.

(* unfold *)
eauto using t_rec. 
 
(* fold *)
inversion 1; eauto. 

(* trans *)
eauto. 

(* nullable *)
eapply t_nullable2. 
inversion 1; eauto using t_nullable1.
Qed.

Instance some_proper : Proper (equiv ==> equiv) (Some (A:= VCon)). 
firstorder. 
Qed. 

Lemma subtype_imp_aimpl: 
   forall G1 G2, subtype_con G1 G2 -> aimpl (Some G1) (Some G2).
unfold subtype_con. 
intros G1 G2 Hsubt.
unfold aimpl. 
destruct r. 
2: simpl; reflexivity. 
simpl. 
autodestruct. 
2: firstorder. 
autodestruct. 
(* post well defined *)
  intro. 
  automatcher. 
  destruct a.
  2: simpl; trivial.
  simpl. destructpair. 
  automatcher.
    (* Stack case *)
    intro Hass.
    intros. 
    unfold union in H1. 
    case_eq (G2 x0); intros; repeat useoptions. 
      (* From G2 *)
      generalize (Hsubt _ _ H2). 
      intros; repeat splitup.
      eapply types_subtype; eauto.
      eapply Hass. 
      unfold union. 
      useoptions.
      trivial.  
      (* Not from G2. *)
      eapply Hass. 
      unfold union. 
      case_eq (G1 x0). 
        (* contradictory case *)
        repeat rewrite disjoint in *.
        elim (H x0); congruence.
        (* Correct case *)
        trivial.
    (* Heap case *)
    trivial. 
(* Post None, so need contradiction. *)
repeat rewrite <- Bool.not_true_iff_false in *;
repeat rewrite disjoint in *.
elim H0; clear H0. 
generalize H; automatcher.
intro; casesplit; try triv.
left.  
generalize (Hsubt x). 
destruct (G2 x); trivial. 
intros HH.
generalize (HH t).
intuition. 
repeat splitup; congruence. 
Qed.

Import Language. 
Lemma so_map_rel_simp : 
  forall {A} {b:Setoid A}(a : ST (A:=A)) (p q : Setof (A:=A)),
      (forall s s', a s s' -> p s -> q s' )
      ->
      subsetof (so_map_rel a p (R_morphism :=st_morph a)) q .
intros. intro.
unfold so_map_rel. simpl.
intro; repeat splitup.
firstorder.
Qed.        

Ltac stack_typ t y 
  := 
  match goal with 
  | H : context C [_ -> types _ _ _ ] |- _ => 
     generalize (H t y);
     let Hfoo := fresh in 
       intro Hfoo;
       compute in Hfoo; repeat (eq_dec; obvious); intuition
  end.

Ltac case_add :=
   match goal with 
   | H : add _ _ _ _ = Some _ |- _ => 
      compute in H; repeat ((eq_dec || useoptions); obvious)
   end.
Ltac heap_typ t l := 
match goal with 
| H : ?Th l = Some t, H1 : context C [?Th _ = Some _ -> _] |- _ =>
        generalize (H1 t l H); 
        let v := fresh "v" in 
        let Heq := fresh "Heq" in 
        let Htyp := fresh "Htyp" in 
        intros [v [Heq Htyp]]
end.


Lemma types_grow :
  forall G v t x t',
  types G v t
  -> G x = None
  -> types (add x t' G) v t.
induction 1;
 eauto using t_null, t_int, t_rec, t_nullable1, t_nullable2.
(* Ref case *)
intros; eapply t_ref; compute; autodestruct; obvious. 
Qed.


Lemma atomic_soundness :
  forall p a q, 
   type_atomic p a q
      -> asat (Some p) (interp a) (Some q).
intros p a q Htype.
intro r.
destruct r. 
(* Deal with cases where r = None *)
2: compute; firstorder.
case_eq (Some p * Some v). 
(* Deal with cases where r overlaps p *)
2: compute; firstorder.
intros v0 Hop. 
compute -[disjoint_dec] in Hop.
(* Insert simplified p * r *)
autodestruct. 
repeat rewrite disjoint in *. 
2: congruence. 
setoid_rewrite <- Hop. clear Hop.
(* Put in friedlier form *)
apply so_map_rel_simp. intros ss se Hinterp Hpre.
generalize Hpre. clear Hpre; intros [Th Hpre]. 
(* None is not in eraseure of pre *)
destruct ss.
2: simpl in Hpre; contradiction.

destructpair. 
simpl in Hpre. 
generalize Hpre;
intros [Hstack Hheap]. clear Hpre.  

(* All the simplification is done, case analysis time. *)
(* Case split on defined post first *)
(* Then type rule *)
case_eq (Some q * Some v).
  intros v1 Hop.
  simpl in Hop.
  autodestruct; try congruence.
  inversion Hop. subst. clear Hop.
  repeat rewrite disjoint in *. 
  simpl. 
  (* Case split on type rule *)
  destruct Htype.
    (* Is_null *)
    exists Th. 
    destruct Hinterp.
    rewrite <- H2.
    split; trivial.
    intros t0 x0.
    generalize (Hstack t0 x0).
    compute.
    autodestruct. 
    (* updated location. *)
      intros; subst. useoptions.
      eapply t_null; eauto.
    (* arbitrary other location *)
      trivial. 

    (* Is not null *)
     exists Th. 
     destruct Hinterp.
     rewrite <- H2.
     split; trivial.
     intros t0 x0.
     generalize (Hstack t0 x0).
     generalize (Hstack (Nullable t) x0).
     compute.
     autodestruct. 
     (* updated location. *)
       intros; subst. useoptions.  
       intuition. inversion H6; try contradiction. 
       try congruence. 
     (* arbitrary other location *)
       intros; subst. auto.

     (* read fst *)
       exists Th.
       stack_typ (Ref t1 t2) y.
       inversion H5.  subst. 
       heap_typ t1 (s y).
       simpl in Hinterp. 
       rewrite Heq in *.
       rewrite Hinterp in *.
       split; trivial. 
       intros t0 x0.
       generalize (Hstack t0 x0). 
       compute. 
       autodestruct. 
       (* x0 = x *)
         intros. repeat  useoptions. trivial. 
       (* x0 != x *)
          autodestruct.
          (* x0 = y *)
          intros; repeat useoptions. trivial. 
          (* x0 != y *)
          trivial. 

     (* read snd *)
       exists Th.
       stack_typ (Ref t1 t2) y.
       inversion H5.  subst. 
       heap_typ t2 (S (s y)).
       simpl in Hinterp. 
       rewrite Heq in *.
       rewrite Hinterp in *.
       split; trivial. 
       intros t0 x0.
       generalize (Hstack t0 x0). 
       compute. 
       autodestruct. 
       (* x0 = x *)
         intros. repeat  useoptions. trivial. 
       (* x0 != x *)
          autodestruct.
          (* x0 = y *)
          intros; repeat useoptions. trivial. 
          (* x0 != y *)
          trivial.

    (* Write fst *)
      exists Th. 
      stack_typ (Ref t1 t2) y.
      stack_typ t1 x.
      inversion H5. subst. 
      heap_typ t1 (s y).
      simpl in Hinterp. 
      rewrite Heq in *.
      rewrite Hinterp in *.
      split; trivial. 
      intros t0 x0.
      generalize (Hheap t0 x0). 
      compute. 
      autodestruct. 
      (* s y == x0 *)
         exists (s x).
         split; trivial. 
         assert (t0 = t1). congruence.
         subst. trivial. 
      (* s y != x0 *)
         trivial. 

    (* Write snd *)
      exists Th. 
      stack_typ (Ref t1 t2) y.
      stack_typ t2 x.
      inversion H5. subst. 
      heap_typ t2 (S (s y)).
      simpl in Hinterp. 
      rewrite Heq in *.
      rewrite Hinterp in *.
      split; trivial. 
      intros t0 x0.
      generalize (Hheap t0 x0). 
      compute. 
      autodestruct. 
      (* s y == x0 *)
         exists (s x).
         split; trivial. 
         assert (t0 = t2). congruence.
         subst. trivial. 
      (* s y != x0 *)
         trivial. 

    (* New ref *)
       destruct Hinterp.
       exists (add x0 t1 (add (S x0) t2 Th)).
       stack_typ t1 y.
       stack_typ t2 z.
       repeat splitup.
       ssubst.
       assert (Th (S x0) = None).
                case_eq (Th (S x0)); trivial.
                  intro tt; generalize (Hheap tt (S x0)).
                  intuition. repeat splitup.  congruence.
       assert (Th x0 = None).
              case_eq (Th x0); trivial.
                intro tt; generalize (Hheap tt x0).
                intuition. repeat splitup.  congruence. 
       split.
       (* Stack case *)
          intros t0 x1. 
          generalize (Hstack t0 x1). 
          compute.
          destruct (eq_dec x x1).
          (* x = x1 *)
            subst. intros. 
            repeat useoptions. 
            apply t_ref;
              repeat (autodestruct; try congruence).
              destruct (eq_dec x0 (S x0)); trivial.
              clear -e. generalize n_Sn. firstorder. 
          (* x != x1 *)
          autodestruct.
            (* y=x1 *)
            intros; repeat useoptions.
            eapply types_grow. 
              eapply types_grow. 
                intuition.
                trivial. 
              case_eq (eq_dec (S x0) x0); trivial. 
                generalize (n_Sn x0). clear. firstorder. 
            (* y != x1. *)
            autodestruct.
            (* y = z *)
             intros; repeat useoptions.
             eapply types_grow. 
               eapply types_grow. 
                 intuition.
                 trivial. 
               case_eq (eq_dec (S x0) x0); trivial. 
                 generalize (n_Sn x0). clear. firstorder. 
            (* y != z *)
             intros; repeat useoptions.
             eapply types_grow. 
               eapply types_grow. 
                 intuition.
                 trivial. 
               case_eq (eq_dec (S x0) x0); trivial. 
                 generalize (n_Sn x0). clear. firstorder. 
 
       (* Heap case *)
       intros t0 x1.
       generalize (Hheap t0 x1). 
       compute. 
       autodestruct.
       (* x0 = x1 *)
         eexists; split; try reflexivity.
           eapply types_grow.
             eapply types_grow.
               repeat useoptions; trivial. 
             trivial.
           case_eq (eq_dec (S x1) x1). 
             generalize (n_Sn x1). clear. firstorder.
           trivial. 
         (* x0 != x1 *)
         autodestruct.
         (* x1 = S x0 *)
          eexists; split; try reflexivity. 
          repeat useoptions. 
            eapply types_grow.
              eapply types_grow. 
                trivial. 
              trivial.
            case_eq (eq_dec (S x0) x0). 
              generalize (n_Sn x0). clear. firstorder.
            trivial.
         (* x1 != S x0 *)
         intuition.
         repeat splitup. 
         eexists; split; eauto. 
            eapply types_grow.
              eapply types_grow. 
                trivial. 
              trivial.
            case_eq (eq_dec (S x0) x0). 
              generalize (n_Sn x0). clear. firstorder.
            trivial.
         
(* None posts *)
  simpl. autodestruct. congruence. 
  repeat rewrite <- Bool.not_true_iff_false in *;
  repeat rewrite disjoint in *.
  elim H0.
  intro x0. clear H0. 
  generalize (H x0).
  intros H0; casesplit; try triv.
  left. 
  generalize H0. 
  (* Case split on rules *)
  destruct  Htype; clear; compute; 
    repeat (trivial; try congruence;  autodestruct).
Qed.