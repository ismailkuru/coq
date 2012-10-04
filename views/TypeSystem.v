Require Import Basics.
Require Import SetoidClass.
Require Import MySetoids.
Require Import Tactics.
Require Import Bool.

Definition Locs := nat.
Definition Vars := nat.
Definition RVars := nat. 
Definition ERVars := nat.

Lemma eq_dec : forall x y:RVars, {x = y} + {x <> y}.
decide equality.
Qed.


(* Types for the system *)
Inductive Types := 
  | Int : Types
  | Null : Types
  | Ref :  Types  -> Types -> Types
  | RVar_b : forall n (p: n > 0), Types
  | Rec : Types -> Types
  | Nullable : Types -> Types 
.


(* Only works on closed terms, but we only use it on closed terms. *)
Fixpoint subst (X : nat) ts (t : Types) :=
  match t with
  | Null
  | Int 
     => t
  | Nullable t => Nullable (subst X ts t)
  | RVar_b Y _ => if eq_dec X Y then ts else t
  | Ref t1 t2 => Ref (subst X ts t1) (subst X ts t2)
  | Rec t1 => Rec (subst (S X) ts t1)
  end. 


Lemma subst_id : forall t X p, (subst X t (RVar_b X p)) = t. 
intros. simpl. autodestruct; congruence. 
Qed.

Definition unfold tb := subst 1 (Rec tb) tb .


(* Subtyping relation *)
Inductive subtype : Types -> Types -> Prop :=
   ts_fold : forall t, subtype (unfold t) (Rec t)
 | ts_unfold : forall t, subtype (Rec t) (unfold t)
(* Nullable Rules *)
 | ts_nullable_drop1 : forall t,
            subtype t (Nullable t)
 | ts_nullable_drop2 : forall t,
            subtype Null (Nullable t)

.

Hint Resolve ts_fold ts_unfold  ts_nullable_drop1 ts_nullable_drop2.





(* Contexts for program variables *)
Instance setoid_types : Setoid (Types) 
   := { equiv := eq }.

Instance setoid_opt_types : Setoid (option Types) 
   := { equiv := eq }.

Definition VCon := Vars -> option Types. 

Program Instance setoid_vars : Setoid Vars.
Instance setoid_m : Setoid VCon := 
  setoid_arrow (option Types) Vars setoid_opt_types setoid_vars . 


Definition add {T} X (t : T) G  :=
   fun Y => if eq_dec X Y then Some t else G Y.

Instance add_proper : 
  Proper (equiv ==> equiv ==> equiv ==> equiv) (add (T:=Types)).
push.
destruct H.
destruct H0.
unfold add.  
autodestruct; triv.
Qed.

Definition delete {T} X G : nat -> option T :=
   fun Y => if eq_dec X Y then None else G Y.

Definition empty {T} {S} :  T-> option S := fun Y => None.

(*
Inductive subtype_con : VCon -> VCon -> Prop :=  
  | sc_refl : forall G1 G2, G1 == G2 -> subtype_con G1 G2
  | sc_trans : forall G1 G2 G3, subtype_con G1 G2 -> subtype_con G2 G3 -> subtype_con G1 G3
  | sc_one : forall G G1 G2 t1 t2 x, 
      G1 == (add x t1 G) -> 
      G2 == (add x t2 G) -> 
      subtype t1 t2 -> subtype_con G1 G2  
  | sc_drop : forall G G1 t1 x, G x = None -> G1 == (add x t1 G) -> subtype_con G1 G.

Instance subtype_proper : Proper (equiv ==> equiv ==> impl) subtype_con.
intro. 
intros y Heq x1 y1 Heq2 Hsub.
generalize Heq2 Heq.
clear Heq Heq2.
generalize y y1.
clear y y1.
induction Hsub; intros.  

(* Refl case *)
  eapply sc_refl; repeat ssubst; intuition. 
(* trans case *)
 eapply sc_trans.
 eapply IHHsub1; eauto. reflexivity.
 eapply IHHsub2; eauto. reflexivity.
(* add case *)
 eapply sc_one;
 repeat ssubst; triv.
(* drop case *)
 eapply sc_drop.
 2: repeat ssubst; reflexivity.
 compute in Heq2.
 use_foralls.
 optionstac. trivial.
Qed.
*)
Definition subtype_con (G1 G2 :VCon) : Prop :=  
  forall x t, G2 x = Some t -> 
      exists t', G1 x = Some t' /\ subtype t' t. 

Instance subtype_proper : Proper (equiv ==> equiv ==> impl) subtype_con.
do 6 intro.
automatcher. 
automatcher. 
ssubst. ssubst. 
trivial. 
Qed.


Require Import Language.

(* Setting up basic commands *)
Module TupleAtoms.

(* Require two stage definition to deal with Coq missing feature. *)
Inductive Atomic_Hack : Set := 
|  is_null : Vars -> Atomic_Hack
|  is_not_null : Vars -> Atomic_Hack
|  read_fst : Vars -> Vars -> Atomic_Hack
|  read_snd : Vars -> Vars -> Atomic_Hack
|  write_fst : Vars -> Vars -> Atomic_Hack
|  write_snd : Vars -> Vars -> Atomic_Hack
|  new : Vars -> Vars -> Vars -> Atomic_Hack
|  new_simp : Vars -> Atomic_Hack.

Definition Atomic := Atomic_Hack.

End TupleAtoms.

Module TupleLang := BasicSyntax TupleAtoms.
Import TupleAtoms.
Import TupleLang.


Module TupleStateTransformers.
  

Definition Heap := Locs -> option nat.
Definition Stack := (Vars -> nat).
Definition State := option (prod Heap Stack).

Definition upd {T} x (v : T) f y := if eq_dec x y then v else f y. 

Instance upd_morph {T} {b : Setoid T}: 
  Proper (equiv ==> equiv ==> equiv ==> equiv) (@upd T).
repeat intro.
compute. compute in H. subst. 
repeat autodestruct; trivial.
intros. generalize (H1 a). intro HH; rewrite HH. reflexivity.
Qed.     

Instance opt_nat_setoid : Setoid (option nat) := { equiv:= eq}.
Program Instance heap_setoid : Setoid Heap.
Program Instance stack_setoid : Setoid Stack. 
Instance pre_state_setoid : Setoid (Heap * Stack) :=
  {
     equiv := prod_equiv
  }.

Instance state_setoid : Setoid State :=
 {
    equiv := option_equiv
  }.

Definition interp_pre : Atomic -> State -> State -> Prop 
  := 
  fun a s e => 
   match s with 
   | None => e = None
   | Some (hp,st) =>
   match a with 
   |  is_null x 
       => st x = 0 /\ s==e 
   |  is_not_null x 
       => st x <> 0 /\ s==e
   |  read_fst x y 
       => 
       match hp (st y) with 
       | None => e = None 
       | Some v => e == Some (hp,upd x v st)
       end
   |  read_snd x y
       => 
       match hp (S(st y)) with 
       | None => e = None 
       | Some v => e == Some (hp, upd x v st)
       end
   |  write_fst x y
       => 
       match hp (st x) with 
       | None => e = None
       | Some _ => 
          e == Some (add (st x) (st y) hp, st)
       end
   |  write_snd x y 
       =>
       match hp (S (st x)) with 
       | None => e = None
       | Some _ => 
          e == Some (add (S (st x)) (st y) hp, st)
       end
   |  new x y z => 
       exists v, hp v = None /\ hp (S v) = None /\
                  e == Some (add v (st y) (add (S v) (st z) hp), (upd x v st))
   |  new_simp x => 
       exists v, hp v = None /\ hp (S v) = None /\
                  e == Some (add v 0 (add (S v) 0 hp), (upd x v st))
   end
   end 
   . 


Instance interp_morph : Proper (eq ==> equiv ==> equiv ==> equiv) interp_pre.
repeat intro. 
subst.
destruct x0; destruct y0. 
2: compute in H0; try contradiction.
2: compute in H0; try contradiction.

2: simpl; intros; destruct x1; destruct y1; split; intros; trivial; 
try congruence;
compute in *; contradiction.

(* Unpack equalities on pair *)
destruct H0. 
repeat destructpair. 
compute [fst snd] in *.

destruct x1; destruct y1.
2: compute in H1; try contradiction.
2: compute in H1; try contradiction.

Focus 2. 
destruct y; simpl; repeat ssubst; try reflexivity; firstorder.


repeat destructpair.
destruct H1. 
compute [fst snd] in *.
destruct y; simpl; unfold prod_equiv; compute [fst snd] in *; unfold upd;
  repeat rewrite H;
  repeat rewrite H0;
  repeat rewrite H1;
  repeat rewrite H2;
  try reflexivity.

destruct (h (s v0)).
2: split; try congruence.
  repeat rewrite H;
  repeat rewrite H0;
  repeat rewrite H1;
  repeat rewrite H2.
  intuition; 
  rewrite H5; compute; intro;  
  autodestruct; try reflexivity;
  rewrite H0; try reflexivity.


destruct (h (S (s v0))).
2: split; try congruence.
  repeat rewrite H;
  repeat rewrite H0;
  repeat rewrite H1;
  repeat rewrite H2.
  intuition; 
  rewrite H5; compute; intro;  
  autodestruct; try reflexivity;
  rewrite H0; try reflexivity.

destruct (h (s v)).
2: split; try congruence.
  unfold add. 
  repeat rewrite H;
  repeat rewrite H0;
  repeat rewrite H1;
  repeat rewrite H2.
  intuition;
  rewrite H4; compute; intro;  
  autodestruct; try reflexivity;
  rewrite H; try reflexivity.

destruct (h (S (s v))).
2: split; try congruence.
  unfold add. 
  repeat rewrite H;
  repeat rewrite H0;
  repeat rewrite H1;
  repeat rewrite H2.
  intuition;
  rewrite H4; compute; intro;  
  autodestruct; try reflexivity;
  rewrite H; try reflexivity.

  unfold add.
  split; intros [x Hc]; exists x;
  generalize Hc; clear Hc; 
  repeat rewrite H;
  repeat rewrite H0;
  repeat rewrite H1;
  repeat rewrite H2.
  intuition; (rewrite H5 || rewrite H7);
  compute; intro; autodestruct; try reflexivity; firstorder;
  compute; autodestruct; try reflexivity; 
  firstorder.
  intuition; (rewrite H5 || rewrite H7);
  compute; try intro; autodestruct; try reflexivity; try rewrite H; firstorder.
  rewrite H0. reflexivity. 

  split; automatcher;
  repeat rewrite H;
  repeat rewrite H0;
  repeat rewrite H1;
  repeat rewrite H2;
  repeat automatcher; trivial;
  compute; autodestruct; trivial; 
  try autodestruct; trivial; 
  repeat rewrite H;
  repeat rewrite H0;
  repeat rewrite H1;
  repeat rewrite H2;
  trivial. 
Qed.

Definition interp a := {| st_trans := interp_pre a |}.

End TupleStateTransformers. 




Module TupleOpSem := OperationalSemantics TupleAtoms TupleLang TupleStateTransformers .

Section Axioms.
Inductive type_atomic  : VCon -> TupleAtoms.Atomic -> VCon -> Prop := 
  | t_atom_null : 
          forall x t,
		type_atomic (add x t empty) 
                            (is_null x) 
                            (add x Null empty)
  | t_atom_not_null : 
          forall x t,
              type_atomic (add x (Nullable t) empty) 
                          (is_not_null x) 
	                  (add x t empty) 
  | t_atom_read_fst : 
          forall x y t t1 t2, x <> y ->
               type_atomic (add x t (add y (Ref t1 t2) empty))
                           (read_fst x y) 
			   (add x t1 (add y (Ref t1 t2) empty))
  | t_atom_read_snd : 
          forall x y t t1 t2, x <> y ->
               type_atomic (add x t (add y (Ref t1 t2) empty))
                           (read_snd x y) 
			   (add x t2 (add y (Ref t1 t2) empty))
  | t_atom_write_fst : 
          forall x y t1 t2, x <> y ->
               type_atomic (add x t1 (add y (Ref t1 t2) empty))
                           (write_fst y x) 
                           (add x t1 (add y (Ref t1 t2) empty))
  | t_atom_write_snd : 
          forall x y t1 t2, x <> y ->
               type_atomic (add x t2 (add y (Ref t1 t2) empty))
                           (write_snd y x) 
                           (add x t2 (add y (Ref t1 t2) empty))
  | t_atom_new : 
         forall x y z t t1 t2, x <> y -> x<>z -> y<>z ->
               type_atomic (add x t (add y t1 (add z t2 empty)))
			   (new x y z)
			   (add x (Ref t1 t2) (add y t1 (add z t2 empty)))
. 
End Axioms. 
