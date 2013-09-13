Add LoadPath "C:\td202\GitHub\coq\views".

Require Import Heaps.
Require Import String.
Require Import FractionalPermissions.
Require Import MSets.
Require Import SetoidClass.
Require Import Tactics.
Require Import CountableFiniteMaps.
Require Import SeparationAlgebras.
Require Import Setof.
Require Import HeapSeparationAlgebra.
Require Import SeparationAlgebraProduct.

Module CAPModel (ht : HeapTypes) .
 Module Export TheHeap := MHeaps ht.
 Module HSA := (HeapSA ht TheHeap).

 (* Action identifiers are pairs of string and lists of values *)
 Definition AID := (string * (list Val))%type.

 (* Region identifiers are natural numbers. *)
 Definition RID := nat.
 Program Instance RID_Setoid : Setoid RID.
 Program Instance RID_Countable : Countable RID.
 Solve Obligations using firstorder.
 


 (* Tokens are pairs of region idenitifer and
    action identifier. *)
 Record Token := { tok_rid : RID; tok_aid : AID }.

 Module CapPSAP <: PermissionSeparationAlgebraParams.
   Definition A := Token.
   Definition PA := FracPerm.T.
   Instance PA_Setoid : Setoid PA := FracPerm.FPsetoid.
   Definition op : partial_dec_op PA := FracPerm.plus.
   Instance PA_PermAlg : PermAlgMixin op := FracPerm.FP_pa.
 End CapPSAP.

 Module CapSA := PermissionSeparationAlgebra CapPSAP.

 Definition Cap := CapSA.S.

 Definition LState := (store * Cap)%type.

 Existing Instance prod_setoid.
 Existing Instance prod_SA.
 Definition ls_sepop := prod_sepop _ HSA.sepop _ CapSA.sepop.
 Instance ls_SA : SepAlg ls_sepop := prod_SA _ _ _ _.

 Definition SState := CFMap RID LState.
 
 Definition lcol (l : LState) (s : SState) : partial_val (T:=LState)
  :=
   cfm_dom_fold
  (fun (X : partial_val) (a : RID) (H : cfm_def_at s a) =>
   lift_op ls_sepop X (lift_val (cfm_def_get H))) (lift_val l).


 Definition Act := SState -> LState -> Prop.
 Definition AMod := Token -> option Act.

 Record wellformed (l : LState) (s : SState) (a : AMod) : Prop :=
   {
     wf_col_def : defined (lcol l s);
     wf_caps_acts : forall t, None = a t -> (snd (val (lcol l s))) t == FracPerm.zero;
     wf_act_regs : forall t, None = cfm s (tok_rid t) -> None = a t
   }.

 Record world :=
   {
     wrld_local : LState;
     wrld_shared : SState;
     wrld_amod : AMod;
     wrld_wf :> wellformed wrld_local wrld_shared wrld_amod
   }.


 Existing Instance cfm_setoid.
 Definition world_sepop : partial_op world.
  intros w1 w2.
  destruct w1.
  destruct w2.
  set (ls_sepop wrld_local0 wrld_local1).
  set (defined p /\ wrld_shared0 == wrld_shared1 /\ wrld_amod0 == wrld_amod1).
  split.
  exact (defined p /\ wrld_shared0 == wrld_shared1 /\ wrld_amod0 == wrld_amod1).
  
  remember (ls_sepop wrld_local0 wrld_local1).
  destruct p.
  
  split.
  

 HSA.sepop

End CAPModel.