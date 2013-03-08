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

 Module CapPSAP : PermissionSeparationAlgebraParams.
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
 
 Definition lcol (l : LState) (s : SState) : partial_val (T:=LState) :=
   cfm_dom_fold s (fun (o : partial_val (T:=LState))
                       (a : 

 Definition Act := SState -> LState -> Prop.
 Definition AMod := Token -> option Act.







 (* Type for interference specifications.
     Choices: this does not need to be local (with respect to the guard) --
       we will interpret it as the local closure.
  *)
 Definition IF_Spec (t : rtype) (rsat : RSA t) (r : RT t) :=
   (sa_dom (rsat r)) -> AID -> relation (SState t rsat).

 Record PreWorld (t : rtype) :=
   {
     world_rsa : RSA t;
     world_local : LState t world_rsa;
     world_shared : SState t world_rsa;
     world_if_spec : forall r : RT t, IF_Spec t world_rsa r
   }.

 (* This should be factored out. *)
 Definition partial_val_fmap {A} (f : A -> A) : 
         partial_val (T := A) -> partial_val (T:=A) :=
   fun v => match v with
     | {| defined := defined; val := val |} =>
         {| defined := defined; val := f val |}
   end.

 Fixpoint sa_op_list {s : SA} (init : s) (l : list s)
    : partial_val (T:=s) :=
   match l with
   | nil => lift_val init
   | cons a l' => let (d, v) := sa_op_list init l' in
     let (d', v') := sa_op _ a v in
       {| defined := d /\ d'; val := v' |}
   end.

  

 Definition guard_total {t : rtype} (w : PreWorld t) (r : RT t)
     : partial_val (T := world_rsa t w r) :=
    let l :=
      map (fun r0 : RT t => ls_gd t (world_rsa t w) (world_shared t w r0) r)
          (RIDs t) in
     sa_op_list (ls_gd t (world_rsa t w) (world_local t w) r) l.

 Record World (t : rtype) :=
   {
     world_wrld :> PreWorld t;
     world_well_guarded : forall (r : RT t), defined (guard_total world_wrld r)
   }.

 (* TODO:
    1. Define Rely relation
    2. Define Guarantee relation
    3. Prove compatability.
  *)
 
(* Guarantee relation.
   An update should be permitted if it is permitted by all regions.
   An update is permitted by a region if it is the identity on that region.
   An update is permitted by 

End TadaModel.