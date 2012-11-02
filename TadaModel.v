Add LoadPath "c:\td202\GitHub\coq\views".

Require Import Heaps.
Require Import String.
Require Import SeparationAlgebras.
Require Import SetoidClass.
Require Import FMaps. 

Module TadaModel (ht : HeapTypes).
 Module Export TheHeap := MHeaps ht.

 (* Region identifiers will be nats *)
 Definition RID := nat.
 Module RID_OT := Nat_as_OT.
 (* Action identifiers are pairs of string and lists of values *)
 Definition AID := (string * (list Val))%type.

 Record SA :=
   {
     sa_dom :> Type;
     sa_setoid : Setoid sa_dom;
     sa_op : partial_op sa_dom;
     sa_sa : SepAlg sa_op
   }.

 
 (* Now let's define a region type as a finite mapping from
    region identifiers to separation algebras. *)

 Module R_Types := FMapList.Make RID_OT.
 Definition R_type := R_Types.t SA.

 Record LState (T : R_type) := { ls_hp : store; ls_gd : Guard }.

 Record world :=
   {
     local_state : LState;
     shared_state : SState;
     if_spec : IFSpec
   }.