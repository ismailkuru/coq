Add LoadPath "c:\td202\GitHub\coq\views".

Require Import Heaps.
Require Import String.
Require Import SeparationAlgebras.
Require Import MSets.
Require Import SetoidClass.
Require Import Tactics.

Module Type RegionTypes.
  Parameter rid : Type.
  Parameter rtype : Type.
  Parameter RT : rtype -> Type.
  Parameter rbelong : rid -> rtype -> Prop.
  Parameter rid_rtype : forall t r,
      rbelong r t -> RT t.
  Axiom rid_rtype_morphism : forall r t p1 p2, rid_rtype t r p1 = rid_rtype t r p2.
  Parameter rbelong_dec : forall r t,
      {rbelong r t} + {~rbelong r t}.
  
  Axiom rid_rtype_injective : forall t r1 B1 r2 B2,
    rid_rtype t r1 B1 = rid_rtype t r2 B2 ->
      r1 = r2.

  Parameter to_rid : forall t, RT t -> rid.
  Axiom to_rid_belong : forall t (rr : RT t),
    rbelong (to_rid t rr) t.
  Axiom to_rid_inverse : forall t r B,
      to_rid t (rid_rtype t r B) = r.

  Axiom rid_rtype_inverse : forall t k,
      k = rid_rtype t (to_rid t k) (to_rid_belong t k).

  Parameter rfresh : rtype -> rid.
  Axiom fresh_not_belong : forall t,
      ~ rbelong (rfresh t) t.

  Parameter rtempty : rtype.
  Axiom rtempty_not_belong : forall r,
      ~ rbelong r rtempty.

  Parameter rtextend : forall t r, ~ rbelong r t -> rtype.
  Axiom rtextend_extended : forall t r P r',
    rbelong r' (rtextend t r P) <->
      (r' = r \/ rbelong r' t).

  Parameter RIDs : forall t, list (RT t).
  Axiom RIDs_spec : forall t x, In x (RIDs t).
End RegionTypes.

(* I think it was premature to create a module type for
   region types.  Just use the concrete representation.
   Otherwise, we have to export a notion of fold...
*)

Module RegionTypesNat <: RegionTypes.
  Require Import ProofIrrelevance.
  Module Nat_Sets := MSetList.Make Nat_as_OT. (*MSets.MSetAVL.Make Nat_as_OT.*)

  Definition rid := nat.
  Definition rtype := Nat_Sets.t.
  Definition RT (t : rtype) := { r | Nat_Sets.In r t }.

  Definition rbelong : rid -> rtype -> Prop := Nat_Sets.In.
  Definition rid_rtype : forall t r,
      rbelong r t -> RT t.
   intros t r.
   exists r.
   trivial.
  Defined.

  Lemma rid_rtype_morphism : forall r t p1 p2, rid_rtype t r p1 = rid_rtype t r p2.
    repeat intro.
    generalize (proof_irrelevance _ p1 p2).
    intro; subst; auto.
  Qed.

  Definition rbelong_dec : forall r t,
      {rbelong r t} + {~rbelong r t}.
   intros.
   generalize (Nat_Sets.mem_spec t r).
   destruct (Nat_Sets.mem r t); intuition.
  Defined.

  Proposition rid_rtype_injective : forall t r1 B1 r2 B2,
    rid_rtype t r1 B1 = rid_rtype t r2 B2 ->
      r1 = r2.
   cbv; intuition.
   inversion H; trivial.
  Qed.

  Definition to_rid t : RT t -> rid :=
      proj1_sig (A:=rid) (P:=_).

  Proposition to_rid_belong : forall t (rr : RT t),
    rbelong (to_rid t rr) t.
   cbv; intuition.
   destruct rr; trivial.
  Qed.

  Proposition to_rid_inverse : forall t r B,
      to_rid t (rid_rtype t r B) = r.
   cbv; intuition.
  Qed.

  Proposition rid_rtype_inverse : forall t k,
      k = rid_rtype t (to_rid t k) (to_rid_belong t k).
   intros.
   destruct k.
   cbv.
   f_equal.
   apply proof_irrelevance.
  Qed.
  
  Definition rfresh (t : rtype) : rid :=
   match (Nat_Sets.max_elt t) with
   | Some r => S r
   | None => 0
   end.

  Lemma fresh_not_belong : forall t,
      ~ rbelong (rfresh t) t.
   cbv [rbelong rfresh rtype]; intuition.
   remember (Nat_Sets.max_elt t) as x.
   symmetry in Heqx.
   destruct x.
    generalize (Nat_Sets.max_elt_spec2 Heqx H).
    auto.
   
    eapply Nat_Sets.max_elt_spec3; eauto.
  Qed.

  Definition rtempty : rtype := Nat_Sets.empty.
  Lemma rtempty_not_belong : forall r,
      ~ rbelong r rtempty.
   apply Nat_Sets.empty_spec.
  Qed.

  Definition rtextend t r : ~ rbelong r t -> rtype :=
    fun _ => Nat_Sets.add r t.

  Proposition rtextend_extended : forall t r P r',
    rbelong r' (rtextend t r P) <->
      (r' = r \/ rbelong r' t).
   cbv; intros.
   generalize (Nat_Sets.add_spec t r r').
   intuition.
  Qed.

 Lemma elements_belong (t : rtype) : forall x,
    InA (@eq nat) x (Nat_Sets.elements t) ->
        rbelong x t.
  intros.
  rewrite <- Nat_Sets.elements_spec1.
  intuition.
 Qed.

 Definition RIDs0 (t : rtype) (l : list rid) : (forall x, In x l -> rbelong x t) -> list (RT t).
  induction l; intros.
   exact nil.

   apply cons.
    apply rid_rtype with a; intuition.
    apply IHl; intuition.
 Defined.

 Lemma elements_belong' (t : rtype) : forall x,
    In x (Nat_Sets.elements t) ->
        rbelong x t.
  intros.
  rewrite <- Nat_Sets.elements_spec1.
  intuition.
 Qed.

 Definition RIDs t := RIDs0 t (Nat_Sets.elements t) (elements_belong' t).

 Lemma RIDs0_spec (t : rtype) (l : list rid) (H : forall x, In x l -> rbelong x t) :
   forall k : RT t, In (to_rid _ k) l -> In k (RIDs0 t l H).
  intros.
  induction l; inversion H0; subst.
   left.
   rewrite rid_rtype_inverse.
   f_equal.
   apply proof_irrelevance.
  
   right.
   apply IHl; trivial.
 Qed.

 Lemma RIDs_spec (t : rtype) : forall x, In x (RIDs t).
  intros.
  apply RIDs0_spec.
  generalize (Nat_Sets.elements_spec1 t (to_rid t x)); intro.
  generalize (to_rid_belong t x).
  intuition.
  rewrite InA_alt in H1.
  firstorder; subst; trivial.
 Qed.


End RegionTypesNat.


Module TadaModel (ht : HeapTypes) .
 Import RegionTypesNat.
 Module Export TheHeap := MHeaps ht.

 (* Action identifiers are pairs of string and lists of values *)
 Definition AID := (string * (list Val))%type.

 Record SA :=
   {
     sa_dom :> Type;
     sa_setoid : Setoid sa_dom;
     sa_op : partial_op sa_dom;
     sa_sa : SepAlg sa_op
   }.

 Program Instance unit_Setoid : Setoid unit.
 Instance unit_sa : SepAlg (fun _ _ => lift_val tt).
  apply Build_SepAlg with (Setof.singleton tt); intuition.
   cbv; auto.
   exists tt; destruct m; cbv; intuition.
    exists tt; intuition.
   destruct m1; destruct m2; reflexivity.
 Defined.

 Definition unit_SA : SA := {| sa_dom := unit |}.

 Definition Promises := (AID -> bool) -> nat.
 Definition Witnesses := AID -> nat.

 Definition RSA (t : rtype) := RT t -> SA.

 Record LState (t : rtype) (rsat : RSA t) := {
   ls_hp : store;
   ls_gd : forall r : RT t, sa_dom (rsat r);
   ls_pr : RT t -> Promises;
   ls_wi : RT t -> Witnesses
  }.

 Definition SState (t : rtype) (rsat : RSA t) := RT t -> LState t rsat.

 (* Type for interference specifications.
     Choices: this does not need to be local (with respect to the guard) --
       we ill interpret it as the local closure.
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

End TadaModel.