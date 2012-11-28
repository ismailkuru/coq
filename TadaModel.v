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
End RegionTypes.

Module RegionTypesNat (ms : SetsOn) : RegionTypes.
  Require Import ProofIrrelevance.

  Module Nat_Sets := ms Nat_as_OT.

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
  
  Definition rfresh (t : rtype) : rid :=
   match (Nat_Sets.max_elt t) with
   | Some r => S r
   | None => 0
   end.

  Lemma fresh_not_belong : forall t,
      ~ rbelong (rfresh t) t.
   cbv; intuition.
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
End RegionTypesNat.

Module TadaModel (ht : HeapTypes) (Import rt : RegionTypes).
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

 Record World (t : rtype) :=
   {
     world_rsa : RSA t;
     world_local : LState t world_rsa;
     world_shared : SState t world_rsa;
     world_if_spec : forall r : RT t, IF_Spec t world_rsa r
   }.

End TadaModel.