Require Import Heaps.
Require Import StateTransformerConstructions.
Require Import Tactics.
Require Import Framework.
Require Import SeparationAlgebras.
Require Import Language.
Require Import Setof.
Require Import Utf8.
Require Import SetoidClass.

Module SLSASafetyParams
  (Import ht : HeapTypes)
  (Import hp : THeaps ht)
  (Import ha : THeapAtomics ht hp)
  (Import hst : THeapStateTransformers ht hp ha)
  <: SASafetyParams ha hst.

  (* The separation algebra is stores, with disjoint
      union as composition.
  *)
  Definition M := store.
  Definition M_setoid : Setoid M := store_setoid.

  (* First, overwrite is a setoid morphism. *)
  Instance overwrite_morphism : Proper
      (equiv ==> equiv ==> equiv) overwrite.
   split; intro; simpl; apply fun_equiv; rewr auto.
  Qed.

  (* Pointwise disjointness of partial functions. *)
  Definition pw_disjoint {A B} (f1 f2 : A -> option B) :=
    forall a, f1 a = None \/ f2 a = None.

  (* Which is a setoid morphism, wrt extensional
      equivalence.
  *)
  Instance pw_disjoint_morphism {A B} :
    Proper (equiv ==> equiv ==> iff)
      (pw_disjoint (A:=A) (B:=B)).
   cbv; intuition; use_foralls; rewr trivial.
  Qed.

  (* Disjointness of stores *)
  Definition st_disjoint (s1 s2 : store) :=
    pw_disjoint (heap s1) (heap s2) /\
    pw_disjoint (vars s1) (vars s2).

  Instance st_disjoint_morphism :
    Proper (equiv ==> equiv ==> iff)
      st_disjoint.
   repeat intro.
   unfold st_disjoint.
   rewr auto.
  Qed.

  (* Disjoint union of stores. *)
  Definition sepop : partial_op store :=
    fun s1 s2 =>
      {|
        defined := st_disjoint s1 s2;
        val := overwrite s1 s2
      |}.

  Instance sepop_morph :
    Proper (equiv ==> equiv ==> equiv)
      sepop.
   unfold sepop.
   split; simpl; rewr auto.
  Qed.

  (* Overwrite is commutative when disjoint *)
  Lemma disjoint_over_comm {A B} :
    forall x y : A -> option B,
      pw_disjoint x y ->
        pw_over x y == pw_over y x.
   cbv; intros.
   use_foralls.
   intuition.
    rewrite H1; destruct (y a); reflexivity.
    rewrite H1; destruct (x a); reflexivity.
  Qed.

  (* Disjoint union is commutative. *)
  Lemma sepop_comm : forall x y,
    sepop x y == sepop y x.
   split.
    cbv; firstorder.
   
    simpl; unfold st_disjoint.
    intuition; apply disjoint_over_comm;
    trivial.
  Qed.

  (* And associative. *)
  Lemma sepop_assoc : forall m1 m2 m3,
          lift_op sepop (sepop m1 m2) (lift_val m3) 
           == lift_op sepop (lift_val m1) (sepop m2 m3).
   intros; split.
   cbv;intuition;use_foralls;intuition;
   repeat match goal with 
       [H : ?X = None, H0 : context [?X] |- _] => rewrite H in H0
     | [H : context [match ?X with Some b => Some b | None => None end] |- _] => destruct X; intuition
     | [ |- context [match ?X with Some b => _ | None => _ end]] => destruct X; intuition
     end; intuition.

   intros; split; intro a;
   simpl; unfold pw_over.
   destruct (heap m1 a); intuition.
   destruct (vars m1 a); intuition.
  Qed.

  (* The unit is the empty store. *)
  Definition is_unit :=
    (fun s => (forall a, heap s a = None) /\ (forall b, vars s b = None)).

  Instance is_unit_morph : Proper (equiv ==> iff) is_unit.
   repeat intro.
   unfold is_unit;
   split; intros;
   use_foralls;
   rewr intuition.
  Qed.

  Definition sepop_unit : Setof (A:=store) :=
    {| elem := is_unit |}.

  Local Notation "a ∈ u" := (elem u a) (at level 50).

  (* There is only one unit, up to equivalence: *)
  Definition the_unit : store :=
   {|
     heap := fun _ : Loc => None;
     vars := fun _ : Var => None;
     heapBound := 0;
     heapFree := fun (m : nat) (_ : 0 <= m) => eq_refl
   |}.

  Lemma the_unit_is_unit : the_unit ∈ sepop_unit.
   cbv; easy.
  Qed.

  Hint Resolve the_unit_is_unit.

  (* There is a unit for every store *)
  Lemma sepop_unit_exists : forall m, exists i, i ∈ sepop_unit /\
                                          sepop i m == lift_val m.
   exists the_unit.
   cbv; intuition.
  Qed.

  (* There are no other units *)
  Lemma sepop_unit_min : forall m1 m2 i, i ∈ sepop_unit ->
                            (sepop i m1) == lift_val m2 ->
                             m1 == m2.
   cbv; intuition;
   use_foralls;
   rewr trivial.
  Qed.

  (* We now have a separation algebra *)
  Instance separationAlgebra : SepAlg sepop :=
    { sa_comm := sepop_comm;
      sa_assoc := sepop_assoc;
      sa_unit := sepop_unit;
      sa_unit_exists := sepop_unit_exists;
      sa_unit_min := sepop_unit_min
    }.

  (* Some convenient definitions and notations. *)
  Definition singlevar x v : Setof (A:=store) :=
    singleton (svstore x v).

  Infix "=>=" := singlevar (at level 25).

  Definition singleloc l v : Setof (A:=store) :=
    singleton (slstore l v).

  Infix "|->" := singleloc (at level 25).

  Infix "*" := (saop sepop).

  Notation "∃ x @ p" :=
     (setof_union (fun z => exists x, z == p))
     (at level 50).

  Coercion loc_val : Loc >-> Val.
  

  (* Now the axioms *)
  Definition axioms (p : (Setof (A:=M))) (c : Atomic) (q : (Setof (A:=M))) : Prop :=
   (∃ x, ∃ y, ∃ v, ∃ u, p = ( x =>= u * y =>= v) /\
                   c = assn x y /\
                   q = ( x =>= v * y =>= v)) \/
   (∃ x, ∃ v, ∃ l:Loc, ∃ u, p = ( x =>= l * l |-> u ) /\
                    c = mut_val x v /\
                    q = ( x =>= l * l |-> v ) ) \/
   (∃ x, ∃ y, ∃ l:Loc, ∃ v, ∃ u,
              p = ( x =>= l * l |-> u * y =>= v ) /\
              c = mut_var x y /\
              q = ( x =>= l * l |-> v * y =>= v)) \/
   (∃ x, ∃ y, ∃ l:Loc, ∃ v, ∃ u,
              p = ( x =>= l * l |-> v * y =>= u ) /\
              c = lu_var y x /\
              q = ( x =>= l * l |-> v * y =>= v)) \/
   (∃ x, ∃ y, ∃ u, ∃ v,
         p = ( x =>= u * y =>= v ) /\
         c = mkref x y /\
         q = ∃ l @ (x =>= loc_val l * l |-> v * y =>= v) )
                   .

  (* Erasure. *)
  Definition erase : M -> Setof (A:=State) :=
    fun p : M => singleton (sOK p).

  (* Now a whole lot of definitions, lemmas and tactics for proving
     atomic soundness.
  *)
  Instance sOK_morphism : Proper (equiv ==> equiv) sOK.
   firstorder.
  Qed.

  Instance pw_over_morphism2 {A B} : Proper (equiv ==> equiv ==> eq ==> eq) (pw_over (A:=A) (B:=B)).
   repeat intro.
   subst.
   apply pw_over_morphism; trivial.
  Qed.

Lemma saop__use {x y z} : saop__ sepop x y z ->
       defined (sepop x y) /\ val (sepop x y) == z.
firstorder.
Qed.

Ltac saop__tac := repeat match goal with
    [H : saop__ sepop _ _ _ |- _] =>
      generalize (saop__use H); clear H; intro H;
      destruct H
    end.

Ltac saoptac := match goal with
    [|- ?X ∈ saop _ _ _] => exists X; intuition end.

Ltac singleel := repeat 
  match goal with
   [H : elem (singleton ?Y) ?X |- _] =>
      generalize (single_elem H); clear H; intro H
  end.

Notation "[[ a ]]" := (interp a).
Infix "⊆" := subsetof (at level 50).
Notation "└  a  ┘" := (erase a).

Ltac nicedestr := repeat match goal with
  | [H : exists k : _, _ |- _] => destruct H as [k H]
  | [H : _ /\ _ |- _] => destruct H
  end.

Lemma singval_facts {s a b} :
   s ∈ a =>= b ->
     vars s a = Some b /\
     (forall x, x = a \/ vars s x = None) /\
     (forall l, heap s l = None).
intro.
repeat destruct H.
rewrite <- H0 in *.
intuition; rewrite H1.
cbv.
destruct (Var_eq_dec a a); intuition.

cbv.
destruct (Var_eq_dec a x0); intuition.
Qed.

Lemma singloc_facts {s a b} :
   s ∈ a |-> b ->
     heap s a = Some b /\
     (forall l, l = a \/ heap s l = None) /\
     (forall x, vars s x = None).
intro.
repeat destruct H.
rewrite <- H0 in *.
intuition; rewrite H;
cbv.
destruct (Loc_eq_dec a a); intuition.
destruct (Loc_eq_dec a l); intuition.
Qed.


Lemma sep_facts {s x0 y0} :
   s ∈ (x0 * y0) -> exists x, exists y, x ∈ x0 /\ y ∈ y0 /\
     (forall v, (vars s v = vars x v /\ vars y v = None) \/
           (vars s v = vars y v /\ vars x v = None)) /\
     (forall l, (heap s l = heap x l /\ heap y l = None) \/
           (heap s l = heap y l /\ heap x l = None)).
intros.
repeat destruct H.
intuition.
saop__tac.
rewrite <- H0 in *.
destruct H1.
unfold pw_disjoint in *.
exists x1; exists x2; intuition.
rewrite <- H3.
simpl.
unfold pw_over.
use_foralls;
destruct (vars x1 v); intuition.
inversion H6.
rewrite <- H3; simpl; unfold pw_over.
use_foralls.
destruct (heap x1 l); intuition.
inversion H6.
Qed. 

Ltac use_facts := repeat match goal with
  | [H : ?s ∈ ?a =>= ?b |- _] =>
     generalize (singval_facts H); clear H; intro H; push
  | [H : ?s ∈ ?a |-> ?b |- _] =>
     generalize (singloc_facts H); clear H; intro H; push
  | [H : ?s ∈ ?x0 * ?y0 |- _] =>
     generalize (sep_facts H); clear H; intro H; push
  end.
   
Lemma sep_facts_rev {s x0 y0} : forall x y,
  x ∈ x0 -> y ∈ y0 ->
   (forall v, (vars s v = vars x v /\ vars y v = None) \/
      (vars s v = vars y v /\ vars x v = None)) ->
   (forall l, (heap s l = heap x l /\ heap y l = None) \/
      (heap s l = heap y l /\ heap x l = None)) ->
        s ∈ x0 * y0.
intros.
exists s; intuition.
exists x; exists y; intuition.
split.
firstorder.

simpl; intuition;
intro;
unfold pw_over.
use_foralls.
destruct (heap x a); intuition.
inversion H7.
rewr auto.
use_foralls.
destruct (vars x a); intuition.
inversion H7.
rewr auto.
Qed.

Lemma singval_facts_rev {s a b} :
     vars s a = Some b ->
     (forall x, x = a \/ vars s x = None) ->
     (forall l, heap s l = None) ->
       s ∈ a =>= b.
intros.
exists s; intuition.
split.
firstorder.
intro.
use_foralls; cbv in *.
destruct (Var_eq_dec a a0);
intuition; rewr intuition.
Qed.

Lemma singloc_facts_rev {s a b} :
     heap s a = Some b ->
     (forall l, l = a \/ heap s l = None) ->
     (forall v, vars s v = None) ->
       s ∈ a |-> b.
intros.
exists s; intuition.
split.
intro.
use_foralls; cbv in *.
destruct (Loc_eq_dec a a0);
intuition; rewr intuition.
firstorder.
Qed.


Ltac blast := match goal with
  [H : ?X = Some _, H0 : ?X = None |- _] => rewrite H0 in H; inversion H
  end.

Ltac useoptions2 := repeat
  match goal with 
  | H : ?a = ?a |- _ => clear H
  | H : Some _ = Some _ |- _ => inversion H; clear H; subst
  | H : Some _ = None |- _ => inversion H
  | H : None = Some _ |- _ => inversion H
  | H : Some _ = ?a |- _ => rewrite <- H in *
  | H : None = ?a |- _ => rewrite <- H in *
  | H : ?a = Some _ |- _ => rewrite H in *
  | H : ?a = None |- _ => rewrite H in *
  | |- Some _ = None => fail 1
  | |- None = Some _ => fail 1
  | |- Some ?x = Some ?y => cut (x=y); [intro; subst; reflexivity | idtac]
  end. 


Ltac vartac := let v0 := fresh "v" in 
   intro v0;
   cbv - [vars heap]; simpl;
   repeat match goal with [ H : forall v : Var, _ |- _ ] => generalize (H v0); clear H; intro H end;
   repeat match goal with [ |- context [Var_eq_dec ?x ?y] ]=> destruct (Var_eq_dec x y); subst end;
   intuition (useoptions2; auto with *).
Ltac loctac := let l0 := fresh "l" in
   intro l0;
   cbv - [vars heap]; simpl;
   repeat match goal with [ H : forall l : Loc, _ |- _ ] => generalize (H l0); clear H; intro H end;
   repeat match goal with [ |- context [Loc_eq_dec ?x ?y] ]=> destruct (Loc_eq_dec x y); subst end;
   intuition (useoptions2; auto with *).


  Ltac updatetac := intros; use_facts;
    match goal with [H: ?W ∈ ?Z |- overwrite ?X ?Y ∈ _ * ?Z ] => apply sep_facts_rev with X W end;
    [ eexists; split; reflexivity | trivial | vartac | loctac ].



  Lemma update_var : forall s x u v o, s ∈ x =>= u * o ->
               (overwrite (svstore x v) s) ∈ x =>= v * o.
   updatetac.
  Qed.

  Lemma update_loc : forall s l u v o, s ∈ l |-> u * o ->
               (overwrite (slstore l v) s) ∈ l |-> v * o.
   updatetac.
  Qed.

Existing Instance saop_smorph.

Ltac commanddes := repeat match goal with
    | [H : choice_st _ _ _ |- _] => let x:= fresh "a" in destruct H as [x H]; simpl in H
    | [H : gchoice_st _ _ _ |- _] => let x:=fresh "a" in destruct H as [x H]; simpl in H; destruct H; subst
    | [H : relseq _ _ _ _ |- _] => let x:=fresh "s" in destruct H as [x H]; simpl in H; destruct H
    | [H : guard_st _ _ _ |- _] => destruct H
    | [H : selector (equiv_guard (sOK ?u)) (sOK ?v) |- _] => assert (u == v) by apply H; clear H
    end.


Ltac blitzcomp := match goal with
    | [|- (match vars ?x ?y with | Some a => _ | None => _ end) == _ ] =>
       repeat match goal with [ H : forall v : Var, _ |- _ ] => generalize (H y) H; clear H; intro H end;
       destruct (vars x y); intuition (useoptions2; auto with *)
    | [|- (match heap ?x ?y with | Some a => _ | None => _ end) == _ ] =>
       repeat match goal with [ H : forall l : Loc, _ |- _ ] => generalize (H y) H; clear H; intro H end;
       destruct (heap x y); intuition (useoptions2; auto with *)
    end.

Ltac axbelong := repeat match goal with
   | [|- sOK ?X ∈ collapse (so_map erase _) ]=> exists (erase X); split
   | [|- sOK ?X ∈ erase _ ] => exists (sOK X); intuition
   | [|- erase ?X ∈ so_map erase _ ] => exists X; intuition
   end.


(* This tactic is supposed to rewrite two assertions
   so their differences are at the start.  It doesn't
   work completely, but good enough for now!?
 *)
Ltac matchup_ U Hu V Hv cleanup :=
  match U with
   | ?a * ?b => match V with
     | a * b => idtac
     | a * ?c => rewrite (saop_comm _ _ a b) in Hu;
          rewrite (saop_comm _ _ a c) in Hv; (matchup_ b Hu c Hv ltac:(rewrite (saop_assoc _ _ _ _ a) in Hu;rewrite (saop_assoc _ _ _ _ a) in Hv)); cleanup
     | ?c * b => (matchup_ a Hu c Hv ltac:(rewrite (saop_assoc _ _ _ _ b) in Hu;rewrite (saop_assoc _ _ _ _ b) in Hv)); cleanup
     | _ => cleanup
     end
   | _ => idtac
  end.
Ltac matchup a b :=
  let x := fresh "A" in let y := fresh "A" in
    set (x := a); set (y := b); let hA := fresh in let hB := fresh in
    assert (x == a) by reflexivity; assert (y == b) by reflexivity;
    matchup_ a hA b hB idtac.

Ltac axmatchup := match goal with
  [H : ?x ∈ ?a * ?b |- _ ∈ collapse (so_map erase ?c)] =>
    matchup (a * b) c; match goal with
    [s := a * b |- _ ] => match goal with
      [H0 : s == _ |- _ ] => unfold s in H0; rewrite H0 in H; clear s H0
      end
    end
end.

  Ltac setoid_subst := repeat match goal with
     [X : _ |- _] =>
       match goal with 
        [H : X == ?Y |- _] => rewrite H in *; clear X H
        end
     end.


  Lemma lu_varAxiom x y (l:Loc) u v m :
    so_map_rel [[lu_var y x]]
     (collapse (so_map erase (x =>= l * l |-> v * y =>= u * singleton m)))
     ⊆ collapse (so_map erase (x =>= l * l |-> v * y =>= v * singleton m)).
   intros a H.
   do 6 destruct H.
   axmatchup.
   generalize (fun w => update_var _ _ _ w _ H); intro Hw.
   use_facts.
   singleel; ssubst.

   assert (a == sOK (overwrite (svstore y v) x2)).
    destruct H1; intuition; setoid_subst.
    simpl in H0.
    commanddes.
    rewrite <- H1.
    clear H1 s H0.
    rewrite H18.
    assert (vars x2 x = Some (loc_val l)).
     repeat match goal with [ H : forall v : Var, _ |- _ ] => generalize (H x); clear H; intro H end.
     intuition (useoptions2; auto with *).
    rewrite H0.
    assert (heap a1 l = Some v).
     rewrite H18.
     repeat match goal with [ H : forall l : Loc, _ |- _ ] => generalize (H l); clear H; intro H end.
     intuition (useoptions2; auto with *).
    rewrite H1.
    rewr easy.

   rewrite H2.
   axbelong.
   rewr trivial.
  Qed.


  Lemma soundAxioms :
     forall p a q, axioms p a q ->
       forall (m : M),
         subsetof (so_map_rel (interp a) 
                      (collapse (so_map erase (saop sepop p (singleton m))))
                     (R_morphism:=st_morph (interp a)))
           (collapse (so_map erase (saop sepop q (singleton m)))).
   intros.
   destruct H.
   nicedestr; subst.
   intros a H.
   do 6 destruct H.
   axmatchup.
   generalize (fun w => update_var _ _ _ w _ H); intro Hw.
   use_facts.
   singleel.
   setoid_subst.

   assert (a == sOK (overwrite (svstore x v) x2)).
    destruct H1; intuition; setoid_subst.
    simpl in H0.
    commanddes.
    rewrite <- H1, H13.
    rewrite <- H13 at 2.
    clear H1 A0 H4 H13 H H0 Hw H7 H9 H12 H14.
    blitzcomp.

   rewrite H2.
   axbelong.
   rewr trivial.


   destruct H.
   nicedestr; subst.
   intros a H.
   do 6 destruct H.
   axmatchup.
   generalize (fun w => update_loc _ _ _ w _ H); intro Hw.
   use_facts.
   singleel; setoid_subst.

   assert (a == sOK (overwrite (slstore l v) x2)).
    destruct H1; intuition; setoid_subst.
    simpl in H0.
    commanddes.
    rewrite <- H1.
    rewrite H13.
    rewrite <- H13 at 2.
    blitzcomp.
    rewrite H13 at 1.
    blitzcomp.

   rewrite H2.
   axbelong.
   rewr trivial.


   destruct H.
   nicedestr; subst.
   intros a H.
   do 6 destruct H.
   axmatchup.
   generalize (fun w => update_loc _ _ _ w _ H); intro Hw.
   use_facts.
   singleel; setoid_subst.

   assert (a == sOK (overwrite (slstore l v) x2)).
    destruct H1; intuition; setoid_subst.
    simpl in H0.
    commanddes.
    rewrite <- H2.
    destruct H0.
    rewrite <- H0.
    rewrite H20.
    clear H H4.
    blitzcomp.
    clear H2.
    rewrite H20.
    blitzcomp;
    rewrite H20; rewrite <- H20 at 2;
    blitzcomp. (* chokepoint! *)

   rewrite H2.
   axbelong.
   rewr trivial.

   destruct H.
   nicedestr; subst.
   apply lu_varAxiom.
   
   destruct H.
   nicedestr; subst.
   intros a H.
   do 6 destruct H.
   use_facts.
   singleel; setoid_subst.
   
   destruct H1; intuition; setoid_subst.
    simpl in H0.
    commanddes.
    rewrite H12 in *.
    assert (vars x2 y = Some v).
     repeat match goal with [ H : forall v : Var, _ |- _ ] => generalize (H y); clear H; intro H end.
     intuition (useoptions2; auto with *).
    rewrite H2 in *.
    destruct H1.
    cbv [fst snd] in H1.
    destruct H1.
    lazy [STmp STmakep st_trans makep_st equiv_guard selector] in H14.
    rewrite <- H14.
    axbelong.
    rewrite H12.
    apply sep_facts_rev with (overwrite (svstore x x0) (overwrite (slstore x0 v) x3)) x4.
     eexists.
      exists x0; reflexivity.
      rewrite (saop_assoc _ _).
      apply sep_facts_rev with (svstore x x0) (overwrite (slstore x0 v) (svstore y v)).
       eexists; split; reflexivity.
       apply sep_facts_rev with (slstore x0 v) (svstore y v).
        eexists; split; reflexivity.
        eexists; split; reflexivity.
        vartac.
        loctac.
        vartac.
        loctac.
        rewrite H; simpl; firstorder.
        vartac.
        rewrite H12 in *.
        loctac.
  Qed.

End SLSASafetyParams.

Module SeparationLogic (Import ht : HeapTypes).
  Module Import hp := MHeaps ht.
  Module Import ha := HeapAtomics ht hp.
  Module hst := HeapStateTransformers ht hp ha.
  Module Import slsp := SLSASafetyParams ht hp ha hst.
  Module Import bs := BasicSyntax ha.
  Module Import slsafe := SA_Safety ha bs hst slsp.
  Import slsafe.msp.

  Inductive SL : V -> Syntax -> V -> Prop :=
    | SL_atom : forall p q a, axioms p a q ->
                    SL p a q
    | SL_skip : forall p, SL p skip p
    | SL_loop : forall p c, SL p c p -> SL p (c)* p
    | SL_sequence : forall p q r c1 c2,
            SL p c1 q -> SL q c2 r -> SL p (c1 ;; c2) r
    | SL_choice : forall p q c1 c2,
            SL p c1 q -> SL p c2 q -> SL p (c1 + c2) q
    | SL_frame : forall p q r c, SL p c q -> SL (p*r) c (q*r)
    | SL_parallel : forall p1 q1 p2 q2 c1 c2,
            SL p1 c1 q1 -> SL p2 c2 q2 ->
                    SL (p1 * p2) (c1 || c2) (q1 * q2)
    | SL_conseq_l : forall p1 p2 c q, subsetof p1 p2 ->
            SL p2 c q -> SL p1 c q
    | SL_conseq_r : forall p c q1 q2, SL p c q1 ->
            subsetof q1 q2 -> SL p c q2
    | SL_disj : forall P c q, (forall p, p ∈ P -> SL p c q) ->
            SL (setof_union P) c q.

  Hint Resolve Safe_atomic.
  Hint Resolve Safe_mjoin_disj.

  Lemma SL_Safe : forall p c q, SL p c q -> Safe p c q.
   induction 1; intuition.
    eauto.
    rewr auto.
    rewr auto.
    apply Safe_mjoin_disj; trivial.
  Qed.

  Hint Resolve SL_Safe.
  Hint Resolve Safe_sound.

  Theorem SL_sound : forall p c q, SL p c q ->
    forall s, s ∈ erase p ->
        forall s', myOpSem.osms c s skip s' ->
            s' ∈ erase q.
   eauto.
  Qed.

End SeparationLogic.
