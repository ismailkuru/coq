Add LoadPath "C:\td202\GitHub\coq\views".
Require Import SetoidClass.
Require Import MySetoids.

Definition partial_dec_op (A : Type) := A -> A -> option A.

Definition lift_op_dec {A} (op : partial_dec_op A) : option A -> option A -> option A
  := fun x y => match x with
       | None => None
       | Some x' => match y with
         | None => None
         | Some y' => op x' y'
         end end.

Class PermAlgMixin {A} `{A_setoid : Setoid A} (op : partial_dec_op A) :=
  {
    pa_morph :> Proper (equiv ==> equiv ==> equiv) op;
    pa_comm : forall x y, op x y == op y x;
    pa_assoc : forall x y z, lift_op_dec op (op x y) (Some z)
                        == lift_op_dec op (Some x) (op y z);
    pa_unit : A;
    pa_unit_law : forall x, op pa_unit x == Some x
  }.

Module FracPerm.
  Require Import QArith.

  Definition T := { k : Q | 0 <= k <= 1 }.

  Definition FPequiv (a b : T) : Prop := proj1_sig a == proj1_sig b.
  Instance FPequiv_equivalence : Equivalence FPequiv.
   intuition.
   repeat intro; unfold FPequiv in *.
   rewrite H; trivial.
  Qed.
  Program Instance FPsetoid : Setoid T.

  Definition compat := fun (a b : T) => proj1_sig a + proj1_sig b <= 1.

  Require Import Tactics.
  Instance compat_morph : Proper (FPequiv ==> FPequiv ==> iff) compat.
   repeat intro.
   unfold FPequiv in *.
   unfold compat.
   split; intro; rewr auto.
  Qed.

  

  Definition compat_dec (a b : T) : {compat a b} + {~compat a b}.
   remember (proj1_sig a + proj1_sig b ?= 1) as c.
   destruct c;
   try solve [left; apply Qle_alt; rewrite <- Heqc; auto with *].
   right; unfold compat; rewrite Qle_alt; auto.
  Defined.


  Program Definition zero : T := 0.
  Program Definition full : T := 1.
  Solve All Obligations using intuition.

  Section plus.
    Variables x y : T.
    Hypothesis small : compat x y.
    Program Definition sum : T := exist _ (proj1_sig x + proj1_sig y) _.
    Obligation 1.
     intuition.
     destruct x; destruct y; simpl.
     destruct a.
     destruct a0.
     apply (Qplus_le_compat 0 _ 0); trivial.
    Qed.
  End plus.

  Definition plus (x y : T) : option T :=
    match compat_dec x y with
      | left l => Some (sum x y l)
      | _ => None
    end.

  Instance proj1_sig_morph : Proper (FPequiv ==> Qeq) (@proj1_sig _ _).
   firstorder.
  Qed.

  Ltac compat_incompat :=
    match goal with [H : compat _ _, H' : ~ compat _ _ |- _] => contradiction H'; rewr auto end.


Lemma Qle_plus_pos_eq : forall x y z, 0 <= x -> (x + y <= z)%Q -> y <= z.
intuition.
apply Qplus_le_r with x. 
eapply Qle_trans; eauto.
rewrite <- Qplus_0_l at 1.
apply Qplus_le_l.
trivial.
Qed.

  Ltac plus_tac :=   cbv [Proper respectful compat]; intuition; repeat match goal with
     | H : Some _ = Some _ |- _ => inversion H; clear H; subst
     | H : Some _ = None |- _ => inversion H
     | H : None = Some _ |- _ => inversion H
     | H : ?X <= 1 |- ?Y <= 1 => let f := fresh in assert (Qeq Y X) as f by first [ring | rewr auto]; rewrite f; trivial
     | |- context [plus ?x ?y] => let f := fresh "PLUS" in remember (plus x y) as f; destruct f
     | x : T |- ?bah <= 1 => match bah with context [ x ] => let f1 := fresh x in let f2 := fresh in destruct x as [f1 f2]; destruct f2; simpl in * end
     | Ha : ?a <= 1 |- ?b <= 1 => let Hpd := fresh in
      assert (0 <= a - b) as Hpd by
        (ring_simplify;
         repeat (auto with *;
             match goal with XX : T |- _ => match goal with |- context [XX] =>
                let F := fresh in destruct XX as [XX F]; destruct F; simpl end end));
      apply (Qle_plus_pos_eq _ _ _ Hpd);
      let H' := fresh in assert (a - b + b == a)%Q by ring; rewrite H'; exact Ha
     | _ => progress (unfold plus in *; simpl)
     | |- context [compat_dec ?x ?y] => lazymatch goal with
            | H' : _ = compat_dec x y |- _ => fail
            | _ => let f := fresh "CD" in remember (compat_dec x y) as f; destruct f end
     | H : context [compat_dec ?x ?y] |- _ => lazymatch goal with
            | H' : _ = compat_dec x y |- _ => fail
            | _ => let f := fresh "CD" in remember (compat_dec x y) as f; destruct f end
     | _ => progress unfold FPequiv; unfold sum; simpl; first [ring | rewr auto]
     | H : compat ?x ?y -> False |- _ => contradiction H; clear dependent H; unfold compat in *
     | _ => progress unfold sum in *; simpl in *
     | _ => progress intuition
   end.

  Local Obligation Tactic := plus_tac.
  Program Instance FP_pa : PermAlgMixin plus := {| pa_unit := zero |}.

  Lemma compat_comm : forall a b, compat a b -> compat b a.
   plus_tac.
  Qed.
  Hint Resolve compat_comm.
  Lemma compat_plus1 : forall a b ab c, Some ab = plus a b -> compat ab c -> compat a c.
   plus_tac.
  Qed.
  Hint Resolve compat_plus1.
  Lemma compat_plus2 : forall a b ab c, Some ab = plus a b -> compat ab c -> compat b c.
   plus_tac.
  Qed.
  Hint Resolve compat_plus2.


  Lemma compat_plus_def : forall a b, forall H: compat a b,
   Some (sum a b H) == plus a b.
   plus_tac.
  Qed.
  Lemma compat_zero : forall a, compat zero a.
   plus_tac.
  Qed.
  Hint Resolve compat_zero.
  Lemma compat_zero2 : forall a, compat a zero.
   plus_tac.
  Qed.
  Hint Resolve compat_zero2.

  Lemma sum_morph : forall x x', FPequiv x x' -> forall y y', FPequiv y y' -> forall c c',
       FPequiv (sum x y c) (sum x' y' c').
   plus_tac.
  Qed.
  Hint Rewrite sum_morph.

  Lemma fp_match : forall x y z, forall P : compat x y,
       FPequiv (match plus x y with Some k => k | _ => z end) (sum x y P).
   plus_tac.
  Qed.


End FracPerm.


Module Type PermissionSeparationAlgebraParams.
  Parameter A : Type.
  Parameter PA : Type.
  Declare Instance PA_Setoid : Setoid PA.
  Parameter op : partial_dec_op PA.
  Declare Instance PA_PermAlg : PermAlgMixin op.
End PermissionSeparationAlgebraParams.

Require Import SeparationAlgebras.
Require Import Tactics.
Require Import Setof.
Module PermissionSeparationAlgebra (Export params : PermissionSeparationAlgebraParams).
  Definition S := A -> PA.
  Program Instance S_Setoid : Setoid S :=
    {| equiv := fun c1 c2 => forall t, c1 t == c2 t |}.
   Obligation 1.
    split; 
     repeat intro; use_foralls; rewr auto.
   Qed.
 
  Definition PA_compat (p1 p2 : PA) : Prop :=
     match op p1 p2 with Some _ => True | _ => False end.
  Local Infix "#" := PA_compat (at level 50).
  Local Infix "+" := op.
  Instance PA_compat_morphism : Proper (equiv ==> equiv ==> Basics.impl) PA_compat.
   repeat intro.
   unfold PA_compat in *.
   remember (y + y0).
   assert (o == y + y0) by (subst; reflexivity).
   destruct o; intuition.
   rewrite <- H, <- H0 in H2.
   remember (x + x0).
   destruct o; intuition.
  Qed.
  

  Definition sepop : partial_op S :=
    fun c1 c2 => {|
            defined := forall t, c1 t # c2 t;
            val := fun t => match c1 t + c2 t with
               | Some perm => perm
               | _ => pa_unit
               end |}.

  Lemma sepop_fact : forall c1 c2, defined (sepop c1 c2) ->
    forall t, Some (val (sepop c1 c2) t) == c1 t + c2 t.
   simpl; unfold PA_compat.
   intros.
   use_foralls.
   remember (c1 t + c2 t).
   destruct o; intuition.
  Qed.

  Lemma PA_compat_comm : forall x y, x # y -> y # x.
   cbv.
   firstorder.
   generalize (pa_comm x y).
   destruct (x + y); destruct (y + x); intuition.
  Qed.
  Hint Resolve PA_compat_comm.

  Program Instance S_SA : SepAlg sepop :=
    {| sa_unit := singleton (fun t => pa_unit) |}.
  Obligation 1.
    repeat intro.
    split; simpl.
     intuition; use_foralls; rewr trivial.

     intuition; use_foralls.
     assert (x t + x0 t == y t + y0 t) as Heq.
      rewr auto.
     induction (x t + x0 t);
      induction (y t + y0 t); intuition.
  Qed.
  Obligation 2.
    split; simpl; intuition; use_foralls.
     assert (x t + y t == y t + x t) as Heq.
      apply pa_comm.
     induction (x t + y t);
      induction (y t + x t); intuition.
  Qed.

  Definition op_foo : forall x y, x # y -> PA.
    intros.
    unfold PA_compat in H.
    destruct (x + y).
    exact p.
    destruct H.
  Defined.

  Lemma op_foo_plus : forall x y, forall P : x # y, x + y = Some (op_foo x y P).
   intros.
   unfold op_foo.
   unfold PA_compat in *.
   destruct (x + y);
    easy.
  Qed.

  Obligation 3.
   split; simpl; intuition;
    repeat (match goal with Hx : A -> _, ht : A |- _ => generalize (Hx ht); clear Hx; intro Hx end);
             generalize (pa_assoc (m1 t) (m2 t) (m3 t)); intro; unfold PA_compat.
    rewrite (op_foo_plus _ _ H0) in *; simpl in *.
    destruct (m2 t + m3 t); intuition.
    rewrite (op_foo_plus _ _ H2) in *.
    destruct H1.

    rewrite (op_foo_plus _ _ H0) in *; simpl in *.
    rewrite (op_foo_plus _ _ H2) in *; simpl in *.
    destruct (m2 t + m3 t); intuition.
    destruct (m1 t + p); intuition.

    rewrite (op_foo_plus _ _ H) in *; simpl in *.
    destruct (m1 t + m2 t); intuition.
    rewrite (op_foo_plus _ _ H2) in *.
    destruct H1.

    rewrite (op_foo_plus _ _ H) in *; simpl in *.
    rewrite (op_foo_plus _ _ H2) in *; simpl in *.
    destruct (m1 t + m2 t); intuition.
    simpl in *.
    destruct (p + m3 t); intuition.

    unfold PA_compat in *.
    destruct (m1 t + m2 t); simpl in *; intuition.
     destruct (p + m3 t); simpl in *; intuition.
      destruct (m2 t + m3 t); simpl in *; intuition.
       destruct (m1 t + p1); simpl in *; intuition.
  Qed.

  Obligation 4.
   exists (fun x => pa_unit); intuition.
    exists (fun x => pa_unit); intuition.
     split;
      simpl; intuition.
      unfold PA_compat.
      generalize (pa_unit_law (m t)); intro.
      destruct (pa_unit + m t); intuition.  

      use_foralls; unfold PA_compat in *.
      generalize (pa_unit_law (m t)); intro.
      destruct (pa_unit + m t); intuition.
  Qed.
  Obligation 5.
   destruct H0.
   unfold lift_val in *; simpl in *; intuition.
   use_foralls.
   rewrite <- H8.
   generalize (pa_unit_law (m1 t)); intro.
   rewrite <- H3, <- H6 in H9.
   destruct (i t + m1 t); intuition.
   unfold equiv in H9; simpl in H9.
   rewrite H9; reflexivity.
  Qed.
End PermissionSeparationAlgebra.