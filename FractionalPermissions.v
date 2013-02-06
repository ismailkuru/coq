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

  Ltac plus_tac :=   cbv [Proper respectful]; intuition; repeat match goal with
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

  Program Instance FP_pa : PermAlgMixin plus := {| pa_unit := zero |}.
  Solve Obligations using plus_tac.

End FracPerm.
