Add LoadPath "C:\td202\GitHub\coq\views".


Require Import SeparationAlgebras.
Require Import SetoidClass.
Require Import Tactics.
Require Import Setof.
Require Import CountableFiniteMaps.

Module Type CFMapSAParams.
  Parameter A : Type.
  Declare Instance A_Setoid : Setoid A.
  Declare Instance A_Countable : Countable A.
  Parameter R : Type.
  Declare Instance R_Setoid : Setoid R.
  Parameter R_sepop : partial_op R.
  Declare Instance R_SepAlg : SepAlg R_sepop.
End CFMapSAParams.

Module CFMapSA (Import params : CFMapSAParams).
  