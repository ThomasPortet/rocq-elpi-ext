
From elpi.ext Require Import automation.
From Stdlib Require Import Reals Lra.


Lemma test15 x (p : x +1 <>0) :
  r 15 x = r_alt 15 x.
Proof.
  unfold r, r_alt.
  Time deep_field.
  reflexivity.
  all:nra.
Qed.
