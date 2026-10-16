
From elpi.ext Require Import automation.
From Stdlib Require Import Reals Lra.


Lemma test5 x (p : x +1 <>0) :
  r 5 x = r_alt 5 x.
Proof.
  unfold r, r_alt.
  Time deep_field.
  reflexivity.
  all:nra.
Qed.
