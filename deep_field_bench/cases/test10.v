
From elpi.ext Require Import automation.
From Stdlib Require Import Reals Lra.


Lemma test10 x (p : x +1 <>0) :
  r 10 x = r_alt 10 x.
Proof.
  unfold r, r_alt.
  Time deep_field.
  reflexivity.
  all:nra.
Qed.
