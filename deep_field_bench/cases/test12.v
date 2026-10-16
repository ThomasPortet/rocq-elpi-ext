
From elpi.ext Require Import automation.
From Stdlib Require Import Reals Lra.


Lemma test12 x (p : x +1 <>0) :
  r 12 x = r_alt 12 x.
Proof.
  unfold r, r_alt.
  Time deep_field.
  reflexivity.
  all:nra.
Qed.
