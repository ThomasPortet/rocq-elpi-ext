
From elpi.ext Require Import automation.
From Stdlib Require Import Reals Lra.


Lemma test7 x (p : x +1 <>0) :
  r 7 x = r_alt 7 x.
Proof.
  unfold r, r_alt.
  Time deep_field.
  reflexivity.
  all:nra.
Qed.
