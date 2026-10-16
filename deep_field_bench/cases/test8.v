
From elpi.ext Require Import automation.
From Stdlib Require Import Reals Lra.


Lemma test8 x (p : x +1 <>0) :
  r 8 x = r_alt 8 x.
Proof.
  unfold r, r_alt.
  Time deep_field.
  reflexivity.
  all:nra.
Qed.
