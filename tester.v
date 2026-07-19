From Stdlib Require Import Reals Lra.
Import Ring_polynom.
From elpi Require Import elpi ext.
From elpi.ext Require Import flipper.
Open Scope R_scope.
Definition RField_lemma5 :=
  Field_theory.Field_rw_pow_correct_w_gcd (Eqsth R) (Eq_ext Rplus Rmult Ropp)
  (@f_equal _ _ Rinv) (F2AF (Eqsth R) (Eq_ext _ _ _) Rfield) R_rm R_power_theory
  get_signZ_th (Ztriv_div_th Rset IZR).
  
Definition Pmul := Pmul 0%Z 1%Z Z.add Z.mul Z.eqb.

(* Term is the expression that was given by the user for simplification.
  FV is the list of sub-expressions of Term that are not recognized as
  compound field expression (they are considered as variables).  D and N
  are two polynomials (in type Pol Z), such that Term = N / D is already
  proved,  but N / D is not a reduced fraction because these two polynomials
  may have a non-trivial common divisor.
  This tactic also assume that the goal has approximately the shape :
  forall nfe, Fnorm FV fe = nfe ->  <some conditions> ->
    FEeval _ .. _ fe -> Pphi_pow N / Pphi_pow D
  where FEeval _ .. _ fe is convertible with Term.  *)
Ltac find_fraction Term FV D N :=
  let hyp := fresh "rewrite_lemma" in
  intros hyp;
  let D1 := eval vm_compute in D in
  let N1 := eval vm_compute in N in
  let fact_n0 := fresh "factor_not_0" in
  let num_eq := fresh "equality_for_numerator" in
  let den_eq := fresh "equality_for_denumerator" in
  let res :=
    constr:(ltac:(elpi factorize_by_gcd ltac_term:(N1) ltac_term:(D1))) in
  let F := eval cbv [fst] in (fst res) in
  let N2 := eval cbv [fst snd] in (fst (snd res)) in
  let D2 := eval cbv [fst snd] in (fst (snd (snd res))) in
  let Gcd := eval cbv [snd fst] in (snd (snd (snd res))) in
  assert (fact_n0 : IZR F <> 0) by (apply eq_IZR_contrapositive; easy);
  enough
  (Peq Z.eqb (Pmul (Pc F) N1) (Pmul N2 Gcd) = true
    /\
    Peq Z.eqb (Pmul (Pc F) D1) (Pmul D2 Gcd) = true) as [num_eq den_eq];
    [generalize (hyp F N2 D2 Gcd fact_n0 num_eq den_eq);
          clear hyp fact_n0 num_eq den_eq;
          let hyp2 := fresh "rewrite_lemma2" in 
          intros hyp2;
          let ty := type of hyp2 in
          lazymatch type of hyp2 with
          | _ -> ?t = ?r =>
            change t with Term in hyp2;
            (rewrite hyp2; clear hyp2);
            [ unfold display_pow_linear; reduce_Pphi_pow|
             cbv [fst snd PCond condition PEeval BinList.nth BinNat.N.to_nat
            List.hd PosDef.Pos.to_nat Init.Nat.add PosDef.Pos.iter_op BinList.jump List.tl]]
          end
          |
          clear hyp fact_n0;
          split; 
           [ reduce_Pphi_pow; easy
          |   easy]
  ].

Lemma happy_life : PI / (PI ^ 2 + PI ^ 2) = 4 / (8 * PI).
Proof.
field.
enough (PI > 0) by nra.
apply PI_RGT_0.
Qed.

Lemma field_unhappy : 1 + exp (PI / (PI ^ 2 + PI ^ 2)) =
  exp (4 / (8 * PI)) + 1.
Proof.
Fail field.
Abort.

Definition Nnorm :=
  norm_subst (0%Z) (1%Z) Z.add Z.mul Z.sub Z.opp Z.eqb Z.div_eucl.

Ltac fs5 := Field_simplify_gcd Nnorm RField_lemma5 ltac:(find_fraction).

Lemma field_still_unhappy :
  exp (PI / (PI ^ 2 + PI ^ 2)) = exp (4 / (8 * PI)).
Proof.
assert (PI_GT0 := PI_RGT_0).
field_simplify (PI / (PI ^ 2 + PI ^ 2)) (4 / (8 * PI)).
Abort.

Lemma field_solution :
  exp (PI / (PI ^ 2 + PI ^ 2)) = exp (4 / (8 * PI)).
Proof.
assert (PI_GT0 := PI_RGT_0).
Fail field.
field_simplify_gcd fs5  / (PI / (PI ^ 2 + PI ^ 2)) (4 / (8 * PI)).
easy.
nra.
nra.
Qed.

Lemma field_simplify_sandbox : cos (PI / 2) = cos (2 * (PI / 4)).
Proof.
field_simplify (2 * (PI / 4)).
field_simplify_gcd fs5 / (2 * PI / 4);[ | nra ..].
easy.
Qed.

Elpi Tactic toto.
From elpi.ext Extra Dependency "encode.elpi" as encode.

Elpi Accumulate Plugin "ext.elpi".
Elpi Accumulate File encode.

Elpi Query lp:{{
  sigma P Q R V1 V2 T1 T2 V1_w V2_w Ne Ne' N' De De' D' Gcd' G' Gcd\
  P = {{@PEadd Z (@PEc Z (-1)%Z) (@PEmul Z (@PEc Z 4%Z) 
       (@PEpow Z (PEX Z 1) (Npos 2)))}},
  Q = {{@PEadd Z (@PEc Z 1%Z) (@PEmul Z (@PEc Z 2%Z)
        (PEX Z 1))}},
  R = {{Nnorm 19 nil lp:P}},
  coq.reduction.vm.norm R T1 V1,
  coq.reduction.vm.norm {{Nnorm 19 nil lp:Q}} T2 V2,
  pol_encode V1 V1_w,!,
  pol_encode V2 V2_w,
  gcd_poly V1_w V2_w Gcd Ne' De',
  collect_glob_lcm_poly Ne' 1 LCMN,
  collect_glob_lcm_poly De' 1 LCMD,
  collect_glob_lcm_poly Gcd 1 LCMG,
  lcm_int LCMN LCMD LCMND,
  multiply_if_gt_one Ne' LCMND N',
  multiply_if_gt_one De' LCMND D',
  multiply_if_gt_one Gcd LCMG G',
  pe_decode N' Ne,
  pe_decode D' De,
  pe_decode G' Gcd',
  LCM2 is LCMND * LCMG,
  z_decode LCM2 LCMZ,
  coq.term->string Ne Nes,
  coq.term->string De Des,
  coq.term->string Gcd' Gcds,
  coq.term->string LCMZ LCMs
  % gcd_and_factors pol_encode pe_decode V1 V2 A B C M
}}.
