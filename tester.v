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

Ltac compute_gcd D N :=
  constr:(pair 1%Z (pair (PX (Pc 2) 1 (Pc 0))
    (pair (Pc 1) (PX (Pc 1) 1 (Pc 0))))%Z).


(* TODO: find how to reduce Pphi_pow without reducing IZR. *)
Ltac reduce_Pphi_pow :=
    cbv [Pphi_pow Pphi_avoid mult_dev Peq Z.eqb P0 mkmult_c
        mkmult_c_pos get_signZ Pos.eqb mkmult_rec List.rev' add_pow_list
        mkmult1 List.rev_append List.hd BinNat.N.add
        add_mult_dev mkadd_mult mkmult_c_pos mkmult_rec BinNat.N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op List.rev' List.rev_append  List.hd List.tl add_pow_list mkmult_rec Pos.add Nat.add]. 

Ltac den_gcd_n0 :=
  split;[ apply Rmult_integral_contrapositive; split;
    [apply not_eq_sym, Rlt_not_eq, Rlt_0_2 | ]| ]; apply PI_neq0.

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

Definition Nnorm :=
  norm_subst (0%Z) (1%Z) Z.add Z.mul Z.sub Z.opp Z.eqb Z.div_eucl.

Ltac fs5 := Field_simplify_gcd Nnorm RField_lemma5 ltac:(find_fraction).

Lemma toto : PI / (PI ^ 2 + PI ^ 2) = exp 1 / (exp 1 + exp 1).

field_simplify_gcd fs5  / (PI / (PI ^ 2 + PI ^ 2))  ( exp 1 / (exp 1 + exp 1)).


Admitted.
 Lemma toto3 x : (3*x + 6 )/3 = x+2.
 field_simplify_gcd fs5  / ((3*x + 6 )/3).
easy.
easy.
Admitted.

Lemma toto1 : (PI^5 + 4* PI^3 + 5* PI^2 +3* PI + 15) /(PI^4 - PI ^3 + 2 *PI^2 - 3 * PI -3) = (PI ^ 3 + PI + 5) / (PI ^ 2 - PI - 1).
field_simplify_gcd fs5 /((PI^5 + 4* PI^3 + 5* PI^2 +3* PI + 15) /(PI^4 - PI ^3 + 2 *PI^2 - 3 * PI -3)).
Lemma toto4 x :(x + 2) /(3/3) = x + 2.
 field_simplify_gcd fs5  / ((x + 2) /(3/3)).
 easy.
Admitted.

Lemma toto5 x : (3*x*x + 6 *x)/ (3 *x) = x +2.
 field_simplify_gcd fs5  / ((3*x*x + 6 *x)/ (3 *x)).
 easy.
Admitted.
