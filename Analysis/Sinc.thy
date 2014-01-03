(*
Theory: Some_Calculus.thy
Authors: Jeremy Avigad, Luke Serafin

Some routine calculations from undergraduate calculus.
*)

theory Sinc
imports Interval_Integral

begin

(** Derivatives and integrals for CLT. **)

lemma exp_alpha_at_top:
  assumes pos: "0 < x"
  shows "LIM (u::real) at_top. exp (u * x) :> at_top"
  apply (rule filterlim_compose[of exp at_top at_top "\<lambda>u. u * x" at_top])
  apply (rule exp_at_top)
  apply (subst mult_commute)
  apply (rule filterlim_at_top_at_top[where Q = "\<lambda>x. True" and P = "\<lambda>x. True" and g = "op * (1/x)"])
  apply (rule mult_left_mono)
  apply simp apply (smt pos) apply simp
  apply (smt pos)
  apply simp
  by auto

lemma positive_integral_eq_erealD:
  assumes "positive_integral M f = ereal x"
  assumes "f \<in> borel_measurable M"
  assumes "AE x in M. 0 \<le> f x"
  shows "integrable M f" "lebesgue_integral M f = x"
  apply (metis PInfty_neq_ereal(1) integrable_nonneg assms)
  by (metis PInfty_neq_ereal(1) assms(1) assms(2) assms(3) integrable_nonneg 
    positive_integral_eq_integral real_of_ereal(2))

lemma integral_expneg_alpha_atLeast0:
  fixes u :: real
  assumes pos: "0 < u"
  shows "LBINT x=0..\<infinity>. exp (-x * u) = 1/u"
apply (subst interval_integral_FTC_nonneg[of _ _ "\<lambda>x. -(1/u) * exp (-x * u)" _ "-(1/u)" 0])
using pos apply (auto intro!: DERIV_intros)
apply (subgoal_tac "(((\<lambda>x. - (exp (- (x * u)) / u)) \<circ> real) ---> - (1 / u)) (at 0)")
apply (subst (asm) filterlim_at_split, force)
apply (subst zero_ereal_def)
apply (subst filterlim_at_split)
apply (simp_all add: ereal_tendsto_simps)
apply (subst filterlim_at_split[symmetric])
apply (auto intro!: tendsto_intros)
apply (subst exp_zero[symmetric])
apply (rule tendsto_compose[of exp])
using isCont_exp unfolding isCont_def apply metis
apply (subst tendsto_minus_cancel_left[symmetric], simp)
apply (rule tendsto_mult_left_zero, rule tendsto_ident_at)
apply (subst divide_inverse, subst minus_mult_left)
apply (rule tendsto_mult_left_zero)
apply (subst tendsto_minus_cancel_left[symmetric], simp)
apply (rule filterlim_compose[of exp _ at_bot])
apply (rule exp_at_bot)
apply (subst filterlim_uminus_at_top [symmetric])
apply (subst mult_commute)
apply (rule filterlim_tendsto_pos_mult_at_top [OF _ pos])
apply auto
by (rule filterlim_ident)

lemma Collect_eq_Icc: "{r. t \<le> r \<and> r \<le> b} = {t .. b}"
  by auto

(* From Billingsley section 18. *)
lemma ex_18_4_1:
  assumes "t \<ge> 0"
  shows "LBINT x=0..t. exp (-u * x) * sin x = (1/(1+u^2)) *
  (1 - exp (-u * t) * (u * sin t + cos t))"

  apply (subst zero_ereal_def)
  apply (subst interval_integral_FTC_finite 
      [where F = "(\<lambda>x. (1/(1+u^2)) * (1 - exp (-u * x) * (u * sin x + cos x)))"])
  apply (auto intro: continuous_at_imp_continuous_on)
  apply (rule DERIV_imp_DERIV_within, auto)
  apply (auto intro!: DERIV_intros)
by (simp_all add: power2_eq_square field_simps)

lemma ex_18_4_2_deriv:
  "DERIV (\<lambda>u. 1/x * (1 - exp (-u * x)) * \<bar>sin x\<bar>) u :> \<bar>exp (-u * x) * sin x\<bar>"
  apply (auto simp only: intro!: DERIV_intros)
  by (simp add: abs_mult)

(* not needed *)
lemma ex_18_4_2_bdd_integral:
  assumes "s \<ge> 0"
  shows "LBINT u=0..s. \<bar>exp (-u * x) * sin x\<bar> =
  1/x * (1 - exp (-s * x)) * \<bar>sin x\<bar>"

  apply (subst zero_ereal_def)
  apply (subst interval_integral_FTC_finite 
      [where F = "\<lambda>u. 1/x * (1 - exp (-u * x)) * \<bar>sin x\<bar>"])
  apply (auto intro: continuous_at_imp_continuous_on) [1]
  apply (rule DERIV_imp_DERIV_within, force)
  (* curiously, just copying the proof of ex_18_4_2_deriv doesn't work *)
  apply (rule ex_18_4_2_deriv)
  apply auto
done

(* clean this up! it should be shorter *)
lemma ex_18_4_2_ubdd_integral:
  fixes x
  assumes pos: "0 < x"
  shows "LBINT u=0..\<infinity>. \<bar>exp (-u * x) * sin x\<bar> = \<bar>sin x\<bar> / x" 

  apply (subst interval_integral_FTC_nonneg [where F = "\<lambda>u. 1/x * (1 - exp (-u * x)) * \<bar>sin x\<bar>"
    and A = 0 and B = "abs (sin x) / x"])
  apply force
  apply (rule ex_18_4_2_deriv)
  apply auto
  (* this is a little annoying -- having to replace 0 by "ereal 0" *)
  apply (subst zero_ereal_def)+
  apply (simp_all add: ereal_tendsto_simps)
  (* What follows are two simple limit calculations. Clean these up -- they should be
  shorter. *)
  apply (rule filterlim_mono [of _ "nhds 0" "at 0"], auto)
  prefer 2
  apply (rule at_le, simp)
  apply (subst divide_real_def)
  apply (rule tendsto_mult_left_zero)+
  apply (subgoal_tac "0 = 1 - 1")
  apply (erule ssubst)
  apply (rule tendsto_diff, auto)
  apply (subgoal_tac "1 = exp 0")
  apply (erule ssubst)
  apply (rule tendsto_compose) back
  apply (subst isCont_def [symmetric], auto)
  apply (rule tendsto_minus_cancel, auto)
  apply (rule tendsto_mult_left_zero, rule tendsto_ident_at)
  (* this is the second *)
  apply (subst divide_real_def)+
  apply (subgoal_tac "abs (sin x) * inverse x = 1 * abs (sin x) * inverse x")
  apply (erule ssubst)
  apply (rule tendsto_mult)+
  apply auto
  apply (subgoal_tac "1 = 1 - 0")
  apply (erule ssubst) back
  apply (rule tendsto_diff, auto)
  apply (rule filterlim_compose) back
  apply (rule exp_at_bot)
  apply (subst filterlim_uminus_at_top [symmetric])
  apply (subst mult_commute)
  apply (rule filterlim_tendsto_pos_mult_at_top [OF _ pos])
  apply auto
by (rule filterlim_ident)

lemma Billingsley_ex_17_5: "LBINT x=-\<infinity>..\<infinity>. inverse (1 + x^2) = pi"
  apply (subst interval_integral_substitution_nonneg[of "-pi/2" "pi/2" tan "\<lambda>x. 1 + (tan x)^2"])
  apply (auto intro: DERIV_intros)
  apply (subst tan_sec)
  using pi_half cos_is_zero
  apply (metis cos_gt_zero_pi less_divide_eq_numeral1(1) less_numeral_extra(3))
  using DERIV_tan
  apply (metis cos_gt_zero_pi less_divide_eq_numeral1(1) power2_less_0 power_inverse power_zero_numeral)
  apply (rule isCont_add, force)
  apply (subst power2_eq_square)
  apply (subst isCont_mult)
  apply (rule isCont_tan)
  (* Following line duplicated from above. *)
  using pi_half cos_is_zero
  apply (metis cos_gt_zero_pi less_divide_eq_numeral1(1) less_numeral_extra(3))
  apply (simp_all add: ereal_tendsto_simps filterlim_tan_at_left)
  apply (subst minus_divide_left)+
  by (rule filterlim_tan_at_right)

definition sinc :: "real \<Rightarrow> real" where "sinc t \<equiv> LBINT x=0..t. sin x / x"

lemma sinc_lim_lemma:
  "sinc t = pi / 2 - (LBINT u=0..\<infinity>. ((exp (- u * t)) / (1 + u^2)) * (u * sin t + cos t))"
unfolding sinc_def apply (subst divide_inverse)
  apply (subst inverse_eq_divide)
  (* Need to restrict this next application to only apply when x > 0. *)
  apply (subst integral_expneg_alpha_atLeast0[symmetric])
  sorry

lemma sinc_at_top: "(sinc ---> \<pi>/2) at_top"
  sorry

lemma Billingsley_26_15:
  assumes "T \<ge> 0"
  shows "\<And>\<theta>. LBINT t=0..T. sin (t * \<theta>) / t = sgn \<theta> * sinc (T * \<bar>\<theta>\<bar>)"
  sorry

end