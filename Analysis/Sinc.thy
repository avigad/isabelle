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

(* Should be easier to conclude integrability from calculation of an integral. *)
(* Adapted from proof in Distributions.thy. *)
lemma integral_expneg_alpha_atLeast0:
  fixes x::real
  assumes pos: "0 < u"
  shows "LBINT x:{0..}. exp (- (x * u)) = 1/u" (is "?eq")
  and "set_integrable lborel {0..} (\<lambda>x. exp (- (x * u)))" (is ?int)

proof -
  have "positive_integral lborel (\<lambda>x. ereal (exp (- (x * u)) * indicator {0..} x)) =
  positive_integral lborel (\<lambda> x. ereal (exp (- (x * u))) * indicator {0..} x)"
    by (intro positive_integral_cong) (auto split: split_indicator)
  also have "\<dots> = ereal (0 - (- 1 / u * exp (- u * 0)))"
    apply (rule positive_integral_FTC_atLeast[where F="\<lambda>x. - 1 / u * exp (- u * x)"])
    apply measurable
    using `0 < u`
    apply (auto intro!: DERIV_intros)
    apply (rule tendsto_eq_intros)
    apply (subst filterlim_at_top_mirror)
    apply (rule tendsto_eq_intros)
    apply (rule filterlim_compose[of exp])
    apply (rule exp_at_bot)
    apply simp_all
    apply (rule filterlim_tendsto_pos_mult_at_bot)
    apply (rule tendsto_const)
    apply (rule `0 < u`)
    apply (rule filterlim_ident)
    apply auto
    done
  finally have *: "positive_integral lborel (\<lambda>x. ereal (exp (- (x * u)) * indicator {0..} x)) = 
      ereal (1 / u)"
    by simp
  show ?eq
    by (rule positive_integral_eq_erealD[OF *]) (simp_all add: mult_nonneg_nonneg)
  show ?int
    by (rule positive_integral_eq_erealD[OF *]) (simp_all add: mult_nonneg_nonneg)
qed

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

definition sinc :: "real \<Rightarrow> real" where "sinc t \<equiv> LBINT x=0..t. sin x / x"

lemma sinc_at_top: "(sinc ---> \<pi>/2) at_top"
  sorry

lemma Billingsley_26_15:
  assumes "T \<ge> 0"
  shows "\<And>\<theta>. LBINT t=0..T. sin (t * \<theta>) / t = sgn \<theta> * sinc (T * \<bar>\<theta>\<bar>)"
  sorry

end