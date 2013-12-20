(*
Theory: Some_Calculus.thy
Authors: Jeremy Avigad, Luke Serafin

Some routine calculations from undergraduate calculus.
*)

theory Some_Calculus
imports Interval_Integral (* Distributions *)

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
  by (metis PInfty_neq_ereal(1) assms(1) assms(2) assms(3) integrable_nonneg positive_integral_eq_integral real_of_ereal(2))

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
  finally have *: "positive_integral lborel (%x. ereal (exp (- (x * u)) * indicator {0..} x)) = ereal (1 / u)"
    by simp
  show ?eq
    by (rule positive_integral_eq_erealD[OF *]) (simp_all add: mult_nonneg_nonneg)
  show ?int
    by (rule positive_integral_eq_erealD[OF *]) (simp_all add: mult_nonneg_nonneg)
qed

lemma Collect_eq_Icc: "{r. t \<le> r \<and> r \<le> b} = {t .. b}"
  by auto

(* From Billingsley section 18. *)
lemma ex_18_4_1_deriv: "DERIV (\<lambda>x. (1/(1+u^2)) * (1 - exp (-u * x) *
    (u * sin x + cos x))) x :> exp (-u * x) * sin x"
  apply (auto intro!: DERIV_intros)
by (simp_all add: power2_eq_square field_simps)

lemma ex_18_4_1:
  assumes "t \<ge> 0"
  shows "LBINT x=0..t. exp (-u * x) * sin x = (1/(1+u^2)) *
  (1 - exp (-u * t) * (u * sin t + cos t))"
  unfolding interval_lebesgue_integral_def
  using integral_FTC_atLeastAtMost[of 0 t "\<lambda>x. (1/(1+u^2)) *
    (1 - exp (-u * x) * (u * sin x + cos x))" "\<lambda>x. exp (-u * x) * sin x"]
    ex_18_4_1_deriv assms apply (simp add:  Collect_eq_Icc)
  sorry

lemma ex_18_4_2_deriv:
  "DERIV (\<lambda>u. 1/x * (1 - exp (-u * x)) * \<bar>sin x\<bar>) u :> \<bar>exp (-u * x) * sin x\<bar>"
  apply (auto simp only: intro!: DERIV_intros)
  by (simp add: abs_mult)

lemma ex_18_4_2_bdd_integral:
  assumes "s \<ge> 0"
  shows "LBINT u=0..s. \<bar>exp (-u * x) * sin x\<bar> =
  1/x * (1 - exp (-s * x)) * \<bar>sin x\<bar>"
using integral_FTC_atLeastAtMost[of 0 s "\<lambda>u. 1/x * (1 - exp (-u * x)) * \<bar>sin x\<bar>" "\<lambda>u. \<bar>exp (-u * x) * sin x\<bar>"] assms
ex_18_4_2_deriv 
apply  simp
  sorry

lemma ex_18_4_2_ubdd_integral:
  fixes x
  assumes pos: "0 < x"
  shows "LBINT u:{0..}. \<bar>exp (-(u * x)) * sin x\<bar> = \<bar>sin x\<bar> / x" (is "LBINT u:{0..}. ?f u = ?sx")
  apply (subst abs_mult)
  apply (subst mult_commute) back
  (* Would be nice not to need to do this explicitly. *)
  apply (subst divide_inverse)
  apply (subst inverse_eq_divide)
  apply (subst integral_expneg_alpha_atMost0 [symmetric], rule pos)
  (* Automated tools should get this. *)
  apply (subst mult_assoc)
  apply (subst integral_cmult(2), simp_all)
  (* Want a theorem which says that if we can calculate the integral of something, it is integrable. *)
sorry

definition sinc :: "real \<Rightarrow> real" where "sinc t \<equiv> LBINT x=0..t. sin x / x"

lemma sinc_at_top: "(sinc ---> \<pi>/2) at_top"
  sorry

lemma Billingsley_26_15:
  assumes "T \<ge> 0"
  shows "\<And>\<theta>. LBINT t=0..T. sin (t * \<theta>) / t = sgn \<theta> * sinc (T * \<bar>\<theta>\<bar>)"
  sorry

end