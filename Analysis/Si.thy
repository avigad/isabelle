(*
Theory: Si.thy
Authors: Jeremy Avigad, Luke Serafin

Integral of sinc.
*)

theory Si

imports Interval_Integral

begin

(* move this to Deriv.thy *)

lemma has_field_derivative_within_open: "a \<in> s \<Longrightarrow> open s \<Longrightarrow>
    (f has_field_derivative f') (at a within s) = (f has_field_derivative f') (at a)"
  unfolding has_field_derivative_def by (rule has_derivative_within_open)

(* copied from Distributions.borel_integral_x_exp -- only the conclusion has changed! *)
(* this shows the integral and integrability should be combined *)
lemma borel_integrable_x_exp:
  "set_integrable lborel {0..} (\<lambda>x :: real. x * exp (- x))"
proof (rule integrable_monotone_convergence)
  let ?f = "\<lambda>i x. x * exp (- x) * indicator {0::real .. i} x"
  have "eventually (\<lambda>b::real. 0 \<le> b) at_top"
    by (rule eventually_ge_at_top)
  then have "eventually (\<lambda>b. 1 - (inverse (exp b) + b / exp b) = integral\<^sup>L lborel (?f b)) at_top"
  proof eventually_elim
   fix b :: real assume [simp]: "0 \<le> b"
    have "(\<integral>x. (exp (-x)) * indicator {0 .. b} x \<partial>lborel) - (integral\<^sup>L lborel (?f b)) = 
      (\<integral>x. (exp (-x) - x * exp (-x)) * indicator {0 .. b} x \<partial>lborel)"
      by (subst integral_diff[symmetric])
         (auto intro!: borel_integrable_atLeastAtMost integral_cong split: split_indicator)
    also have "\<dots> = (\<integral>x. indicator {0 .. b} x *\<^sub>R (exp (-x) - x * exp (-x)) \<partial>lborel)"
      by (simp add: mult_ac)
    also have "\<dots> = b * exp (-b) - 0 * exp (- 0)"
      by (rule integral_FTC_atLeastAtMost)
         (auto intro!: derivative_eq_intros continuous_intros
               simp: has_field_derivative_iff_has_vector_derivative[symmetric])
    also have "(\<integral>x. exp (-x) * indicator {0 .. b} x \<partial>lborel) =
      (\<integral>x. indicator {0 .. b} x *\<^sub>R (exp (-x)) \<partial>lborel)"
      by (simp add: mult_ac)
    also have "\<dots> = - exp (- b) - - exp (- 0)"
      apply (rule integral_FTC_atLeastAtMost)
      apply (auto intro!: derivative_eq_intros continuous_intros
                  simp: has_field_derivative_iff_has_vector_derivative[symmetric])
      done
    finally show "1 - (inverse (exp b) + b / exp b) = integral\<^sup>L lborel (?f b)"
      by (auto simp: field_simps exp_minus inverse_eq_divide)
  qed
  then have "((\<lambda>i. integral\<^sup>L lborel (?f i)) ---> 1 - (0 + 0)) at_top"
  proof (rule Lim_transform_eventually)
    show "((\<lambda>i. 1 - (inverse (exp i) + i / exp i)) ---> 1 - (0 + 0 :: real)) at_top"
      using tendsto_power_div_exp_0[of 1]
      by (intro tendsto_intros tendsto_inverse_0_at_top exp_at_top) simp
  qed
  then show "(\<lambda>i. integral\<^sup>L lborel (?f i)) ----> 1"
    by (intro filterlim_compose[OF _ filterlim_real_sequentially]) simp
  show "AE x in lborel. mono (\<lambda>n::nat. x * exp (- x) * indicator {0..real n} x)"
    by (auto simp: mono_def mult_le_0_iff zero_le_mult_iff split: split_indicator)
  show "\<And>i::nat. integrable lborel (\<lambda>x. x * exp (- x) * indicator {0..real i} x)"
    by (rule borel_integrable_atLeastAtMost) auto
  show "AE x in lborel. (\<lambda>i. x * exp (- x) * indicator {0..real i} x) ----> indicator {0..} x *\<^sub>R (x * exp (- x))"
    apply (intro AE_I2 Lim_eventually )
    apply (rule_tac c="natfloor x + 1" in eventually_sequentiallyI)
    apply (auto simp add: not_le dest!: ge_natfloor_plus_one_imp_gt[simplified] split: split_indicator)
    done
qed (auto intro!: borel_measurable_times borel_measurable_exp)

(* This is really needed  -- it is a canonical way to show that something
   is integrable wrt a product measure. *)


(* Move to Binary_Product_Measure *)
lemma (in pair_sigma_finite) Fubini_integrable:
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes f[measurable]: "f \<in> borel_measurable (M1 \<Otimes>\<^sub>M M2)"
    and integ1: "integrable M1 (\<lambda>x. \<integral> y. norm (f (x, y)) \<partial>M2)"
    and integ2: "AE x in M1. integrable M2 (\<lambda>y. f (x, y))"
  shows "integrable (M1 \<Otimes>\<^sub>M M2) f"
proof (rule integrableI_bounded)
  have "(\<integral>\<^sup>+ p. norm (f p) \<partial>(M1 \<Otimes>\<^sub>M M2)) = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. norm (f (x, y)) \<partial>M2) \<partial>M1)"
    by (simp add: M2.nn_integral_fst [symmetric])
  also have "\<dots> = (\<integral>\<^sup>+ x. \<bar>\<integral>y. norm (f (x, y)) \<partial>M2\<bar> \<partial>M1)"
    apply (intro nn_integral_cong_AE)
    using integ2
  proof eventually_elim
    fix x assume "integrable M2 (\<lambda>y. f (x, y))"
    then have f: "integrable M2 (\<lambda>y. norm (f (x, y)))"
      by simp
    then have "(\<integral>\<^sup>+y. ereal (norm (f (x, y))) \<partial>M2) = ereal (LINT y|M2. norm (f (x, y)))"
      by (rule nn_integral_eq_integral) simp
    also have "\<dots> = ereal \<bar>LINT y|M2. norm (f (x, y))\<bar>"
      using f by (auto intro!: abs_of_nonneg[symmetric] integral_nonneg_AE)
    finally show "(\<integral>\<^sup>+y. ereal (norm (f (x, y))) \<partial>M2) = ereal \<bar>LINT y|M2. norm (f (x, y))\<bar>" .
  qed
  also have "\<dots> < \<infinity>"
    using integ1 by (simp add: integrable_iff_bounded integral_nonneg_AE)
  finally show "(\<integral>\<^sup>+ p. norm (f p) \<partial>(M1 \<Otimes>\<^sub>M M2)) < \<infinity>" .
qed fact

(* more useful stuff *)

(* This is useful to apply the dominated convergence theorem. Are there better ways of
   formulating this, or other facts we should have?
*)

lemma tendsto_at_top_imp_sequentially:
  fixes f :: "real => real"
  assumes *: "\<And>Y. (\<forall>n. Y n > 0) \<Longrightarrow> filterlim Y at_top sequentially \<Longrightarrow> (\<lambda>n. f (Y n)) ----> a"
  shows "((f ---> a) at_top)"

  apply (subst filterlim_at_top_to_right)
  apply (subst tendsto_at_iff_sequentially)
  unfolding comp_def apply auto
  apply (rule *, auto)
  by (erule filterlim_inverse_at_top, auto)

lemma tendsto_at_top_imp_sequentially':
  fixes f :: "real => real"
  assumes *: "\<And>Y. (\<forall>n. Y n \<ge> B) \<Longrightarrow> filterlim Y at_top sequentially \<Longrightarrow> (\<lambda>n. f (Y n)) ----> a"
  shows "((f ---> a) at_top)"
proof (rule tendsto_at_top_imp_sequentially)
  fix Y :: "nat \<Rightarrow> real"
  assume 2: "filterlim Y at_top sequentially"
  hence 3: "eventually (\<lambda>n. Y n \<ge> B) sequentially" by (simp add: filterlim_at_top)
  hence "\<exists>N. \<forall>n \<ge> N. Y n \<ge> B" by (simp add: eventually_sequentially)
  then obtain N where N: "\<forall>n \<ge> N. Y n \<ge> B" ..
  let ?Y' = "\<lambda>n. Y (n + N)"
  from N have 4: "(\<forall>n. ?Y' n \<ge> B)" by auto
  from 2 have 5: "filterlim ?Y' at_top sequentially" apply (simp add: filterlim_at_top)
    by (auto intro!: sequentially_offset)
  have "(\<lambda>n. f (?Y' n)) ----> a" by (rule * [OF 4 5])
  thus "(\<lambda>n. f (Y n)) ----> a" by (rule LIMSEQ_offset)
qed

lemma interval_integral_to_infinity_eq: "(LINT x=ereal a..\<infinity> | M. f x) = (LINT x : {a<..} | M. f x)"
  unfolding interval_lebesgue_integral_def by auto

lemma interval_integrable_to_infinity_eq: "(interval_lebesgue_integrable M a \<infinity> f) = 
  (set_integrable M {a<..} f)"
  unfolding interval_lebesgue_integrable_def by auto

lemma at_right_le_at: "(at_right (x::'a::linorder_topology)) \<le> (at x)" 
  by (simp add: at_eq_sup_left_right)

(* can this be generalized? *)
lemma tendsto_divide_constant: "(f ---> (l :: real)) F \<Longrightarrow> ((\<lambda>x. f x / t) ---> (l / t)) F"
  apply (auto simp add: field_divide_inverse)
  by (auto intro: tendsto_intros)


(*
  Calculations of various integrals.

  TODO: clean these up.
*)

(* TODO: better name? *)
lemma integral_expneg_alpha_atLeast0:
  fixes u :: real
  assumes pos: "0 < u"
  shows
    "set_integrable lborel {0<..} (\<lambda>x. exp (-(x * u)))" 
    "LBINT x=0..\<infinity>. exp (-(x * u)) = 1/u"
proof -
  have 1: "0 < u \<Longrightarrow> (((\<lambda>x. - (exp (- (x * u)) / u)) \<circ> real) ---> - (1 / u)) (at_right (0::ereal))"
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
  by (rule tendsto_mult_left_zero, rule tendsto_ident_at)
  have 2: "0 < u \<Longrightarrow> (((\<lambda>x. - (exp (- (x * u)) / u)) \<circ> real) ---> 0) (at_left (\<infinity>::ereal))"
    apply (simp add: ereal_tendsto_simps)
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
  show "LBINT x=0..\<infinity>. exp (-(x * u)) = 1/u"
    apply (subst interval_integral_FTC_nonneg[of _ _ "\<lambda>x. -(1/u) * exp (-x * u)" _ "-(1/u)" 0])
    using pos apply (auto intro!: derivative_eq_intros)
    by (erule 1, erule 2)
  have "set_integrable lborel (einterval 0 \<infinity>) (\<lambda>x. exp (-x * u))"
    apply (subst interval_integral_FTC_nonneg[of _ _ "\<lambda>x. -(1/u) * exp (-x * u)" _ "-(1/u)" 0])
    using pos apply (auto intro!: derivative_eq_intros)
    by (erule 1, erule 2)
  thus "set_integrable lborel {0<..} (\<lambda>x. exp (-(x * u)))"
    by (auto simp add: zero_ereal_def)
qed

(*
lemma Collect_eq_Icc: "{r. t \<le> r \<and> r \<le> b} = {t .. b}"
  by auto
*)

(* From Billingsley section 18. *)
lemma ex_18_4_1:
  assumes "t \<ge> 0"
  shows "LBINT x=0..t. exp (-(u * x)) * sin x = (1/(1+u^2)) *
  (1 - exp (-(u * t)) * (u * sin t + cos t))"

  apply (subst zero_ereal_def)
  apply (subst interval_integral_FTC_finite 
      [where F = "(\<lambda>x. (1/(1+u^2)) * (1 - exp (-u * x) * (u * sin x + cos x)))"])
  apply (auto intro: continuous_at_imp_continuous_on
    simp: has_field_derivative_iff_has_vector_derivative[symmetric])
  apply (rule DERIV_subset, auto)
  apply (auto intro!: derivative_eq_intros)
by (simp_all add: power2_eq_square field_simps add_nonneg_eq_0_iff)

lemma ex_18_4_2_deriv:
  "DERIV (\<lambda>u. 1/x * (1 - exp (-u * x)) * \<bar>sin x\<bar>) u :> \<bar>exp (-u * x) * sin x\<bar>"
  apply (auto simp only: intro!: derivative_eq_intros)
  by (simp add: abs_mult)

(*** not needed **)
lemma ex_18_4_2_bdd_integral:
  assumes "s \<ge> 0"
  shows "LBINT u=0..s. \<bar>exp (-u * x) * sin x\<bar> =
  1/x * (1 - exp (-s * x)) * \<bar>sin x\<bar>"

  apply (subst zero_ereal_def)
  apply (subst interval_integral_FTC_finite 
      [where F = "\<lambda>u. 1/x * (1 - exp (-u * x)) * \<bar>sin x\<bar>"])
  apply (auto intro: continuous_at_imp_continuous_on) [1]
  unfolding has_field_derivative_iff_has_vector_derivative[symmetric]
  apply (rule DERIV_subset)
  apply (rule ex_18_4_2_deriv)
by auto

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
  apply (rule tendsto_compose[OF tendsto_exp])
  apply (subst isCont_def [symmetric], auto)
  apply (rule tendsto_minus_cancel, auto)
  apply (rule tendsto_mult_left_zero, rule tendsto_ident_at)
  (* this is the second *)
  apply (subst divide_real_def)+
  apply (subgoal_tac "abs (sin x) * inverse x = 1 * abs (sin x) * inverse x")
  apply (erule ssubst)
  apply (rule tendsto_mult)+
  apply auto
  apply (rule tendsto_eq_intros)
  apply (rule tendsto_const)
  apply (rule filterlim_compose[OF exp_at_bot])
  unfolding filterlim_uminus_at_bot
  apply simp
  apply (subst mult_commute)
  apply (rule filterlim_tendsto_pos_mult_at_top[OF tendsto_const pos filterlim_ident])
  apply simp
  done

lemma Billingsley_ex_17_5: 
  shows "set_integrable lborel (einterval (-\<infinity>) \<infinity>) (\<lambda>x. inverse (1 + x^2))"
    "LBINT x=-\<infinity>..\<infinity>. inverse (1 + x^2) = pi"
proof -
  have 1: "\<And>x. - (pi / 2) < x \<Longrightarrow> x * 2 < pi \<Longrightarrow> (tan has_real_derivative 1 + (tan x)\<^sup>2) (at x)"
    apply (subst tan_sec)
    using pi_half cos_is_zero
    apply (metis cos_gt_zero_pi less_divide_eq_numeral1(1) less_numeral_extra(3))
    using DERIV_tan
    by (metis cos_gt_zero_pi less_divide_eq_numeral1(1) power2_less_0 power_inverse 
      power_zero_numeral)
  have 2: "\<And>x. - (pi / 2) < x \<Longrightarrow> x * 2 < pi \<Longrightarrow> isCont (\<lambda>x. 1 + (tan x)\<^sup>2) x"
    apply (rule isCont_add, force)
    apply (subst power2_eq_square)
    apply (subst isCont_mult)
    apply (rule isCont_tan)
    (* Following line duplicated from above. *)
    using pi_half cos_is_zero
    apply (metis cos_gt_zero_pi less_divide_eq_numeral1(1) less_numeral_extra(3))
    by simp
  show "LBINT x=-\<infinity>..\<infinity>. inverse (1 + x^2) = pi"
    apply (subst interval_integral_substitution_nonneg[of "-pi/2" "pi/2" tan "\<lambda>x. 1 + (tan x)^2"])
    apply (auto intro: derivative_eq_intros simp add: ereal_tendsto_simps filterlim_tan_at_left add_nonneg_eq_0_iff)
    apply (erule (1) 1)
    apply (erule (1) 2)
    apply (subst minus_divide_left)+
    by (rule filterlim_tan_at_right)
  show "set_integrable lborel (einterval (-\<infinity>) \<infinity>) (\<lambda>x. inverse (1 + x^2))"
    apply (subst interval_integral_substitution_nonneg[of "-pi/2" "pi/2" tan "\<lambda>x. 1 + (tan x)^2"])
    apply (auto intro: derivative_eq_intros simp add: ereal_tendsto_simps filterlim_tan_at_left add_nonneg_eq_0_iff)
    apply (erule (1) 1)
    apply (erule (1) 2)
    apply (subst minus_divide_left)+
    by (rule filterlim_tan_at_right)
qed

(* a slight modification of the preceding one *)
(* TODO: refactor *)
lemma Billingsley_ex_17_5': 
  shows "set_integrable lborel (einterval 0 \<infinity>) (\<lambda>x. inverse (1 + x^2))"
    "LBINT x=0..\<infinity>. inverse (1 + x^2) = pi / 2"
proof -
  have "(tan ---> tan 0) (at 0)"
    by (rule tendsto_tan, auto intro: tendsto_ident_at)
  hence [intro]: "(tan ---> 0) (at_right 0)"
    by (rule filterlim_mono, auto simp add: at_eq_sup_left_right)
  have 1: "\<And>x. 0 < x \<Longrightarrow> x * 2 < pi \<Longrightarrow> (tan has_real_derivative 1 + (tan x)\<^sup>2) (at x)"
    apply (subst tan_sec)
    apply (subgoal_tac "cos x > 0", force)
    apply (rule cos_gt_zero_pi, auto)
    apply (subst nonzero_power_inverse [symmetric])
    apply (subgoal_tac "cos x > 0", force)
    apply (rule cos_gt_zero_pi, auto)
    apply (rule DERIV_tan)
    apply (subgoal_tac "cos x > 0", force)
    by (rule cos_gt_zero_pi, auto)
  have 2: "\<And>x. 0 < x \<Longrightarrow> x * 2 < pi \<Longrightarrow> isCont (\<lambda>x. 1 + (tan x)\<^sup>2) x"
    apply (rule isCont_add, force)
    apply (subst power2_eq_square)
    apply (rule isCont_mult)
    apply (rule isCont_tan)
    apply (subgoal_tac "cos x > 0", force)
    apply (rule cos_gt_zero_pi, auto)
    apply (rule isCont_tan)
    apply (subgoal_tac "cos x > 0", force)
    by (rule cos_gt_zero_pi, auto)
  show "LBINT x=0..\<infinity>. inverse (1 + x^2) = pi / 2"
    apply (subst interval_integral_substitution_nonneg[of "0" "pi/2" tan "\<lambda>x. 1 + (tan x)^2"])
    apply (auto intro: derivative_eq_intros simp add: ereal_tendsto_simps filterlim_tan_at_left
      zero_ereal_def add_nonneg_eq_0_iff)
    apply (erule (1) 1)
    by (erule (1) 2)
  show "set_integrable lborel (einterval 0 \<infinity>) (\<lambda>x. inverse (1 + x^2))"
    apply (subst interval_integral_substitution_nonneg[of "0" "pi/2" tan "\<lambda>x. 1 + (tan x)^2"])
    apply (auto intro: derivative_eq_intros simp add: ereal_tendsto_simps filterlim_tan_at_left
      zero_ereal_def add_nonneg_eq_0_iff)
    apply (erule (1) 1)
    by (erule (1) 2)
qed

(*
  The sinc function, and the sine integral (Si)
*)

abbreviation sinc :: "real \<Rightarrow> real" where
  "sinc \<equiv> (\<lambda>x. if x = 0 then 1 else sin x / x)"

lemma sinc_at_0: "((\<lambda>x. sin x / x) ---> 1) (at 0)"
using DERIV_sin [of 0] by (auto simp add: has_field_derivative_def field_has_derivative_at)

lemma isCont_sinc: "isCont sinc x"
  apply (case_tac "x = 0", auto)
  apply (simp add: isCont_def)
  apply (subst LIM_equal [where g = "\<lambda>x. sin x / x"], auto intro: sinc_at_0)
  apply (rule continuous_transform_at [where d = "abs x" and f = "\<lambda>x. sin x / x"])
  by (auto simp add: dist_real_def)

lemma continuous_on_sinc[continuous_intros]:
  "continuous_on S f \<Longrightarrow> continuous_on S (\<lambda>x. sinc (f x))"
  using continuous_on_compose[of S f sinc, OF _ continuous_at_imp_continuous_on]
  by (auto simp: isCont_sinc)

lemma borel_measurable_sin[measurable]: "sin \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_on1 continuous_intros)

lemma borel_measurable_cos[measurable]: "cos \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_on1 continuous_intros)

lemma borel_measurable_sinc[measurable]: "sinc \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_on1 continuous_at_imp_continuous_on ballI isCont_sinc)

lemma sinc_AE: "AE x in lborel. sin x / x = sinc x"
  by (rule AE_I [where N = "{0}"], auto)

definition Si :: "real \<Rightarrow> real" where "Si t \<equiv> LBINT x=0..t. sin x / x"

lemma Si_alt_def : "Si t = LBINT x=0..t. sinc x"
  apply (case_tac "0 \<le> t")
  unfolding Si_def apply (rule interval_lebesgue_integral_cong_AE, auto)
  apply (rule AE_I' [where N = "{0}"], auto)
  apply (subst (1 2) interval_integral_endpoints_reverse, simp)
  apply (rule interval_lebesgue_integral_cong_AE, auto)
by (rule AE_I' [where N = "{0}"], auto)

lemma sinc_neg [simp]: "sinc (- x) = sinc x" by auto

lemma Si_neg: 
  fixes T :: real
  assumes "T \<ge> 0"
  shows "Si (- T) = - Si T"
proof -
  have "LBINT x=ereal 0..T. -1 *\<^sub>R sinc (- x) = LBINT y= ereal (- 0)..ereal (- T). sinc y"
    apply (rule interval_integral_substitution_finite [OF assms])
    by (auto intro: derivative_intros continuous_at_imp_continuous_on isCont_sinc)
  also have "(LBINT x=ereal 0..T. -1 *\<^sub>R sinc (- x)) = -(LBINT x=ereal 0..T. sinc x)"
    by (subst sinc_neg) (simp_all add: interval_lebesgue_integral_uminus)
  finally have *: "-(LBINT x=ereal 0..T. sinc x) = LBINT y= ereal 0..ereal (- T). sinc y"
    by simp
  show ?thesis
    using assms unfolding Si_alt_def
     apply (subst zero_ereal_def)+
     by (auto simp add: * [symmetric])
qed

(* TODO: need a better version of FTC2 *)

lemma iSi_isCont: "isCont Si x"
proof -
  have "Si = (\<lambda>t. LBINT x=ereal 0..ereal t. sinc x)"
    apply (rule ext, simp add: Si_def zero_ereal_def)
    apply (rule interval_integral_cong_AE)
    by (auto intro!: AE_I' [where N = "{0}"])
  thus ?thesis
    apply (elim ssubst)
    apply (rule DERIV_isCont)
    apply (subst has_field_derivative_within_open [symmetric, 
      where s = "{(min (x - 1) (- 1))<..<(max 1 (x+1))}"], auto)
    apply (rule DERIV_subset [where s = "{(min (x - 2) (- 2))..(max 2 (x+2))}"])
    unfolding has_field_derivative_iff_has_vector_derivative
    apply (rule interval_integral_FTC2)
    by (auto intro!: continuous_on_sinc continuous_on_id)
qed

lemma borel_measurable_iSi[measurable]: "Si \<in> borel_measurable borel"
  by (auto intro: iSi_isCont continuous_at_imp_continuous_on borel_measurable_continuous_on1)

(** Add to main Lebesgue integration library; does not require integrability as hypothesis, which in
my experience greatly increases usability. **)
(** JDA: this is probably not needed if we keep track of integrability hypotheses
lemma nn_integral_eq_integral_measurable:
  assumes f: "f \<in> borel_measurable M" and I: "integral\<^sup>L M f \<noteq> 0"
  assumes nonneg: "AE x in M. 0 \<le> f x" 
  shows "(\<integral>\<^sup>+ x. ereal (f x) \<partial>M) = ereal (integral\<^sup>L M f)"
proof -
  have "(\<integral>\<^sup>+ x. ereal (- f x) \<partial>M) = (\<integral>\<^sup>+ x. max 0 (ereal (- f x)) \<partial>M)"
    using nn_integral_max_0 by metis
  also have "... = (\<integral>\<^sup>+ x. 0 \<partial>M)"
    using nonneg by (intro nn_integral_cong_AE) (auto split: split_max)
  also have "... = 0" by (subst zero_ereal_def) (subst nn_integral_eq_integral, auto)
  finally have "real (\<integral>\<^sup>+ x. ereal (f x) \<partial>M) = integral\<^sup>L M f"
    using real_of_ereal_0 unfolding lebesgue_integral_def by auto
  thus ?thesis
    apply (subst (asm) ereal.inject[symmetric])
    apply (subst (asm) ereal_real)
    using I ereal_eq_0 by metis
qed
*)


(*
lemma  interval_Fubini_integral:
  fixes f :: "real \<times> real \<Rightarrow> real"
  fixes a b c d :: ereal
  assumes ab: "a < b" and dc: "c < d" (* Interesting: cd is a reserved word. *)
    and M1: "sigma_finite_measure M1" and M2: "sigma_finite_measure M2"
    and f: "integrable (M1 \<Otimes>\<^sub>M M2) f" (* add indicators *)
  shows "LINT y=a..b|M2. (LINT x=c..d|M1. f (x, y)) = LINT x=c..d|M1. (LINT y=a..b|M2. f (x, y))"
*)

lemma Si_at_top_lemma:
  shows "\<And>t. t \<ge> 0 \<Longrightarrow> interval_lebesgue_integrable lborel 0 \<infinity>
     (\<lambda>x. exp (- (x * t)) * (x * sin t + cos t) / (1 + x\<^sup>2))"
  and
    "((\<lambda>t. (LBINT x=0..\<infinity>. exp (-(x * t)) * (x * sin t + cos t) / (1 + x^2))) ---> 0) at_top"
proof -
  have int1: "set_integrable lborel {0<..} (\<lambda>x. exp (- x) * \<bar>x\<bar> :: real)"
    apply (subst integrable_cong_AE)
    prefer 4
    apply (rule borel_integrable_x_exp)
    apply auto
    apply (rule AE_I [where N = "{0}"])
    by (auto split: split_indicator)
  have int2: "set_integrable lborel {0<..} (\<lambda>x. exp (- x) :: real)"
    using integral_expneg_alpha_atLeast0 [of 1] by auto
  {
    fix t x :: real
    assume "t > 0"
    hence "indicator {0<..} x * (exp (- x) * \<bar>x * sin t / t + cos t\<bar>) /
                    ((1 + (x / t)\<^sup>2) * t)
                    \<le> indicator {0<..} x * (exp (- x) * (\<bar>x\<bar> / t + 1)) / t"
      apply (simp add: field_simps split: split_indicator)
      apply (subst pos_divide_le_eq)
      apply (rule add_pos_nonneg)
      apply (auto simp add: field_simps)
      apply (rule order_trans)
      apply (rule mult_left_mono)+
      apply (rule order_trans)
      apply (rule abs_triangle_ineq)
      apply (rule add_mono, subst abs_mult)
      apply (rule mult_left_mono, rule abs_cos_le_one)
      prefer 2
      apply (subst abs_mult, rule mult_left_mono, rule abs_sin_le_one)
      by (auto simp add: field_simps)
  } note aux1 = this
  {
    fix t :: real
    assume "t > 0"
    have "set_integrable lborel {0<..} (\<lambda>x. exp (- x) * (\<bar>x\<bar> / t + 1) / t)"
      apply (rule set_integrable_divide)
      apply (subst distrib_left)
      apply (rule set_integral_add)
      apply (subst times_divide_eq)
      apply (rule set_integrable_divide)
      apply (rule int1)
      apply (rule set_integrable_mult_left)
      by (rule int2)
  } note aux2 = this
  { 
    fix t :: real
    assume "t \<ge> 0"
    hence "integrable lborel (\<lambda>x. indicator {0<..} x * (exp (- x) * \<bar>x * sin t / t + cos t\<bar>) /
          ((1 + (x / t)\<^sup>2) * t))"
      apply (case_tac "t = 0")
      apply simp
      apply (rule integrable_bound)
      apply (rule aux2[of t])
      apply simp
      apply measurable
      apply simp
      apply (rule AE_I2[OF aux1])
      apply simp
      done
  } note aux3 = this
  {
    fix t :: real
    assume [arith]: "t \<ge> 0"
    have 1: "\<And>x. 0 < ereal x \<Longrightarrow> ereal x < \<infinity> \<Longrightarrow> ((\<lambda>x. x / t) has_real_derivative (1 /t)) (at x)"
      apply (case_tac "t = 0", auto)
      by (auto intro!: derivative_eq_intros tendsto_divide_constant)
    have "interval_lebesgue_integrable lborel 0 \<infinity>
       (\<lambda>x. exp (- (x * t)) * abs (x * sin t + cos t) / (1 + x\<^sup>2))"
      unfolding interval_lebesgue_integrable_def
      apply (subst if_P, force)
      apply (case_tac "t = 0")
      using Billingsley_ex_17_5' (1) apply (simp add: field_simps)
      apply (subst zero_ereal_def)
      apply (rule interval_integral_substitution_nonneg [of "ereal 0" \<infinity>, OF _ 1])
      apply (auto simp add: ereal_tendsto_simps add_nonneg_eq_0_iff)
      apply (rule tendsto_mono [OF at_right_le_at])
      apply (auto intro!: tendsto_eq_intros) []
      apply (subst field_divide_inverse, subst mult_commute)
      apply (rule filterlim_tendsto_pos_mult_at_top)
      apply (rule tendsto_const, auto intro!: filterlim_ident)
      by (rule aux3, simp)
  } note aux4 = this
  {
    fix t :: real
    assume "t \<ge> 0"
    hence *: "(\<lambda>x. \<bar>exp (- (x * t)) * (x * sin t + cos t) / (1 + x\<^sup>2)\<bar>) = 
           (\<lambda>x. exp (- (x * t)) * abs (x * sin t + cos t) / (1 + x\<^sup>2))"
      by (intro ext, auto simp add: abs_mult)
    show "interval_lebesgue_integrable lborel 0 \<infinity>
       (\<lambda>x. exp (- (x * t)) * (x * sin t + cos t) / (1 + x\<^sup>2))"
      apply (subst interval_integrable_abs_iff [symmetric])
      apply measurable
      by (subst *, rule aux4 [OF `t \<ge> 0`])
  } note aux5 = this
  {
    fix t x :: real
    have "\<bar>exp (- (x * t)) * (x * sin t + cos t) / (1 + x\<^sup>2) * indicator {0<..} x\<bar> = 
       exp (- (x * t)) * abs (x * sin t + cos t) / (1 + x\<^sup>2) * indicator {0<..} x"
      by (auto simp add: abs_mult)
    also have "\<dots> \<le> exp (- (x * t)) * (x + 1) / 1 * indicator {0<..} x"
      apply (case_tac "x > 0")
      prefer 2 apply force
      apply (rule mult_right_mono)
      apply (rule frac_le, force)
      apply (rule mult_left_mono)
      apply (rule order_trans [OF abs_triangle_ineq])
      apply (rule add_mono)
      by (auto simp add: abs_mult)
    also have "\<dots> = (exp (- (x * t)) * x + exp (- (x* t))) * indicator {0<..} x" 
      by (simp add: field_simps)
    finally have "\<bar>exp (- (x * t)) * (x * sin t + cos t) / (1 + x\<^sup>2) * indicator {0<..} x\<bar> \<le>
       (exp (- (x * t)) * x + exp (- (x * t))) * indicator {0<..} x" .
  } note aux6 = this
  {
    fix t :: real
    assume "t \<ge> 1"
    have "AE x in lborel. norm (indicator {0<..} x *\<^sub>R (exp (- (x * t)) * (x * sin t + cos t) / (1 + x\<^sup>2)))
         \<le> indicator {0<..} x *\<^sub>R (exp (- x) * x + exp (- x))"
       unfolding real_norm_def real_scaleR_def
       apply (subst (1 5) mult_commute)
       apply (rule AE_I2)
       apply (case_tac "x > 0")
       apply (rule order_trans [OF aux6])
       apply (rule mult_right_mono)
       apply (rule add_mono)
       apply (rule mult_right_mono)
       using `t \<ge> 1` by (auto simp add: exp_le_cancel_iff)
  } note aux7 = this
  { 
     fix Y :: "nat \<Rightarrow> real"
     assume Ypos: "\<forall>n. 1 \<le> Y n" and
       Y: "filterlim Y at_top sequentially"
     {
       fix x :: real 
       assume "x > 0"
       have "(\<lambda>n. exp (- (x * Y n))) ----> 0"
         apply (rule filterlim_compose [OF exp_at_bot])
         apply (subst filterlim_uminus_at_top [symmetric])
         apply (rule filterlim_tendsto_pos_mult_at_top [OF _ `x > 0` Y])
         by (rule tendsto_const)
     } note aux8a = this
     {
       fix x :: real 
       assume "x > 0"
       hence "(\<lambda>n. exp (- (x * Y n)) * x) = (\<lambda>n. inverse (Y n) * ((x * Y n)^1 / exp (x * Y n)))"
         apply (intro ext)
         apply (auto simp add: field_simps exp_minus)
         using Ypos by (metis not_one_le_zero)  (* other automated tools should get this! *)
       hence "(\<lambda>n. exp (- (x * Y n)) * x) ----> 0"
         apply (elim ssubst)
         apply (rule tendsto_mult_zero)
         apply (rule tendsto_inverse_0_at_top [OF Y])
         apply (rule filterlim_compose [OF tendsto_power_div_exp_0])
         apply (rule filterlim_tendsto_pos_mult_at_top [OF _ `x > 0` Y])
         by (rule tendsto_const)
     } note aux8b = this
     have "AE x in lborel. (\<lambda>n. exp (- (x * Y n)) * (x * sin (Y n) + cos (Y n)) / (1 + x\<^sup>2) *
         indicator {0<..} x) ----> 0"
       apply (rule AE_I2)
       apply (rule Lim_null_comparison)
       apply (rule always_eventually, rule allI, subst real_norm_def)
       apply (rule aux6)
       apply (auto split: split_indicator)
       by (rule tendsto_add_zero [OF aux8b aux8a])
     hence "AE x in lborel. (\<lambda>n. indicator {0<..} x *\<^sub>R (exp (- (x * Y n)) * (x * sin (Y n) + cos (Y n)) / (1 + x\<^sup>2))) ----> indicator {0<..} x *\<^sub>R 0"
       by (simp add: ac_simps)
  } note aux8 = this
  have aux9: "set_integrable lborel {0<..} (\<lambda>x. exp (- x) * x + exp (- x) :: real)"
    apply (rule set_integral_add)
    apply (subst mult_commute)
    apply (subst integrable_cong_AE)
    prefer 4 apply (rule borel_integrable_x_exp)
    apply auto [2]
    apply (rule AE_I' [where N = "{0}"])
    apply auto [2]
    apply (case_tac "x > 0", force, force)
    using integral_expneg_alpha_atLeast0 [of 1] by simp
  show "((\<lambda>t. (LBINT x=0..\<infinity>. exp (-(x * t)) * (x * sin t + cos t) / (1 + x^2))) ---> 0) at_top"
    apply (rule tendsto_at_top_imp_sequentially' [of 1])
    apply (subst zero_ereal_def)
    apply (subst interval_integral_to_infinity_eq)
    apply (subgoal_tac "0 = (LBINT x:{0<..}. 0)")
    apply (erule ssubst) back
    apply (rule integral_dominated_convergence[OF _ _ aux9 aux8 aux7])
    apply auto
    done
qed

lemma Si_at_top:
  shows "(Si ---> pi / 2) at_top"
proof -
{
  fix t :: real
  assume "t \<ge> 0"

  have "(\<lambda>x. LBINT y. \<bar>sin x\<bar> * exp (- (y * x)) * indicator {0<..} y * indicator {0<..<t} x) =
        (\<lambda>x. \<bar>sin x\<bar> * indicator {0<..<t} x * (LBINT y.  exp (- (y * x)) * indicator {0<..} y))"
    apply (rule ext)
    apply (case_tac "x > 0", auto)
    by (simp add: field_simps)
  also have "\<dots> = (\<lambda>x. \<bar>sin x\<bar> * indicator {0<..<t} x * (1 / x))"
    apply (rule ext)
    apply (case_tac "x > 0")
    apply (subst integral_expneg_alpha_atLeast0 (2) [symmetric])
    apply (auto simp add: interval_lebesgue_integral_def zero_ereal_def mult_ac)
    done
  also have "\<dots> = (\<lambda>x. \<bar>sin x\<bar> / x * indicator {0<..<t} x)" by (simp add: field_simps)
  finally have 
    2: "(\<lambda>x. LBINT y. \<bar>indicator ({0<..} \<times> {0<..<t}) (y, x) *\<^sub>R (sin x * exp (- (y * x)))\<bar>) =
        (\<lambda>x. indicator {0<..<t} x *\<^sub>R (\<bar>sin x\<bar> / x))" 
    by (simp add: indicator_times mult_ac abs_mult)

  { have *: "AE x in lborel. indicator {0<..<t} x *\<^sub>R (\<bar>sin x\<bar> / x) = indicator {0..t} x *\<^sub>R abs (sinc x)"
      by (rule AE_I [where N = "{0, t}"])
         (auto split: split_indicator simp add: emeasure_lborel_countable)
    have "set_integrable lborel {0<..<t} (\<lambda>x. \<bar>sin x\<bar> / x)"
      by (subst integrable_cong_AE [OF _ _ *])
         (auto intro!: borel_integrable_compact continuous_intros simp del: real_scaleR_def)
  } note 3 = this

  have "Si t = LBINT x=0..t. sin x * (LBINT u=0..\<infinity>. exp (-(u * x)))" unfolding Si_def
    using `0 \<le> t`
    by (intro interval_integral_discrete_difference[where X="{0}"])
       (auto simp: integral_expneg_alpha_atLeast0)
  also have "\<dots> = LBINT x. (LBINT u=0..\<infinity>. indicator {0 <..< t} x *\<^sub>R sin x * exp (-(u * x)))"
    using `0 \<le> t` by (simp add: interval_integral_Ioo zero_ereal_def mult_ac)
  also have "\<dots> = LBINT x. (LBINT u. indicator ({0<..} \<times> {0 <..< t}) (u, x) *\<^sub>R (sin x * exp (-(u * x))))"
    by (subst interval_integral_Ioi) (simp_all add: indicator_times mult_ac)
  also have "\<dots> = LBINT u. (LBINT x. indicator ({0<..} \<times> {0 <..< t}) (u, x) *\<^sub>R (sin x * exp (-(u * x))))"
  proof (intro lborel_pair.Fubini_integral[symmetric] lborel_pair.Fubini_integrable)
    show "(\<lambda>(x, y). indicator ({0<..} \<times> {0<..<t}) (y, x) *\<^sub>R (sin x * exp (- (y * x))))
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)" (is "?f \<in> borel_measurable _")
      by measurable
    show "integrable lborel (\<lambda>x. LBINT y. norm (?f (x, y)))"
      by (simp add: abs_mult 2 3 del: real_scaleR_def)

    { fix x :: real assume "0 < x"
      have "set_integrable lborel {0<..} (\<lambda>y. sin x * exp (- (y * x)))"
        by (intro set_integrable_mult_right, rule integral_expneg_alpha_atLeast0[OF `0 < x`])
    } then show "AE x in lborel. integrable lborel (\<lambda>y. ?f (x, y))"
      by (intro AE_I2) (auto simp: indicator_times split: split_indicator)
  qed
  also have "\<dots> = (LBINT u. (LBINT x. sin x * exp (-u * x) * 
      indicator {0<..} u * indicator {0<..<t} x))" by (simp add: indicator_times mult_ac)
  also have "... = LBINT u=0..\<infinity>. (LBINT x=0..t. sin x * exp (-(u * x)))"
    using `t >= 0` apply (auto simp add: interval_lebesgue_integral_def zero_ereal_def)
    by (rule integral_cong, auto simp: mult_ac split: split_indicator)
  also have "\<dots> = LBINT u=0..\<infinity>. 1 / (1 + u\<^sup>2) - 1 / (1 + u\<^sup>2) * (exp (- (u * t)) * (u * sin t + cos t))"
    apply (subst mult_commute)
    apply (subst ex_18_4_1 [OF `t >= 0`])
    apply (rule interval_integral_cong)
    by (subst right_diff_distrib, simp)
  also have "... = (LBINT u=0..\<infinity>. 1 / (1 + u^2)) - (LBINT u=0..\<infinity>. 1 / (1 + u^2) *
      (exp (- (u * t)) * (u * sin t + cos t)))"
    apply (rule interval_lebesgue_integral_diff)
    using  Billingsley_ex_17_5' (1) apply (simp add: zero_ereal_def 
      interval_lebesgue_integrable_def inverse_eq_divide)
      apply simp
      by (rule Si_at_top_lemma (1) [OF `0 \<le> t`])
  finally have "Si t = pi / 2 - (LBINT u=0..\<infinity>. 1 / (1 + u^2) * exp (-(u * t)) *
    (u * sin t + cos t))"
    apply (subst (asm) inverse_eq_divide [symmetric])
    apply (subst (asm) Billingsley_ex_17_5')
    by simp
} note 5 = this
  have 6: "eventually (\<lambda>t. pi / 2 - (LBINT u=0..\<infinity>. 1 / (1 + u^2) * exp (-(u * t)) *
    (u * sin t + cos t)) = Si t) at_top"
    apply (rule eventually_mp [OF _ eventually_ge_at_top [of 0]])
    apply (rule always_eventually, clarify, rule sym)
    by (erule 5)
  show ?thesis
    by (rule Lim_transform_eventually [OF 6])
       (auto intro!: tendsto_eq_intros Si_at_top_lemma)
qed

lemma iSi_integrable: "interval_lebesgue_integrable lborel (ereal 0)
     (ereal T) (\<lambda>t. sin (t * \<theta>) / t)"
proof -
  have *: "interval_lebesgue_integrable lborel (ereal 0) (ereal T) (\<lambda>t. \<theta> * sinc (t * \<theta>))"
    apply (rule interval_lebesgue_integrable_mult_right)
    apply (rule interval_integrable_isCont)
    by (rule continuous_within_compose3 [OF isCont_sinc], auto)
  (* this shouldn't be so hard! *)
  show ?thesis
    apply (rule interval_lebesgue_integrable_cong_AE[THEN iffD1, OF _ _ _ *])
    apply auto
    by (rule AE_I' [where N = "{0}"], auto)
qed

lemma Billingsley_26_15:
  fixes \<theta> :: real
  assumes "T \<ge> 0"
  shows "LBINT t=ereal 0..T. sin (t * \<theta>) / t = sgn \<theta> * Si (T * \<bar>\<theta>\<bar>)"
proof -
  { assume "0 < \<theta>"
    have "(LBINT t=ereal 0..T. sin (t * \<theta>) / t) = (LBINT t=ereal 0..T. \<theta> *\<^sub>R sinc (t * \<theta>))"
      by (rule interval_integral_discrete_difference[of "{0}"]) auto
    also have "\<dots> = (LBINT t=ereal (0 * \<theta>)..T * \<theta>. sinc t)"
      apply (rule interval_integral_substitution_finite [OF assms])
      apply (subst mult_commute, rule DERIV_subset)
      by (auto intro!: derivative_intros continuous_at_imp_continuous_on isCont_sinc)
    also have "\<dots> = (LBINT t=ereal (0 * \<theta>)..T * \<theta>. sin t / t)"
      by (rule interval_integral_discrete_difference[of "{0}"]) auto
    finally have "(LBINT t=ereal 0..T. sin (t * \<theta>) / t) = (LBINT t=ereal 0..T * \<theta>. sin t / t)"
      by simp
    hence "LBINT x. indicator {0<..<T} x * sin (x * \<theta>) / x =
        LBINT x. indicator {0<..<T * \<theta>} x * sin x / x"
      using assms `0 < \<theta>` unfolding interval_lebesgue_integral_def einterval_eq zero_ereal_def 
        by (auto simp: mult_ac)
  } note aux1 = this
  { assume "0 > \<theta>"
    have [simp]: "integrable lborel (\<lambda>x. sin (x * \<theta>) * indicator {0<..<T} x / x)"
      using iSi_integrable [of T \<theta>] assms 
      by (simp add: interval_lebesgue_integrable_def mult_ac)
    have "(LBINT t=ereal 0..T. sin (t * -\<theta>) / t) = (LBINT t=ereal 0..T. -\<theta> *\<^sub>R sinc (t * -\<theta>))"
      by (rule interval_integral_discrete_difference[of "{0}"]) auto
    also have "\<dots> = (LBINT t=ereal (0 * -\<theta>)..T * -\<theta>. sinc t)"
      apply (rule interval_integral_substitution_finite [OF assms])
      apply (subst mult_commute, rule DERIV_subset)
      by (auto intro!: derivative_intros continuous_at_imp_continuous_on isCont_sinc)
    also have "\<dots> = (LBINT t=ereal (0 * -\<theta>)..T * -\<theta>. sin t / t)"
      by (rule interval_integral_discrete_difference[of "{0}"]) auto
    finally have "(LBINT t=ereal 0..T. sin (t * -\<theta>) / t) = (LBINT t=ereal 0..T * -\<theta>. sin t / t)"
      by simp
    hence "LBINT x. indicator {0<..<T} x * sin (x * \<theta>) / x =
       - (LBINT x. indicator {0<..<- (T * \<theta>)} x * sin x / x)"
      using assms `0 > \<theta>` unfolding interval_lebesgue_integral_def einterval_eq zero_ereal_def
        by (auto simp add: field_simps mult_le_0_iff split: split_if_asm)
  } note aux2 = this
  show ?thesis
    using assms unfolding Si_def interval_lebesgue_integral_def sgn_real_def 
      einterval_eq zero_ereal_def
    apply auto
    apply (erule aux1)
    apply (rule aux2)
    apply auto
    done
qed

lemma iSi_bounded: "\<exists>B. \<forall>T. abs (Si T) \<le> B"
proof -
  from Si_at_top have "eventually (\<lambda>T. dist (Si T) (pi / 2) < 1) at_top"
    by (elim tendstoD, simp)
  hence "\<exists>T. \<forall>t \<ge> T. dist (Si t) (pi / 2) < 1" 
    by (simp add: eventually_at_top_linorder)
  then obtain T where T [rule_format]: "\<forall>t \<ge> T. dist (Si t) (pi / 2) < 1" ..
  let ?T' = "max T 0"
  {
    fix t
    assume "t \<ge> ?T'"
    hence *: "t \<ge> T" by auto
    from T [OF *]
    have **: "abs (Si t - pi / 2) < 1" by (simp add: dist_real_def)
    have "abs (Si t) = abs ((Si t - pi / 2) + pi / 2)" by simp
    also have "\<dots> \<le> abs (Si t - pi / 2) + abs (pi / 2)" by (rule abs_triangle_ineq)
    also have "\<dots> \<le> 1 + abs (pi / 2)"
      by (rule add_right_mono, rule less_imp_le, rule **)
    finally have "abs (Si t) \<le> 1 + abs (pi / 2)" .
  } note aux1 = this
  {
    fix t 
    assume *: "t \<le> -?T'"
    have "abs (Si t) = abs (Si (- (-t)))" by simp
    also have "\<dots> = abs (Si (- t))"
      apply (subst Si_neg)
      using * by auto
    also have "\<dots> \<le> 1 + abs (pi / 2)"
      apply (rule aux1)
      using * by auto
    finally have "abs (Si t) \<le> 1 + abs (pi / 2)" .
  } note aux2 = this
  have "\<exists>M. \<forall>t. -?T' \<le> t \<and> t \<le> ?T' \<longrightarrow> abs (Si t) \<le> M"
    apply (rule isCont_bounded)
    by (auto intro!: iSi_isCont continuous_intros)
  then obtain M where M [rule_format]: "\<forall>t. -?T' \<le> t \<and> t \<le> ?T' \<longrightarrow> abs (Si t) \<le> M" ..
  let ?B = "max M (1 + abs (pi / 2))"
  have "\<forall>t. abs (Si t) \<le> ?B"
  proof
    fix t
    show "abs (Si t) \<le> ?B"
      apply (case_tac "t \<ge> ?T'")
      apply (rule order_trans)
      apply (erule aux1, force)
      apply (case_tac "t \<le> -?T'")
      apply (rule order_trans)
      apply (erule aux2, force)
      apply (rule order_trans)
      by (rule M, auto)
  qed
  thus ?thesis ..
qed    

end