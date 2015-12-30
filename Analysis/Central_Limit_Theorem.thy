(*
Theory: Central_Limit_Theorem.thy
Authors: Jeremy Avigad, Luke Serafin
*)

theory Central_Limit_Theorem

imports Levy

begin

(* for sanity, this is a special case of equation_26p5b *)
lemma (in real_distribution) aux:
  fixes t
  assumes
    integrable_1: "integrable M (\<lambda>x. x)" and
    integral_1: "expectation (\<lambda>x. x) = 0" and
    integrable_2: "integrable M (\<lambda>x. x^2)" and
    integral_2: "variance (\<lambda>x. x) = \<sigma>2"
  shows 
    "cmod (char M t - (1 - t^2 * \<sigma>2 / 2)) \<le>  (t^2 / 6) * 
        expectation (\<lambda>x. min (6 * x^2) (abs t * (abs x)^3) )"
proof -
  note real_distribution.char_approx2 [of M 2 t, simplified]
  have [simp]: "prob UNIV = 1" by (metis prob_space space_eq_univ)
  from integral_2 have [simp]: "expectation (\<lambda>x. x * x) = \<sigma>2" 
    by (simp add: integral_1 numeral_eq_Suc)
  {
    fix k :: nat
    assume "k \<le> 2"
    hence "k = 0 \<or> k = 1 \<or> k = 2" by auto
    with assms have "integrable M (\<lambda>x. x^k)" by auto
  } note 1 = this
  note char_approx1
  note 2 = char_approx1 [of 2 t, OF 1, simplified]
  have "cmod (char M t - (\<Sum>k\<le>2. (\<i> * t) ^ k * (expectation (\<lambda>x. x ^ k)) / (fact k)))
      \<le> t\<^sup>2 * expectation (\<lambda>x. min (6 * x\<^sup>2) (\<bar>t\<bar> * \<bar>x\<bar> ^ 3)) / fact (3::nat)"
      using char_approx2 [of 2 t, OF 1] by simp
  also have "(\<Sum>k\<le>2. (\<i> * t) ^ k * expectation (\<lambda>x. x ^ k) / (fact k)) = 1 - t^2 * \<sigma>2 / 2"
    by (simp add: complex_eq_iff numeral_eq_Suc integral_1 Re_divide Im_divide)
  also have "fact 3 = 6" by (simp add: eval_nat_numeral)
  also have "t\<^sup>2 * expectation (\<lambda>x. min (6 * x\<^sup>2) (\<bar>t\<bar> * \<bar>x\<bar> ^ 3)) / 6 = 
     t\<^sup>2 / 6 * expectation (\<lambda>x. min (6 * x\<^sup>2) (\<bar>t\<bar> * \<bar>x\<bar> ^ 3))" by (simp add: field_simps)
  finally show ?thesis .
qed

(* This is a more familiar textbook formulation in terms of random variables, but 
   we will use the previous version for the CLT *)
lemma (in prob_space) aux':
  fixes \<mu> :: "real measure" and X
  assumes
    rv_X [simp]: "random_variable borel X" and
    [simp]: "integrable M X" and
    [simp]: "integrable M (\<lambda>x. (X x)^2)" and
    expect_X [simp]: "expectation X = 0" and
    var_X: "variance X = \<sigma>2"  and
    \<mu>_def: "\<mu> = distr M borel X"
  shows 
    "cmod (char \<mu> t - (1 - t^2 * \<sigma>2 / 2)) \<le>  (t^2 / 6) * 
        expectation (\<lambda>x. min (6 * (X x)^2) (abs t * (abs (X x))^3) )"

  apply (subst \<mu>_def)
  apply (subst integral_distr [symmetric, OF rv_X])
  apply force
  apply (rule real_distribution.aux)
using var_X by (auto simp add: integrable_distr_eq integral_distr)


theorem (in prob_space) central_limit_theorem:
  fixes 
    X :: "nat \<Rightarrow> 'a \<Rightarrow> real" and
    \<mu> :: "real measure" and
    \<sigma> :: real and
    S :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes
    X_indep: "indep_vars (\<lambda>i. borel) X UNIV" and
    X_integrable: "\<And>n. integrable M (X n)" and
    X_mean_0: "\<And>n. expectation (X n) = 0" and
    \<sigma>_pos: "\<sigma> > 0" and
    X_square_integrable: "\<And>n. integrable M (\<lambda>x. (X n x)\<^sup>2)" and
    X_variance: "\<And>n. variance (X n) = \<sigma>\<^sup>2" and
    X_distrib: "\<And>n. distr M borel (X n) = \<mu>"
  defines
    "S n \<equiv> \<lambda>x. \<Sum>i<n. X i x"
  shows
    "weak_conv_m (\<lambda>n. distr M borel (\<lambda>x. S n x / sqrt (n * \<sigma>\<^sup>2))) 
        (density lborel std_normal_density)"

proof -
  let ?S' = "\<lambda>n x. S n x / sqrt (real n * \<sigma>\<^sup>2)"
  def \<phi> \<equiv> "\<lambda>n. char (distr M borel (?S' n))"
  def \<psi> \<equiv> "\<lambda>n t. char \<mu> (t / sqrt (\<sigma>\<^sup>2 * n))"

  have X_rv [simp, measurable]: "\<And>n. random_variable borel (X n)"
    using X_indep unfolding indep_vars_def2 by simp
  interpret \<mu>: real_distribution \<mu>
    by (subst X_distrib [symmetric, of 0], rule real_distribution_distr, simp)
  (* these are equivalent to the hypotheses on X, given X_distr *)
  have \<mu>_integrable [simp]: "integrable \<mu> (\<lambda>x. x)"
    apply (simp add: X_distrib [symmetric, of 0])
    using assms by (subst integrable_distr_eq, auto)
  have \<mu>_mean_integrable [simp]: "\<mu>.expectation (\<lambda>x. x) = 0"
    apply (simp add: X_distrib [symmetric, of 0])
    using assms by (subst integral_distr, auto)
  have \<mu>_square_integrable [simp]: "integrable \<mu> (\<lambda>x. x^2)"
    apply (simp add: X_distrib [symmetric, of 0])
    using assms by (subst integrable_distr_eq, auto)
  have \<mu>_variance [simp]: "\<mu>.expectation (\<lambda>x. x^2) = \<sigma>\<^sup>2"
    apply (simp add: X_distrib [symmetric, of 0])
    using assms by (subst integral_distr, auto)

  have main:
    "\<forall>\<^sub>F n in sequentially.
      cmod (\<phi> n t - (1 + (-(t^2) / 2) / n)^n) \<le> (t\<^sup>2 / (6 * \<sigma>\<^sup>2) * (LINT x|\<mu>. min (6 * x\<^sup>2) (\<bar>t / sqrt (\<sigma>\<^sup>2 * n)\<bar> * \<bar>x\<bar> ^ 3)))" for t
  proof (rule eventually_sequentiallyI)
    fix n :: nat
    assume "n \<ge> nat (ceiling (t^2 / 4))"
    hence n: "n \<ge> t^2 / 4" by (subst nat_ceiling_le_eq [symmetric])
    let ?t = "t / sqrt (\<sigma>\<^sup>2 * n)"

    def \<psi>' \<equiv> "\<lambda>n i. char (distr M borel (\<lambda>x. X i x / sqrt (\<sigma>\<^sup>2 * n)))"
    have *: "\<And>n i t. \<psi>' n i t = \<psi> n t"
      unfolding \<psi>_def \<psi>'_def char_def
      by (subst X_distrib [symmetric]) (auto simp: integral_distr)

    have "\<phi> n t = char (distr M borel (\<lambda>x. \<Sum>i<n. X i x / sqrt (\<sigma>\<^sup>2 * real n))) t"
      by (auto simp: \<phi>_def S_def setsum_divide_distrib ac_simps)
    also have "\<dots> = (\<Prod> i < n. \<psi>' n i t)"
      unfolding \<psi>'_def
      apply (rule char_distr_setsum)
      apply (rule indep_vars_compose2[where X=X])
      apply (rule indep_vars_subset)
      apply (rule X_indep)
      apply auto
      done
    also have "\<dots> = (\<psi> n t)^n"
      by (auto simp add: * setprod_constant)
    finally have \<phi>_eq: "\<phi> n t =(\<psi> n t)^n" .

    have "norm (\<psi> n t - (1 - ?t^2 * \<sigma>\<^sup>2 / 2)) \<le> ?t\<^sup>2 / 6 * (LINT x|\<mu>. min (6 * x\<^sup>2) (\<bar>?t\<bar> * \<bar>x\<bar> ^ 3))"
      unfolding \<psi>_def by (rule \<mu>.aux, auto)
    also have "?t^2 * \<sigma>\<^sup>2 = t^2 / n"
      using \<sigma>_pos by (simp add: power_divide)
    also have "t^2 / n / 2 = (t^2 / 2) / n"
      by simp
    finally have **: "norm (\<psi> n t - (1 + (-(t^2) / 2) / n)) \<le> 
      ?t\<^sup>2 / 6 * (LINT x|\<mu>. min (6 * x\<^sup>2) (\<bar>?t\<bar> * \<bar>x\<bar> ^ 3))" by simp

    have "norm (\<phi> n t - (complex_of_real (1 + (-(t^2) / 2) / n))^n) \<le> 
         n * norm (\<psi> n t - (complex_of_real (1 + (-(t^2) / 2) / n)))"
      using n
      by (auto intro!: norm_power_diff \<mu>.cmod_char_le_1 abs_leI
               simp del: of_real_diff simp: of_real_diff[symmetric] divide_le_eq \<phi>_eq \<psi>_def)
    also have "\<dots> \<le> n * (?t\<^sup>2 / 6 * (LINT x|\<mu>. min (6 * x\<^sup>2) (\<bar>?t\<bar> * \<bar>x\<bar> ^ 3)))"
      by (rule mult_left_mono [OF **], simp)
    also have "\<dots> = (t\<^sup>2 / (6 * \<sigma>\<^sup>2) * (LINT x|\<mu>. min (6 * x\<^sup>2) (\<bar>?t\<bar> * \<bar>x\<bar> ^ 3)))" 
      using \<sigma>_pos by (simp add: field_simps min_absorb2)
    finally show "norm (\<phi> n t - (1 + (-(t^2) / 2) / n)^n) \<le> 
        (t\<^sup>2 / (6 * \<sigma>\<^sup>2) * (LINT x|\<mu>. min (6 * x\<^sup>2) (\<bar>?t\<bar> * \<bar>x\<bar> ^ 3)))" 
      by simp
  qed

  show ?thesis
  proof (rule levy_continuity)
    fix t
    let ?t = "\<lambda>n. t / sqrt (\<sigma>\<^sup>2 * n)"
    have "\<And>x. (\<lambda>n. min (6 * x\<^sup>2) (\<bar>t\<bar> * \<bar>x\<bar> ^ 3 / \<bar>sqrt (\<sigma>\<^sup>2 * real n)\<bar>)) ----> 0"
      using \<sigma>_pos 
      by (auto simp: real_sqrt_mult min_absorb2
               intro!: tendsto_min[THEN tendsto_eq_rhs] sqrt_at_top[THEN filterlim_compose]
                       filterlim_tendsto_pos_mult_at_top filterlim_at_top_imp_at_infinity
                       tendsto_divide_0 filterlim_real_sequentially)
    then have "(\<lambda>n. LINT x|\<mu>. min (6 * x\<^sup>2) (\<bar>?t n\<bar> * \<bar>x\<bar> ^ 3)) ----> (LINT x|\<mu>. 0)"
      by (intro integral_dominated_convergence [where w = "\<lambda>x. 6 * x^2"]) auto
    then have *: "(\<lambda>n. t\<^sup>2 / (6 * \<sigma>\<^sup>2) * (LINT x|\<mu>. min (6 * x\<^sup>2) (\<bar>?t n\<bar> * \<bar>x\<bar> ^ 3))) ----> 0"
      by (simp only: integral_zero tendsto_mult_right_zero)

    have "(\<lambda>n. complex_of_real ((1 + (-(t^2) / 2) / n)^n)) ----> complex_of_real (exp (-(t^2) / 2))"
      by (rule isCont_tendsto_compose [OF _ tendsto_exp_limit_sequentially]) auto
    then have "(\<lambda>n. \<phi> n t) ----> complex_of_real (exp (-(t^2) / 2))"
      by (rule Lim_transform) (rule Lim_null_comparison [OF main *])
    then show "(\<lambda>n. char (distr M borel (?S' n)) t) ----> char std_normal_distribution t"
      by (simp add: \<phi>_def char_std_normal_distribution)
  qed (auto intro!: real_dist_normal_dist simp: S_def)
qed

end
