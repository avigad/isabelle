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
  note real_distribution.equation_26p5b_stronger [of M 2 t, simplified]
  have [simp]: "prob UNIV = 1" by (metis prob_space space_eq_univ)
  from integral_2 have [simp]: "expectation (\<lambda>x. x * x) = \<sigma>2" 
    by (simp add: integral_1 numeral_eq_Suc)
  {
    fix k :: nat
    assume "k \<le> 2"
    hence "k = 0 \<or> k = 1 \<or> k = 2" by auto
    with assms have "integrable M (\<lambda>x. x^k)" by auto
  } note 1 = this
  note equation_26p5b_stronger
  note 2 = equation_26p5b_stronger [of 2 t, OF 1, simplified]
  have "cmod (char M t - (\<Sum>k\<le>2. (\<i> * t) ^ k * (expectation (\<lambda>x. x ^ k)) / (real (fact k))))
      \<le> t\<^sup>2 * expectation (\<lambda>x. min (6 * x\<^sup>2) (\<bar>t\<bar> * \<bar>x\<bar> ^ 3)) / real (fact (3::nat))"
      using equation_26p5b_stronger [of 2 t, OF 1] by simp
  also have "(\<Sum>k\<le>2. (\<i> * t) ^ k * expectation (\<lambda>x. x ^ k) / (real (fact k))) = 1 - t^2 * \<sigma>2 / 2"
    by (simp add: complex_eq_iff numeral_eq_Suc integral_1 Re_divide Im_divide)
  also have "real (fact (3::nat)) = 6" by (simp add: eval_nat_numeral)
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
  def S' \<equiv> "\<lambda>n x. S n x / sqrt (n * \<sigma>\<^sup>2)"
  def \<phi> \<equiv> "\<lambda>n. char (distr M borel (S' n))"
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

  have main: "\<And>t. eventually (\<lambda>n. cmod (\<phi> n t - (1 + (-(t^2) / 2) / n)^n) \<le> 
        (t\<^sup>2 / (6 * \<sigma>\<^sup>2) * (LINT x|\<mu>. min (6 * x\<^sup>2) (\<bar>t / sqrt (\<sigma>\<^sup>2 * n)\<bar> * \<bar>x\<bar> ^ 3))))
      sequentially"
  proof (rule eventually_sequentiallyI)
    fix n :: nat and t :: real
    assume "n \<ge> natceiling (t^2 / 4)"
    hence n: "n \<ge> t^2 / 4" by (subst natceiling_le_eq [symmetric])
    let ?t = "t / sqrt (\<sigma>\<^sup>2 * n)"

    def \<psi>' \<equiv> "\<lambda>n i. char (distr M borel (\<lambda>x. X i x / sqrt (\<sigma>\<^sup>2 * n)))"
    have *: "\<And>n i t. \<psi>' n i t = \<psi> n t"
      unfolding \<psi>_def \<psi>'_def char_def apply auto
      apply (subst X_distrib [symmetric])
      apply (subst integral_distr, auto)
      by (subst integral_distr, auto)

    have 1: "S' n = (\<lambda>x. (\<Sum> i < n. X i x / sqrt (\<sigma>\<^sup>2 * n)))" 
      by (rule ext, simp add: S'_def S_def setsum_divide_distrib ac_simps)

    have "\<phi> n t = (\<Prod> i < n. \<psi>' n i t)"
      unfolding \<phi>_def \<psi>'_def apply (subst 1)
      apply (rule char_distr_setsum)
      apply (rule indep_vars_compose2[where X=X])
      apply (rule indep_vars_subset)
      apply (rule X_indep)
      apply auto
      done
    also have "\<dots> = (\<psi> n t)^n"
      by (auto simp add: * setprod_constant)
    finally have 2: "\<phi> n t =(\<psi> n t)^n" .

    have "cmod (\<psi> n t - (1 - ?t^2 * \<sigma>\<^sup>2 / 2)) \<le> 
        ?t\<^sup>2 / 6 * (LINT x|\<mu>. min (6 * x\<^sup>2) (\<bar>?t\<bar> * \<bar>x\<bar> ^ 3))"
      unfolding \<psi>_def by (rule \<mu>.aux, auto)
    also have "?t^2 * \<sigma>\<^sup>2 = t^2 / n"
      using \<sigma>_pos by (simp add: power_divide)
    also have "t^2 / n / 2 = (t^2 / 2) / n" by simp
    finally have **: "cmod (\<psi> n t - (1 + (-(t^2) / 2) / n)) \<le> 
      ?t\<^sup>2 / 6 * (LINT x|\<mu>. min (6 * x\<^sup>2) (\<bar>?t\<bar> * \<bar>x\<bar> ^ 3))" by simp

    have "cmod (\<phi> n t - (complex_of_real (1 + (-(t^2) / 2) / n))^n) \<le> 
         n * cmod (\<psi> n t - (complex_of_real (1 + (-(t^2) / 2) / n)))"
      apply (subst 2, rule complex_power_diff)
      unfolding \<psi>_def apply (rule \<mu>.cmod_char_le_1)
      apply (simp only: norm_of_real)
      apply (auto intro!: abs_leI)
      using n by (subst divide_le_eq, auto)
    also have "\<dots> \<le> n * (?t\<^sup>2 / 6 * (LINT x|\<mu>. min (6 * x\<^sup>2) (\<bar>?t\<bar> * \<bar>x\<bar> ^ 3)))"
      by (rule mult_left_mono [OF **], simp)
    also have "\<dots> = (t\<^sup>2 / (6 * \<sigma>\<^sup>2) * (LINT x|\<mu>. min (6 * x\<^sup>2) (\<bar>?t\<bar> * \<bar>x\<bar> ^ 3)))" 
      using \<sigma>_pos by (simp add: field_simps min_absorb2)
    finally show "cmod (\<phi> n t - (1 + (-(t^2) / 2) / n)^n) \<le> 
        (t\<^sup>2 / (6 * \<sigma>\<^sup>2) * (LINT x|\<mu>. min (6 * x\<^sup>2) (\<bar>?t\<bar> * \<bar>x\<bar> ^ 3)))" 
      by simp
  qed

  have S_rv [simp, measurable]: "\<And>n. random_variable borel (\<lambda>x. S n x / sqrt (n * \<sigma>\<^sup>2))"
    unfolding S_def by measurable
  have "\<And>t. (\<lambda>n. \<phi> n t) ----> char std_normal_distribution t"
  proof -
    fix t
    let ?t = "\<lambda>n. t / sqrt (\<sigma>\<^sup>2 * n)"
    have *: "\<And>n. integrable \<mu> (\<lambda>x. 6 * x^2)" by auto
    have **: "\<And>n. integrable \<mu> (\<lambda>x. min (6 * x\<^sup>2) (\<bar>t / sqrt (\<sigma>\<^sup>2 * real n)\<bar> * \<bar>x\<bar> ^ 3))"
      by (rule integrable_bound [OF *]) auto
    have ***: "\<And>x. (\<lambda>n. \<bar>t\<bar> * \<bar>x\<bar> ^ 3 / \<bar>sqrt (\<sigma>\<^sup>2 * real n)\<bar>) ----> 0"
      apply (subst divide_inverse)
      apply (rule tendsto_mult_right_zero)
      using \<sigma>_pos apply (subst abs_of_nonneg, simp)
      apply (simp add: real_sqrt_mult)
      apply (rule tendsto_mult_right_zero)
      apply (rule tendsto_inverse_0_at_top)
      by (rule filterlim_compose [OF sqrt_at_top filterlim_real_sequentially])
    have "(\<lambda>n. LINT x|\<mu>. min (6 * x\<^sup>2) (\<bar>?t n\<bar> * \<bar>x\<bar> ^ 3)) ----> (LINT x|\<mu>. 0)"
      apply (rule integral_dominated_convergence [where w = "\<lambda>x. 6 * x^2"])
      using \<sigma>_pos apply (auto intro!: AE_I2)
      apply (rule tendsto_sandwich [OF _ _ tendsto_const ***])
      apply (auto intro!: always_eventually min.cobounded2)
      done
    hence "(\<lambda>n. LINT x|\<mu>. min (6 * x\<^sup>2) (\<bar>?t n\<bar> * \<bar>x\<bar> ^ 3)) ----> 0" by simp
    hence main2: "(\<lambda>n. t\<^sup>2 / (6 * \<sigma>\<^sup>2) * (LINT x|\<mu>. min (6 * x\<^sup>2) (\<bar>?t n\<bar> * \<bar>x\<bar> ^ 3))) ----> 0"
      by (rule tendsto_mult_right_zero)
    have **: "(\<lambda>n. (1 + (-(t^2) / 2) / n)^n) ----> exp (-(t^2) / 2)"
      by (rule exp_limit'')
    have "(\<lambda>n. complex_of_real ((1 + (-(t^2) / 2) / n)^n)) ----> 
        complex_of_real (exp (-(t^2) / 2))"
      by (rule isCont_tendsto_compose [OF _ **], auto)
    hence "(\<lambda>n. \<phi> n t) ----> complex_of_real (exp (-(t^2) / 2))"
      apply (rule LIMSEQ_diff_approach_zero)
      by (rule Lim_null_comparison [OF main main2])
    thus "(\<lambda>n. \<phi> n t) ----> char std_normal_distribution t"
      by (subst char_std_normal_distribution)
  qed
  thus ?thesis
    apply (intro levy_continuity)
    apply (rule real_distribution_distr [OF S_rv])
    unfolding real_distribution_def real_distribution_axioms_def
    apply (simp add: prob_space_normal_density)
    unfolding \<phi>_def S'_def by -
qed

end

