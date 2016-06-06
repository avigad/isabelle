theory CLT_Document
imports
  Probability
  "~~/src/HOL/Library/OptionalSugar"
begin

declare [[show_brackets = false, show_question_marks = false]]

text \<open>
 \DefineSnippet{tendstoadd}{
   @{thm tendsto_add}
 }%EndSnippet
\<close>

text_raw \<open>\DefineSnippet{skorohod}{\<close>
theorem Skorohod:
  fixes \<mu> :: "nat \<Rightarrow> real measure"
    and M :: "real measure"
  assumes \<mu>: "\<And>n. real_distribution (\<mu> n)"
  assumes M: "real_distribution M"
  assumes \<mu>_to_M: "weak_conv_m \<mu> M"
  shows "\<exists>(\<Omega> :: real measure) (Y_seq :: nat \<Rightarrow> real \<Rightarrow> real) (Y :: real \<Rightarrow> real).
    prob_space \<Omega> \<and>
    (\<forall>n. Y_seq n \<in> measurable \<Omega> borel) \<and>
    (\<forall>n. distr \<Omega> borel (Y_seq n) = \<mu> n) \<and>
    Y \<in> measurable \<Omega> lborel \<and>
    distr \<Omega> borel Y = M \<and>
    (\<forall>x \<in> space \<Omega>. (\<lambda>n. Y_seq n x) \<longlonglongrightarrow> Y x)"
text_raw \<open>}%EndSnippet\<close>
oops

text_raw \<open>\DefineSnippet{countableatoms}{\<close>
lemma countable_atoms: "countable {x. measure M {x} > 0}"
text_raw \<open>}%EndSnippet\<close>
oops

text_raw \<open>\DefineSnippet{cltproof}{\<close>
theorem (in prob_space) central_limit_theorem:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
    and \<mu> :: "real measure"
    and \<sigma> :: real
    and S :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes X_indep: "indep_vars (\<lambda>i. borel) X UNIV"
    and X_integrable: "\<And>n. integrable M (X n)"
    and X_mean_0: "\<And>n. expectation (X n) = 0"
    and \<sigma>_pos: "\<sigma> > 0"
    and X_square_integrable: "\<And>n. integrable M (\<lambda>x. (X n x)\<^sup>2)"
    and X_variance: "\<And>n. variance (X n) = \<sigma>\<^sup>2"
    and X_distrib: "\<And>n. distr M borel (X n) = \<mu>"
  defines "S n \<equiv> \<lambda>x. \<Sum>i<n. X i x"
  shows "weak_conv_m (\<lambda>n. distr M borel (\<lambda>x. S n x / sqrt (n * \<sigma>\<^sup>2)))
    std_normal_distribution"
proof -
  let ?S' = "\<lambda>n x. S n x / sqrt (real n * \<sigma>\<^sup>2)"
  define \<phi> where "\<phi> n = char (distr M borel (?S' n))" for n
  define \<psi> where "\<psi> n t = char \<mu> (t / sqrt (\<sigma>\<^sup>2 * n))" for n t

  have X_rv [simp, measurable]: "\<And>n. random_variable borel (X n)"
    using X_indep unfolding indep_vars_def2 by simp
  interpret \<mu>: real_distribution \<mu>
    by (subst X_distrib [symmetric, of 0], rule real_distribution_distr, simp)

  (* these are equivalent to the hypotheses on X, given X_distr *)
  have \<mu>_integrable [simp]: "integrable \<mu> (\<lambda>x. x)"
    and \<mu>_mean_integrable [simp]: "\<mu>.expectation (\<lambda>x. x) = 0"
    and \<mu>_square_integrable [simp]: "integrable \<mu> (\<lambda>x. x^2)"
    and \<mu>_variance [simp]: "\<mu>.expectation (\<lambda>x. x^2) = \<sigma>\<^sup>2"
    using assms by (simp_all add: X_distrib [symmetric, of 0] integrable_distr_eq integral_distr)

  have main: "\<forall>\<^sub>F n in sequentially.
      cmod (\<phi> n t - (1 + (-(t^2) / 2) / n)^n) \<le>
      t\<^sup>2 / (6 * \<sigma>\<^sup>2) * (LINT x|\<mu>. min (6 * x\<^sup>2) (\<bar>t / sqrt (\<sigma>\<^sup>2 * n)\<bar> * \<bar>x\<bar> ^ 3))" for t
  proof (rule eventually_sequentiallyI)
    fix n :: nat
    assume "n \<ge> nat (ceiling (t^2 / 4))"
    hence n: "n \<ge> t^2 / 4" by (subst nat_ceiling_le_eq [symmetric])
    let ?t = "t / sqrt (\<sigma>\<^sup>2 * n)"

    define \<psi>' where "\<psi>' n i = char (distr M borel (\<lambda>x. X i x / sqrt (\<sigma>\<^sup>2 * n)))" for n i
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
      unfolding \<psi>_def by (rule \<mu>.char_approx3, auto)
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
    have "\<And>x. (\<lambda>n. min (6 * x\<^sup>2) (\<bar>t\<bar> * \<bar>x\<bar> ^ 3 / \<bar>sqrt (\<sigma>\<^sup>2 * real n)\<bar>)) \<longlonglongrightarrow> 0"
      using \<sigma>_pos
      by (auto simp: real_sqrt_mult min_absorb2
               intro!: tendsto_min[THEN tendsto_eq_rhs] sqrt_at_top[THEN filterlim_compose]
                       filterlim_tendsto_pos_mult_at_top filterlim_at_top_imp_at_infinity
                       tendsto_divide_0 filterlim_real_sequentially)
    then have "(\<lambda>n. LINT x|\<mu>. min (6 * x\<^sup>2) (\<bar>?t n\<bar> * \<bar>x\<bar> ^ 3)) \<longlonglongrightarrow> (LINT x|\<mu>. 0)"
      by (intro integral_dominated_convergence [where w = "\<lambda>x. 6 * x^2"]) auto
    then have *: "(\<lambda>n. t\<^sup>2 / (6 * \<sigma>\<^sup>2) * (LINT x|\<mu>. min (6 * x\<^sup>2) (\<bar>?t n\<bar> * \<bar>x\<bar> ^ 3))) \<longlonglongrightarrow> 0"
      by (simp only: integral_zero tendsto_mult_right_zero)

    have "(\<lambda>n. complex_of_real ((1 + (-(t^2) / 2) / n)^n)) \<longlonglongrightarrow> complex_of_real (exp (-(t^2) / 2))"
      by (rule isCont_tendsto_compose [OF _ tendsto_exp_limit_sequentially]) auto
    then have "(\<lambda>n. \<phi> n t) \<longlonglongrightarrow> complex_of_real (exp (-(t^2) / 2))"
      by (rule Lim_transform) (rule Lim_null_comparison [OF main *])
    then show "(\<lambda>n. char (distr M borel (?S' n)) t) \<longlonglongrightarrow> char std_normal_distribution t"
      by (simp add: \<phi>_def char_std_normal_distribution)
  qed (auto intro!: real_dist_normal_dist simp: S_def)
qed
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{clt}{\<close>
theorem (in prob_space) central_limit_theorem:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
    and \<mu> :: "real measure"
    and \<sigma> :: real
    and S :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes X_indep: "indep_vars (\<lambda>i. borel) X UNIV"
    and X_integrable: "\<And>n. integrable M (X n)"
    and X_mean_0: "\<And>n. expectation (X n) = 0"
    and \<sigma>_pos: "\<sigma> > 0"
    and X_square_integrable: "\<And>n. integrable M (\<lambda>x. (X n x)\<^sup>2)"
    and X_variance: "\<And>n. variance (X n) = \<sigma>\<^sup>2"
    and X_distrib: "\<And>n. distr M borel (X n) = \<mu>"
  defines "S n \<equiv> \<lambda>x. \<Sum>i<n. X i x"
  shows "weak_conv_m (\<lambda>n. distr M borel (\<lambda>x. S n x / sqrt (n * \<sigma>\<^sup>2)))
    std_normal_distribution"
text_raw \<open>}%EndSnippet\<close>
oops

text_raw \<open>\DefineSnippet{cdf}{\<close>
definition
  cdf :: "real measure \<Rightarrow> real \<Rightarrow> real"
where
  "cdf M \<equiv> \<lambda>x. measure M {..x}"
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{cdfprop1}{\<close>
lemma cdf_nondecreasing:   "x \<le> y \<Longrightarrow> cdf M x \<le> cdf M y"
text_raw \<open>}%EndSnippet\<close>
oops

text_raw \<open>\DefineSnippet{cdfprop2}{\<close>
lemma cdf_is_right_cont:   "continuous (at_right a) (cdf M)"
text_raw \<open>}%EndSnippet\<close>
oops

text_raw \<open>\DefineSnippet{cdfprop3}{\<close>
lemma cdf_lim_at_bot:      "(cdf M \<longlongrightarrow> 0) at_bot"
text_raw \<open>}%EndSnippet\<close>
oops

text_raw \<open>\DefineSnippet{cdfprop4}{\<close>
lemma cdf_lim_at_top_prob: "(cdf M \<longlongrightarrow> 1) at_top"
text_raw \<open>}%EndSnippet\<close>
oops

text_raw \<open>\DefineSnippet{intervalmeasure}{\<close>
lemma real_distribution_interval_measure:
  fixes F :: "real \<Rightarrow> real"
  assumes nondecF : "\<And> x y. x \<le> y \<Longrightarrow> F x \<le> F y"
    and right_cont_F : "\<And>a. continuous (at_right a) F"
    and lim_F_at_bot : "(F \<longlongrightarrow> 0) at_bot"
    and lim_F_at_top : "(F \<longlongrightarrow> 1) at_top"
  shows "real_distribution (interval_measure F)"
text_raw \<open>}%EndSnippet\<close>
oops

text_raw \<open>\DefineSnippet{cdfunique}{\<close>
lemma cdf_unique:
  fixes M1 M2
  assumes "real_distribution M1" and "real_distribution M2"
  assumes "cdf M1 = cdf M2"
  shows "M1 = M2"
text_raw \<open>}%EndSnippet\<close>
oops

text_raw \<open>\DefineSnippet{weakconv}{\<close>
definition
  weak_conv :: "(nat \<Rightarrow> (real \<Rightarrow> real)) \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> bool"
where
  "weak_conv F_seq F \<equiv> \<forall>x. isCont F x \<longrightarrow> (\<lambda>n. F_seq n x) \<longlonglongrightarrow> F x"

definition
  weak_conv_m :: "(nat \<Rightarrow> real measure) \<Rightarrow> real measure \<Rightarrow> bool"
where
  "weak_conv_m M_seq M \<equiv> weak_conv (\<lambda>n. cdf (M_seq n)) (cdf M)"
text_raw \<open>}%EndSnippet\<close>

end