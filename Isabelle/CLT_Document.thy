theory CLT_Document
imports
  Probability
  "~~/src/HOL/Library/OptionalSugar"
begin

declare [[show_brackets = false, show_question_marks = false]]

text_raw \<open>\DefineSnippet{cltproof}{\<close>
theorem (in prob_space) central_limit_theorem_zero_mean:
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
  let ?S' = "\<lambda>n x. S n x / sqrt (real n * \<sigma>\<^sup>2)" and ?m = "\<lambda>x. min (6 * x\<^sup>2)"
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
    using assms by (simp_all add: X_distrib [symmetric, of 0] integrable_distr_eq
                                  integral_distr)

  let ?I = "\<lambda>n t. LINT x|\<mu>. ?m x (\<bar>t / sqrt (\<sigma>\<^sup>2 * n)\<bar> * \<bar>x\<bar> ^ 3)"
  have main: "\<forall>\<^sub>F n in sequentially.
      cmod (\<phi> n t - (1 + (-(t^2) / 2) / n)^n) \<le> t\<^sup>2 / (6 * \<sigma>\<^sup>2) * ?I n t"
      for t
  proof (rule eventually_sequentiallyI)
    fix n :: nat
    assume "n \<ge> nat (ceiling (t^2 / 4))"
    hence n: "n \<ge> t^2 / 4" by (subst nat_ceiling_le_eq [symmetric])
    let ?t = "t / sqrt (\<sigma>\<^sup>2 * n)"

    define \<psi>' where "\<psi>' n i = char (distr M borel
      (\<lambda>x. X i x / sqrt (\<sigma>\<^sup>2 * n)))" for n i
    have *: "\<And>n i t. \<psi>' n i t = \<psi> n t"
      unfolding \<psi>_def \<psi>'_def char_def
      by (subst X_distrib [symmetric]) (auto simp: integral_distr)

    have "\<phi> n t = char (distr M borel
       (\<lambda>x. \<Sum>i<n. X i x / sqrt (\<sigma>\<^sup>2 * real n))) t"
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
    finally have \<phi>_eq: "\<phi> n t = (\<psi> n t)^n" .

    have "norm (\<psi> n t - (1 - ?t^2 * \<sigma>\<^sup>2 / 2)) \<le> ?t\<^sup>2 / 6 * ?I n t"
      unfolding \<psi>_def by (rule \<mu>.char_approx3, auto)
    also have "?t^2 * \<sigma>\<^sup>2 = t^2 / n"
      using \<sigma>_pos by (simp add: power_divide)
    also have "t^2 / n / 2 = (t^2 / 2) / n"
      by simp
    finally have **: "norm (\<psi> n t - (1 + (-(t^2) / 2) / n)) \<le>
        ?t\<^sup>2 / 6 * ?I n t"
      by simp

    have "norm (\<phi> n t - (complex_of_real (1 + (-(t^2) / 2) / n))^n) \<le>
         n * norm (\<psi> n t - (complex_of_real (1 + (-(t^2) / 2) / n)))"
      using n
      by (auto intro!: norm_power_diff \<mu>.cmod_char_le_1 abs_leI simp del: of_real_diff
               simp: of_real_diff[symmetric] divide_le_eq \<phi>_eq \<psi>_def)
    also have "\<dots> \<le> n * (?t\<^sup>2 / 6 * ?I n t)"
      by (rule mult_left_mono [OF **], simp)
    also have "\<dots> = (t\<^sup>2 / (6 * \<sigma>\<^sup>2) * ?I n t)"
      using \<sigma>_pos by (simp add: field_simps min_absorb2)
    finally show "norm (\<phi> n t - (1 + (-(t^2) / 2) / n)^n) \<le>
        (t\<^sup>2 / (6 * \<sigma>\<^sup>2) * ?I n t)"
      by simp
  qed

  show ?thesis
  proof (rule levy_continuity)
    fix t
    have "\<And>x. (\<lambda>n. ?m x (\<bar>t\<bar> * \<bar>x\<bar> ^ 3 / \<bar>sqrt (\<sigma>\<^sup>2 * real n)\<bar>)) \<longlonglongrightarrow> 0"
      using \<sigma>_pos
      by (auto simp: real_sqrt_mult min_absorb2
               intro!: tendsto_min[THEN tendsto_eq_rhs] sqrt_at_top[THEN filterlim_compose]
                       filterlim_tendsto_pos_mult_at_top filterlim_at_top_imp_at_infinity
                       tendsto_divide_0 filterlim_real_sequentially)
    then have "(\<lambda>n. ?I n t) \<longlonglongrightarrow> (LINT x|\<mu>. 0)"
      by (intro integral_dominated_convergence [where w = "\<lambda>x. 6 * x^2"]) auto
    then have *: "(\<lambda>n. t\<^sup>2 / (6 * \<sigma>\<^sup>2) * ?I n t) \<longlonglongrightarrow> 0"
      by (simp only: integral_zero tendsto_mult_right_zero)

    have "(\<lambda>n. complex_of_real ((1 + (-(t^2) / 2) / n)^n)) \<longlonglongrightarrow>
        complex_of_real (exp (-(t^2) / 2))"
      by (rule isCont_tendsto_compose [OF _ tendsto_exp_limit_sequentially])
         auto
    then have "(\<lambda>n. \<phi> n t) \<longlonglongrightarrow> complex_of_real (exp (-(t^2) / 2))"
      by (rule Lim_transform) (rule Lim_null_comparison [OF main *])
    then show "(\<lambda>n. char (distr M borel (?S' n)) t) \<longlonglongrightarrow>
        char std_normal_distribution t"
      by (simp add: \<phi>_def char_std_normal_distribution)
  qed (auto intro!: real_dist_normal_dist simp: S_def)
qed

theorem (in prob_space) central_limit_theorem:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
    and \<mu> :: "real measure"
    and \<sigma> :: real
    and S :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes X_indep: "indep_vars (\<lambda>i. borel) X UNIV"
    and X_integrable: "\<And>n. integrable M (X n)"
    and X_mean: "\<And>n. expectation (X n) = m"
    and \<sigma>_pos: "\<sigma> > 0"
    and X_square_integrable: "\<And>n. integrable M (\<lambda>x. (X n x)\<^sup>2)"
    and X_variance: "\<And>n. variance (X n) = \<sigma>\<^sup>2"
    and X_distrib: "\<And>n. distr M borel (X n) = \<mu>"
  defines "X' i x \<equiv> X i x - m"
  shows "weak_conv_m (\<lambda>n. distr M borel (\<lambda>x. (\<Sum>i<n. X' i x) / sqrt (n*\<sigma>\<^sup>2))) std_normal_distribution"
proof (intro central_limit_theorem_zero_mean)
  show "indep_vars (\<lambda>i. borel) X' UNIV"
    unfolding X'_def[abs_def] using X_indep by (rule indep_vars_compose2) auto
  show "integrable M (X' n)" "expectation (X' n) = 0" for n
    using X_integrable X_mean by (auto simp: X'_def[abs_def] prob_space)
  show "\<sigma> > 0" "integrable M (\<lambda>x. (X' n x)\<^sup>2)" "variance (X' n) = \<sigma>\<^sup>2" for n
    using \<open>0 < \<sigma>\<close> X_integrable X_mean X_square_integrable X_variance unfolding X'_def
    by (auto simp: prob_space power2_diff)
  show "distr M borel (X' n) = distr \<mu> borel (\<lambda>x. x - m)" for n
    unfolding X_distrib[of n, symmetric] using X_integrable
    by (subst distr_distr) (auto simp: X'_def[abs_def] comp_def)
qed
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{tendstoadd}{\<close>
lemma tendsto_add:
  fixes f g :: "_ \<Rightarrow> 'a::topological_monoid_add"
  assumes "(f \<longlongrightarrow> a) F" and "(g \<longlongrightarrow> b) F"
  shows "((\<lambda>x. f x + g x) \<longlongrightarrow> a + b) F"
text_raw \<open>}%EndSnippet\<close>
oops

text_raw \<open>\DefineSnippet{skorohod}{\<close>
theorem Skorohod:
  fixes \<mu> :: "nat \<Rightarrow> real measure" and M :: "real measure"
  assumes "\<And>n. real_distribution (\<mu> n)" "real_distribution M"
    and "weak_conv_m \<mu> M"
  shows
    "\<exists>(\<Omega> :: real measure) (Y_seq :: nat \<Rightarrow> real \<Rightarrow> real) (Y :: real \<Rightarrow> real).
    prob_space \<Omega> \<and>
    (\<forall>n. Y_seq n \<in> \<Omega> \<rightarrow>\<^sub>M borel) \<and>
    (\<forall>n. distr \<Omega> borel (Y_seq n) = \<mu> n) \<and>
    Y \<in> \<Omega> \<rightarrow>\<^sub>M b lborel \<and>
    distr \<Omega> borel Y = M \<and>
    (\<forall>x \<in> space \<Omega>. (\<lambda>n. Y_seq n x) \<longlonglongrightarrow> Y x)"
text_raw \<open>}%EndSnippet\<close>
oops

text_raw \<open>\DefineSnippet{countableatoms}{\<close>
lemma countable_atoms: "countable {x. measure M {x} > 0}"
text_raw \<open>}%EndSnippet\<close>
oops

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
  assumes "mono F" "\<And>a. continuous (at_right a) F"
    and "(F \<longlongrightarrow> 0) at_bot" "(F \<longlongrightarrow> 1) at_top"
  shows "real_distribution (interval_measure F)"
text_raw \<open>}%EndSnippet\<close>
oops

text_raw \<open>\DefineSnippet{cdfunique}{\<close>
lemma cdf_unique:
  fixes M1 M2
  assumes "real_distribution M1" and "real_distribution M2"
    and "cdf M1 = cdf M2"
  shows "M1 = M2"
text_raw \<open>}%EndSnippet\<close>
oops

text_raw \<open>\DefineSnippet{lebesgueintegralcountableadd}{\<close>
lemma integral_countable_add:
  fixes f :: "_ \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes "\<And>i::nat. A i \<in> sets M"
    and "\<And>i j. i \<noteq> j \<Longrightarrow> A i \<inter> A j = {}"
    and "set_integrable M (\<Union>i. A i) f"
  shows "LINT x:(\<Union>i. A i)|M. f x = (\<Sum>i. (LINT x:(A i)|M. f x))"
text_raw \<open>}%EndSnippet\<close>
  oops

text_raw \<open>\DefineSnippet{dominatedconvergence}{\<close>
lemma dominated_convergence:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
    and w :: "'a \<Rightarrow> real"
  assumes "f \<in> M \<rightarrow>\<^sub>M borel" "\<And>i. s i \<in> M \<rightarrow>\<^sub>M borel" "integrable M w"
    and "AE x in M. (\<lambda>i. s i x) \<longlonglongrightarrow> f x"
    and "\<And>i. AE x in M. norm (s i x) \<le> w x"
  shows "integrable M f" and "\<And>i. integrable M (s i)"
    and "(\<lambda>i. LINT x|M. s i x) \<longlonglongrightarrow> (LINT x|M. f x)"
text_raw \<open>}%EndSnippet\<close>
  oops

text_raw \<open>\DefineSnippet{integrablebounded}{\<close>
lemma integrable_iff_bounded:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  shows "integrable M f \<longleftrightarrow> f \<in> M \<rightarrow>\<^sub>M borel \<and> (\<integral>\<^sup>+x. norm (f x) \<partial>M) < \<infinity>"
text_raw \<open>}%EndSnippet\<close>
  by (rule integrable_iff_bounded)

text_raw \<open>\DefineSnippet{integralnormbound}{\<close>
lemma integral_norm_bound:
  fixes f :: "_ \<Rightarrow> 'a :: {banach, second_countable_topology}"
  shows "integrable M f \<Longrightarrow> norm (LINT x|M. f x) \<le> (LINT x|M. norm (f x))"
text_raw \<open>}%EndSnippet\<close>
  oops

text_raw \<open>\DefineSnippet{ftcfinite}{\<close>
lemma interval_integral_FTC_finite:
  fixes f F :: "real \<Rightarrow> 'a::euclidean_space" and a b :: real
  assumes f: "continuous_on {min a b..max a b} f"
   and F: "\<And>x. min a b \<le> x \<Longrightarrow> x \<le> max a b \<Longrightarrow>
    (F has_vector_derivative (f x)) (at x within {min a b..max a b})"
  shows "(LBINT x=a..b. f x) = F b - F a"
text_raw \<open>}%EndSnippet\<close>
oops

text_raw \<open>\DefineSnippet{ftcintegrable}{\<close>
lemma interval_integral_FTC_integrable:
  fixes f F :: "real \<Rightarrow> 'a::euclidean_space" and a b :: ereal
  assumes "a < b"
    and "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow>
    (F has_vector_derivative f x) (at x)"
    and "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> continuous (at x) f"
    and "set_integrable lborel (einterval a b) f"
    and "((F \<circ> real_of_ereal) \<longlongrightarrow> A) (at_right a)"
    and "((F \<circ> real_of_ereal) \<longlongrightarrow> B) (at_left b)"
  shows "(LBINT x=a..b. f x) = B - A"
text_raw \<open>}%EndSnippet\<close>
oops

text_raw \<open>\DefineSnippet{ftc2}{\<close>
lemma interval_integral_FTC2:
  fixes a b c x :: real and f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "a \<le> c" "c \<le> b" "continuous_on {a..b} f" "a \<le> x" "x \<le> b"
  shows "((\<lambda>u. LBINT y=c..u. f y) has_vector_derivative (f x))
    (at x within {a..b})"
text_raw \<open>}%EndSnippet\<close>
  oops

text_raw \<open>\DefineSnippet{substfinite}{\<close>
lemma interval_integral_substitution_finite:
  fixes a b :: real and f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "a \<le> b" and "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow>
      (g has_real_derivative (g' x)) (at x within {a..b})"
    and "continuous_on (g ` {a..b}) f" "continuous_on {a..b} g'"
  shows "LBINT x=a..b. g' x *\<^sub>R f (g x) = LBINT y=g a..g b. f y"
text_raw \<open>}%EndSnippet\<close>
oops

text_raw \<open>\DefineSnippet{substintegrable}{\<close>
lemma interval_integral_substitution_integrable:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space" and a b A B :: ereal
  assumes "a < b"
    and "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> DERIV g x :> g' x"
    and "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> continuous (at (g x)) f"
    and "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> continuous (at x) g'"
    and "\<And>x. a \<le> ereal x \<Longrightarrow> ereal x \<le> b \<Longrightarrow> 0 \<le> g' x"
    and "((ereal \<circ> g \<circ> real_of_ereal) \<longlongrightarrow> A) (at_right a)"
    and "((ereal \<circ> g \<circ> real_of_ereal) \<longlongrightarrow> B) (at_left b)"
    and "set_integrable lborel (einterval a b) (\<lambda>x. g' x *\<^sub>R f (g x))"
    and "set_integrable lborel (einterval A B) (\<lambda>x. f x)"
  shows "(LBINT x=A..B. f x) = (LBINT x=a..b. g' x *\<^sub>R f (g x))"
text_raw \<open>}%EndSnippet\<close>
oops

text_raw \<open>\DefineSnippet{charprop1}{\<close>
lemma (in real_distribution) continuous_char: "continuous (at t) (char M)"
text_raw \<open>}%EndSnippet\<close>
  oops

text_raw \<open>\DefineSnippet{charprop2}{\<close>
lemma (in real_distribution) char_zero: "char M 0 = 1"
text_raw \<open>}%EndSnippet\<close>
  oops

text_raw \<open>\DefineSnippet{charprop3}{\<close>
lemma (in real_distribution) cmod_char_le_1: "norm (char M t) \<le> 1"
text_raw \<open>}%EndSnippet\<close>
  oops

text_raw \<open>\DefineSnippet{chardistrsum}{\<close>
lemma (in prob_space) char_distr_sum:
  assumes "indep_var borel X1 borel X2"
  shows "char (distr M borel (\<lambda>\<omega>. X1 \<omega> + X2 \<omega>)) t =
    char (distr M borel X1) t * char (distr M borel X2) t"
proof -
  from assms have [measurable]: "random_variable borel X1" by (elim indep_var_rv1)
  from assms have [measurable]: "random_variable borel X2" by (elim indep_var_rv2)

  have "char (distr M borel (\<lambda>\<omega>. X1 \<omega> + X2 \<omega>)) t =
      (LINT x|M. iexp (t * (X1 x + X2 x)))"
    by (simp add: char_def integral_distr)
  also have "\<dots> = (LINT x|M. iexp (t * (X1 x)) * iexp (t * (X2 x)))"
    by (simp add: field_simps exp_add)
  also have "\<dots> =
      (LINT x|M. iexp (t * (X1 x))) * (LINT x|M. iexp (t * (X2 x)))"
    by (auto intro!: indep_var_compose[unfolded comp_def, OF assms]
                     integrable_iexp indep_var_lebesgue_integral)
  also have "\<dots> = char (distr M borel X1) t * char (distr M borel X2) t"
    by (simp add: char_def integral_distr)
  finally show ?thesis .
qed
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{chardistrsetsum}{\<close>
lemma (in prob_space) char_distr_setsum:
  "indep_vars (\<lambda>i. borel) X A \<Longrightarrow>
    char (distr M borel (\<lambda>\<omega>. \<Sum>i\<in>A. X i \<omega>)) t =
    (\<Prod>i\<in>A. char (distr M borel (X i)) t)"
proof (induct A rule: infinite_finite_induct)
  case (insert x F) then show ?case
    using indep_vars_subset[of "\<lambda>_. borel" X "insert x F" F]
    by (auto simp add: char_distr_sum indep_vars_setsum)
qed (simp_all add: char_def integral_distr prob_space del: distr_const)
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{charapprox}{\<close>
lemma (in prob_space) char_approx3':
  fixes \<mu> :: "real measure" and X
  assumes "random_variable borel X"
    and "integrable M X" "integrable M (\<lambda>x. (X x)^2)" "expectation X = 0"
    and "variance X = \<sigma>2"
    and "\<mu> = distr M borel X"
  shows "cmod (char \<mu> t - (1 - t^2 * \<sigma>2 / 2)) \<le>
    (t^2 / 6) * expectation (\<lambda>x. min (6 * (X x)^2) (\<bar>t\<bar> * \<bar>X x\<bar>^3))"
text_raw \<open>}%EndSnippet\<close>
  oops

text_raw \<open>\DefineSnippet{momenteven}{\<close>
lemma std_normal_moment_even:
  "has_bochner_integral lborel (\<lambda>x. std_normal_density x * x ^ (2 * k))
    (fact (2 * k) / (2^k * fact k))"
text_raw \<open>}%EndSnippet\<close>
  oops

text_raw \<open>\DefineSnippet{momentodd}{\<close>
lemma std_normal_moment_odd:
  "has_bochner_integral lborel (\<lambda>x. std_normal_density x * x^(2 * k + 1)) 0"
text_raw \<open>}%EndSnippet\<close>
  oops

text_raw \<open>\DefineSnippet{levyunique}{\<close>
theorem Levy_uniqueness:
  fixes M1 M2 :: "real measure"
  assumes "real_distribution M1" "real_distribution M2"
    and "char M1 = char M2"
  shows "M1 = M2"
text_raw \<open>}%EndSnippet\<close>
  oops

text_raw \<open>\DefineSnippet{levycont}{\<close>
theorem levy_continuity:
  fixes M :: "nat \<Rightarrow> real measure" and M' :: "real measure"
  assumes "\<And>n. real_distribution (M n)"
    and "real_distribution M'"
    and "\<And>t. (\<lambda>n. char (M n) t) \<longlonglongrightarrow> char M' t"
  shows "weak_conv_m M M'"
text_raw \<open>}%EndSnippet\<close>
  oops

text_raw \<open>\DefineSnippet{levycont1}{\<close>
theorem levy_continuity1:
  "(\<And>n. real_distribution (M n)) \<Longrightarrow> real_distribution M' \<Longrightarrow>
    weak_conv_m M M' \<Longrightarrow>
    (\<lambda>n. char (M n) t) \<longlonglongrightarrow> char M' t"
  unfolding char_def by (rule weak_conv_imp_integral_bdd_continuous_conv) auto
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{helly}{\<close>
theorem Helly_selection:
  fixes f :: "nat \<Rightarrow> real \<Rightarrow> real"
  assumes "\<And>n x. continuous (at_right x) (f n)"
    and "\<And>n. mono (f n)"
    and "\<And>n x. \<bar>f n x\<bar> \<le> M"
  shows "\<exists>s. subseq s \<and> mono F \<and> (\<forall>x. \<bar>F x\<bar> \<le> M) \<and>
    (\<exists>F. (\<forall>x. continuous (at_right x) F) \<and>
    (\<forall>x. continuous (at x) F \<longrightarrow> (\<lambda>n. f (s n) x) \<longlonglongrightarrow> F x))"
text_raw \<open>}%EndSnippet\<close>
  oops

text_raw \<open>\DefineSnippet{thight}{\<close>
theorem tight_imp_convergent_subsubsequence:
  assumes \<mu>: "tight \<mu>" "subseq s"
  shows "\<exists>r M. subseq r \<and> real_distribution M \<and> weak_conv_m (\<mu> \<circ> s \<circ> r) M"
text_raw \<open>}%EndSnippet\<close>
oops

text_raw \<open>\DefineSnippet{integraladd}{\<close>
lemma integral_add:
  "integrable M f \<Longrightarrow> integrable M g \<Longrightarrow>
    (LINT x|M. f x + g x) = (LINT x|M. f x) + (LINT x|M. g x)"
text_raw \<open>}%EndSnippet\<close>
  oops

text_raw \<open>\DefineSnippet{integrableadd}{\<close>
lemma integrable_add:
  "integrable M f \<Longrightarrow> integrable M g \<Longrightarrow> integrable M (\<lambda>x. f x + g x)"
text_raw \<open>}%EndSnippet\<close>
  oops

text_raw \<open>\DefineSnippet{weakconv}{\<close>
definition
  weak_conv :: "(nat \<Rightarrow> (real \<Rightarrow> real)) \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> bool"
where
  "weak_conv F_seq F \<equiv>
     \<forall>x. continuous (at x) F \<longrightarrow> (\<lambda>n. F_seq n x) \<longlonglongrightarrow> F x"

definition
  weak_conv_m :: "(nat \<Rightarrow> real measure) \<Rightarrow> real measure \<Rightarrow> bool"
where
  "weak_conv_m M_seq M \<equiv> weak_conv (\<lambda>n. cdf (M_seq n)) (cdf M)"
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{distr}{\<close>
definition
  distr :: "'a measure \<Rightarrow> 'b measure \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b measure"
where
  "distr M N f =
    measure_of (space N) (sets N) (\<lambda>A. emeasure M (f -` A \<inter> space M))"
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{density}{\<close>
definition
  density :: "'a measure \<Rightarrow> ('a \<Rightarrow> ennreal) \<Rightarrow> 'a measure"
where
  "density M f =
    measure_of (space M) (sets M) (\<lambda>A. \<integral>\<^sup>+ x. f x * indicator A x \<partial>M)"
text_raw \<open>}%EndSnippet\<close>



text_raw \<open>\DefineSnippet{probspace}{\<close>
locale prob_space =
  fixes M :: "'a measure" assumes "emeasure M (space M) = 1"
begin
  abbreviation "events \<equiv> sets M"
  abbreviation "prob \<equiv> measure M"
  abbreviation "random_variable M' X \<equiv> X \<in> M \<rightarrow>\<^sub>M M'"
  abbreviation "expectation X \<equiv> (LINT x|M. X x)"
  abbreviation "variance X \<equiv> (LINT x|M. (X x - expectation X)\<^sup>2)"
end
text_raw \<open>}%EndSnippet\<close>


text_raw \<open>\DefineSnippet{indepsets}{\<close>
definition (in prob_space)
  indep_sets :: "('i \<Rightarrow> 'a set set) \<Rightarrow> 'i set \<Rightarrow> bool"
where
  "indep_sets F I \<longleftrightarrow>
    (\<forall>i\<in>I. F i \<subseteq> events) \<and>
    (\<forall>J\<subseteq>I. J \<noteq> {} \<longrightarrow> finite J \<longrightarrow>
      (\<forall>A\<in>(\<Pi> i\<in>J. F i). prob (\<Inter>j\<in>J. A j) = (\<Prod>j\<in>J. prob (A j))))"
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{indepevents}{\<close>
definition (in prob_space) "indep_events A I \<longleftrightarrow> indep_sets (\<lambda>i. {A i}) I"
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{indepvars}{\<close>
definition (in prob_space)
  indep_vars :: "('i \<Rightarrow> 'b measure) \<Rightarrow> ('i \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'i set \<Rightarrow> bool"
where
  "indep_vars M' X I \<longleftrightarrow>
    (\<forall>i\<in>I. random_variable (M' i) (X i)) \<and>
    indep_sets (\<lambda>i. { X i -` A \<inter> space M | A. A \<in> sets (M' i)}) I"
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{char}{\<close>
definition
  char :: "real measure \<Rightarrow> real \<Rightarrow> complex"
where
  "char M t = LINT x|M. iexp (t * x)"
text_raw \<open>}%EndSnippet\<close>

experiment
begin

text_raw \<open>\DefineSnippet{normaldistr}{\<close>
definition
  normal_density :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
where
  "normal_density \<mu> \<sigma> x = 1 / sqrt (2 * pi * \<sigma>\<^sup>2) * exp (-(x - \<mu>)\<^sup>2/ (2 * \<sigma>\<^sup>2))"

abbreviation
  std_normal_density :: "real \<Rightarrow> real"
where
  "std_normal_density \<equiv> normal_density 0 1"

abbreviation
  std_normal_distribution :: "real measure"
where
  "std_normal_distribution \<equiv> density lborel std_normal_density"
text_raw \<open>}%EndSnippet\<close>

end

end
