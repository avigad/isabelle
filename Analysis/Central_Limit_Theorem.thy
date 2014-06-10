(*
Theory: Central_Limit_Theorem.thy
Authors: Jeremy Avigad, Luke Serafin
*)

theory Central_Limit_Theorem

imports Levy

begin

(* TODO: move these elsewhere *)

lemma (in prob_space) indep_vars_compose2:
  assumes "indep_vars M' X I"
  assumes rv: "\<And>i. i \<in> I \<Longrightarrow> Y i \<in> measurable (M' i) (N i)"
  shows "indep_vars N (\<lambda>i x. Y i (X i x)) I"
using indep_vars_compose [OF assms] by (simp add: comp_def)

lemma (in prob_space) indep_vars_cmult:
  shows "indep_vars (\<lambda>i. borel) X I \<Longrightarrow> indep_vars (\<lambda>i. borel) (\<lambda>i x. (c :: real) * X i x) I"
  apply (rule indep_vars_compose2) back
  apply assumption
by auto

lemma (in prob_space) real_distribution_distr [intro, simp]: "random_variable borel X \<Longrightarrow> 
    real_distribution (distr M borel X)"
  unfolding real_distribution_def real_distribution_axioms_def apply auto
by (rule prob_space_distr)  

lemma (in prob_space) variance_mean_zero: "expectation X = 0 \<Longrightarrow>
    variance X = expectation (\<lambda>x. (X x)^2)"
by auto

lemma sqrt_at_top: "LIM x at_top. sqrt x :: real :> at_top"
  by (rule filterlim_at_top_at_top[where Q="\<lambda>x. True" and P="\<lambda>x. 0 < x" and g="power2"])
     (auto intro: eventually_gt_at_top)


(* it is funny that this isn't in the library! It could go in Transcendental *)
lemma exp_limit:
  fixes x :: real
  shows "((\<lambda>y.(1 + x * y) powr (1 / y)) ---> exp x) (at_right 0)"
proof - 
  have "((\<lambda>y. ln (1 + x * y)) has_real_derivative 1 * x) (at 0)"
    apply (rule DERIV_chain') back
    by (auto intro!: derivative_eq_intros)
  hence 1: "((\<lambda>y. ln (1 + x * y) / y) ---> x) (at 0)"
    by (auto simp add: has_field_derivative_def field_has_derivative_at) 
  have 2: "(at_right 0) \<le> (at (0::real))"
    by (subst at_eq_sup_left_right, auto)
  have 3: "eventually (\<lambda>y. 0 < 1 + x * y) (at_right 0)"
    apply (case_tac "x = 0")
    apply auto
    apply (subst eventually_at_right)
    apply (rule_tac x = "1 / abs x" in exI)
    apply (auto simp add: field_simps)
    apply (case_tac "x >= 0")
    apply (auto simp add: field_simps)
    apply (rule add_pos_nonneg, auto)
    done
  have 4: "eventually (\<lambda>y. y > (0::real)) (at_right 0)"
    by (subst eventually_at_right, auto intro: gt_ex)
  have 5: "eventually (\<lambda>y. exp (ln ((1 + x * y) powr (1 / y))) =
         (1 + x * y) powr (1 / y)) (at_right 0)"
    apply (rule eventually_elim1 [OF eventually_conj [OF 3 4]])
    by (rule exp_ln, auto)
  have 6: "eventually (\<lambda>y. ln ((1 + x * y) powr (1 / y)) =
         ln (1 + x * y) / y) (at_right 0)"
    apply (rule eventually_elim1 [OF eventually_conj [OF 3 4]])
    apply (subst ln_powr)
    apply (case_tac "x = 0")
    by auto
  have "((\<lambda>y. ln ((1 + x * y) powr (1 / y))) ---> x) (at_right 0)"
    apply (subst filterlim_cong [OF refl refl 6])
    by (rule tendsto_mono [OF 2 1])
  hence "((\<lambda>y. exp (ln ((1 + x * y) powr (1 / y)))) ---> exp x) (at_right 0)"
    by (rule tendsto_exp)
  thus "((\<lambda>y.(1 + x * y) powr (1 / y)) ---> exp x) (at_right 0)"
    by (rule Lim_transform_eventually [OF 5])
qed

lemma exp_limit':
  fixes x :: real
  shows "((\<lambda>y. (1 + x / y) powr y) ---> exp x) at_top"

  apply (subst filterlim_at_top_to_right)
  apply (simp add: inverse_eq_divide)
by (rule exp_limit)

lemma exp_limit'':
  fixes x :: real
  shows "(\<lambda>n. (1 + x / n) ^ n) ----> exp x"
proof -
  from reals_Archimedean2 [of "abs x"] obtain n :: nat where *: "real n > abs x" ..
  hence "eventually (\<lambda>n :: nat. 0 < 1 + x / real n) at_top"
    apply (intro eventually_sequentiallyI [of n])
    apply (case_tac "x \<ge> 0")
    apply (rule add_pos_nonneg, auto intro: divide_nonneg_nonneg)
    apply (subgoal_tac "x / real xa > -1")
    by (auto simp add: field_simps)
  hence *: "eventually (\<lambda>n. (1 + x / n) powr n = (1 + x / n) ^ n) at_top"
    apply (rule eventually_elim1)
    by (erule powr_realpow)
  thus ?thesis
    apply (rule Lim_transform_eventually)
    by (rule filterlim_compose [OF exp_limit' filterlim_real_sequentially])
qed


(** Inequality for difference of complex products. **)
(* probably generalizes to real_normed_algebra_1,(comm_)monoid_mult *)
lemma complex_prod_diff [rule_format]:
  fixes 
    z :: "nat \<Rightarrow> complex" and
    w :: "nat \<Rightarrow> complex" and
    m :: nat
  shows "(\<forall> i < m. cmod (z i) \<le> 1) & (\<forall> i < m. cmod (w i) \<le> 1) \<longrightarrow> 
    norm ((\<Prod> i < m. z i) - (\<Prod> i < m. w i)) \<le> (\<Sum> i < m. cmod (z i - w i))" 
      (is "?H1 m & ?H2 m \<longrightarrow> ?P m") 
proof (induct m)
  let "?Q m" = "?H1 m & ?H2 m \<longrightarrow> ?P m"
  show "?Q 0" by auto
next
  let "?Q m" = "?H1 m & ?H2 m \<longrightarrow> ?P m"
  fix m
  assume ih: "?Q m"
  show "?Q (Suc m)"
  proof (clarify)
    assume zbnd: "?H1 (Suc m)"
       and wbnd : "?H2 (Suc m)"
    with ih have ih1: "?P m" by auto
    show "?P (Suc m)"
    proof -
      have "cmod ((\<Prod> i < Suc m. z i) - (\<Prod> i < Suc m. w i)) = 
        cmod ((\<Prod> i < Suc m. z i) - w m * (\<Prod> i < m. z i) + w m *
        (\<Prod> i < m. z i) - (\<Prod> i < Suc m. w i))"
        by auto
      also have "... = cmod ((\<Prod> i < m. z i) * (z m - w m) + 
        ((\<Prod> i < m. z i) - (\<Prod> i < m. w i)) * w m)"
        (is "?lhs = cmod (?t1 + ?t2)")
        by (auto simp add: field_simps)
      also have "... \<le> cmod(?t1) + cmod(?t2)"
        by (rule norm_triangle_ineq)
      also have "cmod(?t1) \<le> cmod(z m - w m)"
        apply (subst norm_mult)
        apply (rule mult_left_le_one_le, auto)
        apply (subst norm_setprod)
        apply (subst setprod_1 [symmetric])
        apply simp
        apply (rule order_trans)
        apply (rule setprod_mono[of "{..<m}" "\<lambda>i. cmod (z i)" "\<lambda>i. 1"])
        apply (auto intro: zbnd [rule_format])
        done
      also have "cmod(?t2) \<le> cmod((\<Prod> i < m. z i) - (\<Prod> i < m. w i))"
        apply (subst norm_mult)
        apply (rule mult_right_le_one_le)
        apply (auto simp add: wbnd)
        done
      also have "... \<le> (\<Sum> i < m. cmod (z i - w i))"
        by (rule ih1)
      finally show ?thesis
        by (auto simp add: add_ac)
    qed
  qed
qed

lemma complex_power_diff [rule_format]: 
  fixes z w :: complex and m :: nat
  assumes "cmod z \<le> 1" "cmod w \<le> 1"
  shows "cmod (z^m - w^m) \<le> m * cmod (z - w)"
proof -
  have "cmod (z^m - w^m) = cmod ((\<Prod> i < m. z) - (\<Prod> i < m. w))" by (simp add: setprod_constant)
  also have "\<dots> \<le> (\<Sum> i < m. cmod (z - w))" by (intro complex_prod_diff, simp add: assms)
  also have "\<dots> = m * cmod (z - w)" by (simp add: real_of_nat_def)
  finally show ?thesis .
qed

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
        (density lborel standard_normal_density)"

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
  have "\<And>t. (\<lambda>n. \<phi> n t) ----> char standard_normal_distribution t"
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
    thus "(\<lambda>n. \<phi> n t) ----> char standard_normal_distribution t"
      by (subst char_standard_normal_distribution)
  qed
  thus ?thesis
    apply (intro levy_continuity)
    apply (rule real_distribution_distr [OF S_rv])
    unfolding real_distribution_def real_distribution_axioms_def
    apply (simp add: prob_space_normal_density)
    unfolding \<phi>_def S'_def by -
qed

end

