(*
Theory: Central_Limit_Theorem.thy
Authors: Jeremy Avigad, Luke Serafin
*)

theory Central_Limit_Theorem

imports Library_Misc Weak_Convergence Characteristic_Functions Normal_Distribution

begin

(* it is funny that this isn't in the library! *)
lemma exp_limit:
  fixes x :: real
  shows "((\<lambda>y.(1 + x * y) powr (1 / y)) ---> exp x) (at_right 0)"
proof -
  have *: "(at_right 0) \<le> (at (0::real))"
    by (subst at_eq_sup_left_right, auto)
  have **: "eventually (\<lambda>y. 0 < 1 + x * y) (at_right 0)"
    apply (case_tac "x = 0")
    apply auto
    apply (subst eventually_at_right)
    apply (rule_tac x = "1 / abs x" in exI)
    apply (auto simp add: field_simps)
    apply (case_tac "x >= 0")
    apply (auto simp add: field_simps)
    apply (rule add_pos_nonneg, auto)
    by (rule mult_nonneg_nonneg, auto)
  have ***: "eventually (\<lambda>y. y > (0::real)) (at_right 0)"
    by (subst eventually_at_right, auto intro: gt_ex)
  have ****: "eventually (\<lambda>y. exp (ln ((1 + x * y) powr (1 / y))) =
         (1 + x * y) powr (1 / y)) (at_right 0)"
    apply (rule eventually_elim1 [OF eventually_conj [OF ** ***]])
    by (rule exp_ln, auto)
  have 1: "eventually (\<lambda>y. ln ((1 + x * y) powr (1 / y)) =
         ln (1 + x * y) / y) (at_right 0)"
    apply (rule eventually_elim1 [OF eventually_conj [OF ** ***]])
    apply (subst ln_powr)
    apply (case_tac "x = 0")
    by auto
  have a: " ln -- 1 --> ln 1"
    by (subst isCont_def [symmetric], auto intro!: isCont_ln)
  have "((\<lambda>y. ln (1 + x * y)) ---> ln 1) (at_right 0)"
    apply (rule tendsto_mono [OF *])
    apply (rule tendsto_compose [OF a])
    apply (rule tendsto_const_add [of "-1"], simp)
    by (rule tendsto_mult_right_zero, rule tendsto_ident_at)
  hence 2: "((\<lambda>y. ln (1 + x * y)) ---> 0) (at_right 0)" by simp
  have 3: " ((\<lambda>x. x) ---> 0) (at_right 0)" by (rule tendsto_ident_at)
  have 4: "eventually (\<lambda>y. y \<noteq> 0) (at_right 0)"
    by (simp add: eventually_at_filter)
  have 5: "eventually (\<lambda>y. 1 \<noteq> (0 :: real)) (at_right 0)" by (rule always_eventually, auto)
  have 6: "eventually (\<lambda>z. ((\<lambda>y. ln (1 + x * y)) has_real_derivative
            inverse (1 + x * z) * x) (at z)) (at_right 0)"
    apply (rule eventually_elim1 [OF **])
    apply (rule DERIV_chain') back
    by (auto intro!: derivative_eq_intros simp add: divide_inverse)
  have "((\<lambda>y. inverse (1 + x * y) * x) ---> inverse (1 + x * 0) * x) (at_right 0)"
    apply (rule tendsto_mono [OF *])
    apply (subst isCont_def [symmetric])
    by auto
  hence 7: "((\<lambda>y. inverse (1 + x * y) * x) ---> x) (at_right 0)" by simp
  have "((\<lambda>y. ln ((1 + x * y) powr (1 / y))) ---> x) (at_right 0)"
    apply (subst filterlim_cong [OF refl refl 1])
    apply (rule lhopital_right [OF 2 3 4 5 6])
    apply auto
    by (rule 7)
  hence "((\<lambda>y. exp (ln ((1 + x * y) powr (1 / y)))) ---> exp x) (at_right 0)"
    by (rule tendsto_exp)
  thus "((\<lambda>y.(1 + x * y) powr (1 / y)) ---> exp x) (at_right 0)"
    by (rule Lim_transform_eventually [OF ****])
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
  have "eventually (\<lambda>n :: nat. 0 < 1 + x / real n) at_top"

    sorry
  hence *: "eventually (\<lambda>n. (1 + x / n) powr n = (1 + x / n) ^ n) at_top"
    apply (rule eventually_elim1)
    by (erule powr_realpow)
  thus ?thesis
    apply (rule Lim_transform_eventually)
    by (rule filterlim_compose [OF exp_limit' filterlim_real_sequentially])
qed






    
    


    
  have "((\<lambda>y. (1 + x * y) powr (1 / y)) ---> exp x) (at_right 0)"
    sorry

  show ?thesis
    sorry
qed


lemma exp_limit:
  fixes x :: real
  shows 



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

(* for sanity, this is a special case of equation_26p5b *)
lemma (in real_distribution) aux:
  fixes t
  assumes
    integrable_1: "integrable M (\<lambda>x. x)" and
    integral_1: "expectation (\<lambda>x. x) = 0" and
    integrable_2: "integrable M (\<lambda>x. x^2)" and
    integral_2: "variance (\<lambda>x. x) = \<sigma>2"
  shows 
    "cmod (char M t - (1 - t^2 * \<sigma>2 / 2)) \<le>  t^2 * \<sigma>2"
proof -
  note real_distribution.equation_26p5b [of M 2 t]
  have [simp]: "prob UNIV = 1" by (metis prob_space space_eq_univ)
  have 0: "ii * t * ii * t = - t * t"
    by (metis comm_semiring_1_class.normalizing_semiring_rules(7) 
      complex_i_mult_minus of_real_minus of_real_mult)
  from integral_2 have [simp]: "expectation (\<lambda>x. x * x) = \<sigma>2" 
    by (simp add: integral_1 numeral_eq_Suc)
  {
    fix k :: nat
    assume "k \<le> 2"
    hence "k = 0 \<or> k = 1 \<or> k = 2" by auto
    with assms have "integrable M (\<lambda>x. x^k)" by auto
  } note 1 = this 
  have "cmod (char M t - (\<Sum>k\<le>2. (\<i> * t) ^ k / (int (fact k)) * expectation (\<lambda>x. x ^ k))) \<le> 
      2 * (abs t)\<^sup>2 / fact (2::nat) * expectation (\<lambda>x. (abs x)^2)"
    by (rule equation_26p5b [OF 1], simp)
  also have "(\<Sum>k\<le>2. (\<i> * t) ^ k / (int (fact k)) * expectation (\<lambda>x. x ^ k)) = 1 - t^2 * \<sigma>2 / 2"
    apply (simp add: numeral_eq_Suc real_of_nat_Suc integral_1 mult_assoc [symmetric])
    by (subst 0, simp add: of_real_mult)
  also have "2 * (abs t)\<^sup>2 / fact (2::nat) * expectation (\<lambda>x. (abs x)^2) = t^2 * \<sigma>2"
    by (simp add: numeral_eq_Suc integral_2)
  finally show ?thesis .
qed

lemma (in prob_space) variance_mean_zero: "expectation X = 0 \<Longrightarrow>
    variance X = expectation (\<lambda>x. (X x)^2)"
by auto

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
    "cmod (char \<mu> t - (1 - t^2 * \<sigma>2 / 2)) \<le>  t^2 * \<sigma>2"

  apply (subst \<mu>_def)
  apply (rule real_distribution.aux)
  unfolding real_distribution_def real_distribution_axioms_def apply auto
  apply (rule prob_space_distr)
using var_X by (auto simp add: integrable_distr_eq integral_distr)


theorem (in real_distribution) central_limit_theorem:
  fixes 
    X :: "nat \<Rightarrow> real \<Rightarrow> real" and
    \<mu> :: "real measure" and
    \<sigma>2 :: real and
    S :: "nat \<Rightarrow> real \<Rightarrow> real"
  assumes
    X_seq_meas [simp]: "\<And>n. X n \<in> measurable M borel" (* implied by indep_vars? *) and
    X_seq_indep: "indep_vars (\<lambda>i. borel) X UNIV" and
    X_integrable: "\<And>n. integrable M (X n)" and
    X_seq_mean_0: "\<And>n. expectation (X n) = 0" and
    sigma_pos: "\<sigma>2 > 0" (* eliminate this *) and 
    X_square_integrable: "\<And>n. integrable M (\<lambda>x. (X n x)\<^sup>2)" and
    X_seq_variance: "\<And>n. variance (X n) = \<sigma>2" and
    X_seq_distrib: "\<And>n. distr M borel (X n) = \<mu>"
  defines
    "S n x \<equiv> (\<Sum> i < n. X i x) / sqrt (\<sigma>2 * n)"
  shows
    "weak_conv_m (\<lambda>n. distr M borel (\<lambda>x. S n x)) 
       (density lborel standard_normal_density)"

proof -
  def \<phi> \<equiv> "\<lambda>n. char (distr M borel (\<lambda>x. S n x))"
  def \<psi> \<equiv> "\<lambda>n i. char (distr M borel (\<lambda>x. X i x / sqrt (\<sigma>2 * n)))"
  def \<psi>' \<equiv> "\<lambda>n t. char \<mu> (t / sqrt (\<sigma>2 * n))"
  have *: "\<And>n i t. \<psi> n i t = \<psi>' n t"
    unfolding \<psi>_def \<psi>'_def char_def apply auto
      apply (subst X_seq_distrib [symmetric])
      apply (subst complex_integral_distr, auto)
      apply (rule borel_measurable_divide, auto)
      by (subst complex_integral_distr, auto)
  have [simp]: "\<And>i. expectation (\<lambda>x. (X i x)\<^sup>2) = \<sigma>2" 
    using X_seq_variance by (simp add: X_seq_mean_0)
  {
    fix n i :: nat and t :: real
    have 1: "\<psi> n i t = char (distr M borel (\<lambda>x. X i x)) (t / sqrt (\<sigma>2 * n))"
      unfolding char_def \<psi>_def apply auto
      apply (subst complex_integral_distr, auto)
      apply (rule borel_measurable_divide, auto)
      by (subst complex_integral_distr, auto)
    have "cmod (\<psi> n i t - (1 - (t / sqrt (\<sigma>2 * n))^2 * \<sigma>2 / 2)) \<le> (t / sqrt (\<sigma>2 * n))^2 * \<sigma>2"
      apply (subst 1)
      by (rule aux' [of "X i"], auto simp add: assms)
    also have "(t / sqrt (\<sigma>2 * n))^2 * \<sigma>2 = t^2 / n"
      using sigma_pos apply (simp add: power_divide)
      by (subst real_sqrt_pow2, rule mult_nonneg_nonneg, auto)
    also have "(t / sqrt (\<sigma>2 * n))^2 * \<sigma>2 = t^2 / n"  (* factor this! *)
      using sigma_pos apply (simp add: power_divide)
      by (subst real_sqrt_pow2, rule mult_nonneg_nonneg, auto)
    also have "t^2 / n / 2 = t^2 / (2 * n)" by simp
    also note * [of n i t]
    finally have "cmod (\<psi>' n t - (1 - t^2 / (2 * n))) \<le> t^2 / n" .
  } note ** = this

  {
    fix n :: nat and t :: real
    have 1: "S n = (\<lambda>x. (\<Sum> i < n. X i x / sqrt (\<sigma>2 * n)))" 
      by (rule ext, simp add: S_def setsum_divide_distrib)
    have "\<phi> n t = (\<Prod> i < n. \<psi> n i t)"
      unfolding \<phi>_def \<psi>_def apply (subst 1)
      apply (rule char_distr_setsum)
      by (rule indep_vars_compose2 [OF X_seq_indep], auto)
    also have "\<dots> = (\<psi>' n t)^n"
      by (auto simp add: * setprod_constant)
    finally have 2: "\<phi> n t =(\<psi>' n t)^n" .
    have "cmod (\<phi> n t - (complex_of_real (1 - t^2 / (2 * n)))^n) \<le> 
         n * cmod (\<psi>' n t - (complex_of_real (1 - t^2 / (2 * n))))"
      apply (subst 2)
      apply (rule complex_power_diff)
      sorry
    also have "\<dots> \<le> n * (t^2 / n)"
      apply (rule mult_left_mono)
      by (rule **, simp)
    also have "\<dots> = t^2" 
      apply (simp add: field_simps)
      sorry
    finally have "cmod (\<phi> n t - (1 - t^2 / (2 * n))^n) \<le> t^2" 
      by simp
  } note 1 = this

  show ?thesis
    sorry
qed

