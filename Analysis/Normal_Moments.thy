(* 
Normal_Moments
Author: Jeremy Avigad

The moments of the normal distribution.
*)

theory Normal_Moments

imports Normal_Distribution Interval_Integral

begin

(* extracted from Normal_Distribution *)
lemma integral_exp_neg_x_squared: 
  shows
    "set_integrable lborel {0..} (\<lambda>x. exp (- x\<^sup>2))" and 
    "LBINT x:{0..}. exp (- x\<^sup>2) = sqrt pi / 2"
proof -
  have 1: "(\<integral>\<^sup>+xa. ereal (exp (- xa\<^sup>2)) * indicator {0..} xa \<partial>lborel) = ereal (sqrt pi) / ereal 2"
    apply (subst positive_integral_ereal_indicator_mult)
    apply (subst gaussian_integral_positive[symmetric])
    apply (subst(2) positive_integral_even_function) 
    apply (auto simp: field_simps)
    by (cases "\<integral>\<^sup>+x. ereal (indicator {0..} x * exp (- x\<^sup>2)) \<partial>lborel") auto
  (* TODO: refactor *)
  show "set_integrable lborel {0..} (\<lambda>x. exp (- x\<^sup>2))"
    apply (rule integrable_if_positive_integral [of _ _ "sqrt pi / 2"])
    apply (subst positive_integral_ereal_indicator_mult[symmetric])
    apply (subst 1)
    by (auto split:split_indicator)
  show "LBINT x:{0..}. exp (- x\<^sup>2) = sqrt pi / 2"
    apply (rule lebesgue_integral_eq_positive_integral)
    apply (subst positive_integral_ereal_indicator_mult[symmetric])
    apply (subst 1)
    by (auto split:split_indicator)
qed

lemma aux1:
  fixes a b :: real and k :: nat
  assumes "a \<le> b"
  shows "LBINT x:{a..b}. exp (- x\<^sup>2) * (real (k + 1) * x ^ k) =
    exp (- b\<^sup>2) * b ^ (k + 1) -
    exp (- a\<^sup>2) * a ^ (k + 1) -
      (LBINT x:{a..b}. - 2 * x * exp (- x\<^sup>2) * x ^ (k + 1))"
proof -
  let ?g = "\<lambda>x :: real. (k + 1) * x^k"
  let ?G = "\<lambda>x :: real. x^(k + 1)"
  let ?f = "\<lambda>x. - 2 * x * exp (- (x^2))"
  let ?F = "\<lambda>x. exp (- (x^2))"
  from assms show ?thesis
    apply (rule integral_by_parts [of a b ?f ?g ?F ?G])
    apply (auto intro!: DERIV_intros)
    apply (case_tac "k = 0", auto)
    apply (subst mult_assoc)
    by (subst power_Suc2 [symmetric], simp add: real_of_nat_Suc field_simps)
qed

lemma aux2:
  fixes b :: real and k :: nat
  assumes "0 \<le> b"
  shows "(LBINT x:{0..b}. exp (- x\<^sup>2) * x ^ (k + 2)) =
    (k + 1) / 2 * (LBINT x:{0..b}. exp (- x\<^sup>2) * x ^ k) -
    exp (- b\<^sup>2) * b ^ (k + 1) / 2"
proof -
  note aux1 [of 0 b k]
  also have "(LBINT x:{0..b}. exp (- x\<^sup>2) * (real (k + 1) * x ^ k)) = 
      real (k + 1) * (LBINT x:{0..b}. exp (- x\<^sup>2) * x ^ k)"
    apply (subst set_integral_cmult(2) [symmetric])
    apply (rule borel_integrable_atLeastAtMost')
    apply (rule continuous_at_imp_continuous_on)
    by (auto simp add: field_simps)
  also have "(LBINT x:{0..b}. - 2 * x * exp (- x\<^sup>2) * x ^ (k + 1)) =
       -2 * (LBINT x:{0..b}. exp (- x\<^sup>2) * x ^ (k + 2))"
    apply (subst set_integral_cmult(2) [symmetric])
    apply (rule borel_integrable_atLeastAtMost')
    apply (rule continuous_at_imp_continuous_on)
    by (auto simp add: field_simps)
  finally show ?thesis
    by (simp add: field_simps assms)
qed    
    
lemma aux3:
  fixes k :: nat
  shows 
    "set_integrable lborel {0..} (\<lambda>x. exp (- x\<^sup>2) * x ^ (2 * k))" (is "?P k")
  and 
    "(LBINT x:{0..}. exp (- x\<^sup>2) * (x ^ (2 * k))) = (sqrt pi / 2) * 
        (fact (2 * k) / (2^(2 * k) * fact k))" (is "?Q k")
proof (induct k)
  show "?P 0"
    by (auto intro: integral_exp_neg_x_squared)
  show "?Q 0"
    by (auto simp add: integral_exp_neg_x_squared)
next
  fix k
  assume ihP: "?P k" and ihQ: "?Q k"
  let ?f1 = "\<lambda>y::real. LBINT x:{0..y}. exp (- x\<^sup>2) * x ^ (2 * Suc k)"
  let ?f2 = "\<lambda>y::real. LBINT x:{0..y}. exp (- x\<^sup>2) * x ^ (2 * k)"
  let ?f2_lim = "LBINT x:{0..}. exp (- x\<^sup>2) * (x ^ (2 * k))"
  let ?f3 = "\<lambda>y::real. exp (- y\<^sup>2) * y ^ (2 * k + 1) / 2"
  let ?f4 = "\<lambda>y. (2 * k + 1) / 2 * ?f2 y - ?f3 y" 
  have 1: "eventually (\<lambda>y. ?f1 y = ?f4 y) at_top"
    apply (rule eventually_elim1 [OF eventually_ge_at_top [of 0]])
    apply (subgoal_tac "2 * Suc k = 2 * k + 2")
    by (erule ssubst, erule aux2, auto)
  have 2: "(?f2 ---> ?f2_lim) at_top"
  proof -
    have a: "?f2 = (\<lambda>y. LBINT x:{..y}. exp(- x\<^sup>2) * (x ^ (2 * k)) * indicator {0..} x)"
      by (rule ext, rule integral_cong, auto split: split_indicator)
    have b: "(\<dots> ---> (LBINT x:{0..}. exp (- x\<^sup>2) * (x ^ (2 * k)))) at_top"
      by (rule tendsto_integral_at_top, auto, rule ihP)
    show ?thesis by (subst a, rule b)
  qed
  have 3: "(?f3 ---> 0) at_top"
  proof -
    have a: "?f3 = (\<lambda>y :: real. ((y^2)^(k + 1) / exp (y\<^sup>2)) * (1 / (2 * y)))" 
       (is "_ = (\<lambda>y. ?g1 y * ?g2 y)")
      by (rule ext) (simp add: field_simps power2_eq_square exp_minus inverse_eq_divide power_mult
        power_mult_distrib)
    have b: "(?g1 ---> 0) at_top"
      apply (rule filterlim_compose) back
      apply (rule tendsto_power_div_exp_0)
      by (rule filterlim_power2_at_top)
    have c: "(?g2 ---> 0) at_top"
      apply (rule tendsto_divide_0, auto)
      apply (rule filterlim_mono [OF _ at_top_le_at_infinity order_refl])
      by (rule filterlim_tendsto_pos_mult_at_top, auto, rule filterlim_ident)
    show ?thesis
      by (subst a, rule tendsto_mult_zero [OF b c])
  qed
  have 4: "(?f1 ---> (2 * k + 1) / 2 * ?f2_lim) at_top"
    apply (subst filterlim_cong [OF refl refl 1])
    apply (subgoal_tac "(2 * k + 1) / 2 * ?f2_lim = (2 * k + 1) / 2 * ?f2_lim - 0")
    apply (erule ssubst)
    apply (rule tendsto_diff [OF _ 3])
    by (rule tendsto_mult [OF _ 2], auto)
  let ?f0 = "(\<lambda>x. exp (- x\<^sup>2) * x ^ (2 * Suc k) * indicator {0..} (x::real))"
  have 5: "(\<lambda>y. LBINT x:{..y}. ?f0 x) = ?f1"
    by (rule ext, rule integral_cong) (auto split: split_indicator)
  have 6: "AE x in lborel. 0 \<le> ?f0 x"
    apply (rule AE_I2)
    apply (rule mult_nonneg_nonneg)+
    by (auto simp del: power_Suc intro!: zero_le_even_power)
  have 7: "((\<lambda>y. LBINT x:{..y}. ?f0 x) ---> (2 * k + 1) / 2 * ?f2_lim) at_top"
    by (subst 5, rule 4)
  {
    fix y 
    have "set_integrable lborel {..y} (\<lambda>x. exp (- x\<^sup>2) *
                x ^ (2 * Suc k) *
                indicator {0..} x)" 
    proof -
      have "(\<lambda>x. exp (- x\<^sup>2) * x ^ (2 * Suc k) * indicator {0..} x * indicator {..y} x) =
            (\<lambda>x. exp (- x\<^sup>2) * x ^ (2 * Suc k) * indicator {0..y} x)" 
        by (rule ext, simp split: split_indicator)
      thus ?thesis
        apply (elim ssubst)
        by (rule borel_integrable_atLeastAtMost, auto)
    qed
  } note 8 = this
  show "?P (Suc k)"
    by (rule integral_monotone_convergence_at_top [OF _ 6 _ 8 7], auto)
  have 9: "(LBINT x. ?f0 x) = (2 * k + 1) / 2 * ?f2_lim"
    by (rule integral_monotone_convergence_at_top [OF _ 6 _ 8 7], auto)
  also have "\<dots> = (2 * k + 1) / 2 * ((sqrt pi / 2) * (fact (2 * k) / (2^(2 * k) * fact k)))"
    by (subst ihQ, rule refl)
  (* Q: could this calculation be done automatically? *)
  also have "\<dots> = sqrt pi / 2 * ((2 * k + 1) / 2 * (fact (2 * k) / (2^(2 * k) * fact k)))"
    by auto
  also have "(2 * k + 1) / 2 * (fact (2 * k) / (2^(2 * k) * fact k)) = 
      (2 * k + 1) * fact (2 * k) / (2^(2 * k + 1) * fact k)"
    apply (subst times_divide_times_eq)
    apply (subst real_of_nat_mult)+
    by simp
  also have "(2 * k + 1) * fact (2 * k) = fact (2 * k + 1)"
    by auto
  also have "fact (2 * k + 1) = fact (2 * k + 2) / (2 * k + 2)"
    by (simp add: field_simps real_of_nat_Suc)
  finally show "?Q (Suc k)" by (simp add: field_simps real_of_nat_Suc)
qed

end
