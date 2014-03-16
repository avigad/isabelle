(* 
Normal_Moments
Author: Jeremy Avigad

The moments of the normal distribution.

TODO: Merge this file with Normal_Distribution.

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
  fixes b :: real and k :: nat
  assumes "0 \<le> b"
  shows "(LBINT x:{0..b}. exp (- x\<^sup>2) * x ^ (k + 2)) =
    (k + 1) / 2 * (LBINT x:{0..b}. exp (- x\<^sup>2) * x ^ k) - exp (- b\<^sup>2) * b ^ (k + 1) / 2"
proof -
  {
    fix a b :: real and k :: nat
    assume "a \<le> b"    let ?g = "\<lambda>x :: real. (k + 1) * x^k"
    let ?G = "\<lambda>x :: real. x^(k + 1)"
    let ?f = "\<lambda>x. - 2 * x * exp (- (x^2))"
    let ?F = "\<lambda>x. exp (- (x^2))"
    have "LBINT x:{a..b}. exp (- x\<^sup>2) * (real (k + 1) * x ^ k) =
        exp (- b\<^sup>2) * b ^ (k + 1) - exp (- a\<^sup>2) * a ^ (k + 1) -
        (LBINT x:{a..b}. - 2 * x * exp (- x\<^sup>2) * x ^ (k + 1))"
      apply (rule integral_by_parts [of a b ?f ?g ?F ?G])
      using `a \<le> b` apply (auto intro!: DERIV_intros)
      apply (case_tac "k = 0", auto)
      apply (subst mult_assoc)
      by (subst power_Suc2 [symmetric], simp add: real_of_nat_Suc field_simps)
  }
  note this [of 0 b k]
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

lemma aux2:
  fixes k :: nat
  assumes 
    "set_integrable lborel {0..} (\<lambda>x. exp (- x\<^sup>2) * x ^ k)"
  shows
    "set_integrable lborel {0..} (\<lambda>x. exp (- x\<^sup>2) * x ^ (k + 2))"
  and 
    "(LBINT x:{0..}. exp (- x\<^sup>2) * x ^ (k + 2)) = (k + 1) / 2 * (LBINT x:{0..}. exp (- x\<^sup>2) * x ^ k)"
proof -
  let ?f1 = "\<lambda>y::real. LBINT x:{0..y}. exp (- x\<^sup>2) * x ^ (k + 2)"
  let ?f2 = "\<lambda>y::real. LBINT x:{0..y}. exp (- x\<^sup>2) * x ^ k"
  let ?f2_lim = "LBINT x:{0..}. exp (- x\<^sup>2) * (x ^ k)"
  let ?f3 = "\<lambda>y::real. exp (- y\<^sup>2) * y ^ (k + 1) / 2"
  let ?f4 = "\<lambda>y. (k + 1) / 2 * ?f2 y - ?f3 y" 
  have 1: "eventually (\<lambda>y. ?f1 y = ?f4 y) at_top"
    by (rule eventually_elim1 [OF eventually_ge_at_top [of 0]], rule aux1, auto)
  have 2: "(?f2 ---> ?f2_lim) at_top"
  proof -
    have a: "?f2 = (\<lambda>y. LBINT x:{..y}. exp(- x\<^sup>2) * (x ^ k) * indicator {0..} x)"
      by (rule ext, rule integral_cong, auto split: split_indicator)
    have b: "(\<dots> ---> (LBINT x:{0..}. exp (- x\<^sup>2) * (x ^ k))) at_top"
      by (rule tendsto_integral_at_top, auto, rule assms)
    show ?thesis by (subst a, rule b)
  qed
  have 3: "(?f3 ---> 0) at_top"
  proof -
    let ?f5 = "\<lambda>k :: nat. \<lambda>y :: real. (y^2)^(k + 1) / exp (y\<^sup>2)"
    have *: "\<And>k. (?f5 k ---> 0) at_top"
      apply (rule filterlim_compose) back
      apply (rule tendsto_power_div_exp_0)
      by (rule filterlim_power2_at_top)
    let ?f6 = "(\<lambda>y :: real. exp (- y\<^sup>2) * y ^ (k + 1))"
    have **: "(?f6 ---> 0) at_top"
    proof (cases "even k")
      assume "even k"
      hence "\<exists>k'. k = 2 * k'" by (subst (asm) even_mult_two_ex)
      then obtain k' where **: "k = 2 * k'" ..     
      have a: "?f6 = (\<lambda>y. ?f5 k' y * (1 / y))" 
        by (subst **, rule ext) (simp add: field_simps power2_eq_square exp_minus inverse_eq_divide 
          power_mult power_mult_distrib)
      show ?thesis
        apply (subst a, rule tendsto_mult_zero [OF *])
        apply (rule tendsto_divide_0, auto)
        by (rule filterlim_mono [OF _ at_top_le_at_infinity order_refl], rule filterlim_ident)
    next 
      assume "odd k"
      hence "\<exists>k'. k = Suc (2 * k')" by (subst (asm) odd_Suc_mult_two_ex)
      then obtain k' where **: "k = Suc (2 * k')" ..     
      have a: "?f6 = ?f5 k'" 
        by (subst **, rule ext) (simp add: field_simps power2_eq_square exp_minus inverse_eq_divide 
          power_mult power_mult_distrib)
      show ?thesis
        by (subst a, rule *)
    qed
    show ?thesis
      by (subst divide_real_def, rule tendsto_mult_left_zero [OF **])
  qed
  have 4: "(?f1 ---> (k + 1) / 2 * ?f2_lim) at_top"
    apply (subst filterlim_cong [OF refl refl 1])
    apply (subgoal_tac "(k + 1) / 2 * ?f2_lim = (k + 1) / 2 * ?f2_lim - 0")
    apply (erule ssubst)
    apply (rule tendsto_diff [OF _ 3])
    by (rule tendsto_mult [OF _ 2], auto)
  let ?f7 = "(\<lambda>x. exp (- x\<^sup>2) * x ^ (k + 2) * indicator {0..} (x::real))"
  have 5: "(\<lambda>y. LBINT x:{..y}. ?f7 x) = ?f1"
    by (rule ext, rule integral_cong) (auto split: split_indicator)
  have 6: "AE x in lborel. 0 \<le> ?f7 x"
    apply (rule AE_I2, subst mult_assoc, rule mult_nonneg_nonneg)
    by (auto split: split_indicator simp del: power_Suc intro!: zero_le_even_power)
  have 7: "\<And>y. set_integrable lborel {..y} ?f7"
  proof -
    fix y :: real
    have "(\<lambda>x. exp (- x\<^sup>2) * x ^ (k + 2) * indicator {0..} x * indicator {..y} x) =
          (\<lambda>x. exp (- x\<^sup>2) * x ^ (k + 2) * indicator {0..y} x)" 
      by (rule ext, simp split: split_indicator)
    thus "set_integrable lborel {..y} (\<lambda>x. exp (- x\<^sup>2) * x ^ (k + 2) * indicator {0..} x)" 
      apply (elim ssubst)
      by (rule borel_integrable_atLeastAtMost, auto)
  qed
  have 8: "((\<lambda>y. LBINT x:{..y}. ?f7 x) ---> (k + 1) / 2 * ?f2_lim) at_top"
    by (subst 5, rule 4)
  show "set_integrable lborel {0..} (\<lambda>x. exp (- x\<^sup>2) * x ^(k + 2))"
    by (rule integral_monotone_convergence_at_top [OF _ 6 _ 7 8], auto)
  show "(LBINT x:{0..}. exp (- x\<^sup>2) * x ^ (k + 2)) = 
      (k + 1) / 2 * (LBINT x:{0..}. exp (- x\<^sup>2) * x ^ k)"
    by (rule integral_monotone_convergence_at_top [OF _ 6 _ 7 8], auto)
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
  have *: "2 * Suc k = 2 * k + 2" by simp
  show "?P (Suc k)"
    by (subst *, rule aux2 [OF ihP])
  have "(LBINT x:{0..}. exp (- x\<^sup>2) * (x ^ (2 * k + 2)))
      = (2 * k + 1) / 2 * (LBINT x:{0..}. exp (- x\<^sup>2) * (x ^ (2 * k)))"
    by (rule aux2 [OF ihP])
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
