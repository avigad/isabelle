(*
Theory: Levy.thy
Author: Jeremy Avigad

The Levy inversion theorem, and the Levy continuity theorem.
*)

theory Levy

imports Characteristic_Functions Helly_Selection

begin

(* TODO: what to do? this causes problems below, but elsewhere it is needed *)
declare of_real_mult [simp del]

(* 
  The Levy inversion theorem.
*)

(* Actually, this is not needed for us -- but it is useful for other purposes. (See Billingsley.) *)
lemma Levy_Inversion_aux1:
  fixes a b :: real
  assumes "a \<le> b"
  shows "((\<lambda>t. (iexp (-(t * a)) - iexp (-(t * b))) / (ii * t)) ---> b - a) (at 0)"
    (is "(?F ---> _) (at _)")
proof -
  have 1 [rule_format]: "ALL t. t \<noteq> 0 \<longrightarrow> 
      cmod (?F t - (b - a)) \<le> a^2 / 2 * abs t + b^2 / 2 * abs t"
    proof (rule allI, rule impI)
      fix t :: real
      assume "t \<noteq> 0"
      have "cmod (?F t - (b - a)) = cmod (
          (iexp (-(t * a)) - (1 + ii * -(t * a))) / (ii * t) - 
          (iexp (-(t * b)) - (1 + ii * -(t * b))) / (ii * t))"  
             (is "_ = cmod (?one / (ii * t) - ?two / (ii * t))")
        using `t \<noteq> 0` by (intro arg_cong[where f=norm]) (simp add: field_simps of_real_mult)
      also have "\<dots> \<le> cmod (?one / (ii * t)) + cmod (?two / (ii * t))" 
        by (rule norm_triangle_ineq4)
      also have "cmod (?one / (ii * t)) = cmod ?one / abs t"
        by (simp add: norm_divide norm_mult)
      also have "cmod (?two / (ii * t)) = cmod ?two / abs t"
        by (simp add: norm_divide norm_mult)      
      also have "cmod ?one / abs t + cmod ?two / abs t \<le> 
          ((- (a * t))^2 / 2) / abs t + ((- (b * t))^2 / 2) / abs t"
        apply (rule add_mono)
        apply (rule divide_right_mono)
        using equation_26p4a [of "-(t * a)" 1] apply (simp add: field_simps eval_nat_numeral)
        apply force
        apply (rule divide_right_mono)
        using equation_26p4a [of "-(t * b)" 1] apply (simp add: field_simps eval_nat_numeral)
        by force
      also have "\<dots> = a^2 / 2 * abs t + b^2 / 2 * abs t"
        using `t \<noteq> 0` apply (case_tac "t \<ge> 0", simp add: field_simps power2_eq_square)
        using `t \<noteq> 0` by (subst (1 2) abs_of_neg, auto simp add: field_simps power2_eq_square)
      finally show "cmod (?F t - (b - a)) \<le> a^2 / 2 * abs t + b^2 / 2 * abs t" .
    qed
  show ?thesis
    apply (rule LIM_zero_cancel)
    apply (rule tendsto_norm_zero_cancel)
    apply (rule real_LIM_sandwich_zero [OF _ _ 1])
    apply (auto intro!: tendsto_eq_intros)
    done
qed

lemma Levy_Inversion_aux2:
  fixes a b t :: real
  assumes "a \<le> b" and "t \<noteq> 0"
  shows "cmod ((iexp (t * b) - iexp (t * a)) / (ii * t)) \<le> b - a"
    (is "?F \<le> _")
proof -
  have "?F = cmod (iexp (t * a) * (iexp (t * (b - a)) - 1) / (ii * t))"
    using `t \<noteq> 0` by (intro arg_cong[where f=norm]) (simp add: field_simps exp_diff exp_minus)
  also have "\<dots> = cmod (iexp (t * (b - a)) - 1) / abs t"
    apply (subst norm_divide)
    apply (subst norm_mult)
    apply (subst cmod_iexp)
    using `t \<noteq> 0` by (simp add: complex_eq_iff norm_mult)
  also have "\<dots> \<le> abs (t * (b - a)) / abs t"
    apply (rule divide_right_mono)
    using equation_26p4a [of "t * (b - a)" 0] apply (simp add: field_simps eval_nat_numeral)
    by force
  also have "\<dots> = b - a"
    using assms by (auto simp add: abs_mult) 
  finally show ?thesis .
qed

(* TODO: refactor! *)
theorem Levy_Inversion:
  fixes M :: "real measure"
  and a b :: real
  assumes "a \<le> b"
  defines "\<mu> \<equiv> measure M" and "\<phi> \<equiv> char M"
  assumes "real_distribution M"
  and "\<mu> {a} = 0" and "\<mu> {b} = 0"
  shows
  "((\<lambda>T :: nat. 1 / (2 * pi) * (CLBINT t=-T..T. (iexp (-(t * a)) -
  iexp (-(t * b))) / (ii * t) * \<phi> t)) ---> \<mu> {a<..b}) at_top"
  (is "((\<lambda>T :: nat. 1 / (2 * pi) * (CLBINT t=-T..T. ?F t * \<phi> t)) ---> 
      of_real (\<mu> {a<..b})) at_top")
  proof -
    interpret M: real_distribution M by (rule assms)
    interpret P!: pair_sigma_finite lborel M ..
    from iSi_bounded obtain B where Bprop: "\<And>T. abs (Si T) \<le> B" by auto
    from Bprop [of 0] have [simp]: "B \<ge> 0" by auto
    let ?f = "\<lambda>t x :: real. (iexp (t * (x - a)) - iexp(t * (x - b))) / (ii * t)"
    {
      fix T :: real
      assume "T \<ge> 0"
      let ?f' = "\<lambda>(t, x). indicator {-T<..<T} t *\<^sub>R ?f t x"
      {
        fix x
        have 1: "\<And>u v. u \<le> v \<Longrightarrow> complex_interval_lebesgue_integrable lborel
            (ereal u) (ereal v) (\<lambda>t. ?f t x)"
          apply (simp add: interval_lebesgue_integrable_def del: times_divide_eq_left)
          apply (intro integrableI_bounded_set_indicator[where B="b - a"])
          apply auto
          apply (rule AE_I [of _ _ "{0}"], clarify)
          by (rule order_trans, rule Levy_Inversion_aux2, auto simp add: assms)
        have 2: "\<And>u v. u \<le> v \<Longrightarrow> complex_interval_lebesgue_integrable lborel
            (ereal u) (ereal v) (\<lambda>t. ?f (-t) x)"
          apply (simp add: interval_lebesgue_integrable_def del: mult_minus_left)
          apply (rule integrableI_bounded_set_indicator [where B="b - a"])
          apply (auto simp del: mult_minus_left simp add: minus_mult_commute)
          apply (subst (2) minus_diff_eq[symmetric])
          unfolding divide_minus_left norm_minus_cancel
          apply (rule AE_I [of _ _ "{0}"], clarify)
          apply (rule order_trans)
          apply (rule Levy_Inversion_aux2)
          apply (auto simp add: assms)
          done
        have "(CLBINT t. ?f' (t, x)) = (CLBINT t=-T..T. ?f t x)"
          using `T \<ge> 0` by (simp add: interval_lebesgue_integral_def)
        also have "\<dots> = (CLBINT t=-T..(0 :: real). ?f t x) + (CLBINT t=(0 :: real)..T. ?f t x)"
            (is "_ = _ + ?t")
          apply (subst interval_integral_sum[symmetric])
          using `T \<ge> 0` apply (subst min_absorb1, auto)
          apply (subst max_absorb2, auto)+
          by (rule 1, auto)
        also have "(CLBINT t=-T..(0 :: real). ?f t x) = (CLBINT t=(0::real)..T. ?f (-t) x)"
          by (subst interval_integral_reflect) auto
        also have "\<dots> + ?t = (CLBINT t=(0::real)..T. ?f (-t) x + ?f t x)"
          apply (rule interval_lebesgue_integral_add(2) [symmetric])
          apply (rule 2, rule `T \<ge> 0`)
          by (rule 1, rule `T \<ge> 0`)
        also have "\<dots> = (CLBINT t=(0::real)..T. ((iexp(t * (x - a)) - iexp (-(t * (x - a)))) -  
            (iexp(t * (x - b)) - iexp (-(t * (x - b))))) / (ii * t))"
          using `T \<ge> 0` by (intro interval_integral_cong) (auto simp add: divide_simps)
        also have "\<dots> = (CLBINT t=(0::real)..T. complex_of_real(
            2 * (sin (t * (x - a)) / t) - 2 * (sin (t * (x - b)) / t)))"
          apply (rule interval_integral_cong)
          using `T \<ge> 0`
          apply (simp add: field_simps cis.ctr Im_divide Re_divide expi_def complex_eq_iff)
          unfolding minus_diff_eq[symmetric, of "y * x" "y * a" for y a] sin_minus cos_minus
          apply (simp add: field_simps power2_eq_square)
          done
        also have "\<dots> = complex_of_real (LBINT t=(0::real)..T. 
            2 * (sin (t * (x - a)) / t) - 2 * (sin (t * (x - b)) / t))"
          by (rule interval_lebesgue_integral_of_real)
        also have "\<dots> = complex_of_real (2 * (sgn (x - a) * Si (T * abs (x - a)) -
            sgn (x - b) * Si (T * abs (x - b))))"
          apply (subst interval_lebesgue_integral_diff)
          apply (rule interval_lebesgue_integrable_mult_right, rule iSi_integrable)+
          apply (subst interval_lebesgue_integral_mult_right)+
          apply (subst Billingsley_26_15, rule `T \<ge> 0`)+
          apply simp
          done
        finally have "(CLBINT t. ?f' (t, x)) = complex_of_real (
            2 * (sgn (x - a) * Si (T * abs (x - a)) - sgn (x - b) * Si (T * abs (x - b))))" .
      } note main_eq = this
      have "(CLBINT t=-T..T. ?F t * \<phi> t) = 
        (CLBINT t. (CLINT x | M. ?F t * iexp (t * x) * indicator {-T<..<T} t))"
        using `T \<ge> 0` unfolding \<phi>_def char_def interval_lebesgue_integral_def
        apply (simp)
        apply (rule integral_cong, auto split: split_indicator)
        done
      also have "\<dots> = (CLBINT t. (CLINT x | M. ?f' (t, x)))"
        apply (rule integral_cong, clarify)+
        by (simp add: field_simps exp_diff exp_minus split: split_indicator)
      also have "\<dots> = (CLINT x | M. (CLBINT t. ?f' (t, x)))"
        apply (rule P.Fubini_integral [symmetric])
        apply (rule integrableI_bounded_set [where A="{- T<..<T} \<times> space M" and B="b - a"])
        apply simp
        apply simp
        apply (subst M.emeasure_pair_measure_Times, insert `0 \<le> T`, auto) []
        apply (rule AE_I [of _ _ "{0} \<times> UNIV"])
        apply auto
        apply (rule ccontr, erule notE)
        apply (rule order_trans)
        apply (rule Levy_Inversion_aux2)
        using `a \<le> b` apply (auto simp: M.emeasure_pair_measure_Times)
        apply (auto intro!: AE_I2 split: split_indicator split_indicator_asm)
        done
      also have "\<dots> = (CLINT x | M. (complex_of_real (2 * (sgn (x - a) * 
           Si (T * abs (x - a)) - sgn (x - b) * Si (T * abs (x - b))))))"
         using main_eq by (intro integral_cong, auto)
      also have "\<dots> = complex_of_real (LINT x | M. (2 * (sgn (x - a) * 
           Si (T * abs (x - a)) - sgn (x - b) * Si (T * abs (x - b)))))"
         by (rule integral_complex_of_real)
      finally have "(CLBINT t=-T..T. ?F t * \<phi> t) = 
          complex_of_real (LINT x | M. (2 * (sgn (x - a) * 
           Si (T * abs (x - a)) - sgn (x - b) * Si (T * abs (x - b)))))" .
    } note main_eq2 = this
    have "(\<lambda>T :: nat. LINT x | M. (2 * (sgn (x - a) * 
           Si (T * abs (x - a)) - sgn (x - b) * Si (T * abs (x - b))))) ----> 
         (LINT x | M. 2 * pi * indicator {a<..b} x)"
    proof (rule integral_dominated_convergence [where w="\<lambda>x. 4 * B"])
      show "integrable M (\<lambda>x. 4 * B)"
        by (rule M.integrable_const_bound [of _ "4 * B"]) auto
    next
      let ?S = "\<lambda>n::nat. \<lambda>x. sgn (x - a) * Si (n * \<bar>x - a\<bar>) - sgn (x - b) * Si (n * \<bar>x - b\<bar>)"
      { fix n x
        have "norm (?S n x) \<le> norm (sgn (x - a) * Si (n * \<bar>x - a\<bar>)) + norm (sgn (x - b) * Si (n * \<bar>x - b\<bar>))"
          by (rule norm_triangle_ineq4)
        also have "\<dots> \<le> B + B"
          using Bprop by (intro add_mono) (auto simp: abs_mult abs_sgn_eq)
        finally have "norm (2 * ?S n x) \<le> 4 * B"
          by simp }
      then show "\<And>n. AE x in M. norm (2 * ?S n x) \<le> 4 * B"
        by auto
      have "AE x in M. x \<noteq> a" "AE x in M. x \<noteq> b"
        using M.prob_eq_0[of "{a}"] M.prob_eq_0[of "{b}"] `\<mu> {a} = 0` `\<mu> {b} = 0` by (auto simp: \<mu>_def)
      then show "AE x in M. (\<lambda>n. 2 * ?S n x) ----> 2 * pi * indicator {a<..b} x"
      proof eventually_elim
        fix x assume x: "x \<noteq> a" "x \<noteq> b"
        then have "(\<lambda>n. 2 * (sgn (x - a) * Si (\<bar>x - a\<bar> * n) - sgn (x - b) * Si (\<bar>x - b\<bar> * n)))
            ----> 2 * (sgn (x - a) * (pi / 2) - sgn (x - b) * (pi / 2))"
          by (intro tendsto_intros filterlim_compose[OF Si_at_top]
              filterlim_tendsto_pos_mult_at_top[OF tendsto_const] filterlim_real_sequentially)
             auto
        also have "(\<lambda>n. 2 * (sgn (x - a) * Si (\<bar>x - a\<bar> * n) - sgn (x - b) * Si (\<bar>x - b\<bar> * n))) = (\<lambda>n. 2 * ?S n x)"
          by (auto simp: mult_ac)
        also have "2 * (sgn (x - a) * (pi / 2) - sgn (x - b) * (pi / 2)) = 2 * pi * indicator {a<..b} x"
          using x `a \<le> b` by (auto split: split_indicator)
        finally show "(\<lambda>n. 2 * ?S n x) ----> 2 * pi * indicator {a<..b} x" .
      qed
    qed simp_all 
    also have "(LINT x | M. 2 * pi * indicator {a<..b} x) = 2 * pi * \<mu> {a<..b}"
      by (simp add: \<mu>_def)
    finally have main3: "(\<lambda>T. LINT x | M. (2 * (sgn (x - a) * 
           Si (T * abs (x - a)) - sgn (x - b) * Si (T * abs (x - b))))) ----> 
         2 * pi * \<mu> {a<..b}" .
  show ?thesis
    apply (subst real_of_int_minus)
    apply (subst real_of_int_of_nat_eq)
    apply (subst main_eq2, force)
    apply (subst of_real_mult [symmetric])
    apply (rule tendsto_of_real)
    apply (rule tendsto_eq_intros)
    apply (rule tendsto_const)
    apply (rule main3)
    apply auto
    done
qed

 
theorem Levy_uniqueness:
  fixes M1 M2 :: "real measure"
  assumes "real_distribution M1" "real_distribution M2" and
    "char M1 = char M2"
  shows "M1 = M2"
proof -
  interpret M1: real_distribution M1 by (rule assms)
  interpret M2: real_distribution M2 by (rule assms)
  have "(cdf M1 ---> 0) at_bot" by (rule M1.cdf_lim_at_bot)
  have "(cdf M2 ---> 0) at_bot" by (rule M2.cdf_lim_at_bot)
  have "countable {x. measure M1 {x} > 0}" by (rule M1.countable_atoms)
  moreover have "countable {x. measure M2 {x} > 0}" by (rule M2.countable_atoms)
  ultimately have "countable ({x. measure M1 {x} > 0} \<union> {x. measure M2 {x} > 0})"
    by (rule countable_Un)
  also have "{x. measure M1 {x} > 0} \<union> {x. measure M2 {x} > 0} = 
      {x. measure M1 {x} \<noteq> 0 \<or> measure M2 {x} \<noteq> 0}"
    apply auto
    by (metis antisym_conv1 measure_nonneg)+
  finally have count: "countable {x. measure M1 {x} \<noteq> 0 \<or> measure M2 {x} \<noteq> 0}" .

  have "cdf M1 = cdf M2"
  proof (rule ext)
    fix x
    from M1.cdf_is_right_cont [of x] have "(cdf M1 ---> cdf M1 x) (at_right x)"
      by (simp add: continuous_within)
    from M2.cdf_is_right_cont [of x] have "(cdf M2 ---> cdf M2 x) (at_right x)"
      by (simp add: continuous_within)
    show "cdf M1 x = cdf M2 x"
    proof (rule real_arbitrarily_close_eq)
      fix \<epsilon> :: real
      assume "\<epsilon> > 0"
      with `(cdf M1 ---> 0) at_bot` have "eventually (\<lambda>y. abs (cdf M1 y) < \<epsilon> / 4) at_bot"
        by (simp only: tendsto_iff dist_real_def diff_0_right)
      hence "\<exists>a. \<forall>a' \<le> a. abs (cdf M1 a') < \<epsilon> / 4" by (simp add: eventually_at_bot_linorder)
      then obtain a1 where a1 [rule_format]: "\<forall>a' \<le> a1. abs (cdf M1 a') < \<epsilon> / 4"  ..
      from `\<epsilon> > 0` `(cdf M2 ---> 0) at_bot` have "eventually (\<lambda>y. abs (cdf M2 y) < \<epsilon> /4) at_bot"
        by (simp only: tendsto_iff dist_real_def diff_0_right)
      hence "\<exists>a. \<forall>a' \<le> a. abs (cdf M2 a') < \<epsilon> / 4" by (simp add: eventually_at_bot_linorder)
      then obtain a2 where a2 [rule_format]: "\<forall>a' \<le> a2. abs (cdf M2 a') < \<epsilon> / 4"  ..
      have "\<exists>a. a \<in> {min (min a1 a2) x - 1<..<min (min a1 a2) x} \<and> 
          a \<notin> {x. measure M1 {x} \<noteq> 0 \<or> measure M2 {x} \<noteq> 0}"
        by (rule real_interval_avoid_countable_set [OF _ count], auto)
      then guess a ..
      hence "a \<le> x" "a \<le> a1" "a \<le> a2" "measure M1 {a} = 0" "measure M2 {a} = 0" by auto

      from `\<epsilon> > 0` `(cdf M1 ---> cdf M1 x) (at_right x)` 
      have "eventually (\<lambda>y. abs (cdf M1 y - cdf M1 x) < \<epsilon> / 4) (at_right x)"
        by (simp only: tendsto_iff dist_real_def)
      hence "\<exists>b. b > x \<and> (\<forall>z. x < z \<and> z < b \<longrightarrow> abs (cdf M1 z - cdf M1 x) < \<epsilon> / 4)"
        by (simp add: eventually_at_right[OF less_add_one])
      then obtain b1 where "b1 > x \<and> (\<forall>z. x < z \<and> z < b1 \<longrightarrow> abs (cdf M1 z - cdf M1 x) < \<epsilon> / 4)" ..
      hence "b1 > x" and b1: "\<And>z. x < z \<Longrightarrow> z < b1 \<Longrightarrow> abs (cdf M1 z - cdf M1 x) < \<epsilon> / 4" by auto
      from `\<epsilon> > 0` `(cdf M2 ---> cdf M2 x) (at_right x)` 
          have "eventually (\<lambda>y. abs (cdf M2 y - cdf M2 x) < \<epsilon> / 4) (at_right x)"
        by (simp only: tendsto_iff dist_real_def)
      hence "\<exists>b. b > x \<and> (\<forall>z. x < z \<and> z < b \<longrightarrow> abs (cdf M2 z - cdf M2 x) < \<epsilon> / 4)"
        by (simp add: eventually_at_right[OF less_add_one])
      then obtain b2 where "b2 > x \<and> (\<forall>z. x < z \<and> z < b2 \<longrightarrow> abs (cdf M2 z - cdf M2 x) < \<epsilon> / 4)" ..
      hence "b2 > x" and b2: "\<And>z. x < z \<Longrightarrow> z < b2 \<Longrightarrow> abs (cdf M2 z - cdf M2 x) < \<epsilon> / 4" by auto
      with `x < b1` `x < b2` have "\<exists>b. b \<in> {x<..<min b1 b2} \<and> 
          b \<notin> {x. measure M1 {x} \<noteq> 0 \<or> measure M2 {x} \<noteq> 0}"
        by (intro real_interval_avoid_countable_set [OF _ count], auto)
      then guess b ..
      hence "x < b" "b < b1" "b < b2" "measure M1 {b} = 0" "measure M2 {b} = 0" by auto
      from `a \<le> x` `x < b` have "a < b" "a \<le> b" by auto

      note Levy_Inversion [OF `a \<le> b` `real_distribution M1` `measure M1 {a} = 0` 
        `measure M1 {b} = 0`]
      moreover note Levy_Inversion [OF `a \<le> b` `real_distribution M2` `measure M2 {a} = 0` 
        `measure M2 {b} = 0`]
      moreover note `char M1 = char M2`
      ultimately have "complex_of_real (measure M1 {a<..b}) = complex_of_real (measure M2 {a<..b})"
        apply (intro LIMSEQ_unique)
        by (assumption, auto)
      hence "measure M1 {a<..b} = measure M2 {a<..b}" by auto
      hence *: "cdf M1 b - cdf M1 a = cdf M2 b - cdf M2 a"
        apply (subst M1.cdf_diff_eq [OF `a < b`])
        by (subst M2.cdf_diff_eq [OF `a < b`])

      have "abs (cdf M1 x - (cdf M1 b - cdf M1 a)) = abs (cdf M1 x - cdf M1 b + cdf M1 a)" by simp
      also have "\<dots> \<le> abs (cdf M1 x - cdf M1 b) + abs (cdf M1 a)" by (rule abs_triangle_ineq)
      also have "\<dots> \<le> \<epsilon> / 4 + \<epsilon> / 4"
        apply (rule add_mono)
        apply (rule less_imp_le, subst abs_minus_commute, rule b1 [OF `x < b` `b < b1`])
        by (rule less_imp_le, rule a1 [OF `a \<le> a1`])
      finally have 1: "abs (cdf M1 x - (cdf M1 b - cdf M1 a)) \<le> \<epsilon> / 2" by simp

      have "abs (cdf M2 x - (cdf M2 b - cdf M2 a)) = abs (cdf M2 x - cdf M2 b + cdf M2 a)" by simp
      also have "\<dots> \<le> abs (cdf M2 x - cdf M2 b) + abs (cdf M2 a)" by (rule abs_triangle_ineq)
      also have "\<dots> \<le> \<epsilon> / 4 + \<epsilon> / 4"
        apply (rule add_mono)
        apply (rule less_imp_le, subst abs_minus_commute, rule b2 [OF `x < b` `b < b2`])
        by (rule less_imp_le, rule a2 [OF `a \<le> a2`])
      finally have 2: "abs (cdf M2 x - (cdf M2 b - cdf M2 a)) \<le> \<epsilon> / 2" by simp

      have "abs (cdf M1 x - cdf M2 x) = abs ((cdf M1 x - (cdf M1 b - cdf M1 a)) - 
          (cdf M2 x - (cdf M2 b - cdf M2 a)))" by (subst *, simp)
      also have "\<dots> \<le> abs (cdf M1 x - (cdf M1 b - cdf M1 a)) + 
          abs (cdf M2 x - (cdf M2 b - cdf M2 a))" by (rule abs_triangle_ineq4)
      also have "\<dots> \<le> \<epsilon> / 2 + \<epsilon> / 2" by (rule add_mono [OF 1 2])
      finally show "abs (cdf M1 x - cdf M2 x) \<le> \<epsilon>" by simp
    qed
  qed
  thus ?thesis
    by (rule cdf_unique [OF `real_distribution M1` `real_distribution M2`])
qed


(*
  The Levy continuity theorem.
*)

theorem levy_continuity1:
  fixes
    M :: "nat \<Rightarrow> real measure" and
    M' :: "real measure"
  assumes 
    real_distr_M : "\<And>n. real_distribution (M n)" and
    real_distr_M': "real_distribution M'" and
    measure_conv: "weak_conv_m M M'"
  shows
    "(\<lambda>n. char (M n) t) ----> char M' t"
  unfolding char_def
  apply (rule weak_conv_imp_integral_bdd_continuous_conv)
  apply fact+
  apply auto
  done

theorem levy_continuity:
  fixes
    M :: "nat \<Rightarrow> real measure" and
    M' :: "real measure"
  assumes 
    real_distr_M : "\<And>n. real_distribution (M n)" and
    real_distr_M': "real_distribution M'" and
    char_conv: "\<And>t. (\<lambda>n. char (M n) t) ----> char M' t" 
  shows "weak_conv_m M M'"
proof -
  interpret Mn: real_distribution "M n" for n by fact
  interpret M': real_distribution M' by fact

  have *: "\<And>u x. u > 0 \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> (CLBINT t:{-u..u}. 1 - iexp (t * x)) = 
      2 * (u  - sin (u * x) / x)"
  proof -
    fix u :: real and x :: real
    assume "u > 0" and "x \<noteq> 0"
    hence "(CLBINT t:{-u..u}. 1 - iexp (t * x)) = (CLBINT t=-u..u. 1 - iexp (t * x))"
      by (subst interval_integral_Icc, auto)
    also have "\<dots> = (CLBINT t=-u..0. 1 - iexp (t * x)) + (CLBINT t=0..u. 1 - iexp (t * x))"
      using `u > 0`
      apply (subst interval_integral_sum)
      apply (simp add: min_absorb1 min_absorb2 max_absorb1 max_absorb2)
      apply (rule interval_integrable_isCont)
      apply auto
      done
    also have "\<dots> = (CLBINT t=ereal 0..u. 1 - iexp (t * -x)) + (CLBINT t=ereal 0..u. 1 - iexp (t * x))"
      apply (subgoal_tac "0 = ereal 0", erule ssubst)
      by (subst interval_integral_reflect, auto)
    also have "\<dots> = (CLBINT t=ereal 0..u. 2 + -2 * cos (t * x))"
      apply (subst interval_lebesgue_integral_add (2) [symmetric])
      apply (rule interval_integrable_isCont, auto)+
      (* TODO: shouldn't of_real_numeral be a simplifier rule? *)
      by (auto simp add: expi_def cis.ctr of_real_numeral of_real_mult)
    also have "\<dots> = 2 * u - 2 * sin (u * x) / x"
      apply simp
      apply (subst interval_lebesgue_integral_diff)
      apply (auto intro!: interval_integrable_isCont simp: interval_lebesgue_integral_of_real)
      apply (subst (2) mult_commute)
      by (subst integral_cos [OF `x \<noteq> 0`], simp add: mult_commute)
    finally show "(CLBINT t:{-u..u}. 1 - iexp (t * x)) = 2 * (u  - sin (u * x) / x)"
      by (simp add: field_simps)
  qed
  have main_bound: "\<And>u n. u > 0 \<Longrightarrow> Re (CLBINT t:{-u..u}. 1 - char (M n) t) \<ge> 
    u * measure (M n) {x. abs x \<ge> 2 / u}"
  proof -
    fix u :: real and n
    assume "u > 0"
    interpret Mn: real_distribution "M n" by (rule assms)
    interpret P: pair_sigma_finite "M n" lborel ..
    (* TODO: put this in the real_distribution locale as a simp rule? *)
    have Mn1 [simp]: "measure (M n) UNIV = 1" by (metis Mn.prob_space Mn.space_eq_univ)
    (* TODO: make this automatic somehow? *)
    have Mn2 [simp]: "\<And>x. complex_integrable (M n) (\<lambda>t. expi (\<i> * complex_of_real (x * t)))"
      by (rule Mn.integrable_const_bound [where B = 1], auto)
    have Mn3: "set_integrable (M n \<Otimes>\<^sub>M lborel) (UNIV \<times> {- u..u}) (\<lambda>a. 1 - expi (\<i> * complex_of_real (snd a * fst a)))"
      apply (rule integrableI_bounded_set_indicator [where B="2"])
      using `0 < u`
      apply (auto simp: lborel.emeasure_pair_measure_Times)
      apply (auto intro!: AE_I2 split: split_indicator)
      by (rule order_trans [OF norm_triangle_ineq4], auto)
    have "(CLBINT t:{-u..u}. 1 - char (M n) t) = 
        (CLBINT t:{-u..u}. (CLINT x | M n. 1 - iexp (t * x)))"
      unfolding char_def by (rule set_lebesgue_integral_cong, auto)
    also have "\<dots> = (CLBINT t. (CLINT x | M n. indicator {-u..u} t *\<^sub>R (1 - iexp (t * x))))"
      by (rule integral_cong) (auto split: split_indicator)
    also have "\<dots> = (CLINT x | M n. (CLBINT t:{-u..u}. 1 - iexp (t * x)))"
      using Mn3 by (subst P.Fubini_integral) (auto simp: indicator_times split_beta')
    also have "\<dots> = (CLINT x | M n. (if x = 0 then 0 else 2 * (u  - sin (u * x) / x)))"
      using `u > 0` by (intro integral_cong, auto simp add: *)
    also have "\<dots> = (LINT x | M n. (if x = 0 then 0 else 2 * (u  - sin (u * x) / x)))"
      by (rule integral_complex_of_real)
    finally have "Re (CLBINT t:{-u..u}. 1 - char (M n) t) = 
       (LINT x | M n. (if x = 0 then 0 else 2 * (u  - sin (u * x) / x)))" by simp
    also have "\<dots> \<ge> (LINT x : {x. abs x \<ge> 2 / u} | M n. u)"
    proof -
      (* TODO: this parallels the computation of the integral above. In this case, it would
         be natural to have a predicate "f has_integral y" instead of "integrable f" and 
          "integral f = y" *)
      have "complex_integrable (M n) (\<lambda>x. CLBINT t:{-u..u}. 1 - iexp (snd (x, t) * fst (x, t)))"
        using Mn3 by (intro P.integrable_fst) (simp add: indicator_times split_beta')
      hence "complex_integrable (M n) (\<lambda>x. if x = 0 then 0 else 2 * (u  - sin (u * x) / x))"
        apply (subst integrable_cong)
        using `u > 0` by (auto simp add: *)
      hence **: "integrable (M n) (\<lambda>x. if x = 0 then 0 else 2 * (u  - sin (u * x) / x))"
        unfolding complex_of_real_integrable_eq .
      show ?thesis
        apply (rule integral_mono [OF _ **])
        apply (auto split: split_indicator)
        using `u > 0` apply (case_tac "x \<ge> 0", auto simp add: field_simps)
        apply (rule order_trans)
        prefer 2 apply assumption
        apply auto
        apply (subgoal_tac "x * u \<le> -2")
        apply (erule order_trans)
        apply auto
        using `u > 0` apply (case_tac "x > 0", auto simp add: field_simps not_le)
        apply (rule order_trans [OF sin_x_le_x], auto intro!: mult_nonneg_nonneg)
        apply (subst neg_le_iff_le [symmetric])
        apply (subst sin_minus [symmetric])
        by (rule sin_x_le_x, auto intro: mult_nonpos_nonneg)
    qed
    also (xtrans) have "(LINT x : {x. abs x \<ge> 2 / u} | M n. u) = 
        u * measure (M n) {x. abs x \<ge> 2 / u}"
      by (simp add: Mn.emeasure_eq_measure)
    finally show "Re (CLBINT t:{-u..u}. 1 - char (M n) t) \<ge> u * measure (M n) {x. abs x \<ge> 2 / u}" .
  qed

  have tight_aux: "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<exists>a b. a < b \<and> (\<forall>n. 1 - \<epsilon> < measure (M n) {a<..b})"
  proof -
    fix \<epsilon> :: real
    assume "\<epsilon> > 0"
    note M'.isCont_char [of 0]
    hence "\<exists>d>0. \<forall>t. abs t < d \<longrightarrow> cmod (char M' t - 1) < \<epsilon> / 4"
      apply (subst (asm) continuous_at_eps_delta)
      apply (drule_tac x = "\<epsilon> / 4" in spec)
      using `\<epsilon> > 0` by (auto simp add: dist_real_def dist_complex_def M'.char_zero)
    then obtain d where "d > 0 \<and> (\<forall>t. (abs t < d \<longrightarrow> cmod (char M' t - 1) < \<epsilon> / 4))" ..
    hence d0: "d > 0" and d1: "\<And>t. abs t < d \<Longrightarrow> cmod (char M' t - 1) < \<epsilon> / 4" by auto
    have 1: "\<And>x. cmod (1 - char M' x) \<le> 2"
      by (rule order_trans [OF norm_triangle_ineq4], auto simp add: M'.cmod_char_le_1)
    then have 2: "\<And>u v. complex_set_integrable lborel {u..v} (\<lambda>x. 1 - char M' x)"
      by (intro integrableI_bounded_set_indicator[where B=2]) (auto simp: emeasure_lborel_Icc_eq)
    have 3: "\<And>u v. set_integrable lborel {u..v} (\<lambda>x. cmod (1 - char M' x))"
      by (intro borel_integrable_compact[OF compact_Icc] continuous_at_imp_continuous_on
                continuous_intros ballI M'.isCont_char continuous_intros)
    have "cmod (CLBINT t:{-d/2..d/2}. 1 - char M' t) \<le> LBINT t:{-d/2..d/2}. cmod (1 - char M' t)"
      using integral_norm_bound[OF 2] by simp
    also have "\<dots> \<le> LBINT t:{-d/2..d/2}. \<epsilon> / 4"
      apply (rule integral_mono [OF 3])
      apply (simp add: emeasure_lborel_Icc_eq)
      apply (case_tac "x \<in> {-d/2..d/2}", auto)
      apply (subst norm_minus_commute)
      apply (rule less_imp_le)
      apply (rule d1 [simplified])
      using d0 by auto
    also with d0 have "\<dots> = d * \<epsilon> / 4"
      by simp
    finally have bound: "cmod (CLBINT t:{-d/2..d/2}. 1 - char M' t) \<le> d * \<epsilon> / 4" .
    { fix n x
      have "cmod (1 - char (M n) x) \<le> 2"
        by (rule order_trans [OF norm_triangle_ineq4], auto simp add: Mn.cmod_char_le_1)
    } note bd1 = this
    have "(\<lambda>n. CLBINT t:{-d/2..d/2}. 1 - char (M n) t) ----> (CLBINT t:{-d/2..d/2}. 1 - char M' t)"
      using bd1
      apply (intro integral_dominated_convergence[where w="\<lambda>x. indicator {-d/2..d/2} x *\<^sub>R 2"])
      apply (auto intro!: AE_I2 char_conv tendsto_intros 
                  simp: emeasure_lborel_Icc_eq
                  split: split_indicator)
      done
    hence "eventually (\<lambda>n. cmod ((CLBINT t:{-d/2..d/2}. 1 - char (M n) t) -
        (CLBINT t:{-d/2..d/2}. 1 - char M' t)) < d * \<epsilon> / 4) sequentially"
      using d0 `\<epsilon> > 0` apply (subst (asm) tendsto_iff)
      by (subst (asm) dist_complex_def, drule spec, erule mp, auto)
    hence "\<exists>N. \<forall>n \<ge> N. cmod ((CLBINT t:{-d/2..d/2}. 1 - char (M n) t) -
        (CLBINT t:{-d/2..d/2}. 1 - char M' t)) < d * \<epsilon> / 4" by (simp add: eventually_sequentially)
    then guess N ..
    hence N: "\<And>n. n \<ge> N \<Longrightarrow> cmod ((CLBINT t:{-d/2..d/2}. 1 - char (M n) t) -
        (CLBINT t:{-d/2..d/2}. 1 - char M' t)) < d * \<epsilon> / 4" by auto
    {
      fix n
      assume "n \<ge> N"
      interpret Mn: real_distribution "M n" by (rule assms)
      have "cmod (CLBINT t:{-d/2..d/2}. 1 - char (M n) t) = 
        cmod ((CLBINT t:{-d/2..d/2}. 1 - char (M n) t) - (CLBINT t:{-d/2..d/2}. 1 - char M' t)
          + (CLBINT t:{-d/2..d/2}. 1 - char M' t))" by simp
      also have "\<dots> \<le> cmod ((CLBINT t:{-d/2..d/2}. 1 - char (M n) t) - 
          (CLBINT t:{-d/2..d/2}. 1 - char M' t)) + cmod(CLBINT t:{-d/2..d/2}. 1 - char M' t)"
        by (rule norm_triangle_ineq)
      also have "\<dots> < d * \<epsilon> / 4 + d * \<epsilon> / 4" 
        by (rule add_less_le_mono [OF N [OF `n \<ge> N`] bound])
      also have "\<dots> = d * \<epsilon> / 2" by auto
      finally have "cmod (CLBINT t:{-d/2..d/2}. 1 - char (M n) t) < d * \<epsilon> / 2" .
      hence "d * \<epsilon> / 2 > Re (CLBINT t:{-d/2..d/2}. 1 - char (M n) t)"
        by (rule order_le_less_trans [OF complex_Re_le_cmod])
      hence "d * \<epsilon> / 2 > Re (CLBINT t:{-(d/2)..d/2}. 1 - char (M n) t)" (is "_ > ?lhs") by simp
      also have "?lhs \<ge> (d / 2) * measure (M n) {x. abs x \<ge> 2 / (d / 2)}" 
        using d0 by (intro main_bound, simp)
      finally (xtrans) have "d * \<epsilon> / 2 > (d / 2) * measure (M n) {x. abs x \<ge> 2 / (d / 2)}" .
      with d0 `\<epsilon> > 0` have "\<epsilon> > measure (M n) {x. abs x \<ge> 2 / (d / 2)}" by (simp add: field_simps)
      hence "\<epsilon> > 1 - measure (M n) (UNIV - {x. abs x \<ge> 2 / (d / 2)})"
        apply (subst Mn.borel_UNIV [symmetric])
        by (subst Mn.prob_compl, auto)
      also have "UNIV - {x. abs x \<ge> 2 / (d / 2)} = {x. -(4 / d) < x \<and> x < (4 / d)}"
        using d0 apply (auto simp add: field_simps)
        (* very annoying -- this should be automatic *)
        apply (case_tac "x \<ge> 0", auto simp add: field_simps)
        apply (subgoal_tac "0 \<le> x * d", arith, rule mult_nonneg_nonneg, auto)
        apply (case_tac "x \<ge> 0", auto simp add: field_simps)
        apply (subgoal_tac "x * d \<le> 0", arith)
        apply (rule mult_nonpos_nonneg, auto)
        by (case_tac "x \<ge> 0", auto simp add: field_simps)
      finally have "measure (M n) {x. -(4 / d) < x \<and> x < (4 / d)} > 1 - \<epsilon>"
        by auto
    } note 6 = this
    {
      fix n :: nat
      interpret Mn: real_distribution "M n" by (rule assms)
      have *: "(UN (k :: nat). {- real k<..real k}) = UNIV"
        by (auto, metis leI le_less_trans less_imp_le minus_less_iff reals_Archimedean2)
      have "(\<lambda>k. measure (M n) {- real k<..real k}) ----> 
          measure (M n) (UN (k :: nat). {- real k<..real k})"
        by (rule Mn.finite_Lim_measure_incseq, auto simp add: incseq_def)
      hence "(\<lambda>k. measure (M n) {- real k<..real k}) ----> 1"
        using Mn.prob_space unfolding * Mn.borel_UNIV by simp
      hence "eventually (\<lambda>k. measure (M n) {- real k<..real k} > 1 - \<epsilon>) sequentially"
        apply (elim order_tendstoD (1))
        using `\<epsilon> > 0` by auto
    } note 7 = this
    {
      fix n :: nat
      have "eventually (\<lambda>k. \<forall>m < n. measure (M m) {- real k<..real k} > 1 - \<epsilon>) sequentially"
        (is "?P n")
      proof (induct n)
        show "?P 0" by auto
      next
        fix n 
        assume ih: "?P n"
        show "?P (Suc n)"
          apply (rule eventually_rev_mp [OF ih])
          apply (rule eventually_rev_mp [OF 7 [of n]])
          apply (rule always_eventually)
          by (auto simp add: less_Suc_eq)
      qed
    } note 8 = this
    from 8 [of N] have "\<exists>K :: nat. \<forall>k \<ge> K. \<forall>m<N. 1 - \<epsilon> < 
        Sigma_Algebra.measure (M m) {- real k<..real k}"
      by (auto simp add: eventually_sequentially)
    hence "\<exists>K :: nat. \<forall>m<N. 1 - \<epsilon> < Sigma_Algebra.measure (M m) {- real K<..real K}" by auto
    then obtain K :: nat where 
      "\<forall>m<N. 1 - \<epsilon> < Sigma_Algebra.measure (M m) {- real K<..real K}" ..
    hence K: "\<And>m. m < N \<Longrightarrow> 1 - \<epsilon> < Sigma_Algebra.measure (M m) {- real K<..real K}"
      by auto
    let ?K' = "max K (4 / d)"
    have "-?K' < ?K' \<and> (\<forall>n. 1 - \<epsilon> < measure (M n) {-?K'<..?K'})"
      using d0 apply auto
      apply (rule max.strict_coboundedI2, auto)
      proof -
        fix n
        interpret Mn: real_distribution "M n" by (rule assms)
        show " 1 - \<epsilon> < measure (M n) {- max (real K) (4 / d)<..max (real K) (4 / d)}"      
          apply (case_tac "n < N")
          apply (rule order_less_le_trans)
          apply (erule K)
          apply (rule Mn.finite_measure_mono, auto)
          apply (rule order_less_le_trans)
          apply (rule 6, erule leI)
          by (rule Mn.finite_measure_mono, auto)
      qed 
    thus "\<exists>a b. a < b \<and> (\<forall>n. 1 - \<epsilon> < measure (M n) {a<..b})" by (intro exI)
  qed
  have tight: "tight M"
    unfolding tight_def apply (rule conjI)
    apply (force intro: assms)
    apply clarify
    by (erule tight_aux)
  show ?thesis
    proof (rule tight_subseq_weak_converge [OF real_distr_M real_distr_M' tight])
      fix s \<nu>
      assume s: "subseq s"
      assume nu: "weak_conv_m (M \<circ> s) \<nu>"
      assume *: "real_distribution \<nu>"
      have 2: "\<And>n. real_distribution ((M \<circ> s) n)" unfolding comp_def by (rule assms)
      have 3: "\<And>t. (\<lambda>n. char ((M \<circ> s) n) t) ----> char \<nu> t" by (intro levy_continuity1 [OF 2 * nu])
      have 4: "\<And>t. (\<lambda>n. char ((M \<circ> s) n) t) = ((\<lambda>n. char (M n) t) \<circ> s)" by (rule ext, simp)
      have 5: "\<And>t. (\<lambda>n. char ((M \<circ> s) n) t) ----> char M' t"
        by (subst 4, rule lim_subseq [OF s], rule assms)
      hence "char \<nu> = char M'" by (intro ext, intro LIMSEQ_unique [OF 3 5])
      hence "\<nu> = M'" by (rule Levy_uniqueness [OF * `real_distribution M'`])
      thus "weak_conv_m (M \<circ> s) M'" 
        apply (elim subst)
        by (rule nu)  
  qed
qed

end
