(*
Theory: Characteristic_Functions.thy
Authors: Jeremy Avigad, Luke Serafin
*)

theory Characteristic_Functions

imports Weak_Convergence Real_to_Complex

begin

(*
  The characteristic function of a real measure.
*)

definition
  char :: "real measure \<Rightarrow> real \<Rightarrow> complex"
where
  "char M t \<equiv> complex_lebesgue_integral M (\<lambda>x. iexp (t * x))"

lemma (in real_distribution) char_zero: "char M 0 = 1"
  unfolding char_def by (simp del: space_eq_univ add: prob_space)

(*
  Approximations to e^ix from Billingsley, page 343
*)

lemma fact1: "CDERIV (%s. complex_of_real(-((x - s) ^ (Suc n) / (Suc n))) * iexp s)
 s : A :> complex_of_real((x - s)^n) * iexp s + (ii * iexp s) * 
      complex_of_real(-((x - s) ^ (Suc n) / (Suc n)))"
  apply (rule CDERIV_mult)
  apply (rule CDERIV_of_real)
  apply (auto intro!: DERIV_intros simp del: power_Suc)
  apply (subst i_complex_of_real[symmetric])+
by (rule CDERIV_iexp)

lemma equation_26p1:
  fixes x :: real and n :: nat
  defines "f s m \<equiv> complex_of_real ((x - s) ^ m)"
  shows "(CLBINT s=0..x. (f s n) * iexp s) = 
    x^(Suc n) / (Suc n) + (ii / (Suc n)) * 
      (CLBINT s=0..x. (f s (Suc n)) * iexp s)"
proof -
  let ?F = "%s. complex_of_real(-((x - s) ^ (Suc n) / (Suc n))) * iexp s"
  have annoying [simp]: "1 + complex_of_real (real n) =
      complex_of_real (real (Suc n))"
    by (metis of_nat_Suc of_real_of_nat_eq real_of_nat_def)
  have "(CLBINT s=0..x. (f s n * iexp s + (ii * iexp s) * -(f s (Suc n) / (Suc n)))) =
      x^(Suc n) / (Suc n)" (is "?LHS = ?RHS")
  proof -
    have "?LHS = (CLBINT s=0..x. (f s n * iexp s + (ii * iexp s) * 
      complex_of_real(-((x - s) ^ (Suc n) / (Suc n)))))"
      apply (case_tac "0 \<le> x")
      apply (subst (1 2) zero_ereal_def)
      apply (rule complex_interval_integral_cong, force)
      unfolding f_def apply simp
      by simp
    also have "... = ?F x - ?F 0"
      apply (subst zero_ereal_def)
      apply (rule complex_interval_integral_FTC_finite)
      apply (unfold f_def)
      apply (rule continuous_at_imp_continuous_on)
      apply (auto simp del: i_complex_of_real) [1]
      by (rule fact1)
    also have "... = x^(Suc n) / (Suc n)"
      by auto
    finally show ?thesis .
  qed
thus ?thesis
  apply (elim subst)
  apply (subst complex_interval_lebesgue_integral_cmult(2) [symmetric])
  apply (subst zero_ereal_def)
  unfolding f_def 
  apply (rule complex_interval_integrable_isCont, force simp del: i_complex_of_real)
      (* see comment before isCont_iexp in Real_to_Complex *)
  unfolding f_def
  apply (subst complex_interval_lebesgue_integral_add(2) [symmetric])
  (* the next 12 lines should be automatic *)
  apply (subst zero_ereal_def)
  apply (rule complex_interval_integrable_isCont)
  apply (simp del: i_complex_of_real) 
  apply (subst zero_ereal_def)
  apply (rule complex_interval_integrable_isCont)
  apply (simp del: i_complex_of_real) 
  by simp
qed

lemma equation_26p2:
  fixes x :: real
  defines "f s m \<equiv> complex_of_real ((x - s) ^ m)"
  shows "iexp x= (\<Sum>k \<le> n. (ii * x)^k / (fact k)) + 
    ((ii ^ (Suc n)) / (fact n)) * 
       (CLBINT s=0..x. (f s n) * (iexp s))" (is "?P n")
proof (induction n)
  show "?P 0"
    unfolding f_def apply (subst zero_ereal_def)
    by (auto simp add: field_simps interval_integral_iexp simp del: i_complex_of_real)  
next
  fix n 
  assume ih: "?P n"
  show "?P (Suc n)"
    apply (subst setsum_atMost_Suc)
    apply (subst ih)
    apply (unfold f_def)
    apply (subst equation_26p1)
    (* this is a good example of a messy calculation that should be
       automatic! *)
    apply (simp add: field_simps del: i_complex_of_real)  
    (* ugly, but comprehensible: write it out *)
    apply (subst nonzero_eq_divide_eq)
    apply (metis comm_semiring_1_class.normalizing_semiring_rules(3) 
      divisors_zero fact_nonzero_nat less_zeroE nat_less_real_le 
      natceiling_real_of_nat of_real_add of_real_eq_0_iff of_real_mult 
      order_refl real_of_nat_zero)
    by (simp add: field_simps power_mult_distrib real_of_nat_Suc
      del: i_complex_of_real)
qed
(* suggests we should add real_of_nat_Suc, delete i_complex_of_real *)

lemma equation_26p3: 
  fixes x :: real
  defines "f s m \<equiv> complex_of_real ((x - s) ^ m)" 
  shows "iexp x = (\<Sum>k \<le> Suc n. (ii * x)^k / fact k) + 
    ii ^ (Suc n) / fact n * (CLBINT s=0..x. f s n * (iexp s - 1))"
proof -
  have calc1: "(CLBINT s=0..x. f s n * (iexp s - 1)) =
    (CLBINT s=0..x. f s n * iexp s) - (CLBINT s=0..x. f s n)"
    apply (subst complex_interval_lebesgue_integral_diff(2) [symmetric])
    apply (subst zero_ereal_def)
    apply (rule complex_interval_integrable_isCont)
    unfolding f_def apply (simp del: i_complex_of_real)
    apply (subst zero_ereal_def)
    apply (rule complex_interval_integrable_isCont)
    apply (simp del: i_complex_of_real)
    by (simp add: field_simps)
  have calc2: "(CLBINT s=0..x. f s n) = x^(Suc n) / (Suc n)"
    apply (subst zero_ereal_def)
    apply (subst complex_interval_integral_FTC_finite
      [where a = 0 and b = x and f = "\<lambda>s. f s n" and F = 
        "\<lambda>s. complex_of_real (-((x - s) ^ (Suc n) / real (Suc n)))"])
    apply (unfold f_def)
    apply (rule continuous_at_imp_continuous_on, force)
    apply (rule CDERIV_of_real)
    by (auto intro!: DERIV_intros simp del: power_Suc)
  show ?thesis
    apply (subst equation_26p2 [where n = "Suc n"])
    apply (rule arg_cong) back    
    apply (subst calc1)
    apply (subst calc2)
    apply (subgoal_tac 
      "ii ^ (Suc (Suc n)) / complex_of_real (real (int (fact (Suc n)))) = 
       (ii ^ (Suc n) / complex_of_real (real (int (fact n)))) *
       (ii / complex_of_real (real (int (Suc n))))")
    prefer 2
    apply (simp add: field_simps)
    apply (erule ssubst)
    apply (subst mult_assoc)+
    apply (rule arg_cong) back
    apply (unfold f_def)
    apply (subst equation_26p1 [where n = n])
    by auto
qed

lemma equation_26p4a: "cmod (iexp x - (\<Sum>k \<le> n. (ii * x)^k / fact k)) \<le>
    (abs x)^(Suc n) / fact (Suc n)"
  sorry

lemma equation_26p4b: "cmod (iexp x - (\<Sum>k \<le> n. (ii * x)^k / fact k)) \<le>
    2 * (abs x)^n / fact n"
  sorry



(* TODO: finish these off. Need cmod (complex_integral f) <= complex_integral (cmod f). *)

(*
  Independence. 

  TODO: fill in *)

(* 
  A real / complex version of Fubini's theorem.
*)

lemma (in pair_sigma_finite) complex_Fubini_integral:
  fixes f :: "'a \<times> 'b \<Rightarrow> complex"
  assumes "complex_integrable (M1 \<Otimes>\<^sub>M M2) f"
  shows "CLINT y|M2. CLINT x|M1. f (x, y) = CLINT x|M1. CLINT y|M2. f (x, y)"
using assms unfolding complex_lebesgue_integral_def complex_integrable_def
by (auto intro: Fubini_integral)
(* How delightful that this is so easy! *)

(*
  Not needed?

locale pair_finite = M1: finite_measure M1 + M2: finite_measure M2
  for M1 :: "'a measure" and M2 :: "'b measure"

sublocale pair_finite < pair_sigma_finite ..
sublocale pair_finite < finite_measure where M = "M1 \<Otimes>\<^sub>M M2"
proof
  show "emeasure (M1 \<Otimes>\<^sub>M M2) (space (M1 \<Otimes>\<^sub>M M2)) \<noteq> \<infinity>"
    by (auto simp add: space_pair_measure M2.emeasure_pair_measure_Times)
qed

*)

(*

  Complex.abs_Im_le_cmod: \<bar>Im ?x\<bar> \<le> cmod ?x
  Complex.abs_Re_le_cmod: \<bar>Re ?x\<bar> \<le> cmod ?x
*)

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
        apply (rule arg_cong) back
        using `t \<noteq> 0` by (simp add: field_simps del: i_complex_of_real)
      also have "\<dots> \<le> cmod (?one / (ii * t)) + cmod (?two / (ii * t))" 
        by (rule norm_triangle_ineq4)
      also have "cmod (?one / (ii * t)) = cmod ?one / abs t"
        by (simp add: norm_divide)
      also have "cmod (?two / (ii * t)) = cmod ?two / abs t"
        by (simp add: norm_divide)      
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
    apply (subgoal_tac "0 = 0 + 0")
    apply (erule ssubst) back back
    apply (rule tendsto_add)
    apply (rule tendsto_mult_right_zero, rule tendsto_rabs_zero, rule tendsto_ident_at)+
    by auto
qed

lemma cmod_iexp [simp]: "cmod (iexp x) = 1"
  by (simp add: cis_conv_exp [symmetric])

lemma Levy_Inversion_aux2:
  fixes a b t :: real
  assumes "a \<le> b" and "t \<noteq> 0"
  shows "cmod ((iexp (t * b) - iexp (t * a)) / (ii * t)) \<le> b - a"
    (is "?F \<le> _")
proof -
  have "?F = cmod (iexp (t * a) * (iexp (t * (b - a)) - 1) / (ii * t))"
    apply (rule arg_cong) back
    using `t ~= 0` by (simp add: field_simps exp_diff exp_minus)
  also have "\<dots> = cmod (iexp (t * (b - a)) - 1) / abs t"
    apply (subst norm_divide)
    apply (subst norm_mult)
    apply (subst cmod_iexp)
    using `t \<noteq> 0` by simp
  also have "\<dots> \<le> abs (t * (b - a)) / abs t"
    apply (rule divide_right_mono)
    using equation_26p4a [of "t * (b - a)" 0] apply (simp add: field_simps eval_nat_numeral)
    by force
  also have "\<dots> = b - a"
    using assms by (auto simp add: abs_mult) 
  finally show ?thesis .
qed

declare i_complex_of_real [simp del]
declare of_real_mult [simp del]

lemma complex_set_bounded_integrable_AE:
  fixes f A B and M :: "'a measure"
  assumes "A \<in> sets M" "AE x \<in> A in M. cmod (f x) \<le> B"
   and "emeasure M A \<noteq> \<infinity>" and "f \<in> borel_measurable M"
  shows "complex_set_integrable M A f"
using assms unfolding complex_set_integrable_iff apply (intro conjI)
  apply (rule integrable_bound [of _ "\<lambda>x. B * indicator A x"])
  apply (rule integral_cmult, erule (1) integral_indicator)
  apply auto
  apply (rule AE_I [of _ _ "{}"], auto split: split_indicator)
  apply (erule order_trans [OF abs_Re_le_cmod])
  apply (rule integrable_bound [of _ "\<lambda>x. B * indicator A x"])
  apply (rule integral_cmult, erule (1) integral_indicator)
  apply auto
  apply (rule AE_I [of _ _ "{}"], auto split: split_indicator)
by (erule order_trans [OF abs_Im_le_cmod])

lemma set_integral_reflect:
  fixes S and f :: "real \<Rightarrow> real"
  assumes "set_borel_measurable borel S f"
  shows "(LBINT x : S. f x) = (LBINT x : {x. - x \<in> S}. f (- x))"

  using assms apply (subst lebesgue_integral_real_affine [of "-1" _ 0], auto)
by (rule integral_cong, auto split: split_indicator)

(* TODO: can generalize to ereals *)
lemma interval_integral_reflect:
  fixes a b :: real and f
  assumes "f \<in> borel_measurable borel"
  shows "(LBINT x=a..b. f x) = (LBINT x=-b..-a. f (-x))"
unfolding interval_lebesgue_integral_def
  apply (case_tac "a \<le> b", auto)
  apply (subst set_integral_reflect)
  using assms apply auto
  apply (rule integral_cong, auto simp add: einterval_def split: split_indicator)
  apply (subst set_integral_reflect)
  using assms apply auto
by (rule integral_cong, auto simp add: einterval_def split: split_indicator)

lemma complex_interval_integral_reflect:
  fixes a b :: real and f
  assumes "f \<in> borel_measurable borel"
  shows "(CLBINT x=a..b. f x) = (CLBINT x=-b..-a. f (-x))"
unfolding complex_interval_lebesgue_integral_eq
  using assms by (subst interval_integral_reflect, auto)+

lemma complex_integral_of_real: 
  "(CLINT t | M. complex_of_real (f t)) = complex_of_real (LINT t | M. f t)"
unfolding complex_lebesgue_integral_def
  by (simp only: Re_complex_of_real Im_complex_of_real, simp)

lemma complex_set_integral_of_real: 
  "(CLINT t : S | M. complex_of_real (f t)) = complex_of_real (LINT t : S | M. f t)"
unfolding complex_set_lebesgue_integral_eq
  by (simp only: Re_complex_of_real Im_complex_of_real, simp)

lemma complex_interval_integral_of_real: 
  "(CLBINT t=a..b. complex_of_real (f t)) = complex_of_real (LBINT t=a..b. f t)"
unfolding complex_interval_lebesgue_integral_eq
  by (simp only: Re_complex_of_real Im_complex_of_real, simp)

theorem Levy_Inversion:
  fixes M :: "real measure"
  and a b :: real
  assumes "a \<le> b"
  defines "\<mu> \<equiv> measure M" and "\<phi> \<equiv> char M"
  assumes "real_distribution M"
  and "\<mu> {a} = 0" and "\<mu> {b} = 0"
  shows
  "((\<lambda>T :: real. 1 / (2 * pi) * (CLBINT t=-T..T. (iexp (-(t * a)) -
  iexp (-(t * b))) / (ii * t) * \<phi> t)) ---> \<mu> {a<..b}) at_top"
  (is "((\<lambda>T :: real. 1 / (2 * pi) * (CLBINT t=-T..T. ?F t * \<phi> t)) ---> 
      of_real (\<mu> {a<..b})) at_top")
  proof -
    interpret M: real_distribution M by (rule assms)
    interpret P: pair_sigma_finite lborel M ..
    let ?f = "\<lambda>t x :: real. (iexp (t * (x - a)) - iexp(t * (x - b))) / (ii * t)"
    {
      fix T :: real
      assume "T \<ge> 0"
      let ?f' = "\<lambda>(t, x). ?f t x * indicator {-T<..<T} t"
      {
        fix x
        have 1: "\<And>u v. u \<le> v \<Longrightarrow> complex_interval_lebesgue_integrable lborel
            (ereal u) (ereal v) (\<lambda>t. ?f t x)"
          apply (simp add: complex_interval_lebesgue_integrable_def del: times_divide_eq_left)
          apply (rule complex_set_bounded_integrable_AE [of _ _ _ "b -a"], force)
          apply (rule AE_I [of _ _ "{0}"], clarify)
          by (rule order_trans, rule Levy_Inversion_aux2, auto simp add: assms)
        have 2: "\<And>u v. u \<le> v \<Longrightarrow> complex_interval_lebesgue_integrable lborel
            (ereal u) (ereal v) (\<lambda>t. ?f (-t) x)"
          apply (simp add: complex_interval_lebesgue_integrable_def del: times_divide_eq_left
                       of_real_minus mult_minus_left)
          apply (rule complex_set_bounded_integrable_AE [of _ _ _ "b - a"], force)
          apply (rule AE_I [of _ _ "{0}"], clarify)
          by (rule order_trans, rule Levy_Inversion_aux2, auto simp add: assms)
        have "(CLBINT t. ?f' (t, x)) = (CLBINT t=-T..T. ?f t x)"
          using `T \<ge> 0` using complex_interval_lebesgue_integral_def by auto
        also have "\<dots> = (CLBINT t=-T..(0 :: real). ?f t x) + (CLBINT t=(0 :: real)..T. ?f t x)"
            (is "_ = _ + ?t")
          apply (rule complex_interval_integral_sum [symmetric])
          using `T \<ge> 0` apply (subst min_absorb1, auto)
          apply (subst max_absorb2, auto)+
          by (rule 1, auto)
        also have "(CLBINT t=-T..(0 :: real). ?f t x) = (CLBINT t=(0::real)..T. ?f (-t) x)"
          apply (subst complex_interval_integral_reflect)
          by auto
        also have "\<dots> + ?t = (CLBINT t=(0::real)..T. ?f (-t) x + ?f t x)"
          apply (rule complex_interval_lebesgue_integral_add(2) [symmetric])
          apply (rule 2, rule `T \<ge> 0`)
          by (rule 1, rule `T \<ge> 0`)
        also have "\<dots> = (CLBINT t=(0::real)..T. ((iexp(t * (x - a)) - iexp (-(t * (x - a)))) -  
            (iexp(t * (x - b)) - iexp (-(t * (x - b))))) / (ii * t))"
          apply (rule complex_interval_integral_cong)
          using `T \<ge> 0` by (auto simp add: field_simps)
        also have "\<dots> = (CLBINT t=(0::real)..T. complex_of_real(
            2 * sin (t * (x - a)) / t - 2 * sin (t * (x - b)) / t))"
          apply (rule complex_interval_integral_cong)
          using `T \<ge> 0` apply (auto simp add: field_simps of_real_mult expi_def cis_def
             i_complex_of_real)
          apply (subst (2 5 7 10) minus_diff_eq [symmetric])
          apply (simp only: sin_minus cos_minus)
          by (simp add: complex_of_real_def field_simps)
        also have "\<dots> = complex_of_real (LBINT t=(0::real)..T. 
            2 * sin (t * (x - a)) / t - 2 * sin (t * (x - b)) / t)"
          by (rule complex_interval_integral_of_real)
        finally have "(CLBINT t. ?f' (t, x)) = complex_of_real (LBINT t=(0::real)..T. 
            2 * sin (t * (x - a)) / t - 2 * sin (t * (x - b)) / t)" .
      } note main_eq = this
      have "(CLBINT t=-T..T. ?F t * \<phi> t) = 
        (CLBINT t. (CLINT x | M. ?F t * iexp (t * x) * indicator {-T<..<T} t))"
        using `T \<ge> 0` unfolding \<phi>_def char_def complex_interval_lebesgue_integral_def
        apply (simp)
        apply (rule complex_integral_cong, auto)
        apply (subst times_divide_eq(1) [symmetric])
        apply (subst (8) mult_commute)
        apply (subst mult_assoc [symmetric])
        apply (subst complex_integral_cmult(2) [symmetric])
        unfolding complex_integrable_def apply (auto simp add: expi_def)
        apply (rule M.integrable_const_bound [of _ 1], force)
        apply (rule borel_measurable_continuous_on) back
        apply auto
        apply (rule continuous_on_cos, rule continuous_on_id)
        apply (rule M.integrable_const_bound [of _ 1], force)
        apply (rule borel_measurable_continuous_on) back
        apply auto
        apply (rule continuous_on_sin, rule continuous_on_id)
        apply (rule complex_integral_cong)
        by auto
      also have "\<dots> = (CLBINT t. (CLINT x | M. ?f' (t, x)))"
        apply (rule complex_integral_cong, clarify)+
        by (simp add: field_simps exp_diff exp_minus field_divide_inverse)
      also have "\<dots> = (CLINT x | M. (CLBINT t. ?f' (t, x)))"
        apply (rule P.complex_Fubini_integral [symmetric])
        unfolding complex_integrable_def apply (rule conjI)
        apply (rule integrable_bound) 
        apply (rule integral_cmult [of "lborel \<Otimes>\<^sub>M M" 
              "indicator ({-T<..<T} \<times> UNIV)" "b - a"])
        apply (rule integral_indicator, auto)
        apply (subst (asm) M.emeasure_pair_measure_Times, auto)
        apply (rule AE_I [of _ _ "{0} \<times> UNIV"], auto)
        apply (rule ccontr, erule notE)
        apply (rule order_trans, rule abs_Re_le_cmod)
        apply (auto split: split_indicator)
        apply (rule order_trans, rule Levy_Inversion_aux2)
        using `a \<le> b` apply auto
        apply (subst M.emeasure_pair_measure_Times, auto)
        (* TODO: factor to eliminate duplication *)
        apply (rule integrable_bound) 
        apply (rule integral_cmult [of "lborel \<Otimes>\<^sub>M M" 
              "indicator ({-T<..<T} \<times> UNIV)" "b - a"])
        apply (rule integral_indicator, auto)
        apply (subst (asm) M.emeasure_pair_measure_Times, auto)
        apply (rule AE_I [of _ _ "{0} \<times> UNIV"], auto)
        apply (rule ccontr, erule notE)
        apply (rule order_trans, rule abs_Im_le_cmod)
        apply (auto split: split_indicator)
        apply (rule order_trans, rule Levy_Inversion_aux2)
        using `a \<le> b` apply auto
        by (subst M.emeasure_pair_measure_Times, auto)
      also have "\<dots> = (CLINT x | M. (complex_of_real (LBINT t=(0::real)..T. 
            2 * sin (t * (x - a)) / t - 2 * sin (t * (x - b)) / t)))"
         using main_eq by (intro complex_integral_cong, auto)
      also have "\<dots> = complex_of_real (LINT x | M. (LBINT t=(0::real)..T. 
            2 * sin (t * (x - a)) / t - 2 * sin (t * (x - b)) / t))"
         by (rule complex_integral_of_real)
      finally have "(CLBINT t=-T..T. ?F t * \<phi> t) = 
          complex_of_real (LINT x | M. (LBINT t=(0::real)..T. 
            2 * sin (t * (x - a)) / t - 2 * sin (t * (x - b)) / t))" .
    } note main_eq2 = this


(*
    have "?I = (\<lambda>T. (1/(2 * \<pi>) * Re (CLINT x|M. (CLBINT t=-T..T.
      (iexp (-of_real (t * (x - a))) - iexp (-of_real (t * (x - b))))/
      (ii * of_real t)))))"
      apply (unfold \<phi>_def)
      apply (unfold char_def)
      apply (rule pair_sigma_finite.Fubini_integral)
      sorry
    let ?S = "\<lambda>T. (sgn(x - a)/\<pi>) * sinc (T * \<bar>x - a\<bar>) - (sgn(x - b)/\<pi>) *
      sinc (T * \<bar>x - b\<bar>)"
    have real_I: "?I = (\<lambda>T. LINT x|M. ?S T)"
      sorry
    let ?\<psi> = "\<lambda>a. \<lambda>b. \<lambda>x. if x < a then 0::real else (if x = a then 1/2 else
      (if x \<in> {a<..<b} then 1 else (if x = b then 1/2 else (if b < x then 0
      else 0))))"
    have "(?S ---> ?\<psi> a b x) at_top"
      sorry
    have "(?I ---> LINT x|M. ?\<psi> a b x) at_top"
      sorry
    thus ?thesis sorry
  qed
*)

end



