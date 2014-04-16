(*
Theory: Levy.thy
Author: Jeremy Avigad

The Levy inversion theorem, and the Levy continuity theorem.
*)

theory Levy

imports Characteristic_Functions Helly_Selection

begin

(* 
  A real / complex version of Fubini's theorem.
*)

lemma (in pair_sigma_finite) complex_Fubini_integral:
  fixes f :: "'a \<times> 'b \<Rightarrow> complex"
  assumes "complex_integrable (M1 \<Otimes>\<^sub>M M2) f"
  shows "CLINT y|M2. CLINT x|M1. f (x, y) = CLINT x|M1. CLINT y|M2. f (x, y)"
using assms unfolding complex_lebesgue_integral_def complex_integrable_def
by (auto intro: Fubini_integral simp add: i_complex_of_real)
(* How delightful that this is so easy! *)

(* extracted from Binary_Product_Measure.integrable_fst_measurable *)
lemma (in pair_sigma_finite) Fubini_integrable:
  assumes f: "integrable (M1 \<Otimes>\<^sub>M M2) f"
  shows "integrable M1 (\<lambda>x. \<integral>y. f (x, y) \<partial>M2)"
(*
  shows "AE x in M1. integrable M2 (\<lambda> y. f (x, y))" (is "?AE")
    and "(\<integral>x. (\<integral>y. f (x, y) \<partial>M2) \<partial>M1) = integral\<^sup>L (M1 \<Otimes>\<^sub>M M2) f" (is "?INT")
*)
proof -
  have f_borel: "f \<in> borel_measurable (M1 \<Otimes>\<^sub>M M2)"
    using f by auto
  let ?pf = "\<lambda>x. ereal (f x)" and ?nf = "\<lambda>x. ereal (- f x)"
  have
    borel: "?nf \<in> borel_measurable (M1 \<Otimes>\<^sub>M M2)""?pf \<in> borel_measurable (M1 \<Otimes>\<^sub>M M2)" and
    int: "integral\<^sup>P (M1 \<Otimes>\<^sub>M M2) ?nf \<noteq> \<infinity>" "integral\<^sup>P (M1 \<Otimes>\<^sub>M M2) ?pf \<noteq> \<infinity>"
    using assms by auto
  have "(\<integral>\<^sup>+x. (\<integral>\<^sup>+y. ereal (f (x, y)) \<partial>M2) \<partial>M1) \<noteq> \<infinity>"
     "(\<integral>\<^sup>+x. (\<integral>\<^sup>+y. ereal (- f (x, y)) \<partial>M2) \<partial>M1) \<noteq> \<infinity>"
    using borel[THEN M2.positive_integral_fst_measurable(1)] int
    unfolding borel[THEN M2.positive_integral_fst_measurable(2)] by simp_all
  with borel[THEN M2.positive_integral_fst_measurable(1)]
  have AE_pos: "AE x in M1. (\<integral>\<^sup>+y. ereal (f (x, y)) \<partial>M2) \<noteq> \<infinity>"
    "AE x in M1. (\<integral>\<^sup>+y. ereal (- f (x, y)) \<partial>M2) \<noteq> \<infinity>"
    by (auto intro!: positive_integral_PInf_AE )
  then have AE: "AE x in M1. \<bar>\<integral>\<^sup>+y. ereal (f (x, y)) \<partial>M2\<bar> \<noteq> \<infinity>"
    "AE x in M1. \<bar>\<integral>\<^sup>+y. ereal (- f (x, y)) \<partial>M2\<bar> \<noteq> \<infinity>"
    by (auto simp: positive_integral_positive)
(*
  from AE_pos show ?AE using assms
    by (simp add: measurable_Pair2[OF f_borel] integrable_def)
*)
  { fix f have "(\<integral>\<^sup>+ x. - \<integral>\<^sup>+ y. ereal (f x y) \<partial>M2 \<partial>M1) = (\<integral>\<^sup>+x. 0 \<partial>M1)"
      using positive_integral_positive
      by (intro positive_integral_cong_pos) (auto simp: ereal_uminus_le_reorder)
    then have "(\<integral>\<^sup>+ x. - \<integral>\<^sup>+ y. ereal (f x y) \<partial>M2 \<partial>M1) = 0" by simp }
  note this[simp]
  { fix f assume borel: "(\<lambda>x. ereal (f x)) \<in> borel_measurable (M1 \<Otimes>\<^sub>M M2)"
      and int: "integral\<^sup>P (M1 \<Otimes>\<^sub>M M2) (\<lambda>x. ereal (f x)) \<noteq> \<infinity>"
      and AE: "AE x in M1. (\<integral>\<^sup>+y. ereal (f (x, y)) \<partial>M2) \<noteq> \<infinity>"
    have "integrable M1 (\<lambda>x. real (\<integral>\<^sup>+y. ereal (f (x, y)) \<partial>M2))" (is "integrable M1 ?f")
    proof (intro integrable_def[THEN iffD2] conjI)
      show "?f \<in> borel_measurable M1"
        using borel by (auto intro!: M2.positive_integral_fst_measurable)
      have "(\<integral>\<^sup>+x. ereal (?f x) \<partial>M1) = (\<integral>\<^sup>+x. (\<integral>\<^sup>+y. ereal (f (x, y))  \<partial>M2) \<partial>M1)"
        using AE positive_integral_positive[of M2]
        by (auto intro!: positive_integral_cong_AE simp: ereal_real)
      then show "(\<integral>\<^sup>+x. ereal (?f x) \<partial>M1) \<noteq> \<infinity>"
        using M2.positive_integral_fst_measurable[OF borel] int by simp
      have "(\<integral>\<^sup>+x. ereal (- ?f x) \<partial>M1) = (\<integral>\<^sup>+x. 0 \<partial>M1)"
        by (intro positive_integral_cong_pos)
           (simp add: positive_integral_positive real_of_ereal_pos)
      then show "(\<integral>\<^sup>+x. ereal (- ?f x) \<partial>M1) \<noteq> \<infinity>" by simp
    qed }
  with this[OF borel(1) int(1) AE_pos(2)] this[OF borel(2) int(2) AE_pos(1)]
  show "integrable M1 (\<lambda>x. \<integral>y. f (x, y) \<partial>M2)"
    unfolding lebesgue_integral_def[of "M1 \<Otimes>\<^sub>M M2"] lebesgue_integral_def[of M2]
      borel[THEN M2.positive_integral_fst_measurable(2), symmetric]
    using AE[THEN integral_real] by auto
qed

lemma (in pair_sigma_finite) complex_Fubini_integrable:
  fixes f :: "'a \<times> 'b \<Rightarrow> complex"
  assumes "complex_integrable (M1 \<Otimes>\<^sub>M M2) f"
  shows "complex_integrable M1 (\<lambda>x. CLINT y | M2. f (x, y))"
using assms unfolding complex_lebesgue_integral_def complex_integrable_def
by (auto intro: Fubini_integrable simp add: i_complex_of_real)


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
    apply (subgoal_tac "0 = 0 + 0")
    apply (erule ssubst) back back
    apply (rule tendsto_add)
    apply (rule tendsto_mult_right_zero, rule tendsto_rabs_zero, rule tendsto_ident_at)+
    by auto
qed

lemma cmod_iexp [simp]: "cmod (iexp x) = 1"
  by (simp add: cis_conv_exp [symmetric] i_complex_of_real)

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
    using `t \<noteq> 0` by (simp add: i_complex_of_real)
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

(* TODO: need a better version of FTC2 *)

lemma has_field_derivative_within_open: "a \<in> s \<Longrightarrow> open s \<Longrightarrow>
    (f has_field_derivative f') (at a within s) = (f has_field_derivative f') (at a)"
  unfolding has_field_derivative_def by (rule has_derivative_within_open)

abbreviation sin_x_over_x_fixed :: "real \<Rightarrow> real" where
  "sin_x_over_x_fixed \<equiv> (\<lambda>x. if x = 0 then 1 else sin x / x)"

lemma sin_x_over_x_at_0: "((\<lambda>x. sin x / x) ---> 1) (at 0)"
using DERIV_sin [of 0] by (auto simp add: has_field_derivative_def field_has_derivative_at)

lemma isCont_sin_x_over_x_fixed: "isCont sin_x_over_x_fixed x"
  apply (case_tac "x = 0", auto)
  apply (simp add: isCont_def)
  apply (subst LIM_equal [where g = "\<lambda>x. sin x / x"], auto intro: sin_x_over_x_at_0)
  apply (rule continuous_transform_at [where d = "abs x" and f = "\<lambda>x. sin x / x"])
  by (auto simp add: dist_real_def)

lemma iSi_isCont: "isCont Si x"
proof -
  have "Si = (\<lambda>t. LBINT x=ereal 0..ereal t. sin_x_over_x_fixed x)"
    apply (rule ext, simp add: Si_def zero_ereal_def)
    apply (rule interval_integral_cong_AE)
    by (rule AE_I' [where N = "{0}"], auto)
  thus ?thesis
    apply (elim ssubst)
    apply (rule DERIV_isCont)
    apply (subst has_field_derivative_within_open [symmetric, 
      where s = "{(min (x - 1) (- 1))<..<(max 1 (x+1))}"], auto)
    apply (rule DERIV_subset [where s = "{(min (x - 2) (- 2))..(max 2 (x+2))}"])
    apply (rule interval_integral_FTC2)
    by (auto intro: continuous_at_imp_continuous_on isCont_sin_x_over_x_fixed)
qed

lemma borel_measurable_iSi: "f \<in> borel_measurable M \<Longrightarrow> 
  (\<lambda>x. Si (f x)) \<in> borel_measurable M"
  apply (rule borel_measurable_continuous_on) back
  by (rule continuous_at_imp_continuous_on, auto intro: iSi_isCont)

lemma iSi_integrable: "interval_lebesgue_integrable lborel (ereal 0)
     (ereal T) (\<lambda>t. sin (t * theta) / t)"
  sorry

lemma iSi_bounded: "\<exists>B. \<forall>T. abs (Si T) \<le> B"
  sorry

lemma borel_measurable_sgn [measurable (raw)]:
  fixes f :: "real \<Rightarrow> real"
  assumes "f \<in> borel_measurable M"
  shows "(\<lambda>x. sgn (f x)) \<in> borel_measurable M"
proof -
  have "(\<lambda>x. sgn (f x)) = (\<lambda>x. indicator {0<..} (f x) - indicator {..<0} (f x))"
    unfolding indicator_def by auto
  thus ?thesis
    apply (elim ssubst) 
    using assms by measurable
qed

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
    interpret P: pair_sigma_finite lborel M ..
    from iSi_bounded obtain B where Bprop: "\<And>T. abs (Si T) \<le> B" by auto
    from Bprop [of 0] have [simp]: "B \<ge> 0" by auto
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
            2 * (sin (t * (x - a)) / t) - 2 * (sin (t * (x - b)) / t)))"
          apply (rule complex_interval_integral_cong)
          using `T \<ge> 0` apply (auto simp add: field_simps of_real_mult expi_def cis_def
             i_complex_of_real)
          apply (subst (2 5 7 10) minus_diff_eq [symmetric])
          apply (simp only: sin_minus cos_minus)
          by (simp add: complex_of_real_def field_simps)
        also have "\<dots> = complex_of_real (LBINT t=(0::real)..T. 
            2 * (sin (t * (x - a)) / t) - 2 * (sin (t * (x - b)) / t))" 
          by (rule complex_interval_integral_of_real)
        also have "\<dots> = complex_of_real (2 * (sgn (x - a) * Si (T * abs (x - a)) -
            sgn (x - b) * Si (T * abs (x - b))))"
          apply (rule arg_cong) back
          apply (subst interval_lebesgue_integral_diff)
          apply (rule interval_lebesgue_integral_cmult, rule iSi_integrable)+
          apply (subst interval_lebesgue_integral_cmult, rule iSi_integrable)+
          by (subst Billingsley_26_15, rule `T \<ge> 0`)+ (simp) 
        finally have "(CLBINT t. ?f' (t, x)) = complex_of_real (
            2 * (sgn (x - a) * Si (T * abs (x - a)) - sgn (x - b) * Si (T * abs (x - b))))" .
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
        by (simp add: field_simps exp_diff exp_minus)
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
      also have "\<dots> = (CLINT x | M. (complex_of_real (2 * (sgn (x - a) * 
           Si (T * abs (x - a)) - sgn (x - b) * Si (T * abs (x - b))))))"
         using main_eq by (intro complex_integral_cong, auto)
      also have "\<dots> = complex_of_real (LINT x | M. (2 * (sgn (x - a) * 
           Si (T * abs (x - a)) - sgn (x - b) * Si (T * abs (x - b)))))"
         by (rule complex_integral_of_real)
      finally have "(CLBINT t=-T..T. ?F t * \<phi> t) = 
          complex_of_real (LINT x | M. (2 * (sgn (x - a) * 
           Si (T * abs (x - a)) - sgn (x - b) * Si (T * abs (x - b)))))" .
    } note main_eq2 = this
    have "(\<lambda>T :: nat. LINT x | M. (2 * (sgn (x - a) * 
           Si (T * abs (x - a)) - sgn (x - b) * Si (T * abs (x - b))))) ----> 
         (LINT x | M. 2 * pi * indicator {a<..b} x)"
      apply (rule integral_dominated_convergence [of _ _ "\<lambda>x. 4 * B"])
      apply (rule integral_cmult)
      apply (rule integral_diff)
      apply (rule M.integrable_const_bound [of _ B])
      apply (rule AE_I2)
      apply (case_tac "x = xa")
      apply (auto simp add: abs_mult abs_sgn_eq) [1]
      apply (rule Bprop)
      apply (auto simp add: abs_mult abs_sgn_eq) [1]
      apply (rule Bprop)
      apply measurable
      apply (rule borel_measurable_iSi)
      apply measurable
      apply (rule M.integrable_const_bound [of _ B])
      apply (rule AE_I2)
      apply (case_tac "x = xa")
      apply (auto simp add: abs_mult abs_sgn_eq) [1]
      apply (rule Bprop)
      apply (auto simp add: abs_mult abs_sgn_eq) [1]
      apply (rule Bprop)
      apply measurable
      apply (rule borel_measurable_iSi)
      apply measurable
      apply (rule AE_I2)
      apply (subst abs_mult, simp)
      apply (rule order_trans [OF abs_triangle_ineq4])
      apply (case_tac "x = a")
      apply (auto simp add: abs_mult abs_sgn_eq) [1]
      apply (rule order_trans)
      apply (rule Bprop)
      using `B \<ge> 0` apply arith
      apply (auto simp add: abs_mult abs_sgn_eq) [1]
      apply (rule order_trans)
      apply (rule Bprop)
      using `B \<ge> 0` apply arith
      apply (rule order_trans)
      apply (rule add_mono)
      apply (rule Bprop)+
      apply arith
      apply (rule M.lebesgue_integral_const)
      apply (rule AE_I [of _ _ "{a, b}"], auto)
      prefer 2
      using assms apply (simp add: emeasure_insert M.emeasure_eq_measure)
      apply (case_tac "a = b", auto) 
      apply (subst M.finite_measure_eq_setsum_singleton, auto)
      apply (rule ccontr)
      apply (erule notE) back
      apply (auto split: split_indicator)
      apply (subgoal_tac "2 * pi = 2 * (pi / 2) + 2 * (pi / 2)")
      apply (erule ssubst)
      apply (rule tendsto_add)
      apply (rule tendsto_mult, rule tendsto_const)
      apply (rule filterlim_compose [OF Si_at_top])
      apply (subst mult_commute)
      apply (rule filterlim_tendsto_pos_mult_at_top, rule tendsto_const)
      apply force
      apply (rule filterlim_real_sequentially)
      apply (rule tendsto_mult, rule tendsto_const)
      apply (rule filterlim_compose [OF Si_at_top])
      apply (subst mult_commute)
      apply (rule filterlim_tendsto_pos_mult_at_top, rule tendsto_const)
      apply force
      apply (rule filterlim_real_sequentially)
      apply force
      using `a \<le> b` apply auto
      apply (subgoal_tac "0 = 2 * (pi / 2) - 2 * (pi / 2)")
      apply (erule ssubst)
      apply (rule tendsto_diff)
      apply (rule tendsto_mult, rule tendsto_const)
      apply (rule filterlim_compose [OF Si_at_top])
      apply (subst mult_commute)
      apply (rule filterlim_tendsto_pos_mult_at_top, rule tendsto_const)
      apply force
      apply (rule filterlim_real_sequentially)
      apply (rule tendsto_mult, rule tendsto_const)
      apply (rule filterlim_compose [OF Si_at_top])
      apply (subst mult_commute)
      apply (rule filterlim_tendsto_pos_mult_at_top, rule tendsto_const)
      apply force
      apply (rule filterlim_real_sequentially)
      apply force
      (* this duplicates the last 16 lines! *)
      apply (subgoal_tac "0 = 2 * (pi / 2) - 2 * (pi / 2)")
      apply (erule ssubst)
      apply (rule tendsto_diff)
      apply (rule tendsto_mult, rule tendsto_const)
      apply (rule filterlim_compose [OF Si_at_top])
      apply (subst mult_commute)
      apply (rule filterlim_tendsto_pos_mult_at_top, rule tendsto_const)
      apply force
      apply (rule filterlim_real_sequentially)
      apply (rule tendsto_mult, rule tendsto_const)
      apply (rule filterlim_compose [OF Si_at_top])
      apply (subst mult_commute)
      apply (rule filterlim_tendsto_pos_mult_at_top, rule tendsto_const)
      apply force
      apply (rule filterlim_real_sequentially)
      by force
    also have "(LINT x | M. 2 * pi * indicator {a<..b} x) = 2 * pi * \<mu> {a<..b}"
      by (subst set_integral_cmult, auto simp add: M.emeasure_eq_measure \<mu>_def)
    finally have main3: "(\<lambda>T. LINT x | M. (2 * (sgn (x - a) * 
           Si (T * abs (x - a)) - sgn (x - b) * Si (T * abs (x - b))))) ----> 
         2 * pi * \<mu> {a<..b}" .
  show ?thesis
    apply (subst real_of_int_minus)
    apply (subst real_of_int_of_nat_eq)
    apply (subst main_eq2, force)
    apply (subst of_real_mult [symmetric])
    apply (rule tendsto_of_real)
    apply (rule tendsto_const_mult [of "2 * pi"])
    apply auto
    apply (subst right_diff_distrib [symmetric])
    by (rule main3)
qed

(*
  The Levy contintuity theorem.
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
    "\<And>t. (\<lambda>n. char (M n) t) ----> char M' t"

  apply (subst tendsto_complex_iff, rule conjI)
  unfolding char_def complex_lebesgue_integral_def apply simp_all
  apply (rule weak_conv_imp_integral_bdd_continuous_conv [OF assms], auto)
  apply (rule order_trans [OF abs_Re_le_cmod], subst cmod_iexp, rule order_refl)
  apply (rule weak_conv_imp_integral_bdd_continuous_conv [OF assms], auto)
by (rule order_trans [OF abs_Im_le_cmod], subst cmod_iexp, rule order_refl)

(* TODO: should this be a simp rule? *)
lemma complex_of_real_indicator: "complex_of_real (indicator A x) = indicator A x"
  by (simp split: split_indicator)

(* TODO: should we have a library of facts like these? *)
lemma integral_cos: "t \<noteq> 0 \<Longrightarrow> LBINT x=a..b. cos (t * x) = sin (t * b) / t - sin (t * a) / t"
  apply (rule interval_integral_FTC_finite)
  by (rule continuous_at_imp_continuous_on, auto intro!: derivative_eq_intros)

lemma sin_x_le_x: "x \<ge> 0 \<Longrightarrow> sin x \<le> x"
proof -
  fix x :: real 
  assume "x \<ge> 0"
  let ?f = "\<lambda>x. x - sin x"
  have "?f x \<ge> ?f 0"
    apply (rule DERIV_nonneg_imp_nondecreasing [OF `x \<ge> 0`])
    apply auto
    apply (rule_tac x = "1 - cos x" in exI)
    apply (auto intro!: derivative_intros)
    by (simp add: field_simps)
  thus "sin x \<le> x" by simp
qed

lemma sin_x_ge_neg_x: "x \<ge> 0 \<Longrightarrow> sin x \<ge> - x"
proof -
  fix x :: real 
  assume "x \<ge> 0"
  let ?f = "\<lambda>x. x + sin x"
  have "?f x \<ge> ?f 0"
    apply (rule DERIV_nonneg_imp_nondecreasing [OF `x \<ge> 0`])
    apply auto
    apply (rule_tac x = "1 + cos x" in exI)
    apply (auto intro!: derivative_intros)
    by (metis cos_ge_minus_one real_0_le_add_iff)
  thus "sin x \<ge> -x" by simp
qed

lemma abs_sin_x_le_abs_x: "abs (sin x) \<le> abs x"
  using sin_x_ge_neg_x [of x] sin_x_le_x [of x] sin_x_ge_neg_x [of "-x"] sin_x_le_x [of "-x"]
  by (case_tac "x \<ge> 0", auto)

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
  have *: "\<And>u x. u > 0 \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> (CLBINT t:{-u..u}. 1 - iexp (t * x)) = 
      2 * (u  - sin (u * x) / x)"
  proof -
    fix u :: real and x :: real
    assume "u > 0" and "x \<noteq> 0"
    hence "(CLBINT t:{-u..u}. 1 - iexp (t * x)) = (CLBINT t=-u..u. 1 - iexp (t * x))"
      by (subst complex_interval_integral_Icc, auto)
    also have "\<dots> = (CLBINT t=-u..0. 1 - iexp (t * x)) + (CLBINT t=0..u. 1 - iexp (t * x))"
      using `u > 0` apply (subst complex_interval_integral_sum, auto)
      (* TODO: this next part should be automatic *)
      apply (subst min_absorb1)+
      apply auto
      apply (subst max_absorb2)+
      apply auto
      apply (subst max_absorb2)
      apply auto
      by (rule complex_interval_integrable_isCont, auto)
    also have "\<dots> = (CLBINT t=ereal 0..u. 1 - iexp (t * -x)) + (CLBINT t=ereal 0..u. 1 - iexp (t * x))"
      apply (subgoal_tac "0 = ereal 0", erule ssubst)
      by (subst complex_interval_integral_reflect, auto)
    also have "\<dots> = (CLBINT t=ereal 0..u. 2 + -2 * cos (t * x))"
      apply (subst complex_interval_lebesgue_integral_add (2) [symmetric])
      apply (rule complex_interval_integrable_isCont, auto)+
      (* TODO: shouldn't of_real_numeral be a simplifier rule? *)
      by (auto simp add: expi_def cis_def complex_of_real_def [symmetric] of_real_numeral)
    also have "\<dots> = 2 * u - 2 * sin (u * x) / x"
      apply simp
      apply (subst complex_interval_lebesgue_integral_diff)
      apply (auto intro!: complex_interval_integrable_isCont)
      apply (subst complex_interval_integral_of_real)
      apply (subst interval_lebesgue_integral_cmult)
      apply (auto intro!: interval_integrable_isCont)
      apply (subst (2) mult_commute)
      by (subst integral_cos [OF `x \<noteq> 0`], simp add: mult_commute)
    finally show "(CLBINT t:{-u..u}. 1 - iexp (t * x)) = 2 * (u  - sin (u * x) / x)"
      by (simp add: field_simps)
  qed
 
  have "\<And>u n. u > 0 \<Longrightarrow> Re (CLBINT t:{-u..u}. 1 - char (M n) t) / u \<ge> 
    measure (M n) {x. abs x \<ge> 2 / u}"
  proof -
    fix u :: real and n
    assume "u > 0"
    interpret Mn: real_distribution "M n" by (rule assms)
    interpret P: pair_sigma_finite "M n" lborel ..
    (* TODO: put this in the real_distribution locale as a simp rule? *)
    have Mn1 [simp]: "measure (M n) UNIV = 1" by (metis Mn.prob_space Mn.space_eq_univ)
    (* TODO: make this automatic somehow? *)
    have Mn2 [simp]: "\<And>x. complex_integrable (M n) (\<lambda>t. expi (\<i> * complex_of_real (x * t)))"
      by (rule Mn.complex_integrable_const_bound [where B = 1], auto)
    have Mn3: "complex_integrable (M n \<Otimes>\<^sub>M lborel) 
        (\<lambda>a. (1 - expi (\<i> * complex_of_real (snd a * fst a))) * indicator {- u..u} (snd a))"
      apply (rule complex_integrable_bound [where f = "\<lambda>p. 2 * indicator (UNIV \<times> {-u..u}) p"])
      apply (rule integral_cmult)
      apply (rule integral_indicator, auto)
      apply (subst (asm) lborel.emeasure_pair_measure_Times, auto intro!: AE_I2 
         split: split_indicator)
      by (rule order_trans [OF norm_triangle_ineq4], auto)
    have "(CLBINT t:{-u..u}. 1 - char (M n) t) = 
        (CLBINT t:{-u..u}. (CLINT x | M n. 1 - iexp (t * x)))"
      unfolding char_def by (rule complex_set_lebesgue_integral_cong, auto)
    also have "\<dots> = (CLBINT t. (CLINT x | M n. (1 - iexp (t * x)) * indicator {-u..u} t))"
      apply (rule complex_integral_cong, auto)
      (* TODO: have versions of integral_cmult with the constant on the other side? *)
      by (subst (3 6) mult_commute, auto)
    also have "\<dots> = (CLBINT t. (CLINT x | M n. (1 - iexp (snd (x, t) * fst (x, t))) *
        indicator {-u..u} (snd (x, t))))" by simp
    also have "\<dots> = (CLINT x | M n. (CLBINT t:{-u..u}. 1 - iexp (t * x)))"
      by (subst P.complex_Fubini_integral [OF Mn3], auto)
    also have "\<dots> = (CLINT x | M n. (if x = 0 then 0 else 2 * (u  - sin (u * x) / x)))"
      using `u > 0` by (intro complex_integral_cong, auto simp add: *)
    also have "\<dots> = (LINT x | M n. (if x = 0 then 0 else 2 * (u  - sin (u * x) / x)))"
      by (rule complex_of_real_lebesgue_integral [symmetric])
    finally have "Re (CLBINT t:{-u..u}. 1 - char (M n) t) = 
       (LINT x | M n. (if x = 0 then 0 else 2 * (u  - sin (u * x) / x)))" by simp
    also have "\<dots> \<ge> (LINT x : {x. abs x \<ge> 2 / u} | M n. u)"
    proof -
      (* TODO: this parallels the computation of the integral above. In this case, it would
         be natural to have a predicate "f has_integral y" instead of "integrable f" and 
          "integral f = y" *)
      have "complex_integrable (M n) (\<lambda>x. CLBINT t. (1 - iexp (snd (x, t) * fst (x, t))) * 
          indicator {-u..u} (snd (x, t)))"
        by (rule P.complex_Fubini_integrable [OF Mn3])
      hence "complex_integrable (M n) (\<lambda>x. if x = 0 then 0 else 2 * (u  - sin (u * x) / x))"
        apply (subst complex_integrable_cong)
        prefer 2 apply assumption
        using `u > 0` by (auto simp add: *)
      hence **: "integrable (M n) (\<lambda>x. if x = 0 then 0 else 2 * (u  - sin (u * x) / x))"
        by (subst complex_of_real_integrable_eq)
      show ?thesis
        apply (rule integral_mono [OF _ **], auto split: split_indicator)
        using `u > 0` apply (case_tac "t \<ge> 0", auto simp add: field_simps)
        apply (rule order_trans)
        prefer 2 apply assumption
        apply auto
        apply (subgoal_tac "t * u \<le> -2")
        apply (erule order_trans)
        apply auto
        using `u > 0` apply (case_tac "t > 0", auto simp add: field_simps not_le)
        apply (rule order_trans [OF sin_x_le_x], auto intro!: mult_nonneg_nonneg)
        apply (subst neg_le_iff_le [symmetric])
        apply (subst sin_minus [symmetric])
        by (rule sin_x_le_x, auto intro: mult_nonpos_nonneg)
    qed
    also (xtrans) have "(LINT x : {x. abs x \<ge> 2 / u} | M n. u) = 
        u * measure (M n) {x. abs x \<ge> 2 / u}"
      by (simp add: Mn.emeasure_eq_measure)
    finally show "Re (CLBINT t:{-u..u}. 1 - char (M n) t) / u \<ge> measure (M n) {x. abs x \<ge> 2 / u}" 
      by (simp add: field_simps `u > 0`)
  qed

  have "tight M"
    unfolding tight_def apply (auto simp add: assms)
    sorry
  show ?thesis
    sorry
qed



end
