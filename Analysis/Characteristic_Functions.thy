(*
Theory: Characteristic_Functions.thy
Authors: Jeremy Avigad, Luke Serafin
*)

theory Characteristic_Functions

imports Weak_Convergence Real_to_Complex Independent_Family Si Auxiliary Normal_Moments

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
  Independence
*)

lemma (in prob_space)
  assumes "indep_var borel X1 borel X2" "integrable M X1" "integrable M X2"
  shows indep_var_lebesgue_integral: "(\<integral>\<omega>. X1 \<omega> * X2 \<omega> \<partial>M) = (\<integral>\<omega>. X1 \<omega> \<partial>M) * (\<integral>\<omega>. X2 \<omega> \<partial>M)" (is ?eq)
    and indep_var_integrable: "integrable M (\<lambda>\<omega>. X1 \<omega> * X2 \<omega>)" (is ?int)
unfolding indep_var_def
proof -
  have *: "(\<lambda>\<omega>. X1 \<omega> * X2 \<omega>) = (\<lambda>\<omega>. \<Prod>i\<in>UNIV. (case_bool X1 X2 i \<omega>))"
    by (simp add: UNIV_bool mult_commute)
  have **: "(\<lambda> _. borel) = case_bool borel borel"
    by (rule ext, metis (full_types) bool.simps(3) bool.simps(4))
  show ?eq
    apply (subst *, subst indep_vars_lebesgue_integral, auto)
    apply (subst **, subst indep_var_def [symmetric], rule assms)
    apply (simp split: bool.split add: assms)
    by (simp add: UNIV_bool mult_commute)
  show ?int
    apply (subst *, rule indep_vars_integrable, auto)
    apply (subst **, subst indep_var_def [symmetric], rule assms)
    by (simp split: bool.split add: assms)
qed

(* the automation can probably be improved *)  
lemma (in prob_space) char_distr_sum:
  fixes X1 X2 :: "'a \<Rightarrow> real" and t :: real
  assumes "indep_var borel X1 borel X2"
  shows "char (distr M borel (\<lambda>\<omega>. X1 \<omega> + X2 \<omega>)) t =
    char (distr M borel X1) t * char (distr M borel X2) t"
using assms proof -
  note indep_var_compose2 = indep_var_compose [unfolded comp_def]
  from assms have [simp]: "random_variable borel X1" by (elim indep_var_rv1)
  from assms have [simp]: "random_variable borel X2" by (elim indep_var_rv2)
  have [simp]: "random_variable borel (\<lambda>\<omega>. X1 \<omega> + X2 \<omega>)" by (rule borel_measurable_add, auto)
  have [simp]: "(\<lambda>x. cos (t * x)) \<in> borel_measurable borel" by (rule borel_measurable_isCont, auto)
  have [simp]: "(\<lambda>x. sin (t * x)) \<in> borel_measurable borel" by (rule borel_measurable_isCont, auto)
  have [simp]: "random_variable borel (\<lambda>\<omega>. cos (t * X1 \<omega>))"
    by (rule measurable_compose [of _ _ borel "\<lambda>x. cos(t * x)"], simp_all)
  have [simp]: "random_variable borel (\<lambda>\<omega>. cos (t * X2 \<omega>))"
    by (rule measurable_compose [of _ _ borel "\<lambda>x. cos(t * x)"], simp_all)
  have [simp]: "random_variable borel (\<lambda>\<omega>. sin (t * X1 \<omega>))"
    by (rule measurable_compose [of _ _ borel "\<lambda>x. sin(t * x)"], simp_all)
  have [simp]: "random_variable borel (\<lambda>\<omega>. sin (t * X2 \<omega>))"
    by (rule measurable_compose [of _ _ borel "\<lambda>x. sin(t * x)"], simp_all)
  have [simp]: "integrable M (\<lambda>\<omega>. cos (t * X1 \<omega>))" by (rule integrable_const_bound [of _ 1], auto)
  have [simp]: "integrable M (\<lambda>\<omega>. cos (t * X2 \<omega>))" by (rule integrable_const_bound [of _ 1], auto)
  have [simp]: "integrable M (\<lambda>\<omega>. sin (t * X1 \<omega>))" by (rule integrable_const_bound [of _ 1], auto)
  have [simp]: "integrable M (\<lambda>\<omega>. sin (t * X2 \<omega>))" by (rule integrable_const_bound [of _ 1], auto)
  have [simp]: "integrable M (\<lambda>x. cos (t * X1 x) * cos (t * X2 x))" 
    by (rule indep_var_integrable, rule indep_var_compose2 [OF assms], auto)
  have [simp]: "indep_var borel (\<lambda>x. cos (t * X1 x)) borel (\<lambda>x. cos (t * X2 x))"
    by (rule indep_var_compose2 [OF assms], auto) 
  have [simp]: "integrable M (\<lambda>x. sin (t * X1 x) * sin (t * X2 x))" 
    by (rule indep_var_integrable, rule indep_var_compose2 [OF assms], auto)
  have [simp]: "indep_var borel (\<lambda>x. sin (t * X1 x)) borel (\<lambda>x. sin (t * X2 x))"
    by (rule indep_var_compose2 [OF assms], auto) 
  have [simp]: "integrable M (\<lambda>x. cos (t * X1 x) * sin (t * X2 x))" 
    by (rule indep_var_integrable, rule indep_var_compose2 [OF assms], auto)
  have [simp]: "indep_var borel (\<lambda>x. sin (t * X1 x)) borel (\<lambda>x. cos (t * X2 x))"
    by (rule indep_var_compose2 [OF assms], auto) 
  have [simp]: "integrable M (\<lambda>x. sin (t * X1 x) * cos (t * X2 x))" 
    by (rule indep_var_integrable, rule indep_var_compose2 [OF assms], auto)
  have [simp]: "indep_var borel (\<lambda>x. cos (t * X1 x)) borel (\<lambda>x. sin (t * X2 x))"
    by (rule indep_var_compose2 [OF assms], auto) 
  show ?thesis 
    using assms unfolding char_def complex_lebesgue_integral_def expi_def apply auto
    by (simp_all add: integral_distr cos_add sin_add ring_distribs indep_var_lebesgue_integral)
qed

lemma (in prob_space) char_distr_setsum:
  fixes 
    X_seq :: "nat \<Rightarrow> 'a \<Rightarrow> real" and
    t :: real and
    A :: "nat set"
  assumes 
    X_seq_indep: "indep_vars (\<lambda>i. borel) X_seq UNIV" and
    fin_A: "finite A"
  shows "char (distr M borel (\<lambda>\<omega>. \<Sum> i \<in> A. X_seq i \<omega>)) t = 
    (\<Prod> i \<in> A. char (distr M borel (X_seq i)) t)" (is "?P A")
using fin_A proof(induct A rule: finite_induct)
  show "?P {}"
    by (auto simp add: char_def complex_lebesgue_integral_def integral_distr prob_space)
  next
    fix x F
    assume "finite F" and "x \<notin> F" and ih: "?P F"
    thus "?P (insert x F)"
      by (auto simp add: setsum_insert setprod_insert char_distr_sum indep_vars_setsum
        indep_vars_subset [OF X_seq_indep])
qed

(*
  Approximations to e^ix from Billingsley, page 343
*)

lemma fact1: "CDERIV (%s. complex_of_real(-((x - s) ^ (Suc n) / (Suc n))) * iexp s)
 s : A :> complex_of_real((x - s)^n) * iexp s + (ii * iexp s) * 
      complex_of_real(-((x - s) ^ (Suc n) / (Suc n)))"
  apply (rule CDERIV_mult)
  apply (rule CDERIV_of_real)
  apply (auto intro!: derivative_eq_intros simp del: power_Suc simp add: 
    real_of_nat_Suc real_of_nat_def)
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
  (* the nex few lines should be automatic *)
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
  shows "iexp x = (\<Sum>k \<le> n. (ii * x)^k / (fact k)) + 
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
    apply (simp add: field_simps real_of_nat_Suc of_real_mult[symmetric] of_real_add[symmetric]
        del: i_complex_of_real of_real_mult of_real_add)
    done
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
    by (auto intro!: derivative_eq_intros simp del: power_Suc simp add: real_of_nat_def)
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

declare i_complex_of_real [simp del]

lemma equation_26p4a: "cmod (iexp x - (\<Sum>k \<le> n. (ii * x)^k / fact k)) \<le>
    (abs x)^(Suc n) / fact (Suc n)"
proof -
  have "iexp x - (\<Sum>k \<le> n. (ii * x)^k / fact k) = 
         ((ii ^ (Suc n)) / (fact n)) * (CLBINT s=0..x. (x - s)^n * (iexp s))" (is "?t1 = ?t2")
    by (subst equation_26p2 [of _ n], simp add: field_simps)
  hence "cmod (?t1) = cmod (?t2)" by simp
  also have "\<dots> =  (1 / (fact n)) * cmod (CLBINT s=0..x. (x - s)^n * (iexp s))"
    by (simp add: norm_mult norm_divide norm_power)
  also have "\<dots> \<le> (1 / (fact n)) * abs (LBINT s=0..x. cmod ((x - s)^n * (iexp s)))"
    apply (rule mult_left_mono, rule complex_interval_integral_cmod2)
    apply auto
    apply (subst zero_ereal_def)
    apply (rule complex_interval_integrable_isCont)
    by auto
  also have "\<dots> \<le> (1 / (fact n)) * abs (LBINT s=0..x. abs ((x - s)^n))"
    by (simp add: norm_mult i_complex_of_real del: of_real_diff of_real_power)
  also have "abs (LBINT s=0..x. abs ((x - s)^n)) = abs (LBINT s=0..x. (x - s)^n)"
    proof (cases "0 \<le> x | even n")
      assume "0 \<le> x \<or> even n"
      hence "(LBINT s=0..x. abs ((x - s)^n)) = LBINT s=0..x. (x - s)^n"
        apply (subst zero_ereal_def)+
        apply (rule interval_integral_cong, auto simp add: power_even_abs power_abs)
        by (auto simp add: min_absorb1 max_absorb2)
      thus ?thesis by simp
    next
      assume "\<not> (0 \<le> x \<or> even n)" 
      hence "(LBINT s=0..x. abs ((x - s)^n)) = LBINT s=0..x. -((x - s)^n)"
        apply (subst zero_ereal_def)+
        apply (rule interval_integral_cong)
        apply (auto simp add: min_absorb2 max_absorb1 power_abs)
        apply (subst power_minus_odd [symmetric], assumption) 
        by (subst minus_diff_eq, rule refl)
      also have "\<dots> = - (LBINT s=0..x. (x - s)^n)"
        by (subst interval_lebesgue_integral_uminus, rule refl)
      finally show ?thesis by simp 
    qed
  also have "LBINT s=0..x. (x - s)^n =  (x ^ (Suc n) / (Suc n))"
  proof -
    let ?F = "\<lambda>t. - ((x - t)^(Suc n) / Suc n)"
    have "LBINT s=0..x. (x - s)^n = ?F x - ?F 0"
      apply (subst zero_ereal_def, rule interval_integral_FTC_finite)
      apply (rule continuous_at_imp_continuous_on)
      apply force
      apply (rule DERIV_subset)
      by (auto simp del: power_Suc intro!: derivative_eq_intros simp add: real_of_nat_def)
    also have "\<dots> = x ^ (Suc n) / (Suc n)" by simp
    finally show ?thesis .
  qed
  also have "1 / real (fact n) * \<bar>x ^ Suc n / real (Suc n)\<bar> = 
      \<bar>x\<bar> ^ Suc n / real (fact (Suc n))"
    apply (subst abs_divide, subst power_abs, subst (2) abs_of_nonneg, simp)
    by (simp add: field_simps real_of_nat_Suc)
  finally show ?thesis .
qed

lemma equation_26p4b: "cmod (iexp x - (\<Sum>k \<le> n. (ii * x)^k / fact k)) \<le>
    2 * (abs x)^n / fact n" (is "?P n")
proof (induction n)  (* really cases *)
show "?P 0" 
  apply simp
  by (rule order_trans [OF norm_triangle_ineq4], simp add: i_complex_of_real)
next
  {
    fix a b f g
    assume f: "\<And>s. 0 \<le> f s" and g: "(\<And>s. f s \<le> g s)" and
      iif: "interval_lebesgue_integrable lborel a b f" and 
      iig: "interval_lebesgue_integrable lborel a b g"
    have "abs (LBINT s=a..b. f s) \<le> abs (LBINT s=a..b. g s)"
      using f g order_trans[OF f g] iif iig
      unfolding interval_lebesgue_integral_def interval_lebesgue_integrable_def 
      by (auto simp: lebesgue_integral_nonneg intro!: set_integral_mono)
  } note useful = this

fix n
show "?P (Suc n)"
proof -
  have "iexp x - (\<Sum>k \<le> Suc n. (ii * x)^k / fact k) = 
         ((ii ^ (Suc n)) / (fact n)) * (CLBINT s=0..x. (x - s)^n * (iexp s - 1))" 
            (is "?t1 = ?t2")
    by (subst equation_26p3 [of _ n], simp add: field_simps)
  hence "cmod (?t1) = cmod (?t2)" by simp
  also have "\<dots> =  (1 / (fact n)) * cmod (CLBINT s=0..x. (x - s)^n * (iexp s - 1))"
    by (simp add: norm_mult norm_divide norm_power)
  also have "\<dots> \<le> (1 / (fact n)) * abs (LBINT s=0..x. cmod ((x - s)^n * (iexp s - 1)))"
    apply (rule mult_left_mono, rule complex_interval_integral_cmod2)
    apply auto
    apply (subst zero_ereal_def)
    apply (rule complex_interval_integrable_isCont)
    by auto
  also have "\<dots> = (1 / (fact n)) * abs (LBINT s=0..x. abs ((x - s)^n) * cmod((iexp s - 1)))"
    by (simp add: norm_mult i_complex_of_real del: of_real_diff of_real_power)
  also have "\<dots> \<le> (1 / (fact n)) * abs (LBINT s=0..x. abs ((x - s)^n) * 2)"
    apply (rule mult_left_mono)
    prefer 2 apply force
    apply (rule useful)
    apply (rule mult_nonneg_nonneg, auto)
    apply (rule mult_left_mono, auto)
    apply (rule order_trans [OF norm_triangle_ineq4], simp add: i_complex_of_real)
    apply (subst mult_commute)
    apply (subst zero_ereal_def)
    apply (rule interval_integrable_isCont, auto)
    apply (subst zero_ereal_def)
    by (rule interval_integrable_isCont, auto)
  also have "\<dots> = (2 / (fact n)) * abs (LBINT s=0..x. abs ((x - s)^n))"
    apply simp
    apply (subst mult_commute)
    apply (subst interval_lebesgue_integral_cmult)
    apply (subst zero_ereal_def)
    by (rule interval_integrable_isCont, auto)
  (* duplicates lines from previous proof -- refactor *)
  also have "abs (LBINT s=0..x. abs ((x - s)^n)) = abs (LBINT s=0..x. (x - s)^n)"
    proof (cases "0 \<le> x | even n")
      assume "0 \<le> x \<or> even n"
      hence "(LBINT s=0..x. abs ((x - s)^n)) = LBINT s=0..x. (x - s)^n"
        apply (subst zero_ereal_def)+
        apply (rule interval_integral_cong, auto simp add: power_even_abs power_abs)
        by (auto simp add: min_absorb1 max_absorb2)
      thus ?thesis by simp
    next
      assume "\<not> (0 \<le> x \<or> even n)" 
      hence "(LBINT s=0..x. abs ((x - s)^n)) = LBINT s=0..x. -((x - s)^n)"
        apply (subst zero_ereal_def)+
        apply (rule interval_integral_cong)
        apply (auto simp add: min_absorb2 max_absorb1 power_abs)
        apply (subst power_minus_odd [symmetric], assumption) 
        by (subst minus_diff_eq, rule refl)
      also have "\<dots> = - (LBINT s=0..x. (x - s)^n)"
        by (subst interval_lebesgue_integral_uminus, rule refl)
      finally show ?thesis by simp 
    qed
  also have "LBINT s=0..x. (x - s)^n =  (x ^ (Suc n) / (Suc n))"
  proof -
    let ?F = "\<lambda>t. - ((x - t)^(Suc n) / Suc n)"
    have "LBINT s=0..x. (x - s)^n = ?F x - ?F 0"
      apply (subst zero_ereal_def, rule interval_integral_FTC_finite)
      apply (rule continuous_at_imp_continuous_on)
      apply force
      apply (rule DERIV_subset)
      by (auto simp del: power_Suc intro!: derivative_eq_intros simp add: real_of_nat_def)
    also have "\<dots> = x ^ (Suc n) / (Suc n)" by simp
    finally show ?thesis .
  qed
  also have "2 / real (fact n) * \<bar>x ^ Suc n / real (Suc n)\<bar> = 
      2 * \<bar>x\<bar> ^ Suc n / real (fact (Suc n))"
    apply (subst abs_divide, subst power_abs, subst (2) abs_of_nonneg, simp)
    by (simp add: field_simps real_of_nat_Suc)
  finally show ?thesis .
qed
qed


(* move these to Real_to_Complex *)

declare complex_integrable_measurable [simp]

lemma complex_integral_distr:
  "T \<in> measurable M M' \<Longrightarrow> f \<in> borel_measurable M' \<Longrightarrow> 
    complex_lebesgue_integral (distr M M' T) f = (CLINT x | M. f (T x))"
  unfolding complex_lebesgue_integral_def
by (simp add: integral_distr)

lemma complex_integrable_distr_eq:
  "T \<in> measurable M M' \<Longrightarrow> f \<in> borel_measurable M' \<Longrightarrow> complex_integrable (distr M M' T) f \<longleftrightarrow> 
    complex_integrable M (\<lambda>x. f (T x))"
  unfolding complex_integrable_def
by (simp add: integrable_distr_eq)

lemma complex_integrable_distr:
  "T \<in> measurable M M' \<Longrightarrow> complex_integrable (distr M M' T) f \<Longrightarrow> 
    complex_integrable M (\<lambda>x. f (T x))"
  apply (subst complex_integrable_distr_eq[symmetric]) back
  apply auto
by (frule complex_integrable_measurable, simp)

lemma of_real_setsum:
  "of_real (setsum f S) = setsum (\<lambda>x. of_real (f x)) S"
  apply (case_tac "finite S", auto)
by (induct rule: finite_induct, auto)

lemma complex_integrable_bound:
  assumes "integrable M f" and f: "AE x in M. cmod (g x) \<le> f x"
  assumes borel: "g \<in> borel_measurable M"
  shows "complex_integrable M g"
using assms unfolding complex_integrable_def apply auto
  apply (erule integrable_bound, erule AE_mp, rule AE_I2, auto)
  apply (rule order_trans, rule abs_Re_le_cmod, assumption)
  apply (erule integrable_bound, erule AE_mp, rule AE_I2, auto)
by (rule order_trans, rule abs_Im_le_cmod, assumption)

lemma (in finite_measure) complex_integrable_const_bound:
  "AE x in M. cmod (f x) \<le> B \<Longrightarrow> f \<in> borel_measurable M \<Longrightarrow> complex_integrable M f"
by (rule complex_integrable_bound [of _ "\<lambda>x. B"], auto)

lemma complex_integral_setsum [simp, intro]:
  assumes "\<And>n. n \<in> S \<Longrightarrow> complex_integrable M (f n)"
  shows "(CLINT x | M. (\<Sum> i \<in> S. f i x)) = (\<Sum> i \<in> S. (CLINT x | M. (f i x)))"
    and "complex_integrable M (\<lambda>x. \<Sum> i \<in> S. f i x)" (is "?I S")
  apply (case_tac "finite S", auto)
  prefer 2 apply (case_tac "finite S", auto)
  using assms unfolding complex_integrable_def complex_lebesgue_integral_def
by (auto simp add: Re_setsum Im_setsum of_real_setsum setsum_addf setsum_right_distrib)

lemma cmod_expi_real_eq: "cmod (expi (ii * (x :: real))) = 1"
  by (auto simp add: i_complex_of_real)

(* these calculations were difficult -- in some ways I felt like I was fighting with the
   simplifier. Could we do better?
*)

lemma (in real_distribution) equation_26p5b:
  assumes 
    integrable_moments : "\<And>k. k \<le> n \<Longrightarrow> integrable M (\<lambda>x :: real. x ^ k)"
  shows 
    "cmod (char M t - (\<Sum>k \<le> n. ((ii * t)^k / fact k) * expectation (\<lambda>x. x^k)))
      \<le>  (2 * (abs t)^n / fact n) * expectation (\<lambda>x. (abs x)^n)"
      (is "cmod (char M t - ?t1) \<le> _")
proof -
  have [simplified, simp]: "complex_integrable M (\<lambda>x. iexp (t * x))"
    apply (rule complex_integrable_const_bound, rule AE_I2)
    by (subst cmod_expi_real_eq, auto)
  have *: "\<And>k x. (ii * t * x)^k / fact k = (ii * t)^k / fact k * x^k"
    by (simp add: power_mult_distrib)
  have ** [simp]: "!!k. k \<le> n \<Longrightarrow> complex_integrable M (\<lambda>x. complex_of_real (x ^ k))"
    by (rule complex_of_real_integrable, rule integrable_moments)
  have 1: "\<And>k. k \<le> n \<Longrightarrow> complex_integrable M (\<lambda>x. (ii * t * x)^k / fact k)"
     apply (subst *, rule complex_integral_cmult)
     apply (subst of_real_power [symmetric])
     apply (rule complex_of_real_integrable)
     by (rule integrable_moments)
  have 2: "complex_integrable M (\<lambda>x. (\<Sum>k \<le> n. (ii * t * x)^k / fact k))"
    apply (rule complex_integral_setsum)
    apply (subst *)
    apply (subst of_real_power [symmetric])
    apply (rule complex_integral_cmult)
    apply (rule complex_of_real_integrable) 
    by (rule integrable_moments, simp)
  have 3: "complex_integrable M (\<lambda>x. iexp (t * x) - (\<Sum>k \<le> n. (ii * t * x)^k / fact k))"
    by (rule complex_integral_diff [OF _ 2], auto)
  have "?t1 = (CLINT x | M. (\<Sum>k \<le> n. (ii * t * x)^k / fact k))"
    apply (subst complex_integral_setsum [OF 1], simp)
    apply (rule setsum_cong, force)
    apply (subst *, subst of_real_power [symmetric], subst complex_integral_cmult, rule **, simp)
    by (simp add: field_simps complex_of_real_lebesgue_integral)
  hence "char M t - ?t1 = (CLINT x | M. iexp (t * x) - (\<Sum>k \<le> n. (ii * t * x)^k / fact k))"
      (is "_ = (CLINT x | M. ?f x)")
    apply (elim ssubst)
    apply (subst complex_integral_diff [OF _ 2], auto)
    unfolding char_def by auto
  hence "cmod (char M t - ?t1) \<le> expectation (\<lambda>x. cmod (?f x))"
    apply (elim ssubst)
    by (rule complex_lebesgue_integral_cmod, rule 3)  
  also have "\<dots> \<le> expectation (\<lambda>x. (2 * (abs t)^n / fact n) * (abs x)^n)"
    apply (rule integral_mono)
    apply (rule complex_integrable_cmod [OF 3])
    apply (rule integral_cmult, subst power_abs [symmetric])
    apply (rule integrable_abs, rule integrable_moments, simp)
    apply (rule order_trans)
    apply (subst mult_assoc, subst of_real_mult [symmetric])
    by (rule equation_26p4b, auto simp add: abs_mult power_mult_distrib field_simps)
  also have "\<dots> = (2 * (abs t)^n / fact n) * expectation (\<lambda>x. (abs x)^n)"
    apply (rule integral_cmult, subst power_abs [symmetric])
    by (rule integrable_abs, rule integrable_moments, simp)
  finally show ?thesis .
qed

(* strange this isn't in the library *)
lemma mult_min_right: "a \<ge> 0 \<Longrightarrow> (a :: real) * min b c = min (a * b) (a * c)"
by (metis min.absorb_iff2 min_def mult_left_mono)

lemma (in real_distribution) equation_26p5b_stronger:
  assumes 
    integrable_moments : "\<And>k. k \<le> n \<Longrightarrow> integrable M (\<lambda>x :: real. x ^ k)"
  shows 
    "cmod (char M t - (\<Sum>k \<le> n. ((ii * t)^k / (real (fact k))) * expectation (\<lambda>x. x^k)))
      \<le>  ((abs t)^n / fact (Suc n)) * 
            expectation (\<lambda>x. min (2 * (abs x)^n * (Suc n)) (abs t * (abs x)^(Suc n)))"
      (is "cmod (char M t - ?t1) \<le> _")
proof -
  have [simplified, simp]: "complex_integrable M (\<lambda>x. iexp (t * x))"
    apply (rule complex_integrable_const_bound, rule AE_I2)
    by (subst cmod_expi_real_eq, auto)
  have *: "\<And>k x. (ii * t * x)^k / fact k = (ii * t)^k / fact k * x^k"
    by (simp add: power_mult_distrib)
  have ** [simp]: "!!k. k \<le> n \<Longrightarrow> complex_integrable M (\<lambda>x. complex_of_real (x ^ k))"
    by (rule complex_of_real_integrable, rule integrable_moments)
  have 1: "\<And>k. k \<le> n \<Longrightarrow> complex_integrable M (\<lambda>x. (ii * t * x)^k / fact k)"
     apply (subst *, rule complex_integral_cmult)
     apply (subst of_real_power [symmetric])
     apply (rule complex_of_real_integrable)
     by (rule integrable_moments)
  have 2: "complex_integrable M (\<lambda>x. (\<Sum>k \<le> n. (ii * t * x)^k / fact k))"
    apply (rule complex_integral_setsum)
    apply (subst *)
    apply (subst of_real_power [symmetric])
    apply (rule complex_integral_cmult)
    apply (rule complex_of_real_integrable) 
    by (rule integrable_moments, simp)
  have 3: "complex_integrable M (\<lambda>x. iexp (t * x) - (\<Sum>k \<le> n. (ii * t * x)^k / fact k))"
    by (rule complex_integral_diff [OF _ 2], auto)
  have 4: "integrable M (\<lambda>x. min (2 * \<bar>t * x\<bar> ^ n / real (fact n))
            (\<bar>t * x\<bar> ^ Suc n / real (fact (Suc n))))"
    apply (rule integrable_bound)
    prefer 2 apply (rule AE_I2)
    apply (subst abs_of_nonneg)
    prefer 2
    apply (rule min.cobounded1, rule min.boundedI)
    apply (auto simp add: field_simps) [1]    
    apply (simp add: field_simps del: fact_Suc power_Suc)
    apply (subst divide_inverse, subst (3) mult_commute)
    apply (rule integral_cmult)+
    apply (subst power_abs [symmetric])
    apply (rule integrable_abs, subst power_mult_distrib)
    apply (rule integral_cmult)
    apply (rule integrable_moments)
    by auto
  have 5: "integrable M (\<lambda>x. min (2 * \<bar>x\<bar> ^ n * real (Suc n)) (\<bar>t\<bar> * \<bar>x\<bar> ^ Suc n))"
    apply (rule integrable_bound)
    prefer 2 apply (rule AE_I2)
    apply (subst abs_of_nonneg)
    prefer 2
    apply (rule min.cobounded1, rule min.boundedI)
    apply (simp del: power_Suc)
    apply (rule mult_nonneg_nonneg, force, force)
    apply (subst mult_assoc)
    apply (rule integral_cmult)
    apply (subst mult_commute)
    apply (rule integral_cmult)
    apply (subst power_abs [symmetric])
    apply (rule integrable_abs)
    apply (rule integrable_moments, simp)
    by auto
  have 6: "(\<lambda>x. min (2 * (abs (t * x))^n / fact n) 
                      ((abs (t * x))^(Suc n) / fact (Suc n))) = 
    (\<lambda>x. (abs t)^n / fact (Suc n) * min (2 * (abs x)^n * real (Suc n)) (abs t * (abs x)^(Suc n)))"
    apply (rule ext)
    apply (subst mult_min_right)
    apply (simp add: field_simps)
    apply (rule arg_cong2[where f=min])
    apply (simp add: field_simps abs_mult del: fact_Suc)
    apply (simp add: real_of_nat_Suc field_simps)
    by (simp add: field_simps abs_mult del: fact_Suc)
  have "?t1 = (CLINT x | M. (\<Sum>k \<le> n. (ii * t * x)^k / fact k))"
    apply (subst complex_integral_setsum [OF 1], simp)
    apply (rule setsum_cong, force)
    apply (subst *, subst of_real_power [symmetric], subst complex_integral_cmult, rule **, simp)
    by (simp add: field_simps complex_of_real_lebesgue_integral)
  hence "char M t - ?t1 = (CLINT x | M. iexp (t * x) - (\<Sum>k \<le> n. (ii * t * x)^k / fact k))"
      (is "_ = (CLINT x | M. ?f x)")
    apply (elim ssubst)
    apply (subst complex_integral_diff [OF _ 2], auto)
    unfolding char_def by auto
  hence "cmod (char M t - ?t1) \<le> expectation (\<lambda>x. cmod (?f x))"
    apply (elim ssubst)
    by (rule complex_lebesgue_integral_cmod, rule 3)
  also have "\<dots> \<le> expectation (\<lambda>x. min (2 * (abs (t * x))^n / fact n) 
                      ((abs (t * x))^(Suc n) / fact (Suc n)))"
    apply (rule integral_mono)
    apply (rule complex_integrable_cmod [OF 3])
    apply (rule 4)
    apply (rule min.boundedI)
    apply (rule order_trans [OF _ equation_26p4b], simp add: mult_assoc)
    by (rule order_trans [OF _ equation_26p4a], simp add: mult_assoc)
  also have "\<dots> = ((abs t)^n / fact (Suc n)) * 
            expectation (\<lambda>x. min (2 * (abs x)^n * (Suc n)) (abs t * (abs x)^(Suc n)))"
    apply (subst 6)
    apply (rule integral_cmult)
    by (rule 5)
  finally show ?thesis by (simp add: real_of_nat_Suc field_simps)
qed

(* this is the formulation in the book -- in terms of a random variable *with* the distribution,
   rather the distribution itself. I don't know which is more useful, though in principal we can
   go back and forth between them. *)
lemma (in prob_space) equation_26p5b':
  fixes \<mu> :: "real measure" and X
  assumes 
    integrable_moments : "\<And>k. k \<le> n \<Longrightarrow> integrable M (\<lambda>x. X x ^ k)" and
    rv_X : "random_variable lborel X" and
    \<mu>_distr : "distr M borel X = \<mu>"
  shows 
    "cmod (char \<mu> t - (\<Sum>k \<le> n. ((ii * t)^k / fact k) * expectation (\<lambda>x. (X x)^k)))
      \<le>  (2 * (abs t)^n / fact n) * expectation (\<lambda>x. abs (X x)^n)"
      (is "cmod (char \<mu> t - ?t1) \<le> _")
proof -
  have [simplified, simp]: "complex_integrable M (\<lambda>x. iexp (t * X x))"
    apply (rule complex_integrable_const_bound, rule AE_I2)
    using rv_X by (subst cmod_expi_real_eq, auto)
  have *: "\<And>k x. (ii * t * X x)^k / fact k = (ii * t)^k / fact k * (X x)^k"
    by (simp add: power_mult_distrib)
  have ** [simp]: "\<And>k. k \<le> n \<Longrightarrow> complex_integrable M (\<lambda>x. complex_of_real (X x ^ k))"
    by (rule complex_of_real_integrable, rule integrable_moments)
  have 1: "\<And>k. k \<le> n \<Longrightarrow> complex_integrable M (\<lambda>x. (ii * t * X x)^k / fact k)"
     apply (subst *, rule complex_integral_cmult)
     by (rule complex_of_real_integrable, rule integrable_moments)
  have 2: "complex_integrable M (\<lambda>x. (\<Sum>k \<le> n. (ii * t * X x)^k / fact k))"
    apply (rule complex_integral_setsum)
    apply (subst *)
    apply (rule complex_integral_cmult, rule complex_of_real_integrable) 
    by (rule integrable_moments, simp)
  have 3: "complex_integrable M (\<lambda>x. iexp (t * X x) - (\<Sum>k \<le> n. (ii * t * X x)^k / fact k))"
    by (rule complex_integral_diff [OF _ 2], auto)
  have "?t1 = (CLINT x | M. (\<Sum>k \<le> n. (ii * t * X x)^k / fact k))"
    apply (subst complex_integral_setsum [OF 1], simp)
    apply (rule setsum_cong, force)
    apply (subst *, subst complex_integral_cmult, rule **, simp)
    by (simp add: field_simps complex_of_real_lebesgue_integral)
  hence "char \<mu> t - ?t1 = (CLINT x | M. iexp (t * X x) - (\<Sum>k \<le> n. (ii * t * X x)^k / fact k))"
      (is "_ = (CLINT x | M. ?f x)")
    apply (elim ssubst)
    apply (subst complex_integral_diff [OF _ 2], auto)
    unfolding char_def apply auto
    apply (subst \<mu>_distr [symmetric])
    using rv_X by (subst complex_integral_distr, auto)
  hence "cmod (char \<mu> t - ?t1) \<le> expectation (\<lambda>x. cmod (?f x))"
    apply (elim ssubst)
    by (rule complex_lebesgue_integral_cmod, rule 3)  
  also have "\<dots> \<le> expectation (\<lambda>x. (2 * (abs t)^n / fact n) * (abs (X x))^n)"
    apply (rule integral_mono)
    apply (rule complex_integrable_cmod [OF 3])
    apply (rule integral_cmult, subst power_abs [symmetric])
    apply (rule integrable_abs, rule integrable_moments, simp)
    apply (rule order_trans)
    apply (subst mult_assoc, subst of_real_mult [symmetric])
    by (rule equation_26p4b, auto simp add: abs_mult power_mult_distrib field_simps)
  also have "\<dots> = (2 * (abs t)^n / fact n) * expectation (\<lambda>x. abs (X x)^n)"
    apply (rule integral_cmult, subst power_abs [symmetric])
    by (rule integrable_abs, rule integrable_moments, simp)
  finally show ?thesis .
qed

(* Calculation of the characteristic function of the standard distribution *)

lemma real_dist_normal_dist: "real_distribution standard_normal_distribution"
  unfolding real_distribution_def apply (rule conjI)
  apply (rule prob_space_normal_density, auto)
unfolding real_distribution_axioms_def by auto

(* o.k., what is the nicer way to do this? *)
lemma limseq_even_odd: 
  assumes "(\<lambda>n ::nat. f (2 * n)) ----> (l :: real)"
      and "(\<lambda>n ::nat. f (2 * n + 1)) ----> l"
  shows "f ----> l"

  using assms apply (auto simp add: LIMSEQ_def)
  apply (drule_tac x = r in spec)+
  apply auto
  apply (rule_tac x = "max (2 * no) (2 * noa + 1)" in exI, auto)
  apply (case_tac "even n")
  apply (subst (asm) even_mult_two_ex, auto)
by (subst (asm) odd_Suc_mult_two_ex, auto)


(* what is the common space? *)
lemma limseq_even_odd_complex: 
  assumes "(\<lambda>n ::nat. f (2 * n)) ----> (l :: complex)"
      and "(\<lambda>n ::nat. f (2 * n + 1)) ----> l"
  shows "f ----> l"

  using assms apply (auto simp add: LIMSEQ_def)
  apply (drule_tac x = r in spec)+
  apply auto
  apply (rule_tac x = "max (2 * no) (2 * noa + 1)" in exI, auto)
  apply (case_tac "even n")
  apply (subst (asm) even_mult_two_ex, auto)
by (subst (asm) odd_Suc_mult_two_ex, auto)

theorem char_standard_normal_distribution:
  "char standard_normal_distribution = (\<lambda>t. complex_of_real (exp (- (t^2) / 2)))"
proof
  fix t :: real
  let ?f' = "\<lambda>k. (ii * t)^k / fact k * (LINT x | standard_normal_distribution. x^k)"
  let ?f = "\<lambda>n. (\<Sum>k \<le> n. ?f' k)"
  (* This is an absolutely horrible calculation, with casts from nat to real to complex. *)
  (* This makes it a good target for automation. *)
  have 1: "\<And>n :: nat. ?f (2 * n) = complex_of_real (\<Sum>k \<le> n. (1 / fact k) * (- (t^2) / 2)^k)"
  proof -
    fix n :: nat
    let ?g' = "\<lambda>k :: nat. (1 / fact k) * (- (t^2) / 2)^k"
    let ?g = "\<lambda>n. \<Sum>k \<le> n. ?g' k"  
    show "?f (2 * n) = complex_of_real (?g n)"
    proof (induct n)
      have "?f (2 * 0) = complex_of_real (LINT x | standard_normal_distribution. x^(2 * 0))" by simp
      also have "\<dots> = complex_of_real 1" 
        by (subst standard_normal_distribution_even_moments) auto
      also have "\<dots> = ?g 0" by simp
      finally show "?f (2 * 0) = ?g 0" .
    next
      fix n
      assume ih: "?f (2 * n) = ?g n"
      have "?f (2 * (Suc n)) = ?f (2 * n) + ?f' (2 * n + 1) + ?f' (2 * (n + 1))" by simp
      also have "?f (2 * n) = ?g n" by (rule ih)
      also have "?f' (2 * n + 1) = 0" by (subst standard_normal_distribution_odd_moments, simp)
      also have "?f' (2 * (n + 1)) = (ii * t)^(2 * (n + 1)) / fact (2 * (n + 1)) * 
         fact (2 * (n + 1)) / (2^(n + 1) * fact (n + 1))"
        by (subst standard_normal_distribution_even_moments, simp)
      also have "\<dots> = (ii * t)^(2 * (n + 1)) / (2^(n + 1) * fact (n + 1))"
        apply (subst times_divide_eq_left)
        apply (subst (3) mult_commute)
        apply (subst times_divide_eq_left [symmetric])
        apply (subst divide_self)
        (* ouch! how to avoid this? *)
        apply (metis of_nat_fact_not_zero of_real_eq_0_iff real_of_int_zero_cancel)
        by simp
      also have "(ii * t)^(2 * (n + 1)) = (- (t^2))^(n + 1)"
        apply (subst mult_commute)
        apply (subst power_mult_distrib)
        apply (subst (2) power_mult)
        apply (simp add: power_mult_distrib field_simps)
        apply (subst (4) mult_commute)
        apply (subst power_mult)
        by (case_tac "even n", auto simp add: power2_eq_square)
      finally have "?f (2 * Suc n) = ?g n + (- (t^2))^(n + 1) / (2^(n + 1) * fact (n + 1))"
        by simp
      also have "(- (t^2))^(n + 1) / (2^(n + 1) * fact (n + 1)) = 
          (- (t^2 / 2))^(n + 1) / fact (n + 1)"
        apply (subst real_of_nat_mult)
        apply (subst divide_divide_eq_left [symmetric])
        by (metis (hide_lams, no_types) minus_divide_left power_divide 
          real_of_nat_numeral real_of_nat_power)
      also have "\<dots> = ?g' (Suc n)" by simp
      finally show "?f (2 * Suc n) = ?g (Suc n)" by simp
    qed
  qed
  have 2: "\<And>n. ?f(2 * n + 1) = ?f(2 * n)"
  proof -
    fix n :: nat
    have "?f(2 * n + 1) = ?f(2 * n) + ?f'(2 * n + 1)" by simp
    also have "?f' (2 * n + 1) = 0"
      by (subst standard_normal_distribution_odd_moments, simp)
    finally show "?f(2 * n + 1) = ?f(2 * n)" by simp
  qed
  have *: "\<And>x y :: real. 1 / y * x = x /\<^sub>R y" by (simp add: inverse_eq_divide)
  have 3: "(\<lambda>n. ?f(2 * n)) ----> exp (-(t^2) / 2)"
    apply (subst 1)
    apply (rule tendsto_of_real)
    apply (subst *)
    by (subst sums_def2 [symmetric], rule exp_converges)
  have 4: "?f ----> exp (-(t^2) / 2)"
    apply (rule limseq_even_odd_complex)
    apply (rule 3)
    apply (subst 2)
    by (rule 3)
  from summable_LIMSEQ_zero [OF summable_exp] have **: 
    "\<And>x :: real. (\<lambda>n. x ^ n / fact n) ----> 0"
    by (auto simp add: inverse_eq_divide)
  have "(\<lambda>n. 2 * \<bar>t\<bar> ^ (2 * n) / real (fact (2 * n)) *
          (LINT x|standard_normal_distribution. \<bar>x\<bar> ^ (2 * n))) =
          (\<lambda>n. 2 * ((t^2 / 2)^n / fact n))"
    apply (rule ext)
    apply (subst standard_normal_distribution_even_moments_abs)
    by (simp add: power_mult power_divide)
  hence 5: "(\<lambda>n. 2 * \<bar>t\<bar> ^ (2 * n) / real (fact (2 * n)) *
          (LINT x|standard_normal_distribution. \<bar>x\<bar> ^ (2 * n)))
        ----> 0"
    apply (elim ssubst)
    by (rule tendsto_mult_right_zero, rule **)
  {
    fix n  :: nat
    have "(fact n) * (fact n) \<le> fact (2 * n)"
    proof (induct n)
      show "(fact (0 :: nat)) * (fact 0) \<le> fact (2 * 0)" by simp
    next
      fix n :: nat
      assume ih: "(fact n) * (fact n) \<le> fact (2 * n)"
      have "(fact (Suc n)) * (fact (Suc n)) = (Suc n) * (Suc n) * (fact n * fact n)"
        by (simp add: field_simps)
      also have "\<dots> \<le> (Suc n) * (Suc n) * fact (2 * n)"
        by (rule mult_left_mono [OF ih], simp)
      also have "\<dots> \<le> (Suc (Suc (2 * n))) * (Suc (2 * n)) * fact (2 * n)"
        apply (rule mult_right_mono)+
        by auto
      also have "\<dots> = fact (2 * Suc n)" by (simp add: field_simps)
      finally show "(fact (Suc n)) * (fact (Suc n)) \<le> fact (2 * (Suc n))" .
    qed
  } note *** = this
  have  "(\<lambda>n. 2 * \<bar>t\<bar> ^ (2 * n + 1) / real (fact (2 * n + 1)) *
          (LINT x|standard_normal_distribution. \<bar>x\<bar> ^ (2 * n + 1)))
        = (\<lambda>n. (4 * abs t / sqrt (2 * pi)) * 
          ((2 * t^2)^n * fact n / fact (2 * n + 1)))"
    apply (rule ext, subst standard_normal_distribution_odd_moments_abs)
    apply (simp add: power_add power_mult power_mult_distrib)
    by (auto simp add: field_simps of_real_mult power_add power_mult
      power_mult_distrib abs_mult power2_eq_square)
  (* TODO: clean this up! *)
  hence 6: "(\<lambda>n. 2 * \<bar>t\<bar> ^ (2 * n + 1) / real (fact (2 * n + 1)) *
          (LINT x|standard_normal_distribution. \<bar>x\<bar> ^ (2 * n + 1)))
        ----> 0"
    apply (elim ssubst)
    apply (rule tendsto_mult_right_zero)
    apply (rule Lim_null_comparison [OF _ ** [of "2 * t\<^sup>2"]])
    apply (rule always_eventually, rule allI)
    apply (subst real_norm_def)
    apply (subst abs_of_nonneg)
    apply (simp del: One_nat_def add: field_simps)
    apply (rule mult_imp_div_pos_le)
    apply (simp del: One_nat_def)
    apply (subst times_divide_eq_left)
    apply (rule mult_imp_le_div_pos)
    apply (simp del: One_nat_def)
    apply (subst mult_assoc)
    apply (rule mult_left_mono)
    apply (subst real_of_nat_mult [symmetric])
    apply (subst real_of_nat_le_iff)
    apply (rule order_trans)
    apply (rule ***)
    by auto
  have 7: "?f ----> char standard_normal_distribution t"
    apply (subst Lim_null)
    apply (rule tendsto_norm_zero_cancel)
    apply (rule Lim_null_comparison [of _ "\<lambda>n. 2 * (abs t)^n / real(fact n) * 
      (LINT x | standard_normal_distribution. abs (x)^n)"])
    apply (rule eventually_sequentiallyI)
    apply (subst real_norm_def, subst abs_of_nonneg, force)
    apply (subst norm_minus_commute, simp)
    apply (rule real_distribution.equation_26p5b [OF real_dist_normal_dist, 
      simplified])
    apply (case_tac "even k")
    apply (subst (asm) even_mult_two_ex, erule exE, simp)
    apply (rule standard_normal_distribution_even_moments)
    apply (subst (asm) odd_Suc_mult_two_ex, erule exE, erule ssubst)
    apply (subgoal_tac "Suc (2 * m) = 2 * m + 1")
    apply (erule ssubst)
    apply (rule standard_normal_distribution_odd_moments)
    apply simp
    by (rule limseq_even_odd [OF 5 6])
  show "char standard_normal_distribution t = complex_of_real (exp (-(t^2) / 2))"
    by (rule LIMSEQ_unique [OF 7 4])
qed


end



