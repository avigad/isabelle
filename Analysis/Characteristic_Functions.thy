(*
  Theory: Characteristic_Functions.thy
  Authors: Jeremy Avigad, Luke Serafin
*)

section \<open>Characteristic Functions\<close>

theory Characteristic_Functions
  imports Weak_Convergence
begin

(*
  Miscellany
*)

(* strange this isn't in the library *)
lemma mult_min_right: "a \<ge> 0 \<Longrightarrow> (a :: real) * min b c = min (a * b) (a * c)"
  by (metis min.absorb_iff2 min_def mult_left_mono)

(* o.k., what is the nicer way to do this? *)

lemma sequentially_even_odd:
  assumes E: "eventually (\<lambda>n. P (2 * n)) sequentially" and O: "eventually (\<lambda>n. P (2 * n + 1)) sequentially"
  shows "eventually P sequentially"
proof -
  from E obtain n_e where [intro]: "\<And>n. n \<ge> n_e \<Longrightarrow> P (2 * n)"
    by (auto simp: eventually_sequentially)
  moreover
  from O obtain n_o where [intro]: "\<And>n. n \<ge> n_o \<Longrightarrow> P (Suc (2 * n))"
    by (auto simp: eventually_sequentially)
  show ?thesis
    unfolding eventually_sequentially
  proof (intro exI allI impI)
    fix n assume "max (2 * n_e) (2 * n_o + 1) \<le> n" then show "P n"
      by (cases "even n") (auto elim!: evenE oddE )
  qed
qed

lemma limseq_even_odd: 
  assumes "(\<lambda>n. f (2 * n)) ----> (l :: 'a :: topological_space)"
      and "(\<lambda>n. f (2 * n + 1)) ----> l"
  shows "f ----> l"
  using assms by (auto simp: filterlim_iff intro: sequentially_even_odd)

lemma (in comm_ring_1) uminus_power_if: "(- x) ^ n = (if even n then x^n else - (x ^ n))"
  by auto

lemma square_fact_le_2_fact: "(fact n) * (fact n::nat) \<le> fact (2 * n)"
proof (induct n)
  case 0 then show ?case by simp
next
  case (Suc n)
  have "(fact (Suc n)) * (fact (Suc n)) = (Suc n) * (Suc n) * (fact n * fact n)"
    by (simp add: field_simps)
  also have "\<dots> \<le> (Suc n) * (Suc n) * fact (2 * n)"
    by (rule mult_left_mono [OF Suc], simp)
  also have "\<dots> \<le> (Suc (Suc (2 * n))) * (Suc (2 * n)) * fact (2 * n)"
    by (rule mult_right_mono)+ auto
  also have "\<dots> = fact (2 * Suc n)" by (simp add: field_simps)
  finally show ?case .
qed

subsection \<open>Application of the FTC: integrating e^ix\<close>

abbreviation iexp :: "real \<Rightarrow> complex" where
  "iexp \<equiv> (\<lambda>x. exp (\<i> * complex_of_real x))"

lemma isCont_iexp [simp]: "isCont iexp x"
  by (intro continuous_intros)

lemma has_vector_derivative_iexp[derivative_intros]:
  "(iexp has_vector_derivative \<i> * iexp x) (at x within s)"
  by (auto intro!: derivative_eq_intros simp: Re_exp Im_exp has_vector_derivative_complex_iff)

lemma interval_integral_iexp:
  fixes a b :: real
  shows "(CLBINT x=a..b. iexp x) = ii * iexp a - ii * iexp b"
  by (subst interval_integral_FTC_finite [where F = "\<lambda>x. -ii * iexp x"])
     (auto intro!: derivative_eq_intros continuous_intros)

subsection \<open>The Characteristic Function of a Real Measure.\<close>

definition
  char :: "real measure \<Rightarrow> real \<Rightarrow> complex"
where
  "char M t = CLINT x|M. iexp (t * x)"

lemma (in real_distribution) char_zero: "char M 0 = 1"
  unfolding char_def by (simp del: space_eq_univ add: prob_space)

lemma (in prob_space) integrable_iexp: 
  assumes f: "f \<in> borel_measurable M" "\<And>x. Im (f x) = 0"
  shows "integrable M (\<lambda>x. exp (ii * (f x)))"
proof (intro integrable_const_bound [of _ 1])
  from f have "\<And>x. of_real (Re (f x)) = f x"
    by (simp add: complex_eq_iff)
  then show "AE x in M. cmod (exp (\<i> * f x)) \<le> 1"
    using norm_exp_ii_times[of "Re (f x)" for x] by simp
qed (insert f, simp)

lemma (in real_distribution) cmod_char_le_1: "norm (char M t) \<le> 1"
proof -
  have "norm (char M t) \<le> (\<integral>x. norm (iexp (t * x)) \<partial>M)"
    unfolding char_def by (intro integral_norm_bound integrable_iexp) auto
  also have "\<dots> \<le> 1"
    by (simp del: of_real_mult)
  finally show ?thesis .
qed

lemma (in real_distribution) isCont_char: "isCont (char M) t"
  unfolding continuous_at_sequentially
proof safe
  fix X assume X: "X ----> t"
  show "(char M \<circ> X) ----> char M t"
    unfolding comp_def char_def
    by (rule integral_dominated_convergence[where w="\<lambda>_. 1"])
       (auto simp del: of_real_mult intro!: AE_I2 tendsto_intros X)
qed

lemma (in real_distribution) char_measurable [measurable]: "char M \<in> borel_measurable borel"
  by (auto intro!: borel_measurable_continuous_on1 continuous_at_imp_continuous_on isCont_char)

subsection \<open>Independence\<close>

(* the automation can probably be improved *)  
lemma (in prob_space) char_distr_sum:
  fixes X1 X2 :: "'a \<Rightarrow> real" and t :: real
  assumes "indep_var borel X1 borel X2"
  shows "char (distr M borel (\<lambda>\<omega>. X1 \<omega> + X2 \<omega>)) t =
    char (distr M borel X1) t * char (distr M borel X2) t"
proof -
  from assms have [measurable]: "random_variable borel X1" by (elim indep_var_rv1)
  from assms have [measurable]: "random_variable borel X2" by (elim indep_var_rv2)

  have "char (distr M borel (\<lambda>\<omega>. X1 \<omega> + X2 \<omega>)) t = (CLINT x|M. iexp (t * (X1 x + X2 x)))"
    by (simp add: char_def integral_distr)
  also have "\<dots> = (CLINT x|M. iexp (t * (X1 x)) * iexp (t * (X2 x))) "
    by (simp add: field_simps exp_add)
  also have "\<dots> = (CLINT x|M. iexp (t * (X1 x))) * (CLINT x|M. iexp (t * (X2 x)))"
    by (intro indep_var_lebesgue_integral indep_var_compose[unfolded comp_def, OF assms])
       (auto intro!: integrable_iexp)
  also have "\<dots> = char (distr M borel X1) t * char (distr M borel X2) t"
    by (simp add: char_def integral_distr)
  finally show ?thesis .
qed

lemma (in prob_space) char_distr_setsum:
  "indep_vars (\<lambda>i. borel) X A \<Longrightarrow>
    char (distr M borel (\<lambda>\<omega>. \<Sum>i\<in>A. X i \<omega>)) t = (\<Prod>i\<in>A. char (distr M borel (X i)) t)"
proof (induct A rule: infinite_finite_induct)
  case (insert x F) with indep_vars_subset[of "\<lambda>_. borel" X "insert x F" F] show ?case
    by (auto simp add: char_distr_sum indep_vars_setsum)
qed (simp_all add: char_def integral_distr prob_space del: distr_const)

subsection \<open>Approximations to $e^{ix}$\<close>

text \<open>Proofs from Billingsley, page 343.\<close>

lemma fact1:
  "((\<lambda>s. complex_of_real(-((x - s) ^ (Suc n) / (Suc n))) * iexp s)
    has_vector_derivative complex_of_real((x - s)^n) * iexp s + (ii * iexp s) * complex_of_real(-((x - s) ^ (Suc n) / (Suc n))))
    (at s within A)"
  by (intro derivative_eq_intros) auto

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
    by (metis of_nat_Suc of_real_of_nat_eq)
  have "(CLBINT s=0..x. (f s n * iexp s + (ii * iexp s) * -(f s (Suc n) / (Suc n)))) =
      x^(Suc n) / (Suc n)" (is "?LHS = ?RHS")
  proof -
    have "?LHS = (CLBINT s=0..x. (f s n * iexp s + (ii * iexp s) * 
      complex_of_real(-((x - s) ^ (Suc n) / (Suc n)))))"
      apply (case_tac "0 \<le> x")
      apply (subst (1 2) zero_ereal_def)
      apply (rule interval_integral_cong)
      unfolding f_def
      apply simp
      apply simp
      done
    also have "... = ?F x - ?F 0"
      apply (subst zero_ereal_def)
      apply (rule interval_integral_FTC_finite)
      apply (unfold f_def)
      apply (rule continuous_at_imp_continuous_on)
      apply (auto intro!: continuous_intros simp: add_nonneg_eq_0_iff complex_eq_iff) [1]
      by (rule fact1)
    also have "... = x^(Suc n) / (Suc n)"
      by auto
    finally show ?thesis .
  qed
thus ?thesis
  apply (elim subst)
  apply (subst interval_lebesgue_integral_mult_right [symmetric])
  unfolding f_def
  apply (subst interval_lebesgue_integral_add(2) [symmetric])
  (* the next few lines should be automatic *)
  unfolding zero_ereal_def
  apply (intro interval_integrable_isCont continuous_intros)
  apply (simp add: complex_eq_iff)
  apply (intro interval_integrable_isCont continuous_intros)
  apply (simp add: complex_eq_iff)
  done
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
    by (auto simp add: field_simps interval_integral_iexp)
next
  fix n assume ih: "?P n"
  def y \<equiv> "\<Sum>k\<le>n. (\<i> * complex_of_real x) ^ k / of_nat (fact k)"
  def x \<equiv> "CLBINT s=0..ereal x. complex_of_real ((x - s) ^ Suc n) * Exp (\<i> * complex_of_real s)"
  have of_nat_eq_minus_of_nat: "\<And>x y. of_nat x = - (of_nat y::real) \<longleftrightarrow> (x = 0 \<and> y = 0)"
    by linarith
  have *: "of_nat n * of_nat (fact n) \<noteq> - (of_nat (fact n)::complex)"
    using complex_eq_iff of_nat_mult[symmetric] of_nat_eq_minus_of_nat
    proof -
      have f1: "\<And>c. (c::complex) + - c = 0"
        by simp
      have "\<And>n. fact n \<noteq> (0::complex)"
        by auto
      hence "\<exists>c. of_nat (Suc n) * (c::complex) \<noteq> 0"
        by (metis (no_types) fact_num_eq_if nat.simps(3))
      hence "fact n * of_nat (Suc n) \<noteq> (0::complex)"
        by simp
      hence "- (fact n::complex) \<noteq> of_nat n * fact n"
        using f1 by (metis Groups.mult_ac(2) distrib_right mult.left_neutral semiring_1_class.of_nat_simps(2))
      thus ?thesis
        by simp
    qed
  show "?P (Suc n)"
    apply (subst setsum_atMost_Suc)
    apply (subst ih)
    apply (unfold f_def)
    apply (subst equation_26p1)
    (* this is a good example of a messy calculation that should be
       automatic! *)
    unfolding x_def[symmetric] y_def[symmetric]
    apply (simp add: divide_simps add_eq_0_iff of_nat_mult)
    apply (simp add: field_simps of_nat_mult *)
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
    apply (subst interval_lebesgue_integral_diff(2) [symmetric])
    apply (subst zero_ereal_def)
    apply (rule interval_integrable_isCont)
    unfolding f_def apply simp
    apply (subst zero_ereal_def)
    apply (rule interval_integrable_isCont)
    apply simp
    by (simp add: field_simps)
  have calc2: "(CLBINT s=0..x. f s n) = x^(Suc n) / (Suc n)"
    apply (subst zero_ereal_def)
    apply (subst interval_integral_FTC_finite
      [where a = 0 and b = x and f = "\<lambda>s. f s n" and F = 
        "\<lambda>s. complex_of_real (-((x - s) ^ (Suc n) / real (Suc n)))"])
    apply (unfold f_def)
    apply (rule continuous_at_imp_continuous_on, force)
    apply (rule has_vector_derivative_of_real)
    by (auto intro!: derivative_eq_intros simp del: power_Suc simp add: add_nonneg_eq_0_iff)
  show ?thesis
    apply (subst equation_26p2 [where n = "Suc n"])
    apply (rule arg_cong)
    apply (subst calc1)
    apply (subst calc2)
    apply (subgoal_tac
      "ii ^ (Suc (Suc n)) / (fact (Suc n)) = (ii ^ (Suc n) / (fact n)) * (ii / (Suc n))")
    prefer 2
    apply (simp add: field_simps of_nat_mult)
    apply (erule ssubst)
    apply (subst mult.assoc)+
    apply (rule arg_cong)
    apply (unfold f_def)
    apply (subst equation_26p1 [where n = n])
    by auto
qed

lemma equation_26p4a: "cmod (iexp x - (\<Sum>k \<le> n. (ii * x)^k / fact k)) \<le>
    (abs x)^(Suc n) / (fact (Suc n)::real)"
proof -
  have "iexp x - (\<Sum>k \<le> n. (ii * x)^k / fact k) = 
         ((ii ^ (Suc n)) / (fact n)) * (CLBINT s=0..x. (x - s)^n * (iexp s))" (is "?t1 = ?t2")
    by (subst equation_26p2 [of _ n], simp add: field_simps)
  hence "cmod (?t1) = cmod (?t2)" by simp
  also have "\<dots> =  (1 / of_nat (fact n)) * cmod (CLBINT s=0..x. (x - s)^n * (iexp s))"
    by (simp add: norm_mult norm_divide norm_power)
  also have "\<dots> \<le> (1 / of_nat (fact n)) * abs (LBINT s=0..x. cmod ((x - s)^n * (iexp s)))"
    apply (rule mult_left_mono)
    apply (rule interval_integral_norm2)
    apply auto
    apply (subst zero_ereal_def)
    apply (rule interval_integrable_isCont)
    by auto
  also have "\<dots> \<le> (1 / of_nat (fact n)) * abs (LBINT s=0..x. abs ((x - s)^n))"
    by (simp add: norm_mult del: of_real_diff of_real_power)
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
      unfolding has_field_derivative_iff_has_vector_derivative[symmetric]
      apply (rule DERIV_subset)
      by (auto simp del: power_Suc intro!: derivative_eq_intros simp add: add_nonneg_eq_0_iff)
    also have "\<dots> = x ^ (Suc n) / (Suc n)" by simp
    finally show ?thesis .
  qed
  also have "1 / real_of_nat (fact n::nat) * \<bar>x ^ Suc n / real (Suc n)\<bar> = 
      \<bar>x\<bar> ^ Suc n / fact (Suc n)"
    apply (subst abs_divide, subst power_abs, subst (2) abs_of_nonneg, simp)
    by (simp add: field_simps of_nat_Suc)
  finally show ?thesis by (simp add: )
qed

lemma equation_26p4b: "cmod (iexp x - (\<Sum>k \<le> n. (ii * x)^k / fact k)) \<le>
    2 * (abs x)^n / fact n" (is "?P n")
proof (induction n)  (* really cases *)
show "?P 0" 
  apply simp
  by (rule order_trans [OF norm_triangle_ineq4], simp)
next
  {
    fix a b and f g :: "_ \<Rightarrow> real"
    assume f: "\<And>s. 0 \<le> f s" and g: "(\<And>s. f s \<le> g s)" and
      iif: "interval_lebesgue_integrable lborel a b f" and 
      iig: "interval_lebesgue_integrable lborel a b g"
    have "abs (LBINT s=a..b. f s) \<le> abs (LBINT s=a..b. g s)"
      using f g order_trans[OF f g] iif iig
      unfolding interval_lebesgue_integral_def interval_lebesgue_integrable_def 
      apply (auto simp: integral_nonneg_AE
                  intro!: set_integral_mono
                  simp del: real_scaleR_def)
      apply (subst (1 2) abs_of_nonneg)
      apply (simp add: integral_nonneg_AE)
      apply (simp add: integral_nonneg_AE)
      apply (intro integral_mono)
      apply assumption
      apply assumption
      apply (simp add: mult_mono)
      apply (subst (1 2) abs_of_nonneg)
      apply (simp add: integral_nonneg_AE)
      apply (simp add: integral_nonneg_AE)
      apply (intro integral_mono)
      apply assumption
      apply assumption
      apply (simp add: mult_mono)
      done
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
    apply (rule mult_left_mono, rule interval_integral_norm2)
    apply auto
    apply (subst zero_ereal_def)
    apply (rule interval_integrable_isCont)
    by auto
  also have "\<dots> = (1 / (fact n)) * abs (LBINT s=0..x. abs ((x - s)^n) * cmod((iexp s - 1)))"
    by (simp add: norm_mult del: of_real_diff of_real_power)
  also have "\<dots> \<le> (1 / (fact n)) * abs (LBINT s=0..x. abs ((x - s)^n) * 2)"
    apply (rule mult_left_mono)
    prefer 2 apply force
    apply (rule useful)
    apply simp
    apply (rule mult_left_mono, auto)
    apply (rule order_trans [OF norm_triangle_ineq4], simp)
    apply (subst mult.commute)
    apply (subst zero_ereal_def)
    apply (rule interval_integrable_isCont, auto)
    apply (subst zero_ereal_def)
    by (rule interval_integrable_isCont, auto)
  also have "\<dots> = (2 / (fact n)) * abs (LBINT s=0..x. abs ((x - s)^n))"
    by simp
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
      unfolding has_field_derivative_iff_has_vector_derivative[symmetric]
      apply (rule DERIV_subset)
      by (auto simp del: power_Suc intro!: derivative_eq_intros simp add: add_nonneg_eq_0_iff)
    also have "\<dots> = x ^ (Suc n) / (Suc n)" by simp
    finally show ?thesis .
  qed
  also have "2 / fact n * \<bar>x ^ Suc n / real (Suc n)\<bar> = 
      2 * \<bar>x\<bar> ^ Suc n / (fact (Suc n))"
    apply (subst abs_divide, subst power_abs, subst (2) abs_of_nonneg, simp)
    by (simp add: field_simps of_nat_Suc)
  finally show ?thesis .
qed
qed


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
    apply (rule integrable_const_bound, rule AE_I2)
    by (subst norm_exp_ii_times, auto)
  have *: "\<And>k x. (ii * t * x)^k / fact k = (ii * t)^k / fact k * x^k"
    by (simp add: power_mult_distrib)
  have ** [simp]: "!!k. k \<le> n \<Longrightarrow> complex_integrable M (\<lambda>x. complex_of_real (x ^ k))"
    by (rule integrable_of_real, rule integrable_moments)
  have 1: "\<And>k. k \<le> n \<Longrightarrow> complex_integrable M (\<lambda>x. (ii * t * x)^k / fact k)"
     apply (subst *, rule integrable_mult_right)
     apply (subst of_real_power [symmetric])
     apply (rule integrable_of_real)
     by (rule integrable_moments)
  have 2: "complex_integrable M (\<lambda>x. (\<Sum>k \<le> n. (ii * t * x)^k / fact k))"
    apply (rule integrable_setsum)
    apply (subst *)
    apply (subst of_real_power [symmetric])
    apply (rule integrable_mult_right)
    apply (rule integrable_of_real) 
    by (rule integrable_moments, simp)
  have 3: "complex_integrable M (\<lambda>x. iexp (t * x) - (\<Sum>k \<le> n. (ii * t * x)^k / fact k))"
    by (rule integrable_diff [OF _ 2], auto)
  have "?t1 = (CLINT x | M. (\<Sum>k \<le> n. (ii * t * x)^k / fact k))"
    apply (subst integral_setsum [OF 1], simp)
    apply (rule setsum.cong, force)
    apply (subst *, subst of_real_power [symmetric], subst integral_mult_right, rule **, simp)
    by (simp add: field_simps del: of_real_power)
  hence "char M t - ?t1 = (CLINT x | M. iexp (t * x) - (\<Sum>k \<le> n. (ii * t * x)^k / fact k))"
      (is "_ = (CLINT x | M. ?f x)")
    apply (elim ssubst)
    apply (subst integral_diff [OF _ 2], auto)
    unfolding char_def by auto
  hence "cmod (char M t - ?t1) \<le> expectation (\<lambda>x. cmod (?f x))"
    apply (elim ssubst)
    by (rule integral_norm_bound, rule 3)  
  also have "\<dots> \<le> expectation (\<lambda>x. (2 * (abs t)^n / fact n) * (abs x)^n)"
    apply (rule integral_mono)
    apply (rule integrable_norm [OF 3])
    apply (rule integrable_mult_right, subst power_abs [symmetric])
    apply (rule integrable_abs, rule integrable_moments, simp)
    apply (rule order_trans)
    apply (subst mult.assoc, subst of_real_mult [symmetric])
    by (rule equation_26p4b, auto simp add: abs_mult power_mult_distrib field_simps)
  also have "\<dots> = (2 * (abs t)^n / fact n) * expectation (\<lambda>x. (abs x)^n)"
    apply (rule integral_mult_right, subst power_abs [symmetric])
    by (rule integrable_abs, rule integrable_moments, simp)
  finally show ?thesis .
qed

lemma (in real_distribution) equation_26p5b_stronger:
  assumes 
    integrable_moments : "\<And>k. k \<le> n \<Longrightarrow> integrable M (\<lambda>x :: real. x ^ k)"
  shows 
    "cmod (char M t - (\<Sum>k \<le> n. ((ii * t)^k / (fact k)) * expectation (\<lambda>x. x^k)))
      \<le>  ((abs t)^n / fact (Suc n)) * 
            expectation (\<lambda>x. min (2 * (abs x)^n * (Suc n)) (abs t * (abs x)^(Suc n)))"
      (is "cmod (char M t - ?t1) \<le> _")
proof -
  have [simplified, simp]: "complex_integrable M (\<lambda>x. iexp (t * x))"
    apply (rule integrable_const_bound, rule AE_I2)
    by (subst norm_exp_ii_times, auto)
  have *: "\<And>k x. (ii * t * x)^k / fact k = (ii * t)^k / fact k * x^k"
    by (simp add: power_mult_distrib)
  have ** [simp]: "!!k. k \<le> n \<Longrightarrow> complex_integrable M (\<lambda>x. complex_of_real (x ^ k))"
    by (rule integrable_of_real, rule integrable_moments)
  have 1: "\<And>k. k \<le> n \<Longrightarrow> complex_integrable M (\<lambda>x. (ii * t * x)^k / fact k)"
     apply (subst *, rule integrable_mult_right)
     apply (subst of_real_power [symmetric])
     apply (rule integrable_of_real)
     by (rule integrable_moments)
  have 2: "complex_integrable M (\<lambda>x. (\<Sum>k \<le> n. (ii * t * x)^k / fact k))"
    apply (rule integrable_setsum)
    apply (subst *)
    apply (subst of_real_power [symmetric])
    apply (rule integrable_mult_right)
    apply (rule integrable_of_real) 
    by (rule integrable_moments, simp)
  have 3: "complex_integrable M (\<lambda>x. iexp (t * x) - (\<Sum>k \<le> n. (ii * t * x)^k / fact k))"
    by (rule integrable_diff [OF _ 2], auto)
  have 4: "integrable M (\<lambda>x. min (2 * \<bar>t * x\<bar> ^ n / fact n)
            (\<bar>t * x\<bar> ^ Suc n / fact (Suc n)))"
    by (rule integrable_bound[where f="\<lambda>x. 2 * \<bar>t * x\<bar> ^ n / fact n"])
       (auto simp: integrable_moments power_abs[symmetric] power_mult_distrib)
  have 5: "integrable M (\<lambda>x. min (2 * \<bar>x\<bar> ^ n * real (Suc n)) (\<bar>t\<bar> * \<bar>x\<bar> ^ Suc n))"
    by (rule integrable_bound[where f="\<lambda>x. 2 * \<bar>x\<bar> ^ n * real (Suc n)"])
       (auto simp: integrable_moments power_abs[symmetric])
  have 6: "(\<lambda>x. min (2 * (abs (t * x))^n / fact n) 
                      ((abs (t * x))^(Suc n) / fact (Suc n))) = 
    (\<lambda>x. (abs t)^n / fact (Suc n) * min (2 * (abs x)^n * real (Suc n)) (abs t * (abs x)^(Suc n)))"
    apply (rule ext)
    apply (subst mult_min_right)
    apply (simp add: field_simps)
    apply (rule arg_cong2[where f=min])
    apply (simp add: field_simps abs_mult del: fact_Suc)
    apply (simp add: of_nat_Suc field_simps)
    by (simp add: field_simps abs_mult del: fact_Suc)
  have "?t1 = (CLINT x | M. (\<Sum>k \<le> n. (ii * t * x)^k / fact k))"
    apply (subst integral_setsum [OF 1], simp)
    apply (rule setsum.cong, force)
    apply (subst *, subst of_real_power [symmetric], subst integral_mult_right, rule **, simp)
    by (simp add: field_simps integral_of_real del: of_real_power)
  hence "char M t - ?t1 = (CLINT x | M. iexp (t * x) - (\<Sum>k \<le> n. (ii * t * x)^k / fact k))"
      (is "_ = (CLINT x | M. ?f x)")
    apply (elim ssubst)
    apply (subst integral_diff [OF _ 2], auto)
    unfolding char_def by auto
  hence "cmod (char M t - ?t1) \<le> expectation (\<lambda>x. cmod (?f x))"
    apply (elim ssubst)
    by (rule integral_norm_bound, rule 3)
  also have "\<dots> \<le> expectation (\<lambda>x. min (2 * (abs (t * x))^n / fact n) 
                      ((abs (t * x))^(Suc n) / fact (Suc n)))"
    apply (rule integral_mono)
    apply (rule integrable_norm [OF 3])
    apply (rule 4)
    apply (rule min.boundedI)
    apply (rule order_trans [OF _ equation_26p4b], simp add: mult.assoc)
    by (rule order_trans [OF _ equation_26p4a], simp add: mult.assoc)
  also have "\<dots> = ((abs t)^n / fact (Suc n)) * 
            expectation (\<lambda>x. min (2 * (abs x)^n * (Suc n)) (abs t * (abs x)^(Suc n)))"
    apply (subst 6)
    apply (rule integral_mult_right)
    by (rule 5)
  finally show ?thesis by (simp add: of_nat_Suc field_simps)
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
    apply (rule integrable_const_bound, rule AE_I2)
    using rv_X by (subst norm_exp_ii_times, auto)
  have *: "\<And>k x. (ii * t * X x)^k / fact k = (ii * t)^k / fact k * (X x)^k"
    by (simp add: power_mult_distrib)
  have ** [simp]: "\<And>k. k \<le> n \<Longrightarrow> complex_integrable M (\<lambda>x. complex_of_real (X x ^ k))"
    by (rule integrable_of_real, rule integrable_moments)
  have 1: "\<And>k. k \<le> n \<Longrightarrow> complex_integrable M (\<lambda>x. (ii * t * X x)^k / fact k)"
     apply (subst *, rule integrable_mult_right)
     by (rule integrable_of_real, rule integrable_moments)
  have 2: "complex_integrable M (\<lambda>x. (\<Sum>k \<le> n. (ii * t * X x)^k / fact k))"
    apply (rule integrable_setsum)
    apply (subst *)
    apply (rule integrable_mult_right, rule integrable_of_real) 
    by (rule integrable_moments, simp)
  have 3: "complex_integrable M (\<lambda>x. iexp (t * X x) - (\<Sum>k \<le> n. (ii * t * X x)^k / fact k))"
    by (rule integrable_diff [OF _ 2], auto)
  have "?t1 = (CLINT x | M. (\<Sum>k \<le> n. (ii * t * X x)^k / fact k))"
    apply (subst integral_setsum [OF 1], simp)
    apply (rule setsum.cong, force)
    apply (subst *, subst integral_mult_right, rule **, simp)
    by (simp add: field_simps integral_of_real del: of_real_power)
  hence "char \<mu> t - ?t1 = (CLINT x | M. iexp (t * X x) - (\<Sum>k \<le> n. (ii * t * X x)^k / fact k))"
      (is "_ = (CLINT x | M. ?f x)")
    apply (elim ssubst)
    apply (subst integral_diff [OF _ 2], auto)
    unfolding char_def apply auto
    apply (subst \<mu>_distr [symmetric])
    using rv_X by (subst integral_distr, auto)
  hence "cmod (char \<mu> t - ?t1) \<le> expectation (\<lambda>x. cmod (?f x))"
    apply (elim ssubst)
    by (rule integral_norm_bound, rule 3)  
  also have "\<dots> \<le> expectation (\<lambda>x. (2 * (abs t)^n / fact n) * (abs (X x))^n)"
    apply (rule integral_mono)
    apply (rule integrable_norm [OF 3])
    apply (rule integrable_mult_right, subst power_abs [symmetric])
    apply (rule integrable_abs, rule integrable_moments, simp)
    apply (rule order_trans)
    apply (subst mult.assoc, subst of_real_mult [symmetric])
    by (rule equation_26p4b, auto simp add: abs_mult power_mult_distrib field_simps)
  also have "\<dots> = (2 * (abs t)^n / fact n) * expectation (\<lambda>x. abs (X x)^n)"
    apply (rule integral_mult_right, subst power_abs [symmetric])
    by (rule integrable_abs, rule integrable_moments, simp)
  finally show ?thesis .
qed

subsection \<open>Calculation of the Characteristic Function of the Standard Distribution\<close>


abbreviation
  "std_normal_distribution \<equiv> density lborel std_normal_density"

(* TODO: should this be an instance statement? *)
lemma real_dist_normal_dist: "real_distribution std_normal_distribution"
  using prob_space_normal_density by (auto simp: real_distribution_def real_distribution_axioms_def)

lemma std_normal_distribution_even_moments:
  fixes k :: nat
  shows "(LINT x|std_normal_distribution. x^(2 * k)) = fact (2 * k) / (2^k * fact k)"
    and "integrable std_normal_distribution (\<lambda>x. x^(2 * k))"
  using integral_std_normal_moment_even[of k]
  by (subst integral_density)
     (auto simp: normal_density_nonneg integrable_density
           intro: integrable.intros std_normal_moment_even)

lemma integrable_std_normal_distribution_moment: "integrable std_normal_distribution (\<lambda>x. x^k)"
  by (auto simp: normal_density_nonneg integrable_std_normal_moment integrable_density)

lemma integral_std_normal_distribution_moment_odd:
  "odd k \<Longrightarrow> integral\<^sup>L std_normal_distribution (\<lambda>x. x^k) = 0"
  using integral_std_normal_moment_odd[of "(k - 1) div 2"]
  by (auto simp: integral_density normal_density_nonneg elim: oddE)

lemma std_normal_distribution_even_moments_abs:
  fixes k :: nat
  shows "(LINT x|std_normal_distribution. \<bar>x\<bar>^(2 * k)) = fact (2 * k) / (2^k * fact k)"
  using integral_std_normal_moment_even[of k]
  by (subst integral_density) (auto simp: normal_density_nonneg power_even_abs)

lemma std_normal_distribution_odd_moments_abs:
  fixes k :: nat
  shows "(LINT x|std_normal_distribution. \<bar>x\<bar>^(2 * k + 1)) = sqrt (2 / pi) * 2 ^ k * fact k"
  using integral_std_normal_moment_abs_odd[of k]
  by (subst integral_density) (auto simp: normal_density_nonneg)

theorem char_std_normal_distribution:
  "char std_normal_distribution = (\<lambda>t. complex_of_real (exp (- (t^2) / 2)))"
proof
  fix t :: real
  let ?f' = "\<lambda>k. (ii * t)^k / fact k * (LINT x | std_normal_distribution. x^k)"
  let ?f = "\<lambda>n. (\<Sum>k \<le> n. ?f' k)"
  have 4: "?f ----> exp (-(t^2) / 2)"
  proof (rule limseq_even_odd)
    have *: "?f (2 * n) = complex_of_real (\<Sum>k \<le> n. (1 / fact k) * (- (t^2) / 2)^k)" for n :: nat
      unfolding of_real_setsum
      apply (rule setsum.reindex_bij_witness_not_neutral[symmetric,
          where i="\<lambda>n. n div 2" and j="\<lambda>n. 2 * n" and T'="{i. i \<le> 2 * n \<and> odd i}" and S'="{}"])
      apply (auto simp: integral_std_normal_distribution_moment_odd
        std_normal_distribution_even_moments)
      apply (subst power_mult[of _ 2])
      apply (simp add: field_simps uminus_power_if power_mult)
      done
    show "(\<lambda>n. ?f (2 * n)) ----> exp (-(t^2) / 2)"
      unfolding * using exp_converges[where 'a=real]
      by (intro tendsto_of_real)
         (auto simp: inverse_eq_divide lessThan_Suc_atMost [symmetric] sums_def [symmetric]
               simp del: setsum_lessThan_Suc intro!: LIMSEQ_Suc)
    have **: "?f(2 * n + 1) = ?f(2 * n)" for n
    proof -
      have "?f(2 * n + 1) = ?f(2 * n) + ?f'(2 * n + 1)"
        by simp
      also have "?f' (2 * n + 1) = 0"
        by (subst integral_std_normal_distribution_moment_odd) simp_all
      finally show "?f(2 * n + 1) = ?f(2 * n)"
        by simp
    qed
    show "(\<lambda>n. ?f (2 * n + 1)) ----> exp (-(t^2) / 2)"
      unfolding ** by fact
  qed
  from summable_LIMSEQ_zero [OF summable_exp] have **: "(\<lambda>n. x ^ n / fact n) ----> 0" for x :: real
    by (auto simp add: inverse_eq_divide)
  have "(\<lambda>n. 2 * \<bar>t\<bar> ^ (2 * n) / fact (2 * n) * (LINT x|std_normal_distribution. \<bar>x\<bar> ^ (2 * n))) =
      (\<lambda>n. 2 * ((t^2 / 2)^n / fact n))"
    unfolding std_normal_distribution_even_moments_abs by (simp add: power_mult power_divide)
  then have 5:
      "(\<lambda>n. 2 * \<bar>t\<bar> ^ (2 * n) / fact (2 * n) * (LINT x|std_normal_distribution. \<bar>x\<bar> ^ (2 * n)))
        ----> 0"
    apply (elim ssubst)
    by (rule tendsto_mult_right_zero, rule **)
  have  "(\<lambda>n. 2 * \<bar>t\<bar> ^ (2 * n + 1) / fact (2 * n + 1) *
          (LINT x|std_normal_distribution. \<bar>x\<bar> ^ (2 * n + 1)))
        = (\<lambda>n. (2 * \<bar>t\<bar> * sqrt (2 / pi)) * ((2 * t^2)^n * fact n / fact (2 * n + 1)))"
    apply (subst std_normal_distribution_odd_moments_abs)
    apply (simp add: field_simps power_mult[symmetric] power_even_abs)
    done
  (* TODO: clean this up! *)
  hence 6:
      "(\<lambda>n. 2 * \<bar>t\<bar> ^ (2 * n + 1) / fact (2 * n + 1) * (LINT x|std_normal_distribution. \<bar>x\<bar> ^ (2 * n + 1)))
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
    apply (subst mult.assoc)
    apply (rule mult_left_mono)
    unfolding of_nat_fact[symmetric, where 'a=real]
    apply (subst of_nat_mult [symmetric])
    apply (subst of_nat_le_iff)
    apply (rule order_trans)
    apply (rule square_fact_le_2_fact)
    by auto
  have 7: "?f ----> char std_normal_distribution t"
    apply (subst Lim_null)
    apply (rule tendsto_norm_zero_cancel)
    apply (rule Lim_null_comparison [of _ "\<lambda>n. 2 * (abs t)^n / fact n * 
      (LINT x | std_normal_distribution. abs (x)^n)"])
    apply (rule eventually_sequentiallyI)
    apply (subst real_norm_def, subst abs_of_nonneg, force)
    apply (subst norm_minus_commute, simp)
    apply (rule real_distribution.equation_26p5b [OF real_dist_normal_dist,  simplified])
    apply (rule integrable_std_normal_distribution_moment)
    by (rule limseq_even_odd [OF 5 6])
  show "char std_normal_distribution t = complex_of_real (exp (-(t^2) / 2))"
    by (rule LIMSEQ_unique [OF 7 4])
qed

end
