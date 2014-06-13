(* 
Normal_Moments
Author: Jeremy Avigad

The moments of the normal distribution.

TODO: Merge this file with Normal_Distribution.

*)

theory Normal_Moments

imports Normal_Distribution Interval_Integral

begin



lemma tendsto_at_topI_sequentially:
  fixes f :: "real \<Rightarrow> 'b::first_countable_topology"
  assumes *: "\<And>X. filterlim X at_top sequentially \<Longrightarrow> (\<lambda>n. f (X n)) ----> y"
  shows "(f ---> y) at_top"
  unfolding filterlim_iff
proof safe
  fix P assume "eventually P (nhds y)"
  then have seq: "\<And>f. f ----> y \<Longrightarrow> eventually (\<lambda>x. P (f x)) at_top"
    unfolding eventually_nhds_iff_sequentially by simp

  show "eventually (\<lambda>x. P (f x)) at_top"
  proof (rule ccontr)
    assume "\<not> eventually (\<lambda>x. P (f x)) at_top"
    then have "\<And>X. \<exists>x>X. \<not> P (f x)"
      unfolding eventually_at_top_dense by simp
    then obtain r where not_P: "\<And>x. \<not> P (f (r x))" and r: "\<And>x. x < r x"
      by metis
    
    def s \<equiv> "rec_nat (r 0) (\<lambda>_ x. r (x + 1))"
    then have [simp]: "s 0 = r 0" "\<And>n. s (Suc n) = r (s n + 1)"
      by auto

    { fix n have "n < s n" using r
        by (induct n) (auto simp add: real_of_nat_Suc intro: less_trans add_strict_right_mono) }
    note s_subseq = this

    have "mono s"
    proof (rule incseq_SucI)
      fix n show "s n \<le> s (Suc n)"
        using r[of "s n + 1"] by simp
    qed

    have "filterlim s at_top sequentially"
      unfolding filterlim_at_top_gt[where c=0] eventually_sequentially
    proof (safe intro!: exI)
      fix Z :: real and n assume "0 < Z" "natceiling Z \<le> n"
      with real_natceiling_ge[of Z] `n < s n`
      show "Z \<le> s n"
        by auto
    qed
    moreover then have "eventually (\<lambda>x. P (f (s x))) sequentially"
      by (rule seq[OF *])
    then obtain n where "P (f (s n))"
      by (auto simp: eventually_sequentially)
    then show False
      using not_P by (cases n) auto
  qed
qed
  
lemma tendsto_integral_at_top:
  fixes f :: "real \<Rightarrow> 'a::{banach, second_countable_topology}"
  assumes [simp]: "sets M = sets borel" and f[measurable]: "integrable M f"
  shows "((\<lambda>y. \<integral> x. indicator {.. y} x *\<^sub>R f x \<partial>M) ---> \<integral> x. f x \<partial>M) at_top"
proof (rule tendsto_at_topI_sequentially)
  fix X :: "nat \<Rightarrow> real" assume "filterlim X at_top sequentially"
  show "(\<lambda>n. set_lebesgue_integral M {..X n} f) ----> integral\<^sup>L M f"
  proof (rule integral_dominated_convergence)
    show "f \<in> borel_measurable M" "\<And>n. set_borel_measurable M {..X n} f"
      by auto
    show "integrable M (\<lambda>x. norm (f x))"
      by (rule integrable_norm) fact
    show "AE x in M. (\<lambda>n. indicator {..X n} x *\<^sub>R f x) ----> f x"
    proof
      fix x
      from `filterlim X at_top sequentially` 
      have "eventually (\<lambda>n. x \<le> X n) sequentially"
        unfolding filterlim_at_top_ge[where c=x] by auto
      then show "(\<lambda>n. indicator {..X n} x *\<^sub>R f x) ----> f x"
        by (intro Lim_eventually) (auto split: split_indicator elim!: eventually_elim1)
    qed
    fix n show "AE x in M. norm (indicator {..X n} x *\<^sub>R f x) \<le> norm (f x)"
      by (auto split: split_indicator)
  qed
qed

lemma has_bochner_integral_discrete_difference:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes X: "countable X"
  assumes null: "\<And>x. x \<in> X \<Longrightarrow> emeasure M {x} = 0" 
  assumes sets: "\<And>x. x \<in> X \<Longrightarrow> {x} \<in> sets M"
  assumes eq: "\<And>x. x \<in> space M \<Longrightarrow> x \<notin> X \<Longrightarrow> f x = g x"
  shows "has_bochner_integral M f x \<longleftrightarrow> has_bochner_integral M g x"
  using integrable_discrete_difference[of X M f g, OF assms]
  using integral_discrete_difference[of X M f g, OF assms]
  by (metis has_bochner_integral_iff)

lemma has_bochner_integral_even_function:
  fixes f :: "real \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes f: "has_bochner_integral lborel (\<lambda>x. indicator {0..} x *\<^sub>R f x) x"
  assumes even: "\<And>x. f (- x) = f x"
  shows "has_bochner_integral lborel f (2 *\<^sub>R x)"
proof -
  have indicator: "\<And>x::real. indicator {..0} (- x) = indicator {0..} x"
    by (auto split: split_indicator)
  have "has_bochner_integral lborel (\<lambda>x. indicator {.. 0} x *\<^sub>R f x) x"
    by (subst lborel_has_bochner_integral_real_affine_iff[where c="-1" and t=0])
       (auto simp: indicator even f)
  with f have "has_bochner_integral lborel (\<lambda>x. indicator {0..} x *\<^sub>R f x + indicator {.. 0} x *\<^sub>R f x) (x + x)"
    by (rule has_bochner_integral_add)
  then have "has_bochner_integral lborel f (x + x)"
    by (rule has_bochner_integral_discrete_difference[where X="{0}", THEN iffD1, rotated 4])
       (auto split: split_indicator)
  then show ?thesis
    by (simp add: scaleR_2)
qed

lemma has_bochner_integral_odd_function:
  fixes f :: "real \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes f: "has_bochner_integral lborel (\<lambda>x. indicator {0..} x *\<^sub>R f x) x"
  assumes odd: "\<And>x. f (- x) = - f x"
  shows "has_bochner_integral lborel f 0"
proof -
  have indicator: "\<And>x::real. indicator {..0} (- x) = indicator {0..} x"
    by (auto split: split_indicator)
  have "has_bochner_integral lborel (\<lambda>x. - indicator {.. 0} x *\<^sub>R f x) x"
    by (subst lborel_has_bochner_integral_real_affine_iff[where c="-1" and t=0])
       (auto simp: indicator odd f)
  from has_bochner_integral_minus[OF this]
  have "has_bochner_integral lborel (\<lambda>x. indicator {.. 0} x *\<^sub>R f x) (- x)"
    by simp 
  with f have "has_bochner_integral lborel (\<lambda>x. indicator {0..} x *\<^sub>R f x + indicator {.. 0} x *\<^sub>R f x) (x + - x)"
    by (rule has_bochner_integral_add)
  then have "has_bochner_integral lborel f (x + - x)"
    by (rule has_bochner_integral_discrete_difference[where X="{0}", THEN iffD1, rotated 4])
       (auto split: split_indicator)
  then show ?thesis
    by simp
qed

(* extracted from Normal_Distribution *)
lemma integral_exp_neg_x_squared: 
  shows
    "set_integrable lborel {0..} (\<lambda>x. exp (- x\<^sup>2)::real)" and 
    "LBINT x:{0..}. exp (- x\<^sup>2) = sqrt pi / 2"
proof -
  have 1: "(\<integral>\<^sup>+xa. ereal (indicator {0..} xa * exp (- xa\<^sup>2)) \<partial>lborel) = ereal (sqrt pi) / 2"
    apply (subst nn_integral_gaussian[symmetric])
    apply (subst (2) nn_integral_even_function)
    apply (auto simp: field_simps)
    apply (subst mult_commute)
    apply (subst ereal_mult_indicator)
    apply (auto simp: field_simps)
    apply (cases "\<integral>\<^sup>+x. indicator {0..} x * ereal (exp (- x\<^sup>2)) \<partial>lborel")
    apply auto
    done

  (* TODO: refactor *)
  show "set_integrable lborel {0..} (\<lambda>x. exp (- x\<^sup>2)::real)"
    using 1 by (auto intro!: integrableI_nn_integral_finite)
  show "LBINT x:{0..}. exp (- x\<^sup>2) = sqrt pi / 2"
    using 1 by (subst integral_eq_nn_integral) auto
qed

(* rewrite this *)
lemma integral_x_exp_neg_x_squared: 
  shows
    "set_integrable lborel {0..} (\<lambda>x. x * exp (- x\<^sup>2)::real)" and 
    "LBINT x:{0..}. x * exp (- x\<^sup>2) = (1 / 2::real)"
proof -
  have *: "(\<integral>\<^sup>+ x. ereal (indicator {0..} x *\<^sub>R (x * exp (- x\<^sup>2))) \<partial>lborel) = ereal (1 / 2)"
    using nn_integral_x_exp_x_square_indicator
    by (simp add: mult_ac times_ereal.simps(1) [symmetric] ereal_indicator del: times_ereal.simps)

  show "set_integrable lborel {0..} (\<lambda>x. x * exp (- x\<^sup>2)::real)"
    using * by (auto intro!: integrableI_nn_integral_finite AE_I2 split: split_indicator)
  show "LBINT x:{0..}. x * exp (- x\<^sup>2) = (1 / 2::real)"
    using * by (subst integral_eq_nn_integral) (auto intro!: AE_I2 split: split_indicator)
qed

lemma filterlim_at_top_imp_at_infinity:
  fixes f :: "_ \<Rightarrow> real"
  shows "filterlim f at_top F \<Longrightarrow> filterlim f at_infinity F"
  by (rule filterlim_mono[OF _ at_top_le_at_infinity order_refl])

lemma
  fixes k :: nat
  shows gaussian_moment_even_pos:
    "has_bochner_integral lborel (\<lambda>x. indicator {0..} x *\<^sub>R (exp (-x\<^sup>2)*x^(2 * k)))
       ((sqrt pi / 2) * (fact (2 * k) / (2 ^ (2 * k) * fact k)))" (is "?even")
    and gaussian_moment_odd_pos:
      "has_bochner_integral lborel (\<lambda>x. indicator {0..} x *\<^sub>R (exp (-x\<^sup>2)*x^(2 * k + 1))) (fact k / 2)" (is "?odd")
proof -
  let ?M = "\<lambda>k x. exp (- x\<^sup>2) * x^k :: real"

  have moment_0: "has_bochner_integral lborel (\<lambda>x. indicator {0..} x *\<^sub>R ?M 0 x) (sqrt pi / 2)"
    unfolding has_bochner_integral_iff using integral_exp_neg_x_squared by simp

  have moment_1: "has_bochner_integral lborel (\<lambda>x. indicator {0..} x *\<^sub>R ?M 1 x) (1 / 2)"
    unfolding has_bochner_integral_iff using integral_x_exp_neg_x_squared by (simp add: field_simps)

  { fix k I assume Mk: "has_bochner_integral lborel (\<lambda>x. indicator {0..} x *\<^sub>R ?M k x) I"
    have "2 \<noteq> (0::real)"
      by linarith
    let ?f = "\<lambda>b. \<integral>x. indicator {0..} x *\<^sub>R ?M (k + 2) x * indicator {..b} x \<partial>lborel"
    have "((\<lambda>b. (k + 1) / 2 * (LBINT x:{..b}. indicator {0..} x *\<^sub>R ?M k x) - ?M (k + 1) b / 2) --->
        (k + 1) / 2 * (LBINT x:{0..}. ?M k x) - 0 / 2) at_top" (is ?tendsto)
    proof (intro tendsto_intros `2 \<noteq> 0` tendsto_integral_at_top sets_lborel Mk[THEN integrable.intros])
      show "(?M (k + 1) ---> 0) at_top"
      proof cases
        assume "even k"
        have "((\<lambda>x. ((x\<^sup>2)^(k div 2 + 1) / exp (x\<^sup>2)) * (1 / x) :: real) ---> 0 * 0) at_top"
          by (intro tendsto_intros tendsto_divide_0[OF tendsto_const] filterlim_compose[OF tendsto_power_div_exp_0]
                   filterlim_at_top_imp_at_infinity filterlim_ident filterlim_power2_at_top)
        also have "(\<lambda>x. ((x\<^sup>2)^(k div 2 + 1) / exp (x\<^sup>2)) * (1 / x) :: real) = ?M (k + 1)"
          using `even k` by (auto simp: even_mult_two_ex fun_eq_iff exp_minus field_simps power2_eq_square power_mult)
        finally show ?thesis by simp
      next
        assume "odd k"
        have "((\<lambda>x. ((x\<^sup>2)^((k - 1) div 2 + 1) / exp (x\<^sup>2)) :: real) ---> 0) at_top"
          by (intro filterlim_compose[OF tendsto_power_div_exp_0] filterlim_at_top_imp_at_infinity filterlim_ident filterlim_power2_at_top)
        also have "(\<lambda>x. ((x\<^sup>2)^((k - 1) div 2 + 1) / exp (x\<^sup>2)) :: real) = ?M (k + 1)"
          using `odd k` by (auto simp: odd_Suc_mult_two_ex fun_eq_iff exp_minus field_simps power2_eq_square power_mult)
        finally show ?thesis by simp
      qed
    qed
    also have "?tendsto \<longleftrightarrow> ((?f ---> (k + 1) / 2 * (LBINT x:{0..}. ?M k x) - 0 / 2) at_top)"
    proof (intro filterlim_cong refl eventually_at_top_linorder[THEN iffD2] exI[of _ 0] allI impI)
      fix b :: real assume b: "0 \<le> b"
      have "Suc k * (LBINT x:{0..b}. ?M k x) = (LBINT x:{0..b}. exp (- x\<^sup>2) * ((Suc k) * x ^ k))"
        unfolding set_integral_mult_right[symmetric] by (intro integral_cong) auto
      also have "\<dots> = exp (- b\<^sup>2) * b ^ (Suc k) - exp (- 0\<^sup>2) * 0 ^ (Suc k) -
          (LBINT x:{0..b}. - 2 * x * exp (- x\<^sup>2) * x ^ (Suc k))"
        by (rule integral_by_parts')
           (auto intro!: derivative_eq_intros b
                 simp: real_of_nat_def[symmetric] diff_Suc real_of_nat_Suc field_simps split: nat.split)
      also have "(LBINT x:{0..b}. - 2 * x * exp (- x\<^sup>2) * x ^ (Suc k)) =
        (LBINT x:{0..b}. - 2 * (exp (- x\<^sup>2) * x ^ (k + 2)))"
        by (intro integral_cong) auto
      finally have "Suc k * (LBINT x:{0..b}. ?M k x) =
        exp (- b\<^sup>2) * b ^ (Suc k) + 2 * (LBINT x:{0..b}. ?M (k + 2) x)"
        by (simp del: real_scaleR_def)
      then show "(k + 1) / 2 * (LBINT x:{..b}. indicator {0..} x *\<^sub>R ?M k x) - exp (- b\<^sup>2) * b ^ (k + 1) / 2 = ?f b"
        by (simp add: field_simps atLeastAtMost_def indicator_inter_arith)
    qed
    finally have int_M_at_top: "((?f ---> (k + 1) / 2 * (LBINT x:{0..}. ?M k x)) at_top)"
      by simp
    
    have "has_bochner_integral lborel (\<lambda>x. indicator {0..} x *\<^sub>R ?M (k + 2) x) ((k + 1) / 2 * I)"
    proof (rule has_bochner_integral_monotone_convergence_at_top)
      fix y :: real
      have *: "(\<lambda>x. indicator {0..} x *\<^sub>R ?M (k + 2) x * indicator {..y} x::real) =
            (\<lambda>x. indicator {0..y} x *\<^sub>R ?M (k + 2) x)"
        by rule (simp split: split_indicator)
      show "integrable lborel (\<lambda>x. indicator {0..} x *\<^sub>R (?M (k + 2) x) * indicator {..y} x::real)"
        unfolding * by (rule borel_integrable_compact) (auto intro!: continuous_intros)
      show "((?f ---> (k + 1) / 2 * I) at_top)"
        using int_M_at_top has_bochner_integral_integral_eq[OF Mk] by simp
    qed (auto split: split_indicator) }
  note step = this

  show ?even
  proof (induct k)
    case (Suc k)
    note step[OF this]
    also have "(real (2 * k + 1) / 2 * (sqrt pi / 2 * (real (fact (2 * k)) / real (2 ^ (2 * k) * fact k)))) =
      sqrt pi / 2 * (real (fact (2 * Suc k)) / real (2 ^ (2 * Suc k) * fact (Suc k)))"
      by (simp add: field_simps real_of_nat_Suc divide_simps del: fact_Suc) (simp add: field_simps)
    finally show ?case
      by simp
  qed (insert moment_0, simp)

  show ?odd
  proof (induct k)
    case (Suc k)
    note step[OF this]
    also have "(real (2 * k + 1 + 1) / 2 * (real (fact k) / 2)) = real (fact (Suc k)) / 2"
      by (simp add: field_simps real_of_nat_Suc divide_simps del: fact_Suc) (simp add: field_simps)
    finally show ?case
      by simp
  qed (insert moment_1, simp)
qed

lemma std_normal_moment_even:
  fixes k :: nat
  shows "has_bochner_integral lborel
    (\<lambda>x. std_normal_density x * x ^ (2 * k)) (fact (2 * k) / (2^k * fact k))"
proof -
  have "has_bochner_integral lborel (\<lambda>x. exp (-x\<^sup>2)*x^(2 * k))
      (sqrt pi * (fact (2 * k) / (2 ^ (2 * k) * fact k)))"
    using has_bochner_integral_even_function[OF gaussian_moment_even_pos[where k=k]] by simp
  then have "has_bochner_integral lborel (\<lambda>x. (exp (-x\<^sup>2)*x^(2 * k)) * (2^k / sqrt (2 * pi)))
      ((sqrt pi * (fact (2 * k) / (2 ^ (2 * k) * fact k))) * (2^k / sqrt (2 * pi)))"
    by (rule has_bochner_integral_mult_left)
  also have "(\<lambda>x. (exp (-x\<^sup>2)*x^(2 * k)) * (2^k / sqrt (2 * pi))) =
    (\<lambda>x. exp (- ((sqrt 2 * x)\<^sup>2 / 2)) * (sqrt 2 * x) ^ (2 * k) / sqrt (2 * pi))"
    by (auto simp: fun_eq_iff power_mult field_simps real_sqrt_power[symmetric])
  also have "((sqrt pi * (fact (2 * k) / (2 ^ (2 * k) * fact k))) * (2^k / sqrt (2 * pi))) = 
    (inverse (sqrt 2) * (real (fact (2 * k))) / (2 ^ k * real (fact k)))"
    by (auto simp: fun_eq_iff power_mult field_simps real_sqrt_power[symmetric] real_sqrt_mult power2_eq_square)
  finally show ?thesis
    unfolding std_normal_density_def
    by (subst lborel_has_bochner_integral_real_affine_iff[where c="sqrt 2" and t=0]) simp_all
qed

lemma std_normal_moment_abs_odd:
  fixes k :: nat
  shows "has_bochner_integral lborel
    (\<lambda>x. std_normal_density x * \<bar>x\<bar>^(2 * k + 1)) (sqrt (2/pi) * 2^k * fact k)"
proof -
  have "has_bochner_integral lborel (\<lambda>x. indicator {0..} x *\<^sub>R (exp (-x\<^sup>2)*\<bar>x\<bar>^(2 * k + 1))) (fact k / 2)"
    by (rule has_bochner_integral_cong[THEN iffD1, OF _ _ _ gaussian_moment_odd_pos[of k]]) auto
  from has_bochner_integral_even_function[OF this]
  have "has_bochner_integral lborel (\<lambda>x. exp (-x\<^sup>2)*\<bar>x\<bar>^(2 * k + 1)) (fact k)"
    by simp
  then have "has_bochner_integral lborel (\<lambda>x. (exp (-x\<^sup>2)*\<bar>x\<bar>^(2 * k + 1)) * (2^k / sqrt pi))
      (fact k * (2^k / sqrt pi))"
    by (rule has_bochner_integral_mult_left)
  also have "(\<lambda>x. (exp (-x\<^sup>2)*\<bar>x\<bar>^(2 * k + 1)) * (2^k / sqrt pi)) =
    (\<lambda>x. exp (- ((sqrt 2 * x)\<^sup>2 / 2)) * \<bar>sqrt 2 * x\<bar> ^ (2 * k + 1) / sqrt (2 * pi))"
    unfolding real_sqrt_mult
    by (simp add: field_simps abs_mult real_sqrt_power[symmetric] power_mult fun_eq_iff)
  also have "(fact k * (2^k / sqrt pi)) = 
    (inverse (sqrt 2) * (sqrt (2 / pi) * 2 ^ k * real (fact k)))"
    by (auto simp: fun_eq_iff power_mult field_simps real_sqrt_power[symmetric] real_sqrt_divide
                   power2_eq_square)
  finally show ?thesis
    unfolding std_normal_density_def
    by (subst lborel_has_bochner_integral_real_affine_iff[where c="sqrt 2" and t=0]) simp_all
qed

lemma std_normal_moment_odd:
  fixes k :: nat
  shows "has_bochner_integral lborel (\<lambda>x. std_normal_density x * x^(2 * k + 1)) 0"
proof -
  have "has_bochner_integral lborel (\<lambda>x. exp (- x\<^sup>2) * x^(2 * k + 1)::real) 0"
    using gaussian_moment_odd_pos by (rule has_bochner_integral_odd_function) simp
  then have "has_bochner_integral lborel (\<lambda>x. (exp (-x\<^sup>2)*x^(2 * k + 1)) * (2^k/sqrt pi))
      (0 * (2^k/sqrt pi))"
    by (rule has_bochner_integral_mult_left)
  also have "(\<lambda>x. (exp (-x\<^sup>2)*x^(2 * k + 1)) * (2^k/sqrt pi)) =
    (\<lambda>x. exp (- ((sqrt 2 * x)\<^sup>2 / 2)) * (sqrt 2 * x * (sqrt 2 * x) ^ (2 * k)) /
          sqrt (2 * pi))"
    unfolding real_sqrt_mult
    by (simp add: field_simps abs_mult real_sqrt_power[symmetric] power_mult fun_eq_iff)
  finally show ?thesis
    unfolding std_normal_density_def
    by (subst lborel_has_bochner_integral_real_affine_iff[where c="sqrt 2" and t=0]) simp_all
qed

lemma integrable_std_normal_moment: "integrable lborel (\<lambda>x. std_normal_density x * x^k)"
proof cases
  assume "even k" then show ?thesis
    using integrable.intros[OF std_normal_moment_even] by (auto simp add: even_mult_two_ex)
next
  assume "odd k" then show ?thesis
    using integrable.intros[OF std_normal_moment_odd] by (auto simp add: odd_Suc_mult_two_ex)
qed

lemma integrable_std_normal_moment_abs: "integrable lborel (\<lambda>x. std_normal_density x * \<bar>x\<bar>^k)"
proof cases
  assume "even k" then show ?thesis
    using integrable.intros[OF std_normal_moment_even] by (auto simp add: even_mult_two_ex power_even_abs)
next
  assume "odd k" then show ?thesis
    using integrable.intros[OF std_normal_moment_abs_odd] by (auto simp add: odd_Suc_mult_two_ex)
qed

lemma integral_std_normal_moment_even:
  fixes k :: nat
  shows "integral\<^sup>L lborel (\<lambda>x. std_normal_density x * x^(2*k)) = fact (2 * k) / (2^k * fact k)"
  using std_normal_moment_even by (rule has_bochner_integral_integral_eq)

lemma integral_std_normal_moment_abs_odd:
  fixes k :: nat
  shows "integral\<^sup>L lborel (\<lambda>x. std_normal_density x * \<bar>x\<bar>^(2 * k + 1)) = sqrt (2 / pi) * 2^k * fact k"
  using std_normal_moment_abs_odd by (rule has_bochner_integral_integral_eq)

lemma integral_std_normal_moment_odd:
  fixes k :: nat
  shows "integral\<^sup>L lborel (\<lambda>x. std_normal_density x * x^(2 * k + 1)) = 0"
  using std_normal_moment_odd by (rule has_bochner_integral_integral_eq)

(* which is more convenient? *)
abbreviation std_normal_distribution where
  "std_normal_distribution \<equiv> density lborel std_normal_density"

(* a reality check *)
lemma distributed_std_normal_density: 
  "distributed std_normal_distribution lborel (\<lambda>x. x) std_normal_density"
  unfolding distributed_def apply auto
  apply (subst density_distr [symmetric], auto)
by (auto intro!: AE_I2 normal_density_nonneg)

lemma std_normal_distribution_even_moments:
  fixes k :: nat
  shows "integrable std_normal_distribution (\<lambda>x. x ^ (2 * k))" (is ?int)
    and "LINT x | std_normal_distribution. x ^ (2 * k) = (fact (2 * k) / (2^k * fact k))" (is ?eq)
proof -
  show ?int
    by (simp add: integrable_density normal_density_nonneg integrable_std_normal_moment)

  show ?eq
    by (simp add: integral_density normal_density_nonneg integral_std_normal_moment_even power_even_abs)
qed

lemma std_normal_distribution_even_moments_abs:
  fixes k :: nat
  shows "integrable std_normal_distribution (\<lambda>x. abs x ^ (2 * k))" (is ?int)
    and "LINT x | std_normal_distribution. abs x ^ (2 * k) = (fact (2 * k) / (2^k * fact k))" (is ?eq)
proof -
  show ?int
    by (simp add: integrable_density normal_density_nonneg integrable_std_normal_moment_abs)

  show ?eq
    by (simp add: integral_density normal_density_nonneg integral_std_normal_moment_even power_even_abs)
qed

lemma std_normal_distribution_odd_moments:
  fixes k :: nat
  shows "integrable std_normal_distribution (\<lambda>x. x ^ (2 * k + 1))" (is ?int)
    and "LINT x | std_normal_distribution. x ^ (2 * k + 1) = 0" (is ?eq)
proof -
  show ?int
    by (simp add: integrable_density normal_density_nonneg integrable_std_normal_moment 
             del: One_nat_def)

  show ?eq
    by (simp add: integral_density normal_density_nonneg integral_std_normal_moment_odd
             del: One_nat_def)
qed

lemma std_normal_distribution_odd_moments_abs:
  fixes k :: nat
  shows "integrable std_normal_distribution (\<lambda>x. abs x ^ (2 * k + 1))" (is ?int)
    and "LINT x | std_normal_distribution. abs x ^ (2 * k + 1) =  fact k * (2 ^ (k + 1)) / sqrt (2 * pi)" (is ?eq)
proof -
  show ?int
    by (simp add: integrable_density normal_density_nonneg integrable_std_normal_moment_abs 
             del: One_nat_def)

  show ?eq
    by (simp add: integral_density normal_density_nonneg integral_std_normal_moment_abs_odd
             del: One_nat_def)
       (simp add: field_simps real_sqrt_divide real_sqrt_mult)
qed

(* I am uncertain as to which forms are better *)

lemma (in prob_space) standard_normal_distributed_even_moments:
  fixes k :: nat
  assumes D: "distributed M lborel X std_normal_density"
  shows "expectation (\<lambda>x. (X x)^(2 * k)) = (fact (2 * k) / (2^k * fact k))"
  apply (subst distributed_integral[OF D, symmetric])
  apply simp
  apply (rule integral_std_normal_moment_even)
  done

lemma (in prob_space) standard_normal_distributed_odd_moments:
  fixes k :: nat
  assumes D: "distributed M lborel X std_normal_density"
  shows "expectation (\<lambda>x. (X x)^(2 * k + 1)) = 0"
  apply (subst distributed_integral[OF D, symmetric])
  apply simp
  apply (rule integral_std_normal_moment_odd)
  done

end
