(* Normal distribution
   Author: Sudeep Kanav
   Author: Johannes Hölzl *)

theory Normal_Distribution
  imports Probability
begin

lemma filterlim_power2_at_top[intro]: "filterlim (\<lambda>(x::real). x\<^sup>2) at_top at_top"
  by (auto intro!: filterlim_at_top_mult_at_top filterlim_ident simp: power2_eq_square)

lemma distributed_integrable_var:
  fixes X :: "'a \<Rightarrow> real"
  shows "distributed M lborel X (\<lambda>x. ereal (f x)) \<Longrightarrow> integrable lborel (\<lambda>x. f x * x) \<Longrightarrow> integrable M X"
  using distributed_integrable[of M lborel X f "\<lambda>x. x"] by simp

lemma (in ordered_comm_monoid_add) setsum_pos: 
  "finite I \<Longrightarrow> I \<noteq> {} \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> 0 < f i) \<Longrightarrow> 0 < setsum f I"
  by (induct I rule: finite_ne_induct) (auto intro: add_pos_pos)

lemma ln_sqrt: "0 < x \<Longrightarrow> ln (sqrt x) = ln x / 2"
  by (simp add: ln_powr powr_numeral ln_powr[symmetric] mult_commute)

lemma distr_cong: "M = K \<Longrightarrow> sets N = sets L \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> f x = g x) \<Longrightarrow> distr M N f = distr K L g"
  using sets_eq_imp_space_eq[of N L] by (simp add: distr_def Int_def cong: rev_conj_cong)

lemma AE_borel_affine: 
  fixes P :: "real \<Rightarrow> bool"
  shows "c \<noteq> 0 \<Longrightarrow> Measurable.pred borel P \<Longrightarrow> AE x in lborel. P x \<Longrightarrow> AE x in lborel. P (t + c * x)"
  by (subst lborel_real_affine[where t="- t / c" and c="1 / c"])
     (simp_all add: AE_density AE_distr_iff field_simps)

lemma density_distr:
  assumes [measurable]: "f \<in> borel_measurable N" "X \<in> measurable M N"
  shows "density (distr M N X) f = distr (density M (\<lambda>x. f (X x))) N X"
  by (intro measure_eqI)
     (auto simp add: emeasure_density nn_integral_distr emeasure_distr
           split: split_indicator intro!: nn_integral_cong)

lemma ereal_mult_indicator: "ereal (x * indicator A y) = ereal x * indicator A y"
  by (simp split: split_indicator)

lemma (in prob_space) distributed_affine:
  fixes f :: "real \<Rightarrow> ereal"
  assumes f: "distributed M lborel X f"
  assumes c: "c \<noteq> 0"
  shows "distributed M lborel (\<lambda>x. t + c * X x) (\<lambda>x. f ((x - t) / c) / \<bar>c\<bar>)"
  unfolding distributed_def
proof safe
  have [measurable]: "f \<in> borel_measurable borel"
    using f by (simp add: distributed_def)
  have [measurable]: "X \<in> borel_measurable M"
    using f by (simp add: distributed_def)

  show "(\<lambda>x. f ((x - t) / c) / \<bar>c\<bar>) \<in> borel_measurable lborel"
    by simp
  show "random_variable lborel (\<lambda>x. t + c * X x)"
    by simp
  
  have "AE x in lborel. 0 \<le> f x"
    using f by (simp add: distributed_def)
  from AE_borel_affine[OF _ _ this, where c="1/c" and t="- t / c"] c
  show "AE x in lborel. 0 \<le> f ((x - t) / c) / ereal \<bar>c\<bar>"
    by (auto simp add: field_simps)

  have eq: "\<And>x. ereal \<bar>c\<bar> * (f x / ereal \<bar>c\<bar>) = f x"
    using c by (simp add: divide_ereal_def mult_ac one_ereal_def[symmetric])
    
  have "density lborel f = distr M lborel X"
    using f by (simp add: distributed_def)
  with c show "distr M lborel (\<lambda>x. t + c * X x) = density lborel (\<lambda>x. f ((x - t) / c) / ereal \<bar>c\<bar>)"
    by (subst (2) lborel_real_affine[where c="c" and t="t"])
       (simp_all add: density_density_eq density_distr distr_distr field_simps eq cong: distr_cong)
qed

lemma (in prob_space) distributed_affineI:
  fixes f :: "real \<Rightarrow> ereal"
  assumes f: "distributed M lborel (\<lambda>x. (X x - t) / c) (\<lambda>x. \<bar>c\<bar> * f (x * c + t))"
  assumes c: "c \<noteq> 0"
  shows "distributed M lborel X f"
proof -
  have eq: "\<And>x. f x * ereal \<bar>c\<bar> / ereal \<bar>c\<bar> = f x"
    using c by (simp add: divide_ereal_def mult_ac one_ereal_def[symmetric])

  show ?thesis
    using distributed_affine[OF f c, where t=t] c
    by (simp add: field_simps eq)
qed

definition normal_density :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "normal_density \<mu> \<sigma> x = 1 / sqrt (2 * pi * \<sigma>\<^sup>2) * exp (-(x - \<mu>)\<^sup>2/ (2 * \<sigma>\<^sup>2))"

abbreviation standard_normal_density :: "real \<Rightarrow> real" where
  "standard_normal_density \<equiv> normal_density 0 1"

lemma standard_normal_density_def: "standard_normal_density x = (1 / sqrt (2 * pi)) * exp (- x\<^sup>2 / 2)"
  unfolding normal_density_def by simp

lemma borel_measurable_normal_density[measurable]: "normal_density \<mu> \<sigma> \<in> borel_measurable borel"
  by (auto simp: normal_density_def[abs_def])

lemma nn_integral_even_function:
  fixes f :: "real \<Rightarrow> ereal"
  assumes [measurable]: "f \<in> borel_measurable borel"
  assumes even: "\<And>x. f x = f (- x)"
  shows "(\<integral>\<^sup>+x. f x \<partial>lborel) = 2 * (\<integral>\<^sup>+x. f x * indicator {0 ..} x \<partial>lborel)"
proof -
  def f' \<equiv> "\<lambda>x. max 0 (f x)"
  have [measurable]: "f' \<in> borel_measurable borel"
    by (simp add: f'_def)
  
  { fix x :: ereal have "2 * x = x + x"
      by (cases x) auto }
  note two_mult = this

  have "(\<integral>\<^sup>+x. f x \<partial>lborel) = (\<integral>\<^sup>+x. f' x \<partial>lborel)"
    unfolding f'_def nn_integral_max_0 ..
  also have "\<dots> = (\<integral>\<^sup>+x. f' x * indicator {0 ..} x + f' x * indicator {.. 0} x \<partial>lborel)"
    by (intro nn_integral_cong_AE AE_I[where N="{0}"]) (auto split: split_indicator_asm)
  also have "\<dots> = (\<integral>\<^sup>+x. f' x * indicator {0 ..} x \<partial>lborel) + (\<integral>\<^sup>+x. f' x * indicator {.. 0} x \<partial>lborel)"
    by (intro nn_integral_add) (auto simp: f'_def)
  also have "(\<integral>\<^sup>+x. f' x * indicator {.. 0} x \<partial>lborel) = (\<integral>\<^sup>+x. f' x * indicator {0 ..} x \<partial>lborel)"
    using even
    by (subst nn_integral_real_affine[where c="-1" and t=0])
       (auto simp: f'_def one_ereal_def[symmetric] split: split_indicator intro!: nn_integral_cong)
  also have "(\<integral>\<^sup>+x. f' x * indicator {0 ..} x \<partial>lborel) = (\<integral>\<^sup>+x. f x * indicator {0 ..} x \<partial>lborel)"
    unfolding f'_def by (subst (2) nn_integral_max_0[symmetric]) (auto intro!: nn_integral_cong split: split_indicator split_max)
  finally show ?thesis
    unfolding two_mult by simp
qed

lemma nn_integral_gaussian: "(\<integral>\<^sup>+x. (exp (- x\<^sup>2)) \<partial>lborel) = sqrt pi"
proof -
  let ?pI = "\<lambda>f. (\<integral>\<^sup>+s. f (s::real) * indicator {0..} s \<partial>lborel)"
  let ?gauss = "\<lambda>x. exp (- x\<^sup>2)"

  have "?pI ?gauss * ?pI ?gauss = ?pI (\<lambda>s. ?pI (\<lambda>x. ereal (x * exp (-x\<^sup>2 * (1 + s\<^sup>2)))))"
  proof-
    let ?ff= "\<lambda>(x, s). ((x * exp (- x\<^sup>2 * (1 + s\<^sup>2)) * indicator {0<..} s * indicator {0<..} x)) :: real"
  
    have *: "?pI ?gauss = (\<integral>\<^sup>+x. ?gauss x * indicator {0<..} x \<partial>lborel)"
      by (intro nn_integral_cong_AE AE_I[where N="{0}"]) (auto split: split_indicator)
  
    have "?pI ?gauss * ?pI ?gauss = (\<integral>\<^sup>+x. \<integral>\<^sup>+s. ?ff (x, s) \<partial>lborel \<partial>lborel)"
      unfolding *
      apply (auto simp: nn_integral_nonneg nn_integral_cmult[symmetric])
      apply (auto intro!: nn_integral_cong split:split_indicator)
      apply (auto simp: nn_integral_multc[symmetric])
      apply (subst nn_integral_real_affine[where t="0" and c="x"])
      by (auto simp: mult_exp_exp nn_integral_cmult[symmetric] field_simps zero_less_mult_iff
          intro!: nn_integral_cong split:split_indicator)
    also have "... = \<integral>\<^sup>+ (s::real). \<integral>\<^sup>+ (x::real). ?ff (x, s) \<partial>lborel \<partial>lborel"
      by (rule lborel_pair.Fubini[symmetric]) auto
    also have "... = ?pI (\<lambda>s. ?pI (\<lambda>x. ereal (x * exp (-x\<^sup>2 * (1 + s\<^sup>2)))))"
      by (rule nn_integral_cong_AE) (auto intro!: nn_integral_cong_AE AE_I[where N="{0}"] split: split_indicator_asm)
    finally show ?thesis
      by simp
  qed
  also have "\<dots> = ?pI (\<lambda>s. ereal (1 / (2 * (1 + s\<^sup>2))))"
  proof (intro nn_integral_cong ereal_right_mult_cong)
    fix s :: real show "?pI (\<lambda>x. ereal (x * exp (-x\<^sup>2 * (1 + s\<^sup>2)))) = ereal (1 / (2 * (1 + s\<^sup>2)))"
    proof (subst nn_integral_FTC_atLeast)
      have "((\<lambda>a. - (exp (- (a\<^sup>2 * (1 + s\<^sup>2))) / (2 + 2 * s\<^sup>2))) ---> (- (0 / (2 + 2 * s\<^sup>2)))) at_top"
        apply (intro tendsto_intros filterlim_compose[OF exp_at_bot] filterlim_compose[OF filterlim_uminus_at_bot_at_top])
        apply (subst mult_commute)         
        by (auto intro!: filterlim_tendsto_pos_mult_at_top filterlim_at_top_mult_at_top[OF filterlim_ident filterlim_ident] 
          simp: add_pos_nonneg  power2_eq_square add_nonneg_eq_0_iff)
      then show "((\<lambda>a. - (exp (- a\<^sup>2 - s\<^sup>2 * a\<^sup>2) / (2 + 2 * s\<^sup>2))) ---> 0) at_top"
        by (simp add: field_simps)
    qed (auto intro!: derivative_eq_intros simp: field_simps add_nonneg_eq_0_iff)
  qed
  also have "... = ereal (pi / 4)"
  proof (subst nn_integral_FTC_atLeast)
    show "((\<lambda>a. arctan a / 2) ---> (pi / 2) / 2 ) at_top"
      by (intro tendsto_intros) (simp_all add: tendsto_arctan_at_top)
  qed (auto intro!: derivative_eq_intros simp: add_nonneg_eq_0_iff field_simps power2_eq_square)
  finally have "?pI ?gauss^2 = pi / 4"
    by (simp add: power2_eq_square)
  then have "?pI ?gauss = sqrt (pi / 4)"
    using power_eq_iff_eq_base[of 2 "real (?pI ?gauss)" "sqrt (pi / 4)"]
      nn_integral_nonneg[of lborel "\<lambda>x. ?gauss x * indicator {0..} x"]
    by (cases "?pI ?gauss") auto
  then show ?thesis
    by (subst nn_integral_even_function) (auto simp add: real_sqrt_divide)
qed

lemma has_bochner_integral_gaussian: "has_bochner_integral lborel (\<lambda>x. exp (- x\<^sup>2)) (sqrt pi)"
  by (auto intro!: nn_integral_gaussian has_bochner_integral_nn_integral)

lemma integral_gaussian: "(\<integral>x. (exp (- x\<^sup>2)) \<partial>lborel) = sqrt pi"
  using has_bochner_integral_gaussian by (rule has_bochner_integral_integral_eq)

lemma integrable_gaussian[intro]: "integrable lborel (\<lambda>x. exp (- x\<^sup>2)::real)"
  using has_bochner_integral_gaussian by rule

context
  fixes \<sigma> :: real
  assumes \<sigma>_pos[arith]: "0 < \<sigma>"
begin

lemma nn_integral_normal_density: "(\<integral>\<^sup>+x. normal_density \<mu> \<sigma> x \<partial>lborel) = 1"
  unfolding normal_density_def
  apply (subst times_ereal.simps(1)[symmetric],subst nn_integral_cmult)
  apply auto
  apply (subst nn_integral_real_affine[where t=\<mu> and  c="(sqrt 2) * \<sigma>"])
  by (auto simp: power_mult_distrib nn_integral_gaussian real_sqrt_mult one_ereal_def)

lemma 
  shows normal_positive: "\<And>x. 0 < normal_density \<mu> \<sigma> x"
  and normal_nonneg: "\<And>x. 0 \<le> normal_density \<mu> \<sigma> x" 
  by (auto simp: normal_density_def)

lemma integrable_normal[intro]: "integrable lborel (normal_density \<mu> \<sigma>)"
  by (auto intro!: integrableI_nn_integral_finite simp: nn_integral_normal_density normal_nonneg)

lemma integral_normal_density[simp]: "(\<integral>x. normal_density \<mu> \<sigma> x \<partial>lborel) = 1"
  by (simp add: integral_eq_nn_integral normal_nonneg nn_integral_normal_density)

lemma prob_space_normal_density:
  "prob_space (density lborel (normal_density \<mu> \<sigma>))" (is "prob_space ?D")
  proof qed (simp add: emeasure_density nn_integral_normal_density)

end

lemma (in prob_space) normal_density_affine:
  assumes X: "distributed M lborel X (normal_density \<mu> \<sigma>)"
  assumes [simp, arith]: "0 < \<sigma>" "\<alpha> \<noteq> 0"
  shows "distributed M lborel (\<lambda>x. \<beta> + \<alpha> * X x) (normal_density (\<beta> + \<alpha> * \<mu>) (\<bar>\<alpha>\<bar> * \<sigma>))"
proof -
  have eq: "\<And>x. \<bar>\<alpha>\<bar> * normal_density (\<beta> + \<alpha> * \<mu>) (\<bar>\<alpha>\<bar> * \<sigma>) (x * \<alpha> + \<beta>) =
    normal_density \<mu> \<sigma> x"
    by (simp add: normal_density_def real_sqrt_mult field_simps)
       (simp add: power2_eq_square field_simps)
  show ?thesis
    by (rule distributed_affineI[OF _ `\<alpha> \<noteq> 0`, where t=\<beta>]) (simp_all add: eq X)
qed

lemma (in prob_space) normal_standard_normal_convert:
  assumes pos_var[simp, arith]: "0 < \<sigma>"
  shows "distributed M lborel X (normal_density  \<mu> \<sigma>) = distributed M lborel (\<lambda>x. (X x - \<mu>) / \<sigma>) standard_normal_density"
proof auto
  assume "distributed M lborel X (\<lambda>x. ereal (normal_density \<mu> \<sigma> x))"
  then have "distributed M lborel (\<lambda>x. -\<mu> / \<sigma> + (1/\<sigma>) * X x) (\<lambda>x. ereal (normal_density (-\<mu> / \<sigma> + (1/\<sigma>)* \<mu>) (\<bar>1/\<sigma>\<bar> * \<sigma>) x))"
    by(rule normal_density_affine) auto
  
  then show "distributed M lborel (\<lambda>x. (X x - \<mu>) / \<sigma>) (\<lambda>x. ereal (standard_normal_density x))"
    by (simp add: diff_divide_distrib[symmetric] field_simps)
next
  assume *: "distributed M lborel (\<lambda>x. (X x - \<mu>) / \<sigma>) (\<lambda>x. ereal (standard_normal_density x))"
  have "distributed M lborel (\<lambda>x. \<mu> + \<sigma> * ((X x - \<mu>) / \<sigma>)) (\<lambda>x. ereal (normal_density \<mu> \<bar>\<sigma>\<bar> x))"
    using normal_density_affine[OF *, of \<sigma> \<mu>] by simp  
  then show "distributed M lborel X (\<lambda>x. ereal (normal_density \<mu> \<sigma> x))" by simp
qed

lemma conv_normal_density_zero_mean:
  assumes [simp, arith]: "0 < \<sigma>" "0 < \<tau>"
  shows "(\<lambda>x. \<integral>\<^sup>+y. ereal (normal_density 0 \<sigma> (x - y) * normal_density 0 \<tau> y) \<partial>lborel) =
    normal_density 0 (sqrt (\<sigma>\<^sup>2 + \<tau>\<^sup>2))"  (is "?LHS = ?RHS")
proof -
  def \<sigma>' \<equiv> "\<sigma>\<^sup>2" and \<tau>' \<equiv> "\<tau>\<^sup>2"
  then have [simp, arith]: "0 < \<sigma>'" "0 < \<tau>'"
    by simp_all
  let ?\<sigma> = "sqrt ((\<sigma>' * \<tau>') / (\<sigma>' + \<tau>'))"  
  have sqrt: "(sqrt (2 * pi * (\<sigma>' + \<tau>')) * sqrt (2 * pi * (\<sigma>' * \<tau>') / (\<sigma>' + \<tau>'))) = 
    (sqrt (2 * pi * \<sigma>') * sqrt (2 * pi * \<tau>'))"
    by (subst power_eq_iff_eq_base[symmetric, where n=2])
       (simp_all add: real_sqrt_mult[symmetric] power2_eq_square)
  have "?LHS =
    (\<lambda>x. \<integral>\<^sup>+y. ereal((normal_density 0 (sqrt (\<sigma>' + \<tau>')) x) * normal_density (\<tau>' * x / (\<sigma>' + \<tau>')) ?\<sigma> y) \<partial>lborel)"
    apply (intro ext nn_integral_cong)
    apply (simp add: normal_density_def \<sigma>'_def[symmetric] \<tau>'_def[symmetric] sqrt mult_exp_exp)
    apply (simp add: divide_simps power2_eq_square)
    apply (simp add: field_simps)
    done

  also have "... =
    (\<lambda>x. (normal_density 0 (sqrt (\<sigma>\<^sup>2 + \<tau>\<^sup>2)) x) * \<integral>\<^sup>+y. ereal( normal_density (\<tau>\<^sup>2* x / (\<sigma>\<^sup>2 + \<tau>\<^sup>2)) ?\<sigma> y) \<partial>lborel)"
    by (subst nn_integral_cmult[symmetric]) (auto simp: \<sigma>'_def \<tau>'_def normal_density_def)

  also have "... = (\<lambda>x. (normal_density 0 (sqrt (\<sigma>\<^sup>2 + \<tau>\<^sup>2)) x))"
    by (subst nn_integral_normal_density) (auto simp: sum_power2_gt_zero_iff)

  finally show ?thesis by fast
qed

lemma conv_standard_normal_density:
  "(\<lambda>x. \<integral>\<^sup>+y. ereal (standard_normal_density (x - y) * standard_normal_density y) \<partial>lborel) =
  (normal_density 0 (sqrt 2))"
  by (subst conv_normal_density_zero_mean) simp_all

lemma (in prob_space) sum_indep_normal:
  assumes indep: "indep_var borel X borel Y"
  assumes pos_var[arith]: "0 < \<sigma>" "0 < \<tau>"
  assumes normalX[simp]: "distributed M lborel X (normal_density \<mu> \<sigma>)"
  assumes normalY[simp]: "distributed M lborel Y (normal_density \<nu> \<tau>)"
  shows "distributed M lborel (\<lambda>x. X x + Y x) (normal_density (\<mu> + \<nu>) (sqrt (\<sigma>\<^sup>2 + \<tau>\<^sup>2)))"
proof -
  have ind[simp]: "indep_var borel (\<lambda>x. - \<mu> + X x) borel (\<lambda>x. - \<nu> + Y x)"
  proof -
    have "indep_var borel ( (\<lambda>x. -\<mu> + x) o X) borel ((\<lambda>x. - \<nu> + x) o Y)"
      by (auto intro!: indep_var_compose assms) 
    then show ?thesis by (simp add: o_def)
  qed
  
  have "distributed M lborel (\<lambda>x. -\<mu> + 1 * X x) (normal_density (- \<mu> + 1 * \<mu>) (\<bar>1\<bar> * \<sigma>))"
    by(rule normal_density_affine[OF normalX pos_var(1), of 1 "-\<mu>"]) simp
  then have 1[simp]: "distributed M lborel (\<lambda>x. - \<mu> +  X x) (normal_density 0 \<sigma>)" by simp

  have "distributed M lborel (\<lambda>x. -\<nu> + 1 * Y x) (normal_density (- \<nu> + 1 * \<nu>) (\<bar>1\<bar> * \<tau>))"
    by(rule normal_density_affine[OF normalY pos_var(2), of 1 "-\<nu>"]) simp
  then have 2[simp]: "distributed M lborel (\<lambda>x. - \<nu> +  Y x) (normal_density 0 \<tau>)" by simp
  
  have *: "distributed M lborel (\<lambda>x. (- \<mu> + X x) + (- \<nu> + Y x)) (\<lambda>x. ereal (normal_density 0 (sqrt (\<sigma>\<^sup>2 + \<tau>\<^sup>2)) x))"
    using distributed_convolution[OF ind 1 2] conv_normal_density_zero_mean[OF pos_var] by simp
  
  have "distributed M lborel (\<lambda>x. \<mu> + \<nu> + 1 * (- \<mu> + X x + (- \<nu> + Y x)))
        (\<lambda>x. ereal (normal_density (\<mu> + \<nu> + 1 * 0) (\<bar>1\<bar> * sqrt (\<sigma>\<^sup>2 + \<tau>\<^sup>2)) x))"
    by (rule normal_density_affine[OF *, of 1 "\<mu> + \<nu>"]) (auto simp: add_pos_pos)

  then show ?thesis by auto
qed

lemma (in prob_space) diff_indep_normal:
  assumes indep[simp]: "indep_var borel X borel Y"
  assumes [simp, arith]: "0 < \<sigma>" "0 < \<tau>"
  assumes normalX[simp]: "distributed M lborel X (normal_density \<mu> \<sigma>)"
  assumes normalY[simp]: "distributed M lborel Y (normal_density \<nu> \<tau>)"
  shows "distributed M lborel (\<lambda>x. X x - Y x) (normal_density (\<mu> - \<nu>) (sqrt (\<sigma>\<^sup>2 + \<tau>\<^sup>2)))"
proof -
  have "distributed M lborel (\<lambda>x. 0 + - 1 * Y x) (\<lambda>x. ereal (normal_density (0 + - 1 * \<nu>) (\<bar>- 1\<bar> * \<tau>) x))" 
    by(rule normal_density_affine, auto)
  then have [simp]:"distributed M lborel (\<lambda>x. - Y x) (\<lambda>x. ereal (normal_density (- \<nu>) \<tau> x))" by simp

  have "distributed M lborel (\<lambda>x. X x + (- Y x)) (normal_density (\<mu> + - \<nu>) (sqrt (\<sigma>\<^sup>2 + \<tau>\<^sup>2)))"
    apply (rule sum_indep_normal)
    apply (rule indep_var_compose[unfolded comp_def, of borel _ borel _ "\<lambda>x. x" _ "\<lambda>x. - x"])
    apply simp_all
    done
  then show ?thesis by simp
qed

lemma (in prob_space) setsum_indep_normal:
  assumes "finite I" "I \<noteq> {}" "indep_vars (\<lambda>i. borel) X I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> 0 < \<sigma> i"
  assumes normal: "\<And>i. i \<in> I \<Longrightarrow> distributed M lborel (X i) (normal_density (\<mu> i) (\<sigma> i))"
  shows "distributed M lborel (\<lambda>x. \<Sum>i\<in>I. X i x) (normal_density (\<Sum>i\<in>I. \<mu> i) (sqrt (\<Sum>i\<in>I. (\<sigma> i)\<^sup>2)))"
  using assms 
proof (induct I rule: finite_ne_induct)
  case (singleton i) then show ?case by (simp add : abs_of_pos)
next
  case (insert i I)
    then have 1: "distributed M lborel (\<lambda>x. (X i x) + (\<Sum>i\<in>I. X i x)) 
                (normal_density (\<mu> i  + setsum \<mu> I)  (sqrt ((\<sigma> i)\<^sup>2 + (sqrt (\<Sum>i\<in>I. (\<sigma> i)\<^sup>2))\<^sup>2)))"
      apply (intro sum_indep_normal indep_vars_setsum insert real_sqrt_gt_zero)  
      apply (auto intro: indep_vars_subset intro!: setsum_pos)
      apply fastforce
      done
    have 2: "(\<lambda>x. (X i x)+ (\<Sum>i\<in>I. X i x)) = (\<lambda>x. (\<Sum>j\<in>insert i I. X j x))"
          "\<mu> i + setsum \<mu> I = setsum \<mu> (insert i I)"
      using insert by auto
  
    have 3: "(sqrt ((\<sigma> i)\<^sup>2 + (sqrt (\<Sum>i\<in>I. (\<sigma> i)\<^sup>2))\<^sup>2)) = (sqrt (\<Sum>i\<in>insert i I. (\<sigma> i)\<^sup>2))"
      using insert by (simp add: setsum_nonneg)
  
    show ?case using 1 2 3 by simp  
qed

lemma nn_integral_x_exp_x_square: "(\<integral>\<^sup>+x. ereal (x * exp (- x\<^sup>2 )) \<partial>lborel) = ereal 1 / 2" 
  and nn_integral_x_exp_x_square_indicator: "(\<integral>\<^sup>+x. ereal( x * exp (-x\<^sup>2 )) * indicator {0..} x \<partial>lborel) = ereal 1 / 2"
proof - 
  let ?F = "\<lambda>x. - exp (-x\<^sup>2 ) / 2"

  have 1: "(\<integral>\<^sup>+x. ereal (x * exp (- x\<^sup>2)) * indicator {0..} x \<partial>lborel) =ereal( 0 - ?F 0)"
  apply (rule nn_integral_FTC_atLeast)
  apply (auto intro!: derivative_eq_intros)
  apply (rule tendsto_minus_cancel)
  apply (simp add: field_simps)
  proof - 
    have "((\<lambda>(x::real). exp (- x\<^sup>2) / 2) ---> 0 / 2) at_top"
    apply (intro tendsto_divide filterlim_compose[OF exp_at_bot] filterlim_compose[OF filterlim_uminus_at_bot_at_top])
    apply auto
    done
    then show "((\<lambda>(x::real). exp (- x\<^sup>2) / 2) ---> 0) at_top" by simp
  qed

  also have 2: "(\<integral>\<^sup>+x. ereal (x * exp (- x\<^sup>2)) * indicator {0..} x \<partial>lborel) = integral\<^sup>N lborel (\<lambda>x. ereal (x * exp (- x\<^sup>2)))"
    by (subst(2) nn_integral_max_0[symmetric])
       (auto intro!: nn_integral_cong split: split_indicator simp: max_def zero_le_mult_iff)
  finally show "(\<integral>\<^sup>+x. ereal (x * exp (- x\<^sup>2)) \<partial>lborel) = ereal 1 / 2" by auto

  show "(\<integral>\<^sup>+x. ereal (x * exp (- x\<^sup>2)) * indicator {0..} x \<partial>lborel) = ereal 1 / 2" using 1 by auto
qed

lemma borel_integral_x_times_standard_normal[intro]: "(\<integral>x. standard_normal_density x * x \<partial>lborel) = 0" 
  and borel_integrable_x_times_standard_normal[intro]: "integrable lborel (\<lambda>x. standard_normal_density x * x)"
  and borel_integral_x_times_standard_normal'[intro]: "(\<integral>x. x * standard_normal_density x \<partial>lborel) = 0" 
  and borel_integrable_x_times_standard_normal'[intro]: "integrable lborel (\<lambda>x. x * standard_normal_density x)"
proof -    
  have 0: "(\<integral>\<^sup>+x. ereal (x * standard_normal_density x) \<partial>lborel) = \<integral>\<^sup>+x. ereal (x * standard_normal_density x) * indicator {0..} x \<partial>lborel"
    apply (subst nn_integral_max_0[symmetric]) 
    unfolding max_def standard_normal_density_def
    apply (auto intro!: nn_integral_cong split:split_indicator simp: zero_le_divide_iff zero_le_mult_iff)
    apply (metis not_le pi_gt_zero)
    done

  have 1: "(\<integral>\<^sup>+x. ereal (- (x * standard_normal_density x)) \<partial>lborel) = \<integral>\<^sup>+x. ereal (x * standard_normal_density x) * indicator {0..} x \<partial>lborel"
    apply (subst(2) nn_integral_real_affine[where c = "-1" and t = 0])
    apply(auto simp: standard_normal_density_def split: split_indicator)
    apply(subst nn_integral_max_0[symmetric]) 
    unfolding max_def standard_normal_density_def
    apply (auto intro!: nn_integral_cong split: split_indicator
                simp: divide_le_0_iff mult_le_0_iff one_ereal_def[symmetric])
    apply (metis not_le pi_gt_zero)
    done

  have 2: "sqrt pi / sqrt 2 * (\<integral>\<^sup>+x. ereal (x * standard_normal_density x) * indicator {0..} x \<partial>lborel) = integral\<^sup>N lborel (\<lambda>x. ereal (x * exp (- x\<^sup>2)))"
    unfolding standard_normal_density_def
    apply (subst nn_integral_real_affine[where c = "sqrt 2" and t = 0])
    apply (auto simp: power_mult_distrib split: split_indicator)
    apply (subst mult_assoc[symmetric])
    apply (subst nn_integral_cmult[symmetric])
    apply auto
    apply (subst(2) nn_integral_max_0[symmetric])
    apply (auto intro!: nn_integral_cong split: split_indicator simp: max_def zero_le_mult_iff real_sqrt_mult)
    done

  have *: "(\<integral>\<^sup>+x. ereal (x * standard_normal_density x) * indicator {0..} x \<partial>lborel) = sqrt 2 / sqrt pi *(integral\<^sup>N lborel (\<lambda>x. ereal (x * exp (- x\<^sup>2))))"
    apply (subst 2[symmetric])
    apply (subst mult_assoc[symmetric])
    apply (auto simp: field_simps one_ereal_def[symmetric])
    done
    
  show "(\<integral> x. x * standard_normal_density x \<partial>lborel) = 0" "integrable lborel (\<lambda>x. x * standard_normal_density x)"
    by (subst real_lebesgue_integral_def)
       (auto simp: 0 1 * nn_integral_x_exp_x_square real_integrable_def)

  then show "(\<integral> x. standard_normal_density x * x \<partial>lborel) = 0" "integrable lborel (\<lambda>x. standard_normal_density x * x)"
    by (simp_all add:mult_commute)
qed

lemma (in prob_space) standard_normal_distributed_expectation:
  assumes D: "distributed M lborel X standard_normal_density "
  shows "expectation X = 0"
  by (auto simp: distributed_integral[OF D, of "\<lambda>x. x", symmetric])

lemma (in prob_space) normal_distributed_expectation:
  assumes pos_var[arith]: "0 < \<sigma>"
  assumes D: "distributed M lborel X (normal_density \<mu> \<sigma>)"
  shows "expectation X = \<mu>"
proof -
  def X' \<equiv> "\<lambda>x. (X x - \<mu>) / \<sigma>"
  then have D1: "distributed M lborel X' standard_normal_density"
    by (simp add: normal_standard_normal_convert[OF pos_var, of X \<mu>, symmetric] D)
  then have [simp]: "integrable M X'"
    by (rule distributed_integrable_var) auto

  have "expectation X = expectation (\<lambda>x. \<mu> + \<sigma> * X' x)"
    by (simp add: X'_def)
  then show ?thesis
    by (simp add: prob_space standard_normal_distributed_expectation[OF D1])
qed

lemma integral_xsquare_exp_xsquare: "(\<integral> x. (x\<^sup>2 * exp (-x\<^sup>2 )) \<partial>lborel) =  sqrt pi / 2"
  and integrable_xsquare_exp_xsquare: "integrable lborel (\<lambda>x. x\<^sup>2 * exp (- x\<^sup>2)::real)"
proof- 
  note filterlim_compose[OF exp_at_top, intro] filterlim_ident[intro]

  let ?f = "(\<lambda>x. x * - exp (- x\<^sup>2) / 2 - 0 * - exp (- 0\<^sup>2) / 2 -
                 \<integral> xa. 1 * (- exp (- xa\<^sup>2) / 2) * indicator {0..x} xa \<partial>lborel)::real\<Rightarrow>real"
  let ?IFunc = "(\<lambda>z. \<integral>x. (x\<^sup>2 * exp (- x\<^sup>2)) * indicator {0 .. z} x \<partial>lborel)::real\<Rightarrow>real"


  from nn_integral_gaussian  
  have 1: "(\<integral>\<^sup>+xa. ereal (exp (- xa\<^sup>2)) * indicator {0..} xa \<partial>lborel) = ereal (sqrt pi) / ereal 2"
    apply (subst (asm) nn_integral_even_function)
    apply simp
    apply simp
    apply (cases "\<integral>\<^sup>+ xa. ereal (exp (- xa\<^sup>2)) * indicator {0..} xa \<partial>lborel")
    apply auto
    done

  then have I: "(\<integral>xa. exp (- xa\<^sup>2) * indicator {0..} xa \<partial>lborel) = sqrt pi / 2"
    by (subst integral_eq_nn_integral) (auto simp: ereal_mult_indicator)
  
  have byparts: "?IFunc = (\<lambda>z. (if z < 0 then 0 else ?f z))"
    proof (intro HOL.ext, subst split_ifs, safe)
      fix z::real assume [arith]:" \<not> z < 0 "
  
      have "?IFunc z =  \<integral>x. (x * (x * exp (- x\<^sup>2))) * indicator {0 .. z} x \<partial>lborel"
        by(auto intro!: integral_cong split: split_indicator simp: power2_eq_square)
  
      also have "... = (\<lambda>x. x) z * (\<lambda>x. - exp (- x\<^sup>2 ) / 2) z - (\<lambda>x. x) 0 * (\<lambda>x. - exp (- x\<^sup>2) / 2) 0 
          -  \<integral>x. 1 * ( - exp (- x\<^sup>2) / 2) * indicator {0 .. z} x \<partial>lborel"
        by(rule integral_by_parts, auto intro!: derivative_eq_intros)  
      finally have "?IFunc z = ..." .

      then show "?IFunc z = ?f z" by simp
    qed simp    

  have [simp]: "(\<lambda>y. \<integral> x. x\<^sup>2 * exp (- x\<^sup>2) * indicator {0..} x * indicator {..y} x \<partial>lborel) = ?IFunc"
    by(auto intro!: integral_cong split:split_indicator)

  have [intro]: "((\<lambda>(x::real). x * exp (- x\<^sup>2) / 2) ---> 0) at_top"
  proof -
    have "((\<lambda>(x::real). x * exp (- x\<^sup>2) / 2) ---> 0 / 2) at_top"
      apply (intro tendsto_divide filterlim_compose[OF exp_at_bot] filterlim_compose[OF filterlim_uminus_at_bot_at_top])
      apply (auto simp: exp_minus inverse_eq_divide)
      apply (rule lhospital_at_top_at_top[where f' = "\<lambda>x. 1" and g' = "\<lambda>x. 2 * x * exp (x\<^sup>2)"])
      apply (auto intro!: derivative_eq_intros eventually_elim1[OF eventually_gt_at_top, of 1])
      apply (subst inverse_eq_divide[symmetric])
      apply (rule  tendsto_inverse_0_at_top)
      apply (subst mult_assoc)
      by (auto intro!: filterlim_tendsto_pos_mult_at_top[of "\<lambda>x. 2" 2] filterlim_at_top_mult_at_top[OF filterlim_ident])
    
    then show ?thesis by simp
  qed

  have "((\<lambda>x. (\<integral>y. (exp (- y\<^sup>2) * indicator {0..} y) * indicator {.. x} y \<partial>lborel) :: real) ---> \<integral>y. exp (- y\<^sup>2) * indicator {0..} y \<partial>lborel) at_top"
    by (intro tendsto_integral_at_top integrable_mult_indicator) auto
  also have "(\<lambda>x. (\<integral>y. (exp (- y\<^sup>2) * indicator {0..} y) * indicator {.. x} y \<partial>lborel) :: real) = 
    (\<lambda>x. (\<integral>y. exp (- y\<^sup>2) * indicator {0..x} y \<partial>lborel) :: real)"
    by (auto simp: fun_eq_iff split: split_indicator intro!: integral_cong)
  finally have *: "((\<lambda>x. (\<integral>y. exp (- y\<^sup>2) * indicator {0..x} y \<partial>lborel) :: real) ---> \<integral>y. exp (- y\<^sup>2) * indicator {0..} y \<partial>lborel) at_top"
    .

  have tends: "((\<lambda>x. (\<integral> xa. exp (- xa\<^sup>2) * indicator {0..x} xa \<partial>lborel) / 2) ---> (sqrt pi / 2) / 2) at_top"
    apply (rule tendsto_divide)
    apply (subst I[symmetric])
    apply (auto intro: *)
    done

  have [intro]: "(?IFunc ---> sqrt pi / 4) at_top"
    apply (simp add: byparts)
    apply (subst filterlim_cong[where g = ?f])
    apply (auto simp: eventually_ge_at_top linorder_not_less)
  proof -
    have "((\<lambda>x. (\<integral> xa. exp (- xa\<^sup>2) * indicator {0..x} xa / 2 \<partial>lborel) - x * exp (- x\<^sup>2) / 2::real) --->
        (0 + sqrt pi / 4 - 0)) at_top"
      apply (intro tendsto_diff)
      apply auto
      apply (subst divide_real_def)
      using tends
      by (auto intro!: integrable_mult_indicator)
    then show "((\<lambda>x. (\<integral> xa. exp (- xa\<^sup>2) * indicator {0..x} xa \<partial>lborel) / 2 - x * exp (- x\<^sup>2) / 2) ---> sqrt pi / 4) at_top" by  simp
  qed
    
  have [intro]:"\<And>y. integrable lborel (\<lambda>x. x\<^sup>2 * exp (- x\<^sup>2) * indicator {0..} x * indicator {..y} x::real)"
    apply (subst integrable_cong[where g = "\<lambda>x. x\<^sup>2 * exp (- x\<^sup>2) * indicator {0..y} x" for y])
    by (auto intro!: borel_integrable_atLeastAtMost split:split_indicator)
    
  have **[intro]: "integrable lborel (\<lambda>x. x\<^sup>2 * exp (- x\<^sup>2) * indicator {0..} x::real)"
    by (rule integrable_monotone_convergence_at_top) auto

  have "(\<integral>x. x\<^sup>2 * exp (- x\<^sup>2) * indicator {0..} x \<partial>lborel) = sqrt pi / 4"
    by (rule integral_monotone_convergence_at_top) auto
  
  then have "(\<integral>\<^sup>+x. ereal (x\<^sup>2 * exp (- x\<^sup>2)* indicator {0..} x) \<partial>lborel) = sqrt pi / 4"
    by (subst nn_integral_eq_integral) auto

  then have ***: "(\<integral>\<^sup>+ x. ereal (x\<^sup>2 * exp (- x\<^sup>2)) \<partial>lborel) = sqrt pi / 2"
    by (subst nn_integral_even_function)
       (auto simp: real_sqrt_mult real_sqrt_divide ereal_mult_indicator)
  
  then show "(\<integral> x. x\<^sup>2 * exp (- x\<^sup>2) \<partial>lborel) = sqrt pi / 2"
    by (subst integral_eq_nn_integral) auto

  show "integrable lborel (\<lambda>x. x\<^sup>2 * exp (- x\<^sup>2)::real)"
    by (intro integrableI_nn_integral_finite[OF _ _ ***]) auto
qed

lemma integral_xsquare_times_standard_normal[intro]: "(\<integral> x. standard_normal_density x * x\<^sup>2 \<partial>lborel) = 1"
  and integrable_xsquare_times_standard_normal[intro]: "integrable lborel (\<lambda>x. standard_normal_density x * x\<^sup>2)"
proof -
  have [intro]:"integrable lborel (\<lambda>x. exp (- x\<^sup>2) * (2 * x\<^sup>2) / (sqrt 2 * sqrt pi))"
    apply (subst integrable_cong[where g ="(\<lambda>x. (2 * inverse (sqrt 2 * sqrt pi)) * (exp (- x\<^sup>2) * x\<^sup>2))"])
    by (auto intro!: integrable_xsquare_exp_xsquare simp: field_simps)

  have "(\<integral> x. standard_normal_density x * x\<^sup>2 \<partial>lborel) = (2 / sqrt pi) * \<integral> x. x\<^sup>2 * exp (- x\<^sup>2) \<partial>lborel"
    apply (subst integral_mult_right[symmetric])
    apply (rule integrable_xsquare_exp_xsquare)
    unfolding standard_normal_density_def
    apply (subst lborel_integral_real_affine[where c = "sqrt 2" and t=0], simp_all)
    unfolding integral_mult_right_zero[symmetric] integral_divide_zero[symmetric]
    apply (intro integral_cong)
    by (auto simp: power_mult_distrib real_sqrt_mult)
  also have "... = 1"
    by (subst integral_xsquare_exp_xsquare, auto)
  finally show "(\<integral> x. standard_normal_density x * x\<^sup>2 \<partial>lborel) = 1" .

  show "integrable lborel (\<lambda>x. standard_normal_density x * x\<^sup>2)"
    unfolding standard_normal_density_def
    apply (subst lborel_integrable_real_affine_iff[where c = "sqrt 2" and t=0, symmetric])
    by (auto simp: power_mult_distrib real_sqrt_mult)
qed

lemma 
  assumes [arith]: "0 < \<sigma>"
  shows integral_xsquare_times_normal: "(\<integral> x. normal_density \<mu> \<sigma> x * (x - \<mu>)\<^sup>2 \<partial>lborel) = \<sigma>\<^sup>2"
  and integrable_xsquare_times_normal: "integrable lborel (\<lambda>x. normal_density \<mu> \<sigma> x * (x - \<mu>)\<^sup>2)"
proof -
  have "(\<integral> x. normal_density \<mu> \<sigma> x * (x - \<mu>)\<^sup>2 \<partial>lborel) = \<sigma> * \<sigma> * \<integral> x. standard_normal_density x * x\<^sup>2 \<partial>lborel"
    unfolding normal_density_def
    apply (subst lborel_integral_real_affine[ where c = \<sigma> and t = \<mu>])
    apply (auto simp: power_mult_distrib)
    unfolding integral_mult_right_zero[symmetric] integral_divide_zero[symmetric]
    apply (intro integral_cong)
    apply auto
    unfolding normal_density_def
    by (auto simp: real_sqrt_mult field_simps power2_eq_square[symmetric])
    
  also have "... = \<sigma>\<^sup>2" 
    by(auto simp: power2_eq_square[symmetric])

  finally show "(\<integral> x. normal_density \<mu> \<sigma> x * (x - \<mu>)\<^sup>2 \<partial>lborel) = \<sigma>\<^sup>2" .
 
  show "integrable lborel (\<lambda>x. normal_density \<mu> \<sigma> x * (x - \<mu>)\<^sup>2)"
    unfolding normal_density_def
    apply (subst lborel_integrable_real_affine_iff[ where c = \<sigma> and t = \<mu>, symmetric])
    apply auto
    apply (auto simp: power_mult_distrib)
    apply (subst integrable_cong[where g ="(\<lambda>x. \<sigma> * (standard_normal_density x * x\<^sup>2))"], auto)
    unfolding standard_normal_density_def
    by (auto simp: field_simps real_sqrt_mult power2_eq_square[symmetric])
qed
  
lemma (in prob_space) standard_normal_distributed_variance:
  fixes a b :: real
  assumes D: "distributed M lborel X standard_normal_density"
  shows "variance X = 1"
  apply (subst distributed_integral[OF D, of "(\<lambda>x. (x - expectation X)\<^sup>2)", symmetric])
  by (auto simp: standard_normal_distributed_expectation[OF D])

lemma (in prob_space) normal_distributed_variance:
  fixes a b :: real
  assumes [simp, arith]: " 0 < \<sigma>"
  assumes D: "distributed M lborel X (normal_density \<mu> \<sigma>)"
  shows "variance X = \<sigma>\<^sup>2"
proof-  
  have *[intro]: "distributed M lborel (\<lambda>x. (X x - \<mu>) / \<sigma>) (\<lambda>x. ereal (standard_normal_density x))"
    by (subst normal_standard_normal_convert[OF assms(1) , symmetric]) fact

  have "variance X = variance  (\<lambda>x. \<mu> + \<sigma> * ((X x - \<mu>) / \<sigma>) )" by simp
  also have "... = \<sigma>\<^sup>2 * 1"
    apply (subst variance_affine)
    apply (auto intro!: standard_normal_distributed_variance prob_space_normal_density
      simp: distributed_integrable[OF *,of "\<lambda>x. x", symmetric]
      distributed_integrable[OF *,of "\<lambda>x. x\<^sup>2", symmetric] variance_affine
      simp del: integral_divide_zero)
    done

  finally show ?thesis by simp
qed

lemma (in information_space) entropy_normal_density:
  assumes [arith]: "0 < \<sigma>"
  assumes D: "distributed M lborel X (normal_density \<mu> \<sigma>)"
  shows "entropy b lborel X = log b (2 * pi * exp 1 * \<sigma>\<^sup>2) / 2"
proof -
  have "entropy b lborel X = - (\<integral> x. normal_density \<mu> \<sigma> x * log b (normal_density \<mu> \<sigma> x) \<partial>lborel)"
    using D by (rule entropy_distr)
  also have "\<dots> = - (\<integral> x. normal_density \<mu> \<sigma> x * (- ln (2 * pi * \<sigma>\<^sup>2) - (x - \<mu>)\<^sup>2 / \<sigma>\<^sup>2) / (2 * ln b) \<partial>lborel)"
    by (intro arg_cong[where f="uminus"] integral_cong)
       (auto simp: normal_density_def field_simps ln_mult log_def ln_div ln_sqrt)
  also have "\<dots> = - (\<integral>x. - (normal_density \<mu> \<sigma> x * (ln (2 * pi * \<sigma>\<^sup>2)) + (normal_density \<mu> \<sigma> x * (x - \<mu>)\<^sup>2) / \<sigma>\<^sup>2) / (2 * ln b) \<partial>lborel)"
    by (intro arg_cong[where f="uminus"] integral_cong) (auto simp: divide_simps field_simps)
  also have "\<dots> = (\<integral>x. normal_density \<mu> \<sigma> x * (ln (2 * pi * \<sigma>\<^sup>2)) + (normal_density \<mu> \<sigma> x * (x - \<mu>)\<^sup>2) / \<sigma>\<^sup>2 \<partial>lborel) / (2 * ln b)"
    by (simp del: minus_add_distrib)
  also have "\<dots> = (ln (2 * pi * \<sigma>\<^sup>2) + 1) / (2 * ln b)"
    by (simp add: integrable_xsquare_times_normal integrable_normal integral_xsquare_times_normal)
  also have "\<dots> = log b (2 * pi * exp 1 * \<sigma>\<^sup>2) / 2"
    by (simp add: log_def field_simps ln_mult)
  finally show ?thesis .
qed

end
