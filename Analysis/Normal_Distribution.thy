(* Normal distribution
   Author: Sudeep Kanav
   Author: Johannes Hölzl *)

theory Normal_Distribution
  imports Convolution
begin

definition normal_density :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "normal_density \<mu> \<sigma> x = 1 / sqrt (2 * pi * \<sigma>\<^sup>2) * exp (-(x - \<mu>)\<^sup>2/ (2 * \<sigma>\<^sup>2))"

abbreviation "standard_normal_density == normal_density 0 1"

lemma standard_normal_density_def: "standard_normal_density x = (1 / sqrt (2 * pi)) * exp (- x\<^sup>2 /2)"
  unfolding normal_density_def by simp

lemma borel_measurable_normal_density[measurable]: "normal_density \<mu> \<sigma> \<in> borel_measurable borel"
  by (auto simp: normal_density_def[abs_def])

lemma aux3:
  fixes s::real
  shows "(\<integral>\<^sup>+ x. ereal (x * exp (- x\<^sup>2 * (1 + s\<^sup>2))) * indicator {0..} x \<partial>lborel) =  1 / (2 * (1 + s\<^sup>2))"
proof -  
  have "(\<integral>\<^sup>+ x. ereal (x * exp (- x\<^sup>2 * (1 + s\<^sup>2))) * indicator {0..} x \<partial>lborel) = ereal (0 - (\<lambda>x. ((-1 / (2 * (1 + s\<^sup>2)))) * exp (-x\<^sup>2 * (1 + s\<^sup>2))) 0)"
    proof(rule positive_integral_FTC_atLeast, auto intro!: DERIV_intros simp: mult_nonneg_nonneg)
      have "((\<lambda>a. - (exp (- (a\<^sup>2 * (1 + s\<^sup>2))) / (2 + 2 * s\<^sup>2))) ---> (- (0 / (2 + 2 * s\<^sup>2)))) at_top"
        apply (intro tendsto_intros filterlim_compose[OF exp_at_bot] filterlim_compose[OF filterlim_uminus_at_bot_at_top])
        apply (subst mult_commute)         
        by (auto intro!: filterlim_tendsto_pos_mult_at_top filterlim_at_top_mult_at_top[OF filterlim_ident filterlim_ident] 
          simp: add_pos_nonneg  power2_eq_square)        
      then show "((\<lambda>a. - (exp (- (a\<^sup>2 * (1 + s\<^sup>2))) / (2 + 2 * s\<^sup>2))) ---> 0) at_top" by simp      
   qed (simp add:field_simps)
  then show ?thesis by simp
qed

lemma aux4:
    "(\<integral>\<^sup>+ x. ereal (exp (- x\<^sup>2) * indicator {0..} x) \<partial>lborel) * (\<integral>\<^sup>+ x. ereal (exp (- x\<^sup>2) * indicator {0..} x) \<partial>lborel) =
    \<integral>\<^sup>+ s. (\<integral>\<^sup>+ x. ereal (x * exp (- x\<^sup>2 * (1 + s\<^sup>2)) * indicator {0..} x) \<partial>lborel) * indicator {0..} s \<partial>lborel"
proof-
  let ?f = "\<lambda>x. exp (- x\<^sup>2) * indicator {0..} x"
  let ?ff= "\<lambda>(x::real, s::real). ((x * exp (- x\<^sup>2 * (1 + s\<^sup>2)) * indicator {0<..} s * indicator {0<..} x))"

  have *: "(integral\<^sup>P lborel ?f) = (integral\<^sup>P lborel  (\<lambda>x. exp (- x\<^sup>2) * indicator {0<..} x))"
    by (auto intro!: positive_integral_cong_AE split:split_indicator)
       (rule AE_I[where N="{0}"], auto)

  have "(integral\<^sup>P lborel ?f) *  (integral\<^sup>P lborel ?f) = (integral\<^sup>P lborel (\<lambda>(x::real). (integral\<^sup>P lborel (\<lambda>(s::real). x * exp (-x\<^sup>2 * (1 + s\<^sup>2)) * indicator {0<..} s * indicator {0<..} x))))"
    apply (simp add: *)
    apply (auto simp: positive_integral_positive  positive_integral_cmult[symmetric])
    apply (auto intro!: positive_integral_cong split:split_indicator)
    apply (auto simp: positive_integral_multc[symmetric])
    apply (subst positive_integral_real_affine[where t="0" and M=lborel and c="x"])
    by (auto simp: mult_nonneg_nonneg mult_pos_pos mult_exp_exp positive_integral_cmult[symmetric] field_simps power_mult_distrib zero_less_mult_iff
        intro!: positive_integral_cong split:split_indicator)

  also have "... = \<integral>\<^sup>+ (x::real). \<integral>\<^sup>+ (s::real). ?ff (x, s) \<partial>lborel \<partial>lborel" by (auto intro!: positive_integral_cong)
  also have "... = \<integral>\<^sup>+ (s::real). \<integral>\<^sup>+ (x::real). ?ff (x, s) \<partial>lborel \<partial>lborel" by (rule lborel_pair.Fubini[symmetric]) auto
  also have "... = (integral\<^sup>P lborel (\<lambda>(s::real). (integral\<^sup>P lborel (\<lambda>(x::real). x * exp (-x\<^sup>2 * (1 + s\<^sup>2)) * indicator {0..} x) * indicator {0..} s)))"
    apply (rule positive_integral_cong_AE)
    by (auto intro!: positive_integral_cong_AE AE_I[where N="{0}"] split: split_indicator)
   finally show ?thesis by fast
qed

lemma gaussian_integral_positive: "(\<integral>\<^sup>+x. (exp (- x\<^sup>2)) \<partial>lborel) = sqrt pi"
proof -
(*  let ?i = "\<lambda>f. (\<integral>\<^sup>+ x. ereal (f x) * indicator {0..} x \<partial>lborel)" *)
  let ?I = "\<integral>\<^sup>+x. (exp (- x\<^sup>2)) \<partial>lborel"   
  let ?f = "\<lambda>x. exp (- x\<^sup>2) * indicator {0..} x"
  let ?ff = "\<lambda>(x::real, s::real). ((x * exp (- x\<^sup>2 * (1 + s\<^sup>2)) * indicator {0..} s * indicator {0..} x))"
  
  have 1: "?I\<^sup>2 = 4 * (integral\<^sup>P lborel ?f) * (integral\<^sup>P lborel ?f)"
    apply (cases "integral\<^sup>P lborel ?f")
    by (auto simp: power2_eq_square ac_simps positive_integral_even_function)

  have 2: "(integral\<^sup>P lborel ?f) * (integral\<^sup>P lborel ?f) = \<integral>\<^sup>+ s. (\<integral>\<^sup>+ x. ereal (x * exp (- x\<^sup>2 * (1 + s\<^sup>2)) * indicator {0..} x) \<partial>lborel) * indicator {0..} s \<partial>lborel"
    by(rule aux4)

  fix s::real
    
  let ?I1 =" \<integral>\<^sup>+ x. ereal (x * exp (- x\<^sup>2 * (1 + s\<^sup>2))) * indicator {0..} x \<partial>lborel"
  have 3:"?I1 = 1 / (2 * (1 + s\<^sup>2)) "
    by(rule aux3)

  have "(\<integral>\<^sup>+ x. ereal (x * exp (- x\<^sup>2 * (1 + s\<^sup>2)) * indicator {0..} s * indicator {0..} x) \<partial>lborel) = 
        \<integral>\<^sup>+ x. indicator {0..} s * ereal (x * exp (- x\<^sup>2 * (1 + s\<^sup>2)) ) * indicator {0..} x \<partial>lborel"
    by(auto intro!: positive_integral_cong split:split_indicator)

  then have [simp]:"... =  (indicator {0..} s) *  1 / (2 * (1 + s\<^sup>2))" using 3 by (auto split:split_indicator)
     
  have 6:"integral\<^sup>P lborel (\<lambda>(s::real). (integral\<^sup>P lborel (\<lambda>(x::real). x * exp (-x\<^sup>2 * (1 + s\<^sup>2)) * indicator {0..} x) * indicator {0..} s)) 
         = integral\<^sup>P lborel (\<lambda>(s::real). ereal (1 / (2 * (1 + s\<^sup>2))) * (indicator {0..} s))"
    by (subst aux3[symmetric]) (auto simp: aux3[symmetric] intro!: positive_integral_cong split: split_indicator)
        
  also have "... = ereal ( pi / 4 - (\<lambda>x. arctan x / 2) 0)"
    apply (rule positive_integral_FTC_atLeast, auto)
    apply (intro DERIV_intros, auto simp:inverse_eq_divide distrib_left) 
    apply (simp add:field_simps)
    proof-
      have "((\<lambda>a. arctan a / 2) ---> (pi / 2) / 2 ) at_top"
      apply (intro tendsto_intros)
      by (simp_all add: tendsto_arctan_at_top)
      then show "((\<lambda>a. arctan a / 2) ---> pi / 4) at_top" by simp
   qed
  also have "... = pi / 4" by simp
  finally have "(integral\<^sup>P lborel (\<lambda>(s::real). (integral\<^sup>P lborel (\<lambda>(x::real). x * exp (-x\<^sup>2 * (1 + s\<^sup>2)) * indicator {0..} x) * indicator {0..} s))) = pi / 4"
    by linarith

  with 1 2 3 have 8:" (\<integral>\<^sup>+ x. ereal (exp (- x\<^sup>2)) \<partial>lborel)\<^sup>2 = pi" by(simp add:field_simps)
  
  then show ?thesis
    apply (cases "(\<integral>\<^sup>+ x. ereal (exp (- x\<^sup>2)) \<partial>lborel)", auto intro!: power2_eq_imp_eq[where y= "sqrt pi"])
    by (metis ereal_less_eq(5) positive_integral_positive)    
qed

lemma gaussian_integral: "(\<integral>x. (exp (- x\<^sup>2)) \<partial>lborel) = (sqrt pi)"
  by (auto intro!: lebesgue_integral_eq_positive_integral gaussian_integral_positive)

lemma gaussian_integrable[intro]: "integrable lborel (\<lambda>x. exp (- x\<^sup>2))"
  by (auto intro!: integrable_if_positive_integral gaussian_integral_positive)

context
  fixes \<sigma> :: real
  assumes \<sigma>_pos[arith]: "0 < \<sigma>"
begin

lemma positive_integral_normal_density: "(\<integral>\<^sup>+x. normal_density \<mu> \<sigma> x \<partial>lborel) = 1"
  unfolding normal_density_def
  apply (subst times_ereal.simps(1)[symmetric],subst positive_integral_cmult)
  apply (auto simp: mult_nonneg_nonneg)
  apply (subst positive_integral_real_affine[where t=\<mu> and  c="(sqrt 2) * \<sigma>"])
  by (auto simp: power_mult_distrib gaussian_integral_positive mult_nonneg_nonneg real_sqrt_mult one_ereal_def)

lemma 
  shows normal_positive: "\<And>x. 0 < normal_density \<mu> \<sigma> x"
  and normal_non_negative: "\<And>x. 0 \<le> normal_density \<mu> \<sigma> x" 
  unfolding normal_density_def
  by (auto simp: mult_nonneg_nonneg divide_nonneg_nonneg mult_pos_pos divide_pos_pos)


lemma integrable_normal[intro]: "integrable lborel (normal_density \<mu> \<sigma>)"
   by (auto intro!: integrable_if_positive_integral[where x=1] normal_non_negative 
            simp: positive_integral_normal_density one_ereal_def)

lemma integral_normal_density[simp]: "(\<integral>x. normal_density \<mu> \<sigma> x \<partial>lborel) = 1"
  using positive_integral_normal_density
  by (subst lebesgue_integral_eq_positive_integral)
     (auto intro!: normal_non_negative simp: one_ereal_def)

lemma prob_space_normal_density:
  "prob_space (density lborel (normal_density \<mu> \<sigma>))" (is "prob_space ?D")
proof-
  have "emeasure ?D (space ?D) =  emeasure (density lborel (\<lambda>x. normal_density \<mu> \<sigma> x)) UNIV"
    unfolding normal_density_def by auto
  also have "... = \<integral>\<^sup>+ x.  normal_density \<mu> \<sigma> x \<partial>lborel"
    by (subst emeasure_density[of "\<lambda>x. normal_density \<mu> \<sigma> x" lborel UNIV]) auto
  also have " ...  = 1"
    by (rule positive_integral_normal_density)
  finally show "prob_space ?D" by rule
qed

end

lemma (in prob_space) normal_density_affine:
  assumes X: "distributed M lborel X (normal_density \<mu> \<sigma>)"
  assumes [simp, arith]: "0 < \<sigma>" "\<alpha> \<noteq> 0"
  shows "distributed M lborel (\<lambda>x. \<beta> + \<alpha> * X x) (normal_density (\<beta> + \<alpha> * \<mu>) (\<bar>\<alpha>\<bar> * \<sigma>))"
proof -
  have eq: "\<And>x. \<bar>\<alpha>\<bar> * normal_density (\<beta> + \<alpha> * \<mu>) (\<bar>\<alpha>\<bar> * \<sigma>) (x * \<alpha> + \<beta>) =
    normal_density \<mu> \<sigma> x"
    by (simp add: normal_density_def real_sqrt_mult power_mult_distrib field_simps)
       (simp add: power2_eq_square field_simps)
  show ?thesis
    by (rule distributed_affineI[OF _ `\<alpha> \<noteq> 0`, where t=\<beta>]) (simp_all add: eq X)
qed

lemma (in prob_space) normal_standard_normal_convert:
  assumes pos_var[simp, arith]: "0 < \<sigma>"
  shows "distributed M lborel X (normal_density  \<mu> \<sigma>) = distributed M lborel (\<lambda>x. (X x - \<mu>)/ \<sigma>) standard_normal_density"
proof(auto)
  assume "distributed M lborel X (\<lambda>x. ereal (normal_density \<mu> \<sigma> x))"
  then have "distributed M lborel (\<lambda>x. -\<mu> / \<sigma> + (1/\<sigma>) * X x) (\<lambda>x. ereal (normal_density (-\<mu> / \<sigma> + (1/\<sigma>)* \<mu>) (\<bar>1/\<sigma>\<bar> * \<sigma>) x))"
    by(rule normal_density_affine) auto
  
  then show "distributed M lborel (\<lambda>x. (X x - \<mu>) / \<sigma>) (\<lambda>x. ereal (standard_normal_density x))"
    by (simp add: uminus_add_conv_diff diff_divide_distrib[symmetric])
next
  assume *: "distributed M lborel (\<lambda>x. (X x - \<mu>) / \<sigma>) (\<lambda>x. ereal (standard_normal_density x))"
  have "distributed M lborel (\<lambda>x. \<mu> + \<sigma> * ((X x - \<mu>) / \<sigma>)) (\<lambda>x. ereal (normal_density \<mu> \<bar>\<sigma>\<bar> x))"
    using normal_density_affine[OF *, of \<sigma> \<mu>] by simp  
  then show "distributed M lborel X (\<lambda>x. ereal (normal_density \<mu> \<sigma> x))" by simp
qed

lemma conv_standard_normal_density:
  "(\<lambda>x. \<integral>\<^sup>+y. ereal (standard_normal_density (x - y) * standard_normal_density y) \<partial>lborel) = (normal_density 0 (sqrt 2))"
proof -
  have [simp]: "sqrt 4 = 2"
    apply (subgoal_tac "2\<^sup>2 = 4")
    apply (erule subst)
    by (subst real_sqrt_abs, auto simp: power2_eq_square[symmetric])
  
  have "(\<lambda>x. \<integral>\<^sup>+y. ereal (standard_normal_density (x - y) * standard_normal_density y) \<partial>lborel)
            = (\<lambda>x. \<integral>\<^sup>+y. ereal((1 / (2 * pi)) * exp (- x\<^sup>2 / 4) * exp (- (2 * y - x)\<^sup>2 /( 2 * (sqrt 2)\<^sup>2))) \<partial>lborel)"
    apply (rule HOL.ext) unfolding standard_normal_density_def
    apply (auto intro!: positive_integral_cong simp: mult_exp_exp power2_eq_square[symmetric])
    by (simp add: power2_eq_square field_simps)     

  also have "... = (\<lambda>x. \<integral>\<^sup>+y. ereal((1 / (2 * pi)) * exp (- x\<^sup>2 / 4) * exp (- y\<^sup>2)) \<partial>lborel)"
    proof(rule HOL.ext)
    fix x::real
    show "(\<integral>\<^sup>+y. ereal (1 / (2 * pi) * exp (- x\<^sup>2 / 4) * exp (- (2 * y - x)\<^sup>2 / (2 * (sqrt 2)\<^sup>2))) \<partial>lborel) =
        \<integral>\<^sup>+y. ereal (1 / (2 * pi) * exp (- x\<^sup>2 / 4) * exp (- y\<^sup>2)) \<partial>lborel"
      apply (subst positive_integral_real_affine[where t="x/2" and  c="1" and M= lborel], auto)
      by (auto intro!: positive_integral_cong simp: divide_nonneg_nonneg mult_nonneg_nonneg power2_eq_square)      
    qed

  also have "... = (\<lambda>x. ((1 / (2 * pi)) * exp (- x\<^sup>2 / 4)) * \<integral>\<^sup>+ y. ereal ( exp (- y\<^sup>2 ) ) \<partial>lborel)"
    by (auto simp: divide_nonneg_nonneg mult_nonneg_nonneg positive_integral_cmult[symmetric])

  also have "... = (\<lambda>x. ((1 / (2 * pi)) * exp (- x\<^sup>2 / 4)) * sqrt pi)"
    by (subst gaussian_integral_positive, auto)

  also have "... = (normal_density 0 (sqrt 2))"
    unfolding normal_density_def
    apply (rule HOL.ext)
    by (auto simp:field_simps real_sqrt_mult power2_eq_square[symmetric])

  finally show ?thesis by fast
qed

lemma conv_normal_density_zero_mean:
  assumes [simp, arith]: "0 < \<sigma>" "0 < \<tau>"
  shows "(\<lambda>x. \<integral>\<^sup>+y. ereal (normal_density 0 \<sigma> (x - y) * normal_density 0 \<tau> y) \<partial>lborel) = (normal_density 0 (sqrt (\<sigma>\<^sup>2 + \<tau>\<^sup>2)))"  (is "?LHS = ?RHS")
proof -
  have [simp]: "sqrt (pi * (2 * \<sigma>\<^sup>2) + pi * (2 * \<tau>\<^sup>2)) * sqrt (pi * (2 * (sqrt (\<sigma>\<^sup>2 * \<tau>\<^sup>2 / (\<sigma>\<^sup>2 + \<tau>\<^sup>2)))\<^sup>2)) = 2 * pi * \<sigma> * \<tau>"
    apply (subst distrib_left[symmetric])+
    apply (subst real_sqrt_mult)+
    by(auto simp : mult_nonneg_nonneg real_sqrt_divide real_sqrt_mult field_simps power2_eq_square[symmetric])
  
  have [simp]: "sqrt (pi * (2 * \<sigma>\<^sup>2)) * sqrt (pi * (2 * \<tau>\<^sup>2)) = pi * 2 * \<sigma> * \<tau>"
    by (auto simp: field_simps real_sqrt_mult) (auto simp:  power2_eq_square[symmetric])

  have 1: "\<And>x y. y\<^sup>2 / (2 * \<tau>\<^sup>2) = (y\<^sup>2 * \<sigma>\<^sup>2 * \<sigma>\<^sup>2 + y\<^sup>2 * \<sigma>\<^sup>2 * \<tau>\<^sup>2) / ( 2 * \<sigma>\<^sup>2 * \<tau>\<^sup>2 * (\<sigma>\<^sup>2 + \<tau>\<^sup>2))"
    by (auto simp:field_simps power2_eq_square mult_nonneg_nonneg frac_eq_eq) 

  have 2: "\<And>x y. (x - y)\<^sup>2 / (2 * \<sigma>\<^sup>2) 
          = (x\<^sup>2 * \<sigma>\<^sup>2 * \<tau>\<^sup>2 + x\<^sup>2 * \<tau>\<^sup>2 * \<tau>\<^sup>2 + y\<^sup>2 * \<sigma>\<^sup>2 * \<tau>\<^sup>2 + y\<^sup>2 * \<tau>\<^sup>2 * \<tau>\<^sup>2 
          - 2 * x * y * \<sigma>\<^sup>2 * \<tau>\<^sup>2 - 2 * x * y * \<tau>\<^sup>2 * \<tau>\<^sup>2) / ( 2 * \<sigma>\<^sup>2 * \<tau>\<^sup>2 * (\<sigma>\<^sup>2 + \<tau>\<^sup>2))"
    by (auto simp:field_simps power2_eq_square mult_nonneg_nonneg frac_eq_eq)
  
  have 3: "\<And>x y. x\<^sup>2 / (2 * \<sigma>\<^sup>2 + 2 * \<tau>\<^sup>2) = (x\<^sup>2 * \<sigma>\<^sup>2 * \<tau>\<^sup>2 ) / ( 2 * \<sigma>\<^sup>2 * \<tau>\<^sup>2* (\<sigma>\<^sup>2 + \<tau>\<^sup>2))"
    by (auto simp:field_simps power2_eq_square mult_nonneg_nonneg frac_eq_eq)  

  have 4: "\<And>x y.((y * \<sigma>\<^sup>2 + y * \<tau>\<^sup>2 - x * \<tau>\<^sup>2) / (\<sigma>\<^sup>2 + \<tau>\<^sup>2))\<^sup>2 / (2 * (sqrt (\<sigma>\<^sup>2 * \<tau>\<^sup>2 / (\<sigma>\<^sup>2 + \<tau>\<^sup>2)))\<^sup>2)
          = (y\<^sup>2 * \<sigma>\<^sup>2 * \<sigma>\<^sup>2 +  y\<^sup>2 * \<tau>\<^sup>2 * \<tau>\<^sup>2 + 2* y\<^sup>2 *\<sigma>\<^sup>2 *\<tau>\<^sup>2 + x\<^sup>2 * \<tau>\<^sup>2 * \<tau>\<^sup>2 
            - 2* x*y*\<sigma>\<^sup>2 *\<tau>\<^sup>2 - 2*x* y*\<tau>\<^sup>2 *\<tau>\<^sup>2  ) / ( 2 * \<sigma>\<^sup>2 * \<tau>\<^sup>2* (\<sigma>\<^sup>2 + \<tau>\<^sup>2))"
    apply(subst power_divide)
    apply(subst real_sqrt_pow2)
    by (auto simp:field_simps power2_eq_square zero_le_mult_iff zero_le_divide_iff frac_eq_eq power_divide) 

  let ?new_var = "sqrt ((\<sigma>\<^sup>2 * \<tau>\<^sup>2 )/ (\<sigma>\<^sup>2 + \<tau>\<^sup>2))"  
  
  have "?LHS = (\<lambda>x. \<integral>\<^sup>+y. ereal((1 / sqrt (2 * pi * (\<sigma>\<^sup>2 + \<tau>\<^sup>2))) * exp (- x\<^sup>2 / (2 * (sqrt (\<sigma>\<^sup>2 + \<tau>\<^sup>2))\<^sup>2))
                * (1 / sqrt (2 * pi *  ?new_var\<^sup>2)) * exp (- (y - \<tau>\<^sup>2 * x/  (\<sigma>\<^sup>2 + \<tau>\<^sup>2))\<^sup>2 /( 2 * ?new_var\<^sup>2))) \<partial>lborel)"
    apply(rule HOL.ext)
    unfolding normal_density_def
    apply(rule positive_integral_cong)
    apply(auto simp:field_simps) 
    apply (simp only: 1 2 3 4 mult_exp_exp minus_add_distrib[symmetric] add_divide_distrib[symmetric])  
    by auto
  
  also have "... = (\<lambda>x. \<integral>\<^sup>+y. ereal((normal_density 0 (sqrt (\<sigma>\<^sup>2 + \<tau>\<^sup>2)) x) * normal_density (\<tau>\<^sup>2 * x /  (\<sigma>\<^sup>2 + \<tau>\<^sup>2)) ?new_var y) \<partial>lborel)"
    unfolding normal_density_def by auto
  
  also have "... = (\<lambda>x. (normal_density 0 (sqrt (\<sigma>\<^sup>2 + \<tau>\<^sup>2)) x) * \<integral>\<^sup>+y. ereal( normal_density (\<tau>\<^sup>2* x/  (\<sigma>\<^sup>2 + \<tau>\<^sup>2)) ?new_var y) \<partial>lborel)"
    apply (subst positive_integral_cmult[symmetric])
    unfolding normal_density_def 
    by (auto simp: divide_nonneg_nonneg mult_nonneg_nonneg)

  also have "... = (\<lambda>x. (normal_density 0 (sqrt (\<sigma>\<^sup>2 + \<tau>\<^sup>2)) x))"
    by (subst positive_integral_normal_density, auto simp: divide_pos_pos mult_pos_pos sum_power2_gt_zero_iff)

  finally show ?thesis by fast
qed

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
    using convolution_distributed_indep_random_variable_sum[OF ind 1 2] conv_normal_density_zero_mean[OF pos_var, symmetric]
    by (metis normal_non_negative pos_var(1) pos_var(2))
  
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
    by (intro sum_indep_normal indep_var_neg) simp_all
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
      by (intro sum_indep_normal indep_vars_setsum insert real_sqrt_gt_zero setsum_pos_pos)  
        (auto intro: indep_vars_subset, fastforce)
         
    have 2: "(\<lambda>x. (X i x)+ (\<Sum>i\<in>I. X i x)) = (\<lambda>x. (\<Sum>j\<in>insert i I. X j x))"
          "\<mu> i + setsum \<mu> I = setsum \<mu> (insert i I)"
      using insert by(auto simp:random_vars_insert)    
  
    have 3: "(sqrt ((\<sigma> i)\<^sup>2 + (sqrt (\<Sum>i\<in>I. (\<sigma> i)\<^sup>2))\<^sup>2)) = (sqrt (\<Sum>i\<in>insert i I. (\<sigma> i)\<^sup>2))"
      apply(subst real_sqrt_pow2, rule less_imp_le)
      using insert 
      by(auto intro!:setsum_pos_pos simp:random_vars_insert, fastforce)
  
    show ?case using 1 2 3 by simp  
qed

lemma positive_integral_x_exp_x_square: "(\<integral>\<^sup>+x. ereal (x * exp (- x\<^sup>2 )) \<partial>lborel) = ereal 1 / 2" 
  and positive_integral_x_exp_x_square_indicator: "(\<integral>\<^sup>+x. ereal( x * exp (-x\<^sup>2 )) * indicator {0..} x \<partial>lborel) = ereal 1 / 2"
proof - 
  let ?F = "\<lambda>x. - exp (-x\<^sup>2 ) / 2"

  have 1: "(\<integral>\<^sup>+x. ereal (x * exp (- x\<^sup>2)) * indicator {0..} x \<partial>lborel) =ereal( 0 - ?F 0)"
  apply (rule positive_integral_FTC_atLeast)
  apply (auto intro!: DERIV_intros tendsto_minus_cancel[of "(\<lambda>a. - (exp (- a\<^sup>2) / 2))" 0] simp: mult_nonneg_nonneg)
  proof - 
    have "((\<lambda>(x::real). exp (- x\<^sup>2) / 2) ---> 0 / 2) at_top"
    apply (intro tendsto_divide filterlim_compose[OF exp_at_bot] filterlim_compose[OF filterlim_uminus_at_bot_at_top])
    by auto
    then show "((\<lambda>(x::real). exp (- x\<^sup>2) / 2) ---> 0) at_top" by simp
  qed

  also have 2: "(\<integral>\<^sup>+x. ereal (x * exp (- x\<^sup>2)) * indicator {0..} x \<partial>lborel) = integral\<^sup>P lborel (\<lambda>x. ereal (x * exp (- x\<^sup>2)))"
    apply (subst(2) positive_integral_max_0[symmetric])
    unfolding max_def 
    by (auto intro!: positive_integral_cong split:split_indicator simp: mult_nonneg_nonneg zero_le_mult_iff)
  finally show "(\<integral>\<^sup>+x. ereal (x * exp (- x\<^sup>2)) \<partial>lborel) = ereal 1 / 2" by auto

  show "(\<integral>\<^sup>+x. ereal (x * exp (- x\<^sup>2)) * indicator {0..} x \<partial>lborel) = ereal 1 / 2" using 1 by auto
qed

lemma borel_integral_x_times_standard_normal[intro]: "(\<integral>x. standard_normal_density x * x \<partial>lborel) = 0" 
  and borel_integrable_x_times_standard_normal[intro]: "integrable lborel (\<lambda>x. standard_normal_density x * x)"
  and borel_integral_x_times_standard_normal'[intro]: "(\<integral>x. x * standard_normal_density x \<partial>lborel) = 0" 
  and borel_integrable_x_times_standard_normal'[intro]: "integrable lborel (\<lambda>x. x * standard_normal_density x)"
proof -    
  have 0: "(\<integral>\<^sup>+x. ereal (x * standard_normal_density x) \<partial>lborel) = \<integral>\<^sup>+x. ereal (x * standard_normal_density x) * indicator {0..} x \<partial>lborel"
    apply(subst positive_integral_max_0[symmetric]) 
    unfolding max_def standard_normal_density_def
    apply(auto intro!: positive_integral_cong split:split_indicator 
      simp: mult_nonneg_nonneg divide_nonneg_nonneg zero_le_divide_iff zero_le_mult_iff)
    by (metis not_le pi_gt_zero)

  have 1: "(\<integral>\<^sup>+x. ereal (- (x * standard_normal_density x)) \<partial>lborel) = \<integral>\<^sup>+x. ereal (x * standard_normal_density x) * indicator {0..} x \<partial>lborel"
    apply (subst(2) positive_integral_real_affine[where c = "-1" and t = 0])
    apply(auto simp: standard_normal_density_def split:split_indicator simp: mult_nonneg_nonneg divide_nonneg_nonneg)
    apply(subst positive_integral_max_0[symmetric]) 
    unfolding max_def standard_normal_density_def
    by(auto intro!: positive_integral_cong split:split_indicator 
      simp: mult_nonneg_nonneg divide_nonneg_nonneg divide_le_0_iff mult_le_0_iff)
     (metis not_le pi_gt_zero)
  
  have 2: "sqrt pi / sqrt 2 * (\<integral>\<^sup>+x. ereal (x * standard_normal_density x) * indicator {0..} x \<partial>lborel) = integral\<^sup>P lborel (\<lambda>x. ereal (x * exp (- x\<^sup>2)))"
    unfolding standard_normal_density_def
    apply (subst positive_integral_real_affine[where c = "sqrt 2" and t = 0])
    apply (auto simp: mult_nonneg_nonneg divide_nonneg_nonneg power_mult_distrib split: split_indicator)
    apply (subst mult_assoc[symmetric])
    apply (subst positive_integral_cmult[symmetric])
    apply (auto simp: mult_nonneg_nonneg)
    apply (subst(2) positive_integral_max_0[symmetric])
    unfolding max_def 
    by (auto intro!: positive_integral_cong split:split_indicator simp:mult_nonneg_nonneg zero_le_mult_iff real_sqrt_mult)

  have *: "(\<integral>\<^sup>+x. ereal (x * standard_normal_density x) * indicator {0..} x \<partial>lborel) = sqrt 2 / sqrt pi *(integral\<^sup>P lborel (\<lambda>x. ereal (x * exp (- x\<^sup>2))))"
    apply (subst 2[symmetric])
    apply (subst mult_assoc[symmetric])
    by (auto simp: field_simps)
    
  show "(\<integral> x. x * standard_normal_density x \<partial>lborel) = 0" "integrable lborel (\<lambda>x. x * standard_normal_density x)"
   unfolding lebesgue_integral_def integrable_def
   by (auto simp: 0 1 * positive_integral_x_exp_x_square)

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
  have D1: "distributed M lborel (\<lambda>x. (X x - \<mu>) / \<sigma>) standard_normal_density"
    by (simp add: normal_standard_normal_convert[OF pos_var, of X \<mu>, symmetric] D)

  have "expectation X = expectation (\<lambda>x. \<mu> + \<sigma> * (\<lambda>x. (X x - \<mu>) / \<sigma>) x)" by simp
  also have "... = \<mu> + \<sigma>*(expectation (\<lambda>x. (X x - \<mu>) / \<sigma>))"
    by(subst expectation_affine[OF D1]) (auto simp: prob_space_normal_density)    
  also have "... = \<mu>"
    by (auto simp: standard_normal_distributed_expectation[OF D1])  
  finally show ?thesis .
qed

lemma integral_xsquare_exp_xsquare: "(\<integral> x. (x\<^sup>2 * exp (-x\<^sup>2 )) \<partial>lborel) =  sqrt pi / 2"
  and integrable_xsquare_exp_xsquare: "integrable lborel (\<lambda>x. x\<^sup>2 * exp (- x\<^sup>2))"
proof- 
  note mult_nonneg_nonneg[simp]
  note filterlim_compose[OF exp_at_top, intro] filterlim_ident[intro]

  let ?f = "(\<lambda>x. x * - exp (- x\<^sup>2) / 2 - 0 * - exp (- 0\<^sup>2) / 2 -
                 \<integral> xa. 1 * (- exp (- xa\<^sup>2) / 2) * indicator {0..x} xa \<partial>lborel)"
  let ?IFunc = "(\<lambda>z. \<integral>x. (x\<^sup>2 * exp (- x\<^sup>2)) * indicator {0 .. z} x \<partial>lborel)"

  have 1: "(\<integral>\<^sup>+xa. ereal (exp (- xa\<^sup>2)) * indicator {0..} xa \<partial>lborel) = ereal (sqrt pi) / ereal 2"
    apply (subst positive_integral_ereal_indicator_mult)
    apply (subst gaussian_integral_positive[symmetric])
    apply (subst(2) positive_integral_even_function) 
    apply (auto simp: field_simps)
    by (cases "\<integral>\<^sup>+x. ereal (indicator {0..} x * exp (- x\<^sup>2)) \<partial>lborel") auto

  have I: "(\<integral>xa. exp (- xa\<^sup>2) * indicator {0..} xa \<partial>lborel) = sqrt pi / 2"
    apply (rule lebesgue_integral_eq_positive_integral)
    apply (subst positive_integral_ereal_indicator_mult[symmetric])
    apply (subst 1)
    by (auto split:split_indicator)
  
  have byparts: "?IFunc = (\<lambda>z. (if z < 0 then 0 else ?f z))"
    proof (intro HOL.ext, subst split_ifs, safe)
      fix z::real assume [arith]:" \<not> z < 0 "
  
      have "?IFunc z =  \<integral>x. (x * (x * exp (- x\<^sup>2))) * indicator {0 .. z} x \<partial>lborel"
        by(auto intro!: integral_cong split: split_indicator simp: power2_eq_square)
  
      also have "... = (\<lambda>x. x) z * (\<lambda>x. - exp (- x\<^sup>2 ) / 2) z - (\<lambda>x. x) 0 * (\<lambda>x. - exp (- x\<^sup>2) / 2) 0 
          -  \<integral>x. 1 * ( - exp (- x\<^sup>2) / 2) * indicator {0 .. z} x \<partial>lborel"
        by(rule integral_by_parts, auto intro!: DERIV_intros)  
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
      apply (auto intro!: DERIV_intros eventually_elim1[OF eventually_gt_at_top, of 1])
      apply (subst inverse_eq_divide[symmetric])
      apply (rule  tendsto_inverse_0_at_top)
      apply (subst mult_assoc)
      by (auto intro!: filterlim_tendsto_pos_mult_at_top[of "\<lambda>x. 2" 2] filterlim_at_top_mult_at_top[OF filterlim_ident])
    
    then show ?thesis by simp
  qed

  have [intro]: "((\<lambda>x. \<integral>y. exp (- y\<^sup>2) * indicator {0..x} y \<partial>lborel) ---> \<integral>y. exp (- y\<^sup>2) * indicator {0..} y \<partial>lborel) at_top"
    by(auto intro!: tendsto_mult_indicator)

  have tends: "((\<lambda>x. (\<integral> xa. exp (- xa\<^sup>2) * indicator {0..x} xa \<partial>lborel) / 2) ---> (sqrt pi / 2) / 2) at_top"
    apply (rule tendsto_divide)
    by (subst I[symmetric]) auto

  have [intro]: "(?IFunc ---> sqrt pi / 4) at_top"
    apply (simp add: byparts)
    apply (subst filterlim_cong[where g = ?f])
    apply (auto simp: eventually_ge_at_top linorder_not_less lebesgue_integral_uminus)
  proof -
    have "((\<lambda>x. (\<integral> xa. exp (- xa\<^sup>2) * indicator {0..x} xa / 2 \<partial>lborel) - x * exp (- x\<^sup>2) / 2) --->
        (0 + sqrt pi / 4 - 0)) at_top"
      apply (intro tendsto_diff)
      apply auto
      apply (subst divide_real_def)
      apply (subst integral_multc)
      using tends
      by (auto intro!: integrable_mult_indicator integral_multc)

    then show "((\<lambda>x. (\<integral> xa. exp (- xa\<^sup>2) * indicator {0..x} xa / 2 \<partial>lborel) - (x * exp (- x\<^sup>2) / 2)) --->
       sqrt pi / 4) at_top" by  simp
  qed
    
  have [intro]:"\<And>y. integrable lborel (\<lambda>x. x\<^sup>2 * exp (- x\<^sup>2) * indicator {0..} x * indicator {..y} x)"
    apply (subst integrable_cong[where g = "\<lambda>x. x\<^sup>2 * exp (- x\<^sup>2) * indicator {0..y} x"])
    by (auto intro!: borel_integrable_atLeastAtMost split:split_indicator)
    
  have **[intro]: "integrable lborel (\<lambda>x. x\<^sup>2 * exp (- x\<^sup>2) * indicator {0..} x)"
    by (rule integral_monotone_convergence_at_top) auto

  have "(\<integral>x. x\<^sup>2 * exp (- x\<^sup>2) * indicator {0..} x \<partial>lborel) = sqrt pi / 4"
    by (rule integral_monotone_convergence_at_top) auto
  
  then have "(\<integral>\<^sup>+x. ereal (x\<^sup>2 * exp (- x\<^sup>2)* indicator {0..} x) \<partial>lborel) = sqrt pi / 4"
    by (subst positive_integral_eq_integral) auto

  then have ***: "(\<integral>\<^sup>+ x.  ereal (x\<^sup>2 * exp (- x\<^sup>2)) \<partial>lborel) = sqrt pi / 2"
    by (auto simp: real_sqrt_mult real_sqrt_divide positive_integral_even_function)
  
  show "(\<integral> x. x\<^sup>2 * exp (- x\<^sup>2) \<partial>lborel) = sqrt pi / 2" "integrable lborel (\<lambda>x. x\<^sup>2 * exp (- x\<^sup>2))"
    by (auto simp: lebesgue_integral_eq_positive_integral[OF ***] integrable_if_positive_integral[OF ***])
qed

lemma integral_xsquare_times_standard_normal[intro]: "(\<integral> x. standard_normal_density x * x\<^sup>2 \<partial>lborel) = 1"
  and integrable_xsquare_times_standard_normal[intro]: "integrable lborel (\<lambda>x. standard_normal_density x * x\<^sup>2)"
proof -
  have [intro]:"integrable lborel (\<lambda>x. exp (- x\<^sup>2) * (2 * x\<^sup>2) / (sqrt 2 * sqrt pi))"
    apply (subst integrable_cong[where g ="(\<lambda>x. (2 * inverse (sqrt 2 * sqrt pi)) * (exp (- x\<^sup>2) * x\<^sup>2))"])
    by (auto intro!: integral_cmult(1) integrable_xsquare_exp_xsquare simp: field_simps)

  have "(\<integral> x. standard_normal_density x * x\<^sup>2 \<partial>lborel) = (2 / sqrt pi) * \<integral> x. x\<^sup>2 * exp (- x\<^sup>2) \<partial>lborel"
    apply (subst integral_cmult(2)[symmetric])
    apply (rule integrable_xsquare_exp_xsquare)
    unfolding standard_normal_density_def
    apply (subst lebesgue_integral_real_affine[where c = "sqrt 2" and t=0], simp_all)
    apply (subst integral_cmult(2)[symmetric])
    by (auto intro!: integral_cong simp: power_mult_distrib real_sqrt_mult)
  also have "... = 1"
    by (subst integral_xsquare_exp_xsquare, auto)
  finally show "(\<integral> x. standard_normal_density x * x\<^sup>2 \<partial>lborel) = 1" .

  show "integrable lborel (\<lambda>x. standard_normal_density x * x\<^sup>2)"
    unfolding standard_normal_density_def
    apply (subst integrable_affine[where c = "sqrt 2" and t=0])
    by (auto simp: power_mult_distrib real_sqrt_mult)
qed

lemma 
  assumes [arith]: "0 < \<sigma>"
  shows integral_xsquare_times_normal: "(\<integral> x. normal_density \<mu> \<sigma> x * (x - \<mu>)\<^sup>2 \<partial>lborel) = \<sigma>\<^sup>2"
  and integrable_xsquare_times_normal: "integrable lborel (\<lambda>x. normal_density \<mu> \<sigma> x * (x - \<mu>)\<^sup>2)"
proof -
  have "(\<integral> x. normal_density \<mu> \<sigma> x * (x - \<mu>)\<^sup>2 \<partial>lborel) = \<sigma> * \<sigma> * \<integral> x. standard_normal_density x * x\<^sup>2 \<partial>lborel"
    unfolding normal_density_def
    apply (subst lebesgue_integral_real_affine[ where c = \<sigma> and t = \<mu>])
    apply (auto simp: power_mult_distrib)
    apply (subst integral_cmult(2)[symmetric])
    apply (auto intro!: integral_cong)
    apply (subst integrable_cong[where g = "(\<lambda>x. standard_normal_density x * x\<^sup>2)"], auto)
    unfolding normal_density_def
    by (auto simp: real_sqrt_mult field_simps power2_eq_square[symmetric])
    
  also have "... = \<sigma>\<^sup>2" 
    by(auto simp: power2_eq_square[symmetric])

  finally show "(\<integral> x. normal_density \<mu> \<sigma> x * (x - \<mu>)\<^sup>2 \<partial>lborel) = \<sigma>\<^sup>2" .
 
  show "integrable lborel (\<lambda>x. normal_density \<mu> \<sigma> x * (x - \<mu>)\<^sup>2)"
    unfolding normal_density_def
    apply (subst integrable_affine[ where c = \<sigma> and t = \<mu>], auto)
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
    by (auto intro!: standard_normal_distributed_variance prob_space_normal_density
      simp: distributed_integrable[OF *,of "\<lambda>x. x", symmetric]
      distributed_integrable[OF *,of "\<lambda>x. x\<^sup>2", symmetric] variance_affine)    
  
  finally show ?thesis by simp
qed

lemma (in information_space) entropy_normal_density:
  assumes [arith]: "0 < \<sigma>"
  assumes D: "distributed M lborel X (normal_density \<mu> \<sigma>)"
  shows "entropy b lborel X =  log b (2 * pi * exp 1 * \<sigma>\<^sup>2) / 2"
proof (subst entropy_distr[OF D])
(* have to use lebesgue integral here, wanted to use positive integral but this function is not positive for all x>0 *)
(* can not convert to standard normal density as it resutls in goal integrable lborel \<lambda>x. standard_normal_density x * log b _ ,
or something of this form after applying integral_cmult after lebesgue_integral_real_affine*)
  let ?I = "- (\<integral> x. normal_density \<mu> \<sigma> x * log b (normal_density \<mu> \<sigma> x) \<partial>lborel)"
  note integrable_xsquare_times_normal[OF assms(1), intro] times_divide_eq_left[simp del] divide_pos_pos[simp, intro] mult_pos_pos[simp, intro] 
        integrable_normal[OF assms(1), intro] 
 
  have 1: "\<And>x. log b (normal_density \<mu> \<sigma> x) = (- ln (2 * pi * \<sigma>\<^sup>2) - (x - \<mu>)\<^sup>2 / \<sigma>\<^sup>2) / (2 * ln b)"
    unfolding normal_density_def
    by(auto simp: ln_mult add_divide_distrib diff_divide_distrib log_def ln_div ln_sqrt)    

  have "?I = (ln (sqrt (2 * pi * \<sigma>\<^sup>2)) / ln b ) * (\<integral> x. normal_density \<mu> \<sigma> x \<partial>lborel)
       + (1 / (\<sigma>\<^sup>2 * (2 * ln b))) * \<integral> x. normal_density \<mu> \<sigma> x * (x - \<mu>)\<^sup>2 \<partial>lborel"
    apply (subst lebesgue_integral_uminus[symmetric])
    apply (subst integral_cmult(2)[symmetric], auto)+
    apply (subst integral_add(2)[symmetric])    
    apply (auto intro!: integral_cong simp: 1)
    by (auto simp: field_simps ln_sqrt minus_divide_left add_divide_distrib)

  also have "... = log b (2 * pi * exp 1 * \<sigma>\<^sup>2) / 2"
    apply (subst integral_xsquare_times_normal[OF assms(1)])
    apply (subst integral_normal_density)
    apply (auto simp: field_simps log_def ln_sqrt ln_mult)
    by (auto simp: add_divide_distrib)

  finally show "?I = log b (2 * pi * exp 1 * \<sigma>\<^sup>2) / 2" .
qed
end
