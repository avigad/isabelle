(* Exponential and Erlang distribution
   Author: Sudeep Kanav
   Author: Johannes Hölzl *)

theory Exponential_Erlang_Distribution
  imports Auxiliary Convolution
begin

subsection {* Exponential *}

lemma exponential_density_nonneg: "0 < l \<Longrightarrow> 0 \<le> exponential_density l x"
  by (auto simp:mult_nonneg_nonneg exponential_density_def)

lemma (in prob_space) exponential_distributed_min:
  assumes expX: "distributed M lborel X (exponential_density l)"
  assumes expY: "distributed M lborel Y (exponential_density u)"
  assumes ind: "indep_var borel X borel Y"
  shows "distributed M lborel (\<lambda>x. min (X x) (Y x)) (exponential_density (l + u))"
proof (subst exponential_distributed_iff, safe)
  have randX: "random_variable borel X" using expX by (simp add: exponential_distributed_iff)
  moreover have randY: "random_variable borel Y" using expY by (simp add: exponential_distributed_iff)
  ultimately show "random_variable borel (\<lambda>x. min (X x) (Y x))" by auto
  
  have "0 < l" by (rule exponential_distributed_params) fact
  moreover have "0 < u" by (rule exponential_distributed_params) fact
  ultimately  show " 0 < l + u" by force

  fix a::real assume a[arith]: "0 \<le> a"
  have gt1[simp]: "\<P>(x in M. a < X x ) = exp (- a * l)" by (rule exponential_distributedD_gt[OF expX a]) 
  have gt2[simp]: "\<P>(x in M. a < Y x ) = exp (- a * u)" by (rule exponential_distributedD_gt[OF expY a]) 

  have "\<P>(x in M. a < (min (X x) (Y x)) ) =  \<P>(x in M. a < (X x) \<and> a < (Y x))" by (auto intro!:arg_cong[where f=prob])

  also have " ... =  \<P>(x in M. a < (X x)) *  \<P>(x in M. a< (Y x) )"
    using prob_indep_random_variable[OF ind, of "{a <..}" "{a <..}"] by simp
  also have " ... = exp (- a * (l + u))" by (auto simp:field_simps mult_exp_exp)
  finally have indep_prob: "\<P>(x in M. a < (min (X x) (Y x)) ) = exp (- a * (l + u))" .

  have "{x \<in> space M. (min (X x) (Y x)) \<le>a } = (space M - {x \<in> space M. a<(min (X x) (Y x)) })"
    by auto
  then have "1 - prob {x \<in> space M. a < (min (X x) (Y x))} = prob {x \<in> space M. (min (X x) (Y x)) \<le> a}"
    using randX randY by (auto simp: prob_compl) 
  then show "prob {x \<in> space M. (min (X x) (Y x)) \<le> a} = 1 - exp (- a * (l + u))"
    using indep_prob by auto
qed
 
lemma (in prob_space) exponential_distributed_min_nvar:
  assumes finI: "finite I"
  assumes A: "I \<noteq> {}"
  assumes expX: "\<And>i. i \<in> I \<Longrightarrow> distributed M lborel (X i) (exponential_density (l i))"
  assumes ind: "indep_vars (\<lambda>i. borel) X I" 
  shows "distributed M lborel (\<lambda>x. Min {X i x| i. i \<in> I}) (exponential_density (\<Sum>i\<in>I. l i))"
using assms
proof (induct rule: finite_ne_induct)
  case (singleton i) then show ?case by simp
next
  case (insert i I)
  then have "distributed M lborel (\<lambda>x. min (X i x) (Min {X i x| i. i \<in> I})) (exponential_density (l i + (\<Sum>i\<in>I. l i)))"
      by (intro exponential_distributed_min indep_vars_Min insert)
       (auto intro: indep_vars_subset) 
  also have "(\<lambda>x. min (X i x) (Min {X i x| i. i \<in> I})) = (\<lambda>x. Min {X j x| j. j \<in> insert i I})"
    using insert by (subst random_vars_insert) simp
  finally show ?case
    using insert by simp
qed

subsection {* Erlang *}

definition erlang_density :: "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "erlang_density k l x = (if x < 0 then 0 else (l^(Suc k) * x^k * exp (- l * x)) / fact k)"

definition erlang_CDF ::  "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "erlang_CDF k l x = 1 - (\<Sum>n = 0..k. ((l * x)^n * exp (- l * x) / fact n))"

lemma borel_measurable_erlang_density[measurable]: "erlang_density k l \<in> borel_measurable borel"
  by (auto simp add: erlang_density_def[abs_def])

lemma integral_for_erlang:
  fixes k::nat
  shows "(\<integral>\<^sup>+ x. ereal (x ^ k * exp (-x)) * indicator {0..} x \<partial>lborel) = fact k"
  and "0 \<le> a \<Longrightarrow> (\<integral>\<^sup>+ x. ereal (x ^ k * exp (-x)) * indicator {0..a} x \<partial>lborel) = 
      ereal ((\<lambda>x. -((\<Sum>n= 0..k. (x^n * exp(- x))/fact n))) a + 1) * fact k"
proof -
  note fact_Suc[simp del] power_Suc[simp del]
  let ?f = "\<lambda>x. x^k * exp( -x) / fact k"
  let ?F = "\<lambda>x. - ((\<Sum>n= 0..k. (x^n * exp(- x))/fact n))"

  have  deriv:"\<And>x. DERIV ?F x :> ?f x"
  proof(induction k)
    case 0 show ?case by (auto intro!:DERIV_intros)
  next
    case (Suc m)
    have *: " DERIV (\<lambda>x. x ^ Suc m * exp (- x) / real (fact (Suc m))) x :>
         (((Suc m)* x^m * exp(- x) - x ^ Suc m * exp (- x) )/fact (Suc m))"
      by (intro DERIV_intros, auto)
    show ?case
      apply auto
      apply (rule DERIV_intros)
      apply (rule Suc.IH)
      apply (rule *)
      apply (auto simp: field_simps)
      by (metis Fact.fact_Suc mult_commute real_of_nat_mult)+
  qed

  have L: "(?F ---> 0) at_top" 
    apply(subst tendsto_minus_cancel_left[symmetric])
    apply (induction k)
    apply(auto simp: filterlim_uminus_at_bot_at_top filterlim_compose[OF exp_at_bot])
    apply(rule tendsto_add_zero)
    proof -
      fix p
      have " ((\<lambda>x. (x ^ (Suc p) * exp (- x) / (real (fact (Suc p))))) ---> (0/ (real (fact (Suc p))))) at_top"
        apply (intro tendsto_intros)
        apply (rule filterlim_compose[of "\<lambda>x. x ^ (Suc p) * exp (- x)" "nhds 0" "at_top" "\<lambda>x. x" "at_top"])
        apply (simp add:exp_minus inverse_eq_divide)
        by (auto intro!: tendsto_power_div_exp_0 filterlim_ident simp: inverse_eq_divide)
      then  show "((\<lambda>x. x ^ Suc p * exp (- x) / real (fact (Suc p))) ---> 0) at_top" by simp
    qed simp

  have F0: "- (?F 0) = 1" by (induction k, auto)

  have "(\<integral>\<^sup>+ x. ereal (x^k * exp (-x)/ real (fact k)) * indicator {0..} x \<partial>lborel) = ereal (0 - ?F 0)"
    apply (rule positive_integral_FTC_atLeast)
    using L deriv by (auto simp: field_simps mult_nonneg_nonneg)
  then have I: "(\<integral>\<^sup>+ x. ereal (x^k * exp (-x)/ real (fact k)) * indicator {0..} x \<partial>lborel) = ereal 1" 
    using F0 by (simp add: one_ereal_def)
  show "(\<integral>\<^sup>+ x. ereal (x^k * exp (-x)) * indicator {0..} x \<partial>lborel) = fact k"
    apply (subst ereal_mult1_right[of "fact k", symmetric])
    by (auto intro!: positive_integral_cong split: split_indicator simp: positive_integral_cmult[symmetric] I[symmetric])
     
  assume "0 \<le> a"
  have "(\<integral>\<^sup>+x. ereal (?f x) * indicator {0..a} x \<partial>lborel) = ereal (?F a) - ereal (?F 0)"
    using `0 \<le> a` deriv
    apply (intro positive_integral_FTC_atLeastAtMost)
    by (auto simp:field_simps mult_nonneg_nonneg)
  also have "... = ereal (?F a + 1)" using F0 by auto
  finally have **: "(\<integral>\<^sup>+x. ereal (?f x) * indicator {0..a} x \<partial>lborel) = ereal (?F a + 1)" .
    
  show "(\<integral>\<^sup>+ x. ereal (x ^ k * exp (- x)) * indicator {0..a} x \<partial>lborel) = ereal (?F a + 1) * ereal (real (fact k))"
    apply (subst **[symmetric])
    by (auto intro!: positive_integral_cong split: split_indicator simp: positive_integral_multc[symmetric])
qed

lemma
  assumes l_bd[arith]: "0 < l"
  shows emeasure_erlang_density_ge0: "0 \<le> a \<Longrightarrow> emeasure (density lborel (erlang_density k l)) {.. a} 
      = erlang_CDF k l a"
    and prob_space_erlang_density: "prob_space (density lborel (erlang_density k l))"
      (is "prob_space ?D")
proof -
  let ?f = "\<lambda>x. l^(Suc k) * x^k * exp( -l*x) /fact k  "
  let ?F = "\<lambda>x. - (\<Sum>n= 0..k. ((l* x)^n * exp( -l*x) /fact n ))"

  have "emeasure ?D (space ?D) = (\<integral>\<^sup>+ x. ereal (?f x) * indicator {0..} x \<partial>lborel)"
    apply (auto simp: emeasure_density erlang_density_def split: split_indicator)
    apply (intro positive_integral_cong)
    by(auto split: split_indicator)
  also have "... = (1 / real (fact k)) * \<integral>\<^sup>+ x. ereal (x ^ k * exp (-x)) * indicator {0..} x \<partial>lborel"
    apply (subst(2) positive_integral_real_affine[where t = 0 and c = "l"])
    by (auto intro!: positive_integral_cong split: split_indicator
      simp: zero_le_mult_iff zero_le_divide_iff positive_integral_cmult[symmetric] power_mult_distrib)
  also have "... = 1" by (auto simp: one_ereal_def integral_for_erlang)
  finally show "prob_space ?D" by rule

  assume [arith]: "0 \<le> a"
  have "emeasure ?D {..a} = (\<integral>\<^sup>+x. ereal (?f x) * indicator {0..a} x \<partial>lborel)"
    by (auto simp: emeasure_density erlang_density_def intro!: positive_integral_cong split:split_indicator)
  also have "(\<integral>\<^sup>+x. ereal (?f x) * indicator {0..a} x \<partial>lborel) = 
    (1 / real (fact k)) * \<integral>\<^sup>+ x. ereal (x ^ k * exp (-x)) * indicator {0..(l * a)} x \<partial>lborel"
    apply (subst(2) positive_integral_real_affine[where t = 0 and c = "l"])
    by (auto intro!: positive_integral_cong split: split_indicator
      simp: zero_le_mult_iff zero_le_divide_iff positive_integral_cmult[symmetric] power_mult_distrib)
  also have "... = ereal ( 1 + ?F a)" by (auto simp: mult_nonneg_nonneg integral_for_erlang)
  finally show " emeasure ?D {.. a} = erlang_CDF k l a" 
    unfolding erlang_CDF_def by simp  
qed

lemma (in prob_space) erlang_distributed_le:
  assumes D: "distributed M lborel X (erlang_density k l)"
  assumes [simp, arith]: "0 < l" "0 \<le> a"
  shows "\<P>(x in M. X x \<le> a) = erlang_CDF k l a"
proof -
  have "emeasure M {x \<in> space M. X x \<le> a } = emeasure (distr M lborel X) {.. a}"
    using distributed_measurable[OF D]
    by (subst emeasure_distr) (auto intro!: arg_cong2[where f=emeasure])
  also have "\<dots> = emeasure (density lborel (erlang_density k l)) {.. a}"
    unfolding distributed_distr_eq_density[OF D] ..
  also have "\<dots> = erlang_CDF k l a"
    by (auto intro!: emeasure_erlang_density_ge0)
  finally show ?thesis
    by (auto simp: measure_def)
qed

lemma (in prob_space) erlang_distributed_gt:
  assumes D[simp]: "distributed M lborel X (erlang_density k l)"
  assumes [arith]: "0 < l" "0 \<le> a"
  shows "\<P>(x in M. a < X x ) = 1 - (erlang_CDF k l a)"
proof -
  have " 1 - (erlang_CDF k l a) = 1 - \<P>(x in M. X x \<le> a)" by (subst erlang_distributed_le) auto
  also have "\<dots> = prob (space M - {x \<in> space M. X x \<le> a })"
    using distributed_measurable[OF D] by (auto simp: prob_compl)
  also have "\<dots> = \<P>(x in M. a < X x )" by (auto intro!: arg_cong[where f=prob] simp: not_le)
  finally show ?thesis by simp
qed

lemma erlang_CDF_at0: "erlang_CDF k l 0 = 0"
  by (induction k) (auto simp: erlang_CDF_def)

lemma erlang_distributedI:
  assumes X[measurable]: "X \<in> borel_measurable M" and [arith]: "0 < l"
    and X_distr: "\<And>a. 0 \<le> a \<Longrightarrow> emeasure M {x\<in>space M. X x \<le> a} = erlang_CDF k l a"
  shows "distributed M lborel X (erlang_density k l)"
proof (rule distributedI_borel_atMost)
  fix a :: real
  { assume "a \<le> 0"  
    with X have "emeasure M {x\<in>space M. X x \<le> a} \<le> emeasure M {x\<in>space M. X x \<le> 0}"
      by (intro emeasure_mono) auto
    also have "... = 0"  by (auto intro!: erlang_CDF_at0 simp: X_distr[of 0])
    finally have "emeasure M {x\<in>space M. X x \<le> a} \<le>0" by simp
    then have "emeasure M {x\<in>space M. X x \<le> a} = 0" by (simp add:emeasure_le_0_iff)
  }
  note eq_0 = this

  have "\<And>x. \<not> 0 \<le> a \<Longrightarrow> ereal (erlang_density k l x) * indicator {..a} x = 0"
    by (simp add: erlang_density_def)
  then show "(\<integral>\<^sup>+ x. erlang_density k l x * indicator {..a} x \<partial>lborel) = ereal (if 0 \<le> a then (erlang_CDF k l a) else 0)"
    using emeasure_erlang_density_ge0[of l a]
    by (auto simp: emeasure_density times_ereal.simps[symmetric] ereal_indicator
             simp del: times_ereal.simps ereal_zero_times)
  show "emeasure M {x\<in>space M. X x \<le> a} = ereal (if 0 \<le> a then (erlang_CDF k l a) else 0)"
    using X_distr[of a] eq_0 by (auto simp: one_ereal_def)
  show "AE x in lborel. 0 \<le> erlang_density k l x "
    by (auto simp: erlang_density_def mult_nonneg_nonneg field_simps)
qed simp_all

lemma (in prob_space) erlang_distributed_iff:
  assumes [arith]: "0<l"
  shows "distributed M lborel X (erlang_density k l) \<longleftrightarrow>
    (X \<in> borel_measurable M \<and> 0 < l \<and>  (\<forall>a\<ge>0. \<P>(x in M. X x \<le> a) =  erlang_CDF k l a ))"
  using
    distributed_measurable[of M lborel X "erlang_density k l"]
    emeasure_erlang_density_ge0[of l]
    erlang_distributed_le[of X k l]
  by (auto intro!: erlang_distributedI simp: one_ereal_def emeasure_eq_measure) 

lemma erlang_density_nonneg[simp, intro]:
  assumes [arith]: "0 < l"
  shows "\<And>x. 0 \<le> erlang_density k l x"
  unfolding erlang_density_def
  by (auto simp: mult_nonneg_nonneg divide_nonneg_nonneg)

lemma (in prob_space) erlang_distributed_mult_const:
  assumes erlX: "distributed M lborel X (erlang_density k l)"
  assumes a_pos[arith]: "0< \<alpha>"  "0<l"
  shows  "distributed M lborel (\<lambda>x. \<alpha> * X x) (erlang_density k (l / \<alpha>))"
proof (subst erlang_distributed_iff, safe)
  have [measurable]: "random_variable borel X"  and  [arith]: "0 < l " 
  and  [simp]: "\<And>a. 0 \<le> a \<Longrightarrow> prob {x \<in> space M. X x \<le> a} = erlang_CDF k l a"
    by(insert erlX, auto simp: erlang_distributed_iff)

  show "random_variable borel (\<lambda>x. \<alpha> * X x)" "0 < l / \<alpha>"  "0 < l / \<alpha>" 
    by (auto simp:field_simps)
  
  fix a:: real assume [arith]: "0 \<le> a"
  obtain b:: real  where [simp, arith]: "b = a/ \<alpha>" by blast 

  have [arith]: "0 \<le> b" by (auto simp: divide_nonneg_pos)
 
  have "prob {x \<in> space M. \<alpha> * X x \<le> a}  = prob {x \<in> space M.  X x \<le> b}"
    by (rule arg_cong[where f= prob]) (auto simp:field_simps)
  
  moreover have " prob {x \<in> space M. X x \<le> b} = erlang_CDF k l b" by auto
  moreover have "erlang_CDF k (l / \<alpha>) a = erlang_CDF k l b" unfolding erlang_CDF_def by auto
  ultimately show "prob {x \<in> space M. \<alpha> * X x \<le> a} = erlang_CDF k (l / \<alpha>) a" by fastforce  
qed

lemma (in prob_space)
  fixes i :: nat
  assumes [arith]: "0 < l" 
  assumes D: "distributed M lborel X (erlang_density k l)"
  shows erlang_ith_moment: "(\<integral>\<^sup>+ x. ereal (erlang_density k l x * x ^ i) \<partial>lborel) = ereal ((1 / l ^ i) * (fact (k + i) / fact k))"
   and erlang_ith_moment_integrable: "integrable M (\<lambda>x. (X x) ^ i)"
proof -  
  note mult_nonneg_nonneg[simp]
  have "(\<integral>\<^sup>+x. erlang_density k l x * x ^ i \<partial>lborel) =
     (1 / (l ^ i * fact k)) * \<integral>\<^sup>+x. ereal (x ^ (k + i) * exp (- x)) * indicator {0..} x \<partial>lborel"
    apply (subst(2) positive_integral_real_affine[where t=0 and c = l])
    by  (auto intro!: positive_integral_cong split: split_indicator simp: zero_le_mult_iff 
        power_mult_distrib positive_integral_cmult[symmetric] power_add erlang_density_def)
  also have "... = (1 / (l ^ i * fact k)) * (fact (k + i))"
    by (subst integral_for_erlang, auto)
  finally show *: "(\<integral>\<^sup>+ x. ereal (erlang_density k l x * x ^ i) \<partial>lborel) = 
      ereal (1 / l ^ i * (real (fact (k + i)) / real (fact (int k))))"
    by (auto simp: transfer_int_nat_factorial)

  show "integrable M (\<lambda>x. X x ^ i)"
    apply (subst distributed_integrable[OF D, of "(\<lambda>x. x ^ i)", symmetric])
    apply (auto intro!: integrable_if_positive_integral *)
    unfolding erlang_density_def
    by (auto simp:divide_nonneg_nonneg) 
qed

lemma (in prob_space) erlang_distributed_expectation:
  assumes [arith]: "0 < l" 
  assumes D: "distributed M lborel X (erlang_density k l)"
  shows "expectation X = (k + 1) / l"
  apply (subst distributed_integral[OF D, of "\<lambda>x. x", symmetric], simp)
  apply (auto intro!: lebesgue_integral_eq_positive_integral)
  apply (subst(8) power_one_right[symmetric])
  apply (subst erlang_ith_moment[OF assms, of 1])
  unfolding erlang_density_def
  by (auto simp:field_simps transfer_int_nat_factorial mult_nonneg_nonneg divide_nonneg_nonneg)

lemma (in prob_space) erlang_distributed_variance:
  assumes [arith]: "0 < l" 
  assumes D: "distributed M lborel X (erlang_density k l)"
  shows "variance X = (k + 1) / l\<^sup>2"
proof(subst variance_eq)
  have *: "fact (k + 2) = (k + 2) * (k + 1)* fact k"
    by (subgoal_tac "k + 2 = (k + 1) + 1") (auto simp:field_simps)

  have **: "expectation (\<lambda>x. (X x)\<^sup>2) = int (k + 1) * (k + 2) / l\<^sup>2"
    apply (subst distributed_integral[OF D, of "\<lambda>x. x\<^sup>2", symmetric], simp)
    apply (auto intro!: lebesgue_integral_eq_positive_integral simp: erlang_ith_moment[OF assms, of 2])  
    unfolding erlang_density_def
    by (auto simp:field_simps transfer_int_nat_factorial mult_nonneg_nonneg divide_nonneg_nonneg) 
  
  show "expectation (\<lambda>x. (X x)\<^sup>2) - (expectation X)\<^sup>2 = (real k + 1) / l\<^sup>2"
    by (auto simp: ** erlang_distributed_expectation[OF assms])
      (auto simp:  field_simps power2_eq_square) 

  show "integrable M X"
    apply (subst integrable_cong[where g ="(\<lambda>x. X x ^ 1)"], simp)
    by (rule erlang_ith_moment_integrable[OF assms,of 1] )
  
  show "integrable M (\<lambda>x. (X x)\<^sup>2)"
    apply (subst integrable_cong[where g ="(\<lambda>x. X x ^ 2)"], simp)
    by (rule erlang_ith_moment_integrable[OF assms,of 2])
qed

lemma (in prob_space)
  fixes k :: nat
  assumes D: "distributed M lborel X (exponential_density l)"
  shows exponential_kth_moment: "(\<integral>\<^sup>+ x. ereal (exponential_density l x * x ^ k) \<partial>lborel) = ereal (real (fact k) / l ^ k)"
   and exponential_kth_moment_integrable: "integrable M (\<lambda>x. (X x) ^ k)"
proof -
  have [arith]: "0 < l" by (rule exponential_distributed_params[OF D])
  have "(\<integral>\<^sup>+ x. exponential_density l x * x ^ k \<partial>lborel) = (1 / l ^ k) * \<integral>\<^sup>+ x. ereal (x ^ k * exp (- x)) * indicator{0..} x \<partial>lborel"
  apply(subst positive_integral_real_affine[where c = "1 / l" and t = 0])
  unfolding exponential_density_def
  by (auto intro!: positive_integral_cong split:split_indicator
    simp: positive_integral_cmult[symmetric] mult_nonneg_nonneg power_divide divide_less_0_iff)
  
  also have "... = (fact k) / l ^ k" by (auto simp: integral_for_erlang)
  finally show **: "(\<integral>\<^sup>+ x. exponential_density l x * x ^ k \<partial>lborel) =..." .

  show "integrable M (\<lambda>x. X x ^ k)"
    apply (subst distributed_integrable[OF D, of "(\<lambda>x. x^k)", symmetric])
    apply (auto intro!: integrable_if_positive_integral **)
    by (auto simp:mult_nonneg_nonneg exponential_density_def)
qed

lemma (in prob_space) exponential_distributed_variance:
  assumes D: "distributed M lborel X (exponential_density l)"
  shows "variance X = 1 / l\<^sup>2"
proof (subst variance_eq)
  let ?\<mu> = "expectation X"
  have [arith]: "0 < l" by(rule exponential_distributed_params[OF D])

  have "expectation (\<lambda>x. (X x)\<^sup>2) = 2 / l\<^sup>2"
   apply (subst distributed_integral[OF D, of "(\<lambda>x. x\<^sup>2)", symmetric])
   apply (auto simp: exponential_kth_moment[OF D] lebesgue_integral_eq_positive_integral 
      exponential_density_nonneg mult_nonneg_nonneg)
   by (subst numeral_2_eq_2, simp)
  then show "expectation (\<lambda>x. (X x)\<^sup>2) - (expectation X)\<^sup>2 = 1/l\<^sup>2"
    by (auto simp:exponential_distributed_expectation[OF D] power_divide)

  show "integrable M X"
    apply(subst integrable_cong[where g ="(\<lambda>x. X x ^ 1)"], simp)
    by(rule exponential_kth_moment_integrable[OF D,of 1])
  
  show "integrable M (\<lambda>x. (X x)\<^sup>2)"
    apply(subst integrable_cong[where g ="(\<lambda>x. X x ^ 2)"], simp)
    by(rule exponential_kth_moment_integrable[OF D,of 2] )
qed 

lemma exponential_erlang_zero: "exponential_density l = erlang_density 0 l"
  by (auto simp:exponential_density_def erlang_density_def)

lemma conv_exponential_density:
  assumes [simp, arith]: " 0 < l"
  shows "(\<lambda>x. \<integral>\<^sup>+ y. ereal (exponential_density l (x - y) * exponential_density l y) \<partial>lborel) = (erlang_density 1 l)" 
    (is "?LHS = ?RHS")
proof-
  have "?LHS = (\<lambda>x. ereal (l\<^sup>2 * exp (- x * l)) *(integral\<^sup>P lborel (indicator {0..x})))"
    unfolding exponential_density_def
    by (subst positive_integral_cmult[symmetric])
      (auto intro!: positive_integral_cong simp:mult_exp_exp mult_nonneg_nonneg power2_eq_square field_simps split:split_indicator)
  also have "... =  (erlang_density 1 l)"
    unfolding erlang_density_def
    apply(rule HOL.ext, case_tac "0>x")    
    by (auto simp: power2_eq_square)
  finally show ?thesis by fast        
qed

lemma (in information_space) entropy_exponential:
  assumes D: "distributed M lborel X (exponential_density l)"
  shows "entropy b lborel X = log b (exp 1 /l)"
proof (subst entropy_distr[OF D])
  note times_divide_eq_left[simp del]
  have [simp, arith]: "0 < l" by(rule exponential_distributed_params[OF D])

  have *[intro]: "integrable lborel ( exponential_density l)"
     "integrable lborel (\<lambda>t. exponential_density l t * t)"
    apply (rule integrable_if_positive_integral)
    apply (auto simp:one_ereal_def exponential_density_nonneg prob_space_exponential_density)
    apply (subst distributed_integrable[OF D], simp)
    apply (subst integrable_cong[where g ="(\<lambda>x. X x ^ 1)"], simp)
    by (rule exponential_kth_moment_integrable[OF D,of 1])

  have "(\<integral> x. exponential_density l x * indicator {0..} x \<partial>lborel) = \<integral> x. exponential_density l x \<partial>lborel"
    by (auto intro!: integral_cong split:split_indicator simp :exponential_density_def)
  also have "... = 1"
    by (auto intro!: lebesgue_integral_eq_positive_integral simp: one_ereal_def 
      exponential_density_nonneg prob_space_exponential_density)
  finally have [simp]: "(\<integral> x. exponential_density l x * indicator {0..} x \<partial>lborel) = 1" .

  have "(\<integral> x. exponential_density l x * x * indicator {0..} x \<partial>lborel) = \<integral> x. exponential_density l x * x^1 \<partial>lborel"
    by(auto intro!: integral_cong split:split_indicator simp: exponential_density_def)
  also have "... = 1 / l"
    apply (subst lebesgue_integral_eq_positive_integral)
    apply (subst exponential_kth_moment[OF D])
    by (auto split:split_indicator simp: mult_nonneg_nonneg exponential_density_def exponential_kth_moment[OF D])
  finally have **: "(\<integral> x. exponential_density l x * x * indicator {0..} x \<partial>lborel) = 1 / l" .

  have "- (\<integral> x. exponential_density l x * log b (exponential_density l x) \<partial>lborel) =
      - (ln l / ln b)* (\<integral> x. exponential_density l x * indicator {0..} x \<partial>lborel) +
      (l / ln b)* \<integral> x. (exponential_density l x * x) * indicator {0..} x \<partial>lborel"
    apply (subst integral_cmult(2)[symmetric])
    apply (auto intro!: integrable_mult_indicator)
    apply (subst integral_cmult(2)[symmetric])
    apply (auto intro!: integrable_mult_indicator)
    apply (subst lebesgue_integral_uminus[symmetric])
    apply (subst integral_add(2)[symmetric])
    apply (auto intro!: integrable_mult_indicator)
    by (auto intro!: integral_cong split:split_indicator
      simp: log_def ln_mult diff_divide_distrib times_divide_eq_left field_simps exponential_density_def)
  also have "... = log b (exp 1 / l)" by (auto simp: ** log_def ln_div diff_divide_distrib)
  finally show "- (\<integral> x. exponential_density l x * log b (exponential_density l x) \<partial>lborel) = log b (exp 1 / l)" .
qed

lemma conv_exponential_erlang_density:
  fixes k::nat
  assumes [simp, arith]: "0 < l" 
  shows "(\<lambda>x. \<integral>\<^sup>+y. ereal (exponential_density l (x - y) * erlang_density k l y) \<partial>lborel) 
      = (erlang_density (1 + k) l)" (is "?LHS = ?RHS")
proof -
  have "?LHS = (\<lambda>x. ereal (l ^ (k + 2) * exp (- x * l) / real (fact k)) 
                * (integral\<^sup>P lborel (\<lambda>y. ereal y ^ k * indicator {0..x} y)))"
    unfolding exponential_density_def erlang_density_def
    apply (subst positive_integral_cmult[symmetric])
    by (auto intro!: positive_integral_cong split:split_indicator
       simp: mult_exp_exp mult_nonneg_nonneg power2_eq_square field_simps split:split_indicator)
  also have "... = erlang_density (1 + k) l"
    unfolding erlang_density_def
    apply (rule HOL.ext, case_tac "0>x")
    by (auto simp:field_simps positive_integral_power_nat)
       (auto simp: comm_semiring_1_class.normalizing_semiring_rules(3))
  finally show ?thesis .
qed

lemma (in prob_space) sum_indep_exponential_erlang:
  assumes indep: "indep_var lborel X lborel Y"
  assumes expX: "distributed M lborel X (exponential_density l)"
  assumes "distributed M lborel Y (erlang_density k l)"
  shows "distributed M lborel (\<lambda>x. X x + Y x) (erlang_density (1 + k) l)"
proof-
  have [simp, arith]:"0 <l" using expX by (auto simp: exponential_distributed_params)

  show "distributed M lborel (\<lambda>x. X x + Y x) (\<lambda>x. ereal (erlang_density (1 + k) l x))"
    apply (subst conv_exponential_erlang_density[symmetric], simp)
    apply (rule convolution_distributed_indep_random_variable_sum)
    using assms unfolding exponential_density_def erlang_density_def
    by (auto intro!: convolution_distributed_indep_random_variable_sum simp:mult_nonneg_nonneg divide_nonneg_nonneg)
qed

lemma (in prob_space) exponential_distributed_setsum:
  assumes finI: "finite I"
  assumes A: "I \<noteq> {}"
  assumes expX: "\<And>i. i\<in> I \<Longrightarrow> distributed M lborel (X i) (exponential_density l)"
  assumes ind: "indep_vars (\<lambda>i. borel) X I" 
  shows "distributed M lborel (\<lambda>x. \<Sum>i\<in>I. X i x) (erlang_density ((card I) - 1) l)"
using assms
proof (induct rule: finite_ne_induct)
  case (singleton i) then show ?case by (auto simp: exponential_erlang_zero)
next
  case (insert i I)
    then have "distributed M lborel (\<lambda>x. (X i x) + (\<Sum>i\<in> I. X i x)) (erlang_density ( 1 + ((card  I) - 1)) l )"
      by (intro sum_indep_exponential_erlang indep_vars_setsum) (auto intro!:indep_vars_subset)
    also have "(\<lambda>x. (X i x) + (\<Sum>i\<in> I. X i x)) = (\<lambda>x. \<Sum>i\<in> insert i I. X i x)" using insert by auto
    also have " 1 + ((card  I) - 1) = card (insert i I) - 1"
      apply (subst card_insert_disjoint)
      using insert by (auto intro!: Suc_pred)     
    finally show ?case .
qed

lemma conv_erlang_density:
  fixes k\<^sub>1 :: nat
  fixes k\<^sub>2 :: nat
  assumes [simp, arith]: "0 < l"  "0 < k\<^sub>1" (* for the case when 0= k\<^sub>1 we have exponential_erlang *)
  shows "(\<lambda>x. \<integral>\<^sup>+y. ereal (erlang_density k\<^sub>1 l (x- y) * erlang_density k\<^sub>2 l y) \<partial>lborel) = (erlang_density (Suc k\<^sub>1 + Suc k\<^sub>2 - 1) l)"
      (is "?LHS = ?RHS")
proof (rule HOL.ext,  case_tac "0\<ge>x")
  fix x::real assume [arith]: "0 \<ge> x"
  show "?LHS x = ?RHS x"
    proof -
      have "(integral\<^sup>P lborel (\<lambda>y. (erlang_density k\<^sub>1 l (x- y) * erlang_density k\<^sub>2 l y)) = 0)"
        unfolding erlang_density_def
        by(auto simp:positive_integral_0_iff_AE  power_0_left order_le_less)
      then show "(\<integral>\<^sup>+ y. ereal (erlang_density k\<^sub>1 l (x - y) * erlang_density k\<^sub>2 l y) \<partial>lborel) =
         ereal (erlang_density (Suc k\<^sub>1 + Suc k\<^sub>2 - 1) l x)" 
        unfolding erlang_density_def by simp
    qed
next
  note zero_le_mult_iff[simp] zero_le_divide_iff[simp]

  have I_eq1: "integral\<^sup>P lborel (erlang_density (Suc k\<^sub>1 + Suc k\<^sub>2 - 1) l) = 1"
    by (auto intro!: prob_space_erlang_density[OF assms(1)] simp: one_ereal_def)

  have 1: "(\<integral>\<^sup>+ x. ereal (erlang_density (Suc k\<^sub>1 + Suc k\<^sub>2 - 1) l x * indicator {0<..} x) \<partial>lborel) = 1"
    apply (subst I_eq1[symmetric])
    unfolding erlang_density_def
    by (auto intro!: positive_integral_cong split:split_indicator)

  have "prob_space (density  lborel ?LHS)"
    by (auto intro!: prob_space_convolution_density prob_space_erlang_density)
  then have 2: "integral\<^sup>P lborel ?LHS = 1" by (auto simp: one_ereal_def)

  let ?I = "(integral\<^sup>P lborel (\<lambda>y. ereal ((1 - y)^ k\<^sub>1 * y^k\<^sub>2 * indicator {0..1} y)))"
  let ?C = "real (fact (Suc (k\<^sub>1 + k\<^sub>2))) / (real (fact k\<^sub>1) * real (fact k\<^sub>2))"
  let ?s = "Suc k\<^sub>1 + Suc k\<^sub>2 - 1"
  let ?L = "(\<lambda>x. \<integral>\<^sup>+y. ereal (erlang_density k\<^sub>1 l (x- y) * erlang_density k\<^sub>2 l y * indicator {0..x} y) \<partial>lborel)"

  have *: "\<And>x. 0 < x \<Longrightarrow> ?LHS x = (\<lambda>x. ereal (?C)* ?I * (erlang_density ?s l x)) x"
  proof -
    fix x::real assume [arith]: "0 < x"
    have "?LHS x = ?L x"
      unfolding erlang_density_def
      by (auto intro!: positive_integral_cong split:split_indicator)
    also have "... = (\<lambda>x. ereal (?C)* ?I * (erlang_density ?s l x)) x"
      apply (subst positive_integral_real_affine[where c=x and t = 0 and M = lborel])
      apply (auto intro!: positive_integral_cong simp: mult_less_0_iff positive_integral_cmult[symmetric]
               positive_integral_multc[symmetric] erlang_density_def power_mult_distrib split:split_indicator)
      by(auto simp: field_simps power_mult_distrib[symmetric] mult_exp_exp power_add)
    finally show "?LHS x = (\<lambda>x. ereal (?C)* ?I * (erlang_density ?s l x)) x" .
  qed

  fix x::real assume  "\<not> 0 \<ge> x" then have [arith]: "0 < x" by simp
  have 3: "1 = integral\<^sup>P lborel (\<lambda>xa. ?LHS xa * indicator {0<..} xa)"
    apply (subst 2[symmetric])
    unfolding erlang_density_def 
    by (auto intro!: positive_integral_cong simp:positive_integral_multc[symmetric] split:split_indicator)
  also have "... = integral\<^sup>P lborel (\<lambda>x. (ereal (?C) * ?I) * ((erlang_density ?s l x) * indicator {0<..} x))"
    by (auto intro!: positive_integral_cong simp: * split:split_indicator)
  also have "... = ereal (?C) * ?I"
    using 1
    by (auto simp: positive_integral_positive positive_integral_cmult)  
  finally have " ereal (?C) * ?I = 1" by presburger

  then show "(\<integral>\<^sup>+ y. ereal (erlang_density k\<^sub>1 l (x - y) * erlang_density k\<^sub>2 l y) \<partial>lborel) = erlang_density ?s l x"
    using * by simp
qed

lemma (in prob_space) sum_indep_erlang:
  assumes indep: "indep_var lborel X lborel Y"
  assumes [simp, arith]: "0 < l"
  assumes erlX: "distributed M lborel X (erlang_density k\<^sub>1 l)"
  assumes erlY: "distributed M lborel Y (erlang_density k\<^sub>2 l)"
  shows "distributed M lborel (\<lambda>x. X x + Y x) (erlang_density (Suc k\<^sub>1 + Suc k\<^sub>2 - 1) l)"
proof (cases k\<^sub>1)
case 0
  then have "distributed M lborel (\<lambda>x. X x + Y x) (erlang_density ( 1+ k\<^sub>2) l)"
    apply (subst conv_exponential_erlang_density[symmetric], simp)
    using assms by (auto intro!: convolution_distributed_indep_random_variable_sum
        simp:exponential_erlang_zero conv_exponential_erlang_density[symmetric])
  then show ?thesis using 0 by auto
next
case (Suc n) 
  then show ?thesis
    apply (subst conv_erlang_density[symmetric])
    using assms by (auto intro!: convolution_distributed_indep_random_variable_sum)
qed

lemma (in prob_space) erlang_distributed_setsum:
  assumes finI : "finite I"
  assumes A: "I \<noteq> {}"
  assumes [simp, arith]: "0 < l"
  assumes expX: "\<And>i. i\<in> I \<Longrightarrow> distributed M lborel (X i) (erlang_density (k i) l)"
  assumes ind: "indep_vars (\<lambda>i. borel) X I"
  shows "distributed M lborel (\<lambda>x. \<Sum>i\<in>I. X i x) (erlang_density ((\<Sum>i\<in>I. Suc (k i)) - 1) l)"
using assms
proof (induct rule: finite_ne_induct)
  case (singleton i) then show ?case by (auto simp: exponential_erlang_zero)
next
  case (insert i I)
    then have "distributed M lborel (\<lambda>x. (X i x) + (\<Sum>i\<in> I. X i x)) (erlang_density (Suc (k i) + Suc ((\<Sum>i\<in>I. Suc (k i)) - 1) - 1) l)"
      by(intro sum_indep_erlang indep_vars_setsum) (auto intro!: indep_vars_subset)
    also have "(\<lambda>x. (X i x) + (\<Sum>i\<in> I. X i x)) = (\<lambda>x. \<Sum>i\<in>insert i I. X i x)"
      using insert by auto
    also have "Suc(k i) + Suc ((\<Sum>i\<in>I. Suc (k i)) - 1) - 1 = (\<Sum>i\<in>insert i I. Suc (k i)) - 1"
      using insert by (auto intro!: Suc_pred simp: ac_simps)    
    finally show ?case by fast
qed

end
