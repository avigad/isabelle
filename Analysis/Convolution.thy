(* Convolution Measure
   Author: Sudeep Kanav
   Author: Johannes Hölzl *)

theory Convolution
  imports Probability Auxiliary
begin

definition convolution :: "('a :: ordered_euclidean_space) measure \<Rightarrow> 'a measure \<Rightarrow> 'a measure" (infix "\<star>" 50) where
  "convolution M N = distr (M \<Otimes>\<^sub>M N) borel (\<lambda>(x, y). x + y)"

lemma
  shows space_convolution[simp]: "space (convolution M N) = space borel"
    and sets_convolution[simp]: "sets (convolution M N) = sets borel"
    and measurable_convolution1[simp]: "measurable A (convolution M N) = measurable A borel"
    and measurable_convolution2[simp]: "measurable (convolution M N) B = measurable borel B"
  by (simp_all add: convolution_def)

lemma positive_integral_convolution:
  assumes "finite_measure M" "finite_measure N"
  assumes [simp]: "sets N = sets borel" "sets M = sets borel"
  assumes [measurable]: "f \<in> borel_measurable borel"
  shows "(\<integral>\<^sup>+x. f x \<partial>convolution M N) = (\<integral>\<^sup>+x. \<integral>\<^sup>+y. f (x + y) \<partial>N \<partial>M)"
proof -
  interpret M: finite_measure M by fact
  interpret N: finite_measure N by fact
  interpret pair_sigma_finite M N ..
  show ?thesis
    unfolding convolution_def
    by (simp add: positive_integral_distr N.positive_integral_fst_measurable(2)[symmetric])
qed

lemma convolution_emeasure:
  assumes "A \<in> sets borel" "finite_measure M" "finite_measure N"
  assumes [simp]: "sets N = sets borel" "sets M = sets borel"
  assumes [simp]: "space M = space N" "space N = space borel"
  shows "emeasure (M \<star> N) A = \<integral>\<^sup>+x. (emeasure N {a. a + x \<in> A}) \<partial>M "
  using assms by (auto intro!: positive_integral_cong simp del: positive_integral_indicator simp: positive_integral_convolution 
    positive_integral_indicator[symmetric] ab_semigroup_add_class.add_ac split:split_indicator)

lemma convolution_emeasure':
  assumes [simp]:"A \<in> sets borel"
  assumes [simp]: "finite_measure M" "finite_measure N"
  assumes [simp]: "sets N = sets borel" "sets M = sets borel"
  shows  "emeasure (M \<star> N) A = \<integral>\<^sup>+x. \<integral>\<^sup>+y.  (indicator  A (x + y)) \<partial>N  \<partial>M"
  by (auto simp del: positive_integral_indicator simp: positive_integral_convolution
    positive_integral_indicator[symmetric] borel_measurable_indicator)

lemma convolution_finite:
  assumes [simp]: "finite_measure M" "finite_measure N"
  assumes [simp]: "sets N = sets borel" "sets M = sets borel"
  shows "finite_measure (M \<star> N)"
  unfolding convolution_def
  by (intro finite_measure_pair_measure finite_measure.finite_measure_distr) auto

lemma convolution_emeasure_3:
  assumes [simp, measurable]: "A \<in> sets borel"
  assumes [simp]: "finite_measure M" "finite_measure N" "finite_measure L"
  assumes [simp]: "sets N = sets borel" "sets M = sets borel" "sets L = sets borel"
  shows "emeasure (L \<star> (M \<star> N )) A = \<integral>\<^sup>+x. \<integral>\<^sup>+y. \<integral>\<^sup>+z. indicator A (x + y + z) \<partial>N \<partial>M \<partial>L"
  apply (subst positive_integral_indicator[symmetric], simp)
  apply (subst positive_integral_convolution, 
        auto intro!: borel_measurable_indicator borel_measurable_indicator' convolution_finite)+
  by (rule positive_integral_cong)+ (auto simp: semigroup_add_class.add_assoc)

lemma convolution_emeasure_3':
  assumes [simp, measurable]:"A \<in> sets borel"
  assumes [simp]: "finite_measure M" "finite_measure N"  "finite_measure L"
  assumes [simp]: "sets N = sets borel" "sets M = sets borel" "sets L = sets borel"
  shows "emeasure ((L \<star> M) \<star> N ) A = \<integral>\<^sup>+x. \<integral>\<^sup>+y. \<integral>\<^sup>+z. indicator A (x + y + z) \<partial>N \<partial>M \<partial>L"
  apply (subst positive_integral_indicator[symmetric], simp)+
  by (subst positive_integral_convolution, auto simp: finite_measure.borel_measurable_positive_integral
   intro!: borel_measurable_indicator borel_measurable_indicator' convolution_finite)+ 

lemma convolution_commutative:
  assumes [simp]: "finite_measure M" "finite_measure N"
  assumes [simp]: "sets N = sets borel" "sets M = sets borel"
  shows "(M \<star> N) = (N \<star> M)"
proof (rule measure_eqI)  
  interpret M: finite_measure M by fact
  interpret N: finite_measure N by fact
  interpret pair_sigma_finite M N ..

  show "sets (M \<star> N) = sets (N \<star> M)" by simp

  fix A assume "A \<in> sets (M \<star> N)"
  then have 1[measurable]:"A \<in> sets borel" by simp
  have "emeasure (M \<star> N) A = \<integral>\<^sup>+x. \<integral>\<^sup>+y. indicator A (x + y) \<partial>N \<partial>M" by (auto intro!: convolution_emeasure')
  also have "... = \<integral>\<^sup>+x. \<integral>\<^sup>+y. (\<lambda>(x,y). indicator A (x + y)) (x, y) \<partial>N \<partial>M" by (auto intro!: positive_integral_cong)
  also have "... = \<integral>\<^sup>+y. \<integral>\<^sup>+x. (\<lambda>(x,y). indicator A (x + y)) (x, y) \<partial>M \<partial>N" by (rule Fubini[symmetric]) simp
  also have "... = emeasure (N \<star> M) A" by (auto intro!: positive_integral_cong simp: add_commute convolution_emeasure')
  finally show "emeasure (M \<star> N) A = emeasure (N \<star> M) A" by simp
qed

lemma convolution_associative:
  (*distributive also*)
  assumes [simp]: "finite_measure M" "finite_measure N"  "finite_measure L"
  assumes [simp]: "sets N = sets borel" "sets M = sets borel" "sets L = sets borel"
  shows "(L \<star> (M \<star> N)) = ((L \<star> M) \<star> N)"
  by (auto intro!: measure_eqI simp: convolution_emeasure_3 convolution_emeasure_3')

lemma (in prob_space) sum_indep_random_variable:
  assumes ind: "indep_var borel X borel Y"
  assumes [simp, measurable]: "random_variable borel X"
  assumes [simp, measurable]: "random_variable borel Y"
  shows "distr M borel (\<lambda>x. X x + Y x) = convolution (distr M borel X)  (distr M borel Y)"
  using ind unfolding indep_var_distribution_eq convolution_def
  by (auto simp: distr_distr intro!:arg_cong[where f = "distr M borel"])

lemma (in prob_space) sum_indep_random_variable_lborel:
  assumes ind: "indep_var borel X borel Y"
  assumes [simp, measurable]: "random_variable lborel X"
  assumes [simp, measurable]:"random_variable lborel Y" 
  shows "distr M lborel (\<lambda>x. X x + Y x) = convolution (distr M lborel X)  (distr M lborel Y)"
  using ind unfolding indep_var_distribution_eq convolution_def 
  by (auto simp: distr_distr o_def intro!: arg_cong[where f = "distr M borel"] cong: distr_cong)

lemma convolution_density_ereal:
  fixes f :: "real \<Rightarrow> ereal"
  fixes g::"real \<Rightarrow> ereal" 
  assumes [simp, measurable]:"f \<in> borel_measurable lborel"  "g \<in> borel_measurable lborel"
  assumes [simp]:"finite_measure (density lborel f)" "finite_measure (density lborel g)"
(* need this assumption to be forall instead of AE because positive_integral_cmult needs it *)
  assumes gt_0[simp, arith]: "\<And> x. 0\<le> f x"  "\<And>x. 0\<le> g x"
  shows "density lborel f \<star> density lborel g = density lborel (\<lambda>x. \<integral>\<^sup>+y. f (x - y) * g y \<partial>lborel)"
apply (auto intro!: measure_eqI  simp: convolution_emeasure' positive_integral_density)
apply (subst emeasure_density, measurable, auto simp: positive_integral_cmult[symmetric])
apply (subst positive_integral_multc[symmetric], measurable, auto)
proof -
  fix A:: "real set"
  assume [simp, measurable]:"A \<in> sets borel"  
  
  have "(\<integral>\<^sup>+ x. \<integral>\<^sup>+ xa. f (x - xa) * g xa * indicator A x \<partial>lborel \<partial>lborel) = \<integral>\<^sup>+ x. \<integral>\<^sup>+ xa. (\<lambda>(x, xa). f (x - xa) * g xa * indicator A x) (x, xa) \<partial>lborel \<partial>lborel"
    by(rule positive_integral_cong)+ auto    
  also have "... =  \<integral>\<^sup>+ xa. \<integral>\<^sup>+ x. (\<lambda>(y, z). f (y - z) * g z * indicator A y) (x, xa) \<partial>lborel \<partial>lborel"
    by(rule lborel_pair.Fubini[symmetric], measurable, auto)    
  also have "... =  \<integral>\<^sup>+ xa. \<integral>\<^sup>+ x. f (x - xa) * g xa * indicator A x \<partial>lborel \<partial>lborel" by(auto intro!: positive_integral_cong)
  also have "... =  \<integral>\<^sup>+ xa. \<integral>\<^sup>+ x. f x * g xa * indicator A (x + xa) \<partial>lborel \<partial>lborel"
    apply (rule positive_integral_cong)
    apply (subst(2) positive_integral_real_affine[where t = "- x" and c = 1])
    by (auto intro!: positive_integral_cong simp: add_commute)
      
  also have "... = \<integral>\<^sup>+ xa. \<integral>\<^sup>+ x. (\<lambda>(xa, x). f x * g xa * indicator A (x + xa)) (xa, x) \<partial>lborel \<partial>lborel"
    by (auto intro!: positive_integral_cong)
  also have "... = \<integral>\<^sup>+ x. \<integral>\<^sup>+ xa. (\<lambda>(xa, x). f x * g xa * indicator A (x + xa)) (xa, x) \<partial>lborel \<partial>lborel"
    by (rule lborel_pair.Fubini[symmetric]) simp
  also have "... = \<integral>\<^sup>+ x. \<integral>\<^sup>+ xa. f x *  g xa * indicator A (x + xa) \<partial>lborel \<partial>lborel"
    by (auto intro!: positive_integral_cong)

  finally have 1: "(\<integral>\<^sup>+ x. \<integral>\<^sup>+ xa. f (x - xa) * g xa * indicator A x \<partial>lborel \<partial>lborel) 
      = \<integral>\<^sup>+ x. \<integral>\<^sup>+ xa. f x * g xa * indicator A (x + xa) \<partial>lborel \<partial>lborel" by simp
  
  show "(\<integral>\<^sup>+ x. \<integral>\<^sup>+ xa. f x * (g xa * indicator A (x + xa)) \<partial>lborel \<partial>lborel) = \<integral>\<^sup>+ x. \<integral>\<^sup>+ xa. f (x - xa) * g xa * indicator A x \<partial>lborel \<partial>lborel"
    by (subst 1) (auto intro!: positive_integral_cong simp: field_simps)
qed

lemma convolution_density:
  fixes f :: "real \<Rightarrow> real"
  fixes g::"real \<Rightarrow> real"
  assumes [simp, measurable]:"f \<in> borel_measurable lborel"  "g \<in> borel_measurable lborel"
  assumes [simp]:"finite_measure (density lborel f)" "finite_measure (density lborel g)"
  assumes gt_0[simp]: "\<And>x. 0\<le> f x"  "\<And>x. 0\<le> g x"
  shows "density lborel f \<star> density lborel g = density lborel (\<lambda>x.\<integral>\<^sup>+y. f (x - y) * g y \<partial>lborel)"
  by (auto simp: convolution_density_ereal)

lemma (in prob_space) convolution_distributed_indep_random_variable_sum:
  fixes f :: "real \<Rightarrow> real"
  fixes g :: "real \<Rightarrow> real"
  assumes ind[simp]: "indep_var borel X borel Y"
  assumes [simp, measurable]: "distributed M lborel X f"
  assumes [simp, measurable]: "distributed M lborel Y g"
  (* wanted to use AE but have to use for all as convolution_density uses forall *)
  assumes gt_0[simp, arith]: "\<And> x. 0\<le> f x"  "\<And>x. 0\<le> g x"
  shows "distributed M lborel (\<lambda>x. X x + Y x) (\<lambda>x.\<integral>\<^sup>+y. f (x - y) * g y \<partial>lborel)"
proof(auto simp: distributed_def)  
  from assms(2) have 1[simp, measurable]:"distr M lborel X = density lborel  (\<lambda>x. ereal (f x))"
      "(\<lambda>x. ereal (f x)) \<in> borel_measurable lborel"
      "(AE x in lborel. 0 \<le> f x)"
      "random_variable lborel X"
       by(auto simp: distributed_def)

  from assms(3) have 2[simp, measurable]:"distr M lborel Y = density lborel (\<lambda>x. ereal (g x))"
      "(\<lambda>x. ereal (g x)) \<in> borel_measurable lborel"
      "(AE x in lborel. 0 \<le> g x)"
      "random_variable lborel Y"
      by(auto simp: distributed_def )

  show "distr M lborel (\<lambda>x. X x + Y x) = density lborel (\<lambda>x. \<integral>\<^sup>+ y. f (x - y) * g y \<partial>lborel)"
    apply (subst sum_indep_random_variable_lborel)
    apply fact+
    apply (auto intro!: convolution_density finite_measure_distr)
    apply (simp_all only: 1(1)[symmetric]  2(1)[symmetric])
    by (intro finite_measure_distr, fact)+

  show "random_variable borel (\<lambda>x. X x + Y x)" using 1(4) 2(4) by simp

  show "AE x in lborel. 0 \<le> \<integral>\<^sup>+ xa. ereal (f (x - xa) * g xa) \<partial>lborel" by (auto simp: positive_integral_positive)      

  show "(\<lambda>x. \<integral>\<^sup>+ xa. ereal (f (x - xa) * g xa) \<partial>lborel) \<in> borel_measurable borel" by (measurable) auto
qed

lemma prob_space_convolution_density:
  fixes f:: "real \<Rightarrow> real"
  fixes g:: "real \<Rightarrow> real"
  assumes [measurable]: "f\<in> borel_measurable borel"
  assumes [measurable]: "g\<in> borel_measurable borel"
  assumes gt_0[simp]: "\<And>x. 0\<le> f x" "\<And>x. 0\<le> g x"
  assumes [simp]: "prob_space (density lborel f)" (is "prob_space ?F")
  assumes [simp]: "prob_space (density lborel g)" (is "prob_space ?G")
  shows "prob_space (density lborel (\<lambda>x.\<integral>\<^sup>+y. f (x - y) * g y \<partial>lborel))" (is "prob_space ?D")
proof -
  have [simp]: "integral\<^sup>P lborel f = 1" "integral\<^sup>P lborel g = 1" by(auto simp: one_ereal_def)

  have "emeasure ?D (space ?D) =  emeasure (density lborel (\<lambda>x.\<integral>\<^sup>+y. f (x - y) * g y  \<partial>lborel)) UNIV" by auto
  also have "... = \<integral>\<^sup>+ x. \<integral>\<^sup>+y. f (x - y) * g y \<partial>lborel \<partial>lborel" by (simp add:emeasure_density)
  also have "... = \<integral>\<^sup>+ x. \<integral>\<^sup>+y. (\<lambda>(x,y). f (x - y) * g y) (x,y) \<partial>lborel \<partial>lborel" by (auto intro!: positive_integral_cong)
  also have "... = \<integral>\<^sup>+ y. \<integral>\<^sup>+x. (\<lambda>(x,y). f (x - y) * g y) (x,y) \<partial>lborel \<partial>lborel" by (rule lborel_pair.Fubini[symmetric]) simp
  also have "... = \<integral>\<^sup>+ y. (\<integral>\<^sup>+x.  f (x - y) \<partial>lborel) * g y \<partial>lborel"
    by(subst positive_integral_multc[symmetric]) auto
  also have "... = \<integral>\<^sup>+ y. (\<integral>\<^sup>+x. f x  \<partial>lborel) * g y \<partial>lborel"
    apply (rule positive_integral_cong)
    by (subst positive_integral_real_affine[of 1 f lborel "- x"]) (auto simp: field_simps)    
  finally have "emeasure ?D (space ?D) = 1" by simp

  then show "prob_space ?D" by rule 
qed
end
