(*
Theory: Weak_Convergence.thy
Authors: Jeremy Avigad 

Properties of weak convergence of functions and measures, including the portmanteau theorem.
*)

theory Weak_Convergence

imports Probability Distribution_Functions Distributions

begin

definition
  weak_conv :: "(nat \<Rightarrow> (real \<Rightarrow> real)) \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> bool"
where
  "weak_conv F_seq F \<equiv> \<forall>x. isCont F x \<longrightarrow> (\<lambda>n. F_seq n x) ----> F x"

definition
  weak_conv_m :: "(nat \<Rightarrow> real measure) \<Rightarrow> real measure \<Rightarrow> bool"
where
  "weak_conv_m M_seq M \<equiv> weak_conv (\<lambda>n. cdf (M_seq n)) (cdf M)"


(* state using obtains? *)
theorem Skorohod:
  fixes 
    M_seq :: "nat \<Rightarrow> real measure" and
    M :: "real measure"
  assumes 
    "\<And>n. real_distribution (M_seq n)" and 
    "real_distribution M" and 
    "weak_conv_m M_seq M"
  shows "\<exists> (Omega :: real measure) (Y_seq :: nat \<Rightarrow> (real \<Rightarrow> real)) (Y :: real \<Rightarrow> real). 
    prob_space Omega \<and>
    (\<forall>n. Y_seq n \<in> measurable Omega borel) \<and>
    (\<forall>n. distr Omega borel (Y_seq n) = M_seq n) \<and>
    Y \<in> measurable Omega lborel \<and>
    distr Omega borel Y = M \<and>
    (\<forall>x \<in> space Omega. (\<lambda>n. Y_seq n x) ----> Y x)"
sorry

lemma isCont_borel:
  fixes f :: "real \<Rightarrow> real"
  assumes "f \<in> borel_measurable borel"
  shows "{x. isCont f x} \<in> sets borel"
proof -
  {
    fix x
    have "isCont f x = (\<forall>(i::nat). \<exists>(j::nat). \<forall>y z. 
      abs(x - y) < inverse(real (j + 1)) \<and> abs(x - z) < inverse(real (j + 1)) \<longrightarrow>
        abs(f(y) - f(z)) \<le> inverse (real (i + 1)))"
      apply (subst continuous_at_real_range, auto)
      apply (drule_tac x = "inverse(2 * real(Suc i))" in spec, auto)
      apply (frule reals_Archimedean, auto)
      apply (rule_tac x = n in exI, auto)
      apply (frule_tac x = y in spec)
      apply (drule_tac x = z in spec, auto)
      (* gee, it would be nice if this could be done automatically *)
      apply (subgoal_tac "f y - f z = f y - f x + (f x - f z)")
      apply (erule ssubst)
      apply (rule order_trans)
      apply (rule abs_triangle_ineq)
      apply (auto simp add: abs_minus_commute)
      apply (frule reals_Archimedean, auto)
      apply (drule_tac x = n in spec, auto)
      apply (rule_tac x = "inverse (real (Suc j))" in exI, auto)
      apply (drule_tac x = x' in spec)
      by (drule_tac x = x in spec, auto)
  } note isCont_iff = this
  {
    fix i j :: nat
    have "open {x. (\<exists>y. \<bar>x - y\<bar> < inverse (real (Suc i)) \<and> 
        (\<exists>z. \<bar>x - z\<bar> < inverse (real (Suc i)) \<and> inverse (real (Suc j)) < \<bar>f y - f z\<bar>))}"
    proof (auto simp add: not_le open_real)
      fix x y z 
      assume 1: "\<bar>x - y\<bar> < inverse (real (Suc i))" and 2: "\<bar>x - z\<bar> < inverse (real (Suc i))"
        and 3: "inverse (real (Suc j)) < \<bar>f y - f z\<bar>"
      hence "\<exists>e > 0. abs(x - y) + e \<le> inverse (real (Suc i)) \<and> 
                     abs(x - z) + e \<le> inverse (real (Suc i))"
        apply (rule_tac x = "min (inverse (real (Suc i)) - abs(x - y)) 
             (inverse (real (Suc i)) - abs(x - z))" in exI)
        by (auto split: split_min)
      then obtain e where 4: "e > 0" and 5: "abs(x - y) + e \<le> inverse (real (Suc i))"
          and 6: "abs(x - z) + e \<le> inverse (real (Suc i))" by auto
      have "e > 0 \<and> (\<forall>x'. \<bar>x' - x\<bar> < e \<longrightarrow>
               (\<exists>y. \<bar>x' - y\<bar> < inverse (real (Suc i)) \<and>
               (\<exists>z. \<bar>x' - z\<bar> < inverse (real (Suc i)) \<and> inverse (real (Suc j)) < \<bar>f y - f z\<bar>)))"
           (is "?P e")
        using 1 2 3 4 5 6 apply auto
        apply (rule_tac x = y in exI, auto)
        by (rule_tac x = z in exI, auto)
      thus "\<exists>e. ?P e" ..
    qed
  } note * = this
  show ?thesis
    apply (subst isCont_iff)
    apply (subst Collect_all_eq)
    apply (rule countable_Un_Int, auto)
    apply (subst Collect_ex_eq)
    apply (rule countable_Un_Int, auto)
    apply (rule borel_closed)
    apply (subst closed_def)
    apply (subst Compl_eq, simp add: not_le)
    by (rule *)
qed

theorem weak_conv_bdd_ae_cont:
  fixes 
    M_seq :: "nat \<Rightarrow> real measure" and
    M :: "real measure" and
    f :: "real \<Rightarrow> real"
  assumes 
    distr_M_seq: "\<And>n. real_distribution (M_seq n)" and 
    distr_M: "real_distribution M" and 
    wcM: "weak_conv_m M_seq M" and
    discont_null: "M ({x. \<not> isCont f x}) = 0" and
    f_bdd: "\<And>x. abs (f x) \<le> B" and
    [simp]: "f \<in> borel_measurable borel"
  shows 
    "(\<lambda> n. integral\<^sup>L (M_seq n) f) ----> integral\<^sup>L M f"
proof -
  note Skorohod [OF distr_M_seq distr_M wcM]
  then obtain Omega Y_seq Y where
    ps_Omega [simp]: "prob_space Omega" and
    Y_seq_measurable [simp]: "\<And>n. Y_seq n \<in> borel_measurable Omega" and
    distr_Y_seq: "\<And>n. distr Omega borel (Y_seq n) = M_seq n" and
    Y_measurable [simp]: "Y \<in> borel_measurable Omega" and
    distr_Y: "distr Omega borel Y = M" and
    YnY: "\<And>x :: real. x \<in> space Omega \<Longrightarrow> (\<lambda>n. Y_seq n x) ----> Y x"  by force
  have *: "emeasure Omega (Y -` {x. \<not> isCont f x} \<inter> space Omega) = 0"
    apply (subst emeasure_distr [symmetric])
    apply (rule Y_measurable)
    apply (subst double_complement [symmetric])
    apply (rule borel_comp)
    apply (subst Compl_eq, simp, rule isCont_borel, simp)
    by (subst distr_Y, rule discont_null)
    thm pred_Collect_borel
  show ?thesis
    apply (subst distr_Y_seq [symmetric])
    apply (subst distr_Y [symmetric])
    apply (subst integral_distr, simp_all)+
    apply (rule integral_dominated_convergence)
    apply (rule finite_measure.integrable_const_bound)
    apply force
    apply (rule always_eventually, rule allI, rule f_bdd)
    apply (rule measurable_compose) back
    apply (rule Y_seq_measurable, force)
    apply (rule always_eventually, rule allI, rule f_bdd)
    apply (rule finite_measure.lebesgue_integral_const, force)
    prefer 2    
    apply (rule measurable_compose) back
    apply (rule Y_measurable, simp)
    apply (rule AE_I [where N = "Y -` {x. \<not> isCont f x} \<inter> space Omega"])
    apply auto [1]
    apply (erule notE)
    apply (erule isCont_tendsto_compose)
    apply (erule YnY)
    apply (rule *)
    apply (rule measurable_sets)
    apply (rule Y_measurable)
    apply (subst double_complement [symmetric])
    apply (rule borel_comp)
    apply (subst Compl_eq, simp)
    by (rule isCont_borel, simp)
qed

end




