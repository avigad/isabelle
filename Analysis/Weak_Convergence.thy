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
    (\<forall>n. Y_seq n \<in> measurable Omega lborel) \<and>
    (\<forall>n. distr Omega lborel (Y_seq n) = M_seq n) \<and>
    Y \<in> measurable Omega lborel \<and>
    distr Omega lborel Y = M \<and>
    weak_conv Y_seq Y"
sorry

theorem weak_conv_bdd_ae_cont:
  fixes 
    M_seq :: "nat \<Rightarrow> real measure" and
    M :: "real measure" and
    f :: "real \<Rightarrow> real"
  assumes 
    distr_M_seq: "\<And>n. real_distribution (M_seq n)" and 
    distr_M: "real_distribution M" and 
    wcM: "weak_conv_m M_seq M" and
    "M ({x. \<not> isCont f x}) = 0" and
    f_bdd: "\<And>x. abs (f x) \<le> B" and
    [simp]: "f \<in> borel_measurable borel"
  shows 
    "(\<lambda> n. integral\<^sup>L (M_seq n) f) ----> integral\<^sup>L M f"
proof -
  note Skorohod [OF distr_M_seq distr_M wcM]
  then obtain Omega Y_seq Y where
    ps_Omega [simp]: "prob_space Omega" and
    [simp]: "\<And>n. Y_seq n \<in> borel_measurable Omega" and
    distr_Y_seq: "\<And>n. distr Omega lborel (Y_seq n) = M_seq n" and
    [simp]: "Y \<in> borel_measurable Omega" and
    distr_Y: "distr Omega lborel Y = M" and
    wcY: "weak_conv Y_seq Y" by auto
  show ?thesis
    apply (subst distr_Y_seq [symmetric])
    apply (subst distr_Y [symmetric])
    apply (subst integral_distr, simp_all)+
    apply (rule integral_dominated_convergence)
    apply (rule finite_measure.integrable_const_bound, auto)
    apply (rule always_eventually, rule allI, rule f_bdd)
    apply (rule measurable_compose) back



    sorry
qed

term prob_space
term measurable
term distributed
term distr

end




