(*  
Theory: Set_Integral.thy
Authors: Jeremy Avigad, Johannes Hölzl, Luke Serafin 

Notation and useful facts for working with integrals over a set.

TODO: keep all these? Need unicode translations as well.
*)

theory Set_Integral
  imports Probability
begin

(* 
    Notation 
*)

syntax
"_ascii_lebesgue_integral" :: "pttrn \<Rightarrow> 'a measure \<Rightarrow> real \<Rightarrow> real"
("(3LINT _|_. _)" [0,110,60] 60)

translations
"LINT x|M. f" == "CONST lebesgue_integral M (\<lambda>x. f)"

abbreviation "set_borel_measurable M A f \<equiv> (\<lambda>x. f x * indicator A x) \<in> borel_measurable M"

abbreviation "set_integrable M A f \<equiv> integrable M (\<lambda>x. f x * indicator A x)"

abbreviation "set_lebesgue_integral M A f \<equiv> lebesgue_integral M (\<lambda>x. f x * indicator A x)"

syntax
"_ascii_set_lebesgue_integral" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'a measure \<Rightarrow> real \<Rightarrow> real"
("(4LINT _:_|_. _)" [0,60,110,61] 60)

translations
"LINT x:A|M. f" == "CONST set_lebesgue_integral M A (\<lambda>x. f)"

abbreviation
  "set_almost_everywhere A M P \<equiv> AE x in M. x \<in> A \<longrightarrow> P x"

syntax
  "_set_almost_everywhere" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> bool"
("AE _\<in>_ in _. _" [0,0,0,10] 10)

translations
  "AE x\<in>A in M. P" == "CONST set_almost_everywhere A M (\<lambda>x. P)"

(* 
    Basic properties 
*)

lemma indicator_abs_eq: "\<And>A x. abs (indicator A x) = ((indicator A x) :: real)"
  by (auto simp add: indicator_def)

lemma set_AE_func_int_eq:
  assumes "AE x \<in> A in M. f x = g x"
  shows "LINT x:A|M. f x = LINT x:A|M. g x"
proof-
  have "AE x in M. f x * indicator A x = g x * indicator A x"
    using assms by auto
  thus ?thesis using integral_cong_AE by metis
qed

lemma set_integrable_subset: 
  fixes M A B f
  assumes "set_integrable M A f" "B \<in> sets M" "B \<subseteq> A"  
  shows "set_integrable M B f"
proof -
  have "set_integrable M B (\<lambda>x. f x * indicator A x)"
    by (rule integrable_mult_indicator, rule assms, rule assms)
  also have "(\<lambda>x. f x * indicator A x * indicator B x) = (\<lambda>x. f x * indicator B x)"
    apply (rule ext)
    using `B \<subseteq> A` by (auto simp add: indicator_def)
  finally show ?thesis .
qed

(* TODO: integral_cmul_indicator should be named set_integral_const *)
(* TODO: borel_integrable_atLeastAtMost should be named something like set_integrable_Icc_isCont *)

lemma set_integral_cmult [simp, intro]:
  assumes "set_integrable M A f"
  shows "set_integrable M A (\<lambda>t. a * f t)"
  and "LINT t:A|M. a * f t = a * (LINT t:A|M. f t)"
using assms by (auto simp add: mult_assoc)

lemma set_integral_add [simp, intro]:
  assumes "set_integrable M A f" "set_integrable M A g"
  shows "set_integrable M A (\<lambda>x. f x + g x)" and "LINT x:A|M. f x + g x =
    (LINT x:A|M. f x) + (LINT x:A|M. g x)"
using assms by (auto simp add: field_simps)

lemma set_integral_diff [simp, intro]:
  assumes "set_integrable M A f" "set_integrable M A g"
  shows "set_integrable M A (\<lambda>x. f x - g x)" and "LINT x:A|M. f x - g x =
    (LINT x:A|M. f x) - (LINT x:A|M. g x)"
using assms by (auto simp add: field_simps)

lemma set_integral_mono: 
  assumes "set_integrable M A f" "set_integrable M A g"
    "\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x"
  shows "(LINT x:A|M. f x) \<le> (LINT x:A|M. g x)"
using assms by (auto intro: integral_mono split: split_indicator)

lemma set_integral_mono_AE: 
  assumes "set_integrable M A f" "set_integrable M A g"
    "AE x \<in> A in M. f x \<le> g x"
  shows "(LINT x:A|M. f x) \<le> (LINT x:A|M. g x)"
using assms by (auto intro: integral_mono_AE split: split_indicator)

lemma set_integrable_abs: "set_integrable M A f \<Longrightarrow> set_integrable M A (\<lambda>x. \<bar>f x\<bar>)"
  using integrable_abs[of M "\<lambda>x. f x * indicator A x"] by (simp add: abs_mult)

lemma set_integrable_Un:
  assumes "set_integrable M A f" "set_integrable M B f"
    "A \<in> sets M" "B \<in> sets M"
  shows "set_integrable M (A \<union> B) f"

  apply (subst indicator_union_arith)
  apply (simp add: field_simps)
  apply (rule integral_diff)
  apply (rule integral_add)
  apply (rule assms)+
  apply (rule integrable_bound)
  prefer 2
  apply (rule AE_I2)
  apply (subst mult_assoc [symmetric], subst abs_mult)
  apply (rule mult_right_le_one_le, auto)
  apply (subst integrable_abs_iff)
  apply (rule borel_measurable_integrable)
  apply (rule assms)+
  apply (subst mult_assoc [symmetric], rule borel_measurable_times)
  apply (rule borel_measurable_integrable, rule assms)
by (rule borel_measurable_indicator, rule assms)

lemma set_integrable_UN:
  assumes "finite I" "\<And>i. i\<in>I \<Longrightarrow> set_integrable M (A i) f"
    "\<And>i. i\<in>I \<Longrightarrow> A i \<in> sets M"
  shows "set_integrable M (\<Union>i\<in>I. A i) f"
using assms by (induct I, auto intro!: set_integrable_Un)

lemma set_integral_Un:
  assumes "A \<inter> B = {}"
  and "set_integrable M A f"
  and "set_integrable M B f"
  shows "LINT x:A\<union>B|M. f x = (LINT x:A|M. f x) + (LINT x:B|M. f x)"
by (auto simp add: indicator_union_arith indicator_inter_arith[symmetric]
      distrib_left assms)

lemma set_integral_finite_Union:
  assumes "finite I" "disjoint_family_on A I"
    and "\<And>i. i \<in> I \<Longrightarrow> set_integrable M (A i) f" "\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets M"
  shows "(LINT x:(\<Union>i\<in>I. A i)|M. f x) = (\<Sum>i\<in>I. LINT x:A i|M. f x)"

  using assms
  apply induct
  apply (auto intro!: set_integral_Un set_integrable_Un set_integrable_UN simp: disjoint_family_on_def)
by (subst set_integral_Un, auto intro: set_integrable_UN)

lemma pos_integrable_to_top:
  fixes l::real
  assumes "\<And>i. A i \<in> sets M" "mono A"
  assumes nneg: "\<And>x i. x \<in> A i \<Longrightarrow> 0 \<le> f x"
  and intgbl: "\<And>i::nat. set_integrable M (A i) f"
  and lim: "(\<lambda>i::nat. LINT x:A i|M. f x) ----> l"
  shows "set_integrable M (\<Union>i. A i) f"

  apply (rule integral_monotone_convergence_pos[where f = "\<lambda>i::nat. \<lambda>x. f x * indicator (A i) x" and x = l])
  apply (rule intgbl)
  prefer 4 apply (rule lim)
  apply (rule AE_I2)
  using `mono A` apply (auto simp: mono_def nneg split: split_indicator) []
  apply (auto intro!: AE_I2 nneg split: split_indicator) []
proof (rule AE_I2)
  { fix x assume "x \<in> space M"
    show "(\<lambda>i. f x * indicator (A i) x) ----> f x * indicator (\<Union>i. A i) x"
    proof cases
      assume "\<exists>i. x \<in> A i"
      then guess i ..
      then have *: "eventually (\<lambda>i. x \<in> A i) sequentially"
        using `x \<in> A i` `mono A` by (auto simp: eventually_sequentially mono_def)
      show ?thesis
        apply (intro Lim_eventually)
        using *
        apply eventually_elim
        apply (auto split: split_indicator)
        done
    qed auto }
  then show "(\<lambda>x. f x * indicator (\<Union>i. A i) x) \<in> borel_measurable M"
    by (rule borel_measurable_LIMSEQ) (auto intro: borel_measurable_integrable intgbl)
qed

(* Proof from Royden Real Analysis, p. 91. *)
lemma lebesgue_integral_countable_add:
  assumes meas[intro]: "\<And>i::nat. A i \<in> sets M"
  and disj: "\<And>i j. i \<noteq> j \<Longrightarrow> A i \<inter> A j = {}"
  and intgbl: "set_integrable M (\<Union>i. A i) f"
  shows "LINT x:(\<Union>i. A i)|M. f x = (\<Sum>i. (LINT x:(A i)|M. f x))"

  apply (subst integral_sums(2)[THEN sums_unique, symmetric])
  apply (rule set_integrable_subset[OF intgbl])
  apply auto []
  apply auto []
proof -
  { fix x assume "x \<in> space M"
    have "(\<lambda>i. indicator (A i) x::real) sums (if \<exists>i. x \<in> A i then 1 else (0::real))"
    proof auto
      fix i assume "x \<in> A i"
      then have "\<And>j. j \<noteq> i \<Longrightarrow> indicator (A j) x = (0::real)"
        using disj[of _ i] by (auto split: split_indicator)
      with `x \<in> A i` have "(\<lambda>i. indicator (A i) x) sums (\<Sum>j\<in>{i}. indicator (A j) x)"
        by (intro sums_finite) (auto dest!: disj split: split_indicator)
      then show "(\<lambda>i. indicator (A i) x) sums 1"
        using `x \<in> A i` by simp
    qed }
  note sums = this
  from sums_summable[OF this]
  show "\<And>x. x \<in> space M \<Longrightarrow> summable (\<lambda>i. \<bar>f x * indicator (A i) x\<bar>)"
    by (simp add: abs_mult summable_mult)

  show "summable (\<lambda>i. LINT x|M. \<bar>f x * indicator (A i) x\<bar>)"
  proof (rule pos_summable)
    fix n
    show "0 \<le> LINT x|M. \<bar>f x * indicator (A n) x\<bar>"
      by (auto intro!: lebesgue_integral_nonneg)
    have "(\<Sum>i = 0..<n. LINT x|M. \<bar>f x * indicator (A i) x\<bar>) =
      (\<Sum>i = 0..<n. set_lebesgue_integral M (A i) (\<lambda>x. \<bar>f x\<bar>))"
      by (simp add: abs_mult)
    also have "\<dots> = set_lebesgue_integral M (\<Union>i<n. A i) (\<lambda>x. \<bar>f x\<bar>)"
      apply (subst set_integral_finite_Union)
      apply (auto simp: disjoint_family_on_def disj atLeast0LessThan
                  intro!: set_integrable_abs)
      apply (rule set_integrable_subset[OF intgbl])
      apply auto
      done
    also have "\<dots> \<le> set_lebesgue_integral M (\<Union>i. A i) (\<lambda>x. \<bar>f x\<bar>)"
      apply (intro integral_mono set_integrable_abs intgbl)
      apply (rule integrable_bound[OF intgbl[THEN  set_integrable_abs]])
      apply (auto intro!: AE_I2 split: split_indicator)
      apply (rule borel_measurable_integrable)
      apply (rule set_integrable_subset[OF intgbl])
      apply auto
      done
    finally show "(\<Sum>i = 0..<n. LINT x|M. \<bar>f x * indicator (A i) x\<bar>) \<le>
      set_lebesgue_integral M (\<Union>i. A i) (\<lambda>x. \<bar>f x \<bar>)"
      by simp
  qed
  show "set_lebesgue_integral M (UNION UNIV A) f = LINT x|M. (\<Sum>i. f x * indicator (A i) x)"
    apply (rule integral_cong)
    apply (subst suminf_mult[OF sums_summable[OF sums]])
  proof -
    fix x assume x: "x \<in> space M"
    from sums_unique[OF sums, OF this, symmetric]
    have "indicator (UNION UNIV A) x = (\<Sum>i. indicator (A i) x :: real)"
      by (simp split: split_indicator)
    then show "f x * indicator (UNION UNIV A) x = f x * (\<Sum>i. indicator (A i) x)"
      by simp
  qed
qed

lemma set_integral_cont_up:
  assumes A: "\<And>i. A i \<in> sets M" "incseq A"
  and intgbl: "set_integrable M (\<Union>i. A i) f"
  shows "(\<lambda>i. LINT x:(A i)|M. f x) ----> LINT x:(\<Union>i. A i)|M. f x"
proof (intro integral_dominated_convergence[of M
    "\<lambda>i. \<lambda>x. f x * indicator (A i) x"
    "\<lambda>x. \<bar>f x\<bar> * indicator (\<Union>i. A i) x"
    "\<lambda>x. f x * indicator (\<Union>i. A i) x"])
  fix i::nat show "set_integrable M (A i) f"
    using set_integrable_subset[where B = "A i" and A = "\<Union>i. A i"] A intgbl by auto
next
  fix j::nat show "AE x in M. \<bar>f x * indicator (A j) x\<bar> \<le>
    \<bar>f x\<bar> * indicator (\<Union>i. A i) x"
    apply (rule AE_I2)
    apply (subst abs_mult)
    apply (case_tac "x \<in> A j")
    apply simp
    apply (subgoal_tac "x \<in> (\<Union>i. A i)")
    apply simp apply auto
    apply (case_tac "x \<in> (\<Union>i. A i)")
    by simp_all
next
  show "set_integrable M (\<Union>i. A i) (\<lambda>x. \<bar>f x\<bar>)"
    apply (subst indicator_abs_eq [symmetric])
    apply (subst abs_mult [symmetric])
    apply (rule integrable_abs)
    using assms by auto
next
  show "AE x in M. (\<lambda>i. f x * indicator (A i) x) ---->
    f x * indicator  (\<Union>i. A i) x"
    proof (rule AE_I2)
    fix x
    assume Mx: "x \<in> space M"
    show "(\<lambda>i. f x * indicator (A i) x) ---->
      f x * indicator (\<Union>i. A i) x"
      apply (rule tendsto_mult, auto)
      apply (rule increasing_LIMSEQ)
      unfolding indicator_def using assms A by (auto simp: incseq_Suc_iff)
  qed
next
  show "(\<lambda>x. f x * indicator (\<Union>i. A i) x) \<in> borel_measurable M"
    unfolding integrable_def using assms by simp
qed
        
(* Can the int0 hypothesis be dropped? *)
lemma set_integral_cont_down:
  assumes A: "\<And>i. A i \<in> sets M" "decseq A"
  and int0: "set_integrable M (A 0) f"
  shows "(\<lambda>i::nat. LINT x:(A i)|M. f x) ----> LINT x:(\<Inter>i. A i)|M. f x"
proof (rule integral_dominated_convergence(3))
  have A_super: "\<And>i. A i \<subseteq> A 0"
    using A by (auto simp add: decseq_def)
  with A show int: "\<And>i. set_integrable M (A i) f"
    by (intro set_integrable_subset[OF int0]) auto
  show "set_integrable M (A 0) (\<lambda>x. \<bar>f x\<bar>)"
    using int0 by (rule set_integrable_abs)
  show "\<And>j. AE x in M. \<bar>f x * indicator (A j) x\<bar> \<le> \<bar>f x\<bar> * indicator (A 0) x"
    using A_super by (auto simp: abs_mult split: split_indicator)
  { fix x assume "x \<in> space M"
    have "(\<lambda>i. f x * indicator (A i) x) ----> f x * indicator (\<Inter>i. A i) x"
      apply (intro tendsto_intros)
      apply (cases "\<forall>i. x \<in> A i")
      apply auto
      apply (rule decreasing_tendsto)
      apply (simp_all add: eventually_sequentially)
      apply (rule_tac x=i in exI)
      using `decseq A`
      apply (auto split: split_indicator simp: decseq_def)
      done }
  note LIMSEQ = this
  then show "AE x in M. (\<lambda>i. f x * indicator (A i) x) ----> f x * indicator (\<Inter>i. A i) x"
    by simp
  show "(\<lambda>x. f x * indicator (\<Inter>i. A i) x) \<in> borel_measurable M"
    using LIMSEQ by (rule borel_measurable_LIMSEQ) (auto intro: borel_measurable_integrable int)
qed

lemma set_integral_at_point:
  fixes a :: real
  assumes "set_integrable M {a} f"
  and "{a} \<in> sets M" and "(emeasure M) {a} \<noteq> \<infinity>"
  shows "(LINT x:{a} | M. f x) = f a * real (emeasure M {a})"
proof-
  have eq: "{r. a \<le> r \<and> r \<le> a} = {a}" by auto
  have int_at: "set_lebesgue_integral M {a} f = set_lebesgue_integral M {a} (%x. f a)"
    by (metis (full_types) indicator_simps(2) mult_zero_right singletonE)
  also have "... = f a * real (emeasure M {a})" using assms by auto
  finally show ?thesis using int_at by (simp add: eq)
qed

end


