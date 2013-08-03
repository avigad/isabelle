theory Some_Calculus
imports Library_Misc Distributions

begin

(** Integral notations. **)

(* TODO: Fix precedences so parentheses are not required around integrals too
often. *)

syntax
"_ascii_lebesgue_integral" :: "pttrn \<Rightarrow> 'a measure \<Rightarrow> real \<Rightarrow> real"
("(3LINT _|_. _)" [0,110,60] 60)

translations
"LINT x|M. f" == "CONST lebesgue_integral M (\<lambda>x. f)"

syntax
"_ascii_lebesgue_borel_integral" :: "pttrn \<Rightarrow> real \<Rightarrow> real"
("(2LBINT _. _)" [0,60] 60)

translations
"LBINT x. f" == "CONST lebesgue_integral CONST lborel (\<lambda>x. f)"

(* maybe use indicator A x *\<^sub>R f x *)
abbreviation
"set_lebesgue_integral M A f \<equiv> lebesgue_integral M (\<lambda>x. f x * indicator A x)"

syntax
"_ascii_set_lebesgue_integral" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'a measure \<Rightarrow> real \<Rightarrow> real"
("(4LINT _:_|_. _)" [0,60,110,61] 60)

translations
"LINT x:A|M. f" == "CONST set_lebesgue_integral M A (\<lambda>x. f)"

syntax
"_ascii_set_lebesgue_borel_integral" :: "pttrn \<Rightarrow> real set \<Rightarrow> real \<Rightarrow> real"
("(3LBINT _:_. _)" [0,60,61] 60)

translations
"LBINT x:A. f" == "CONST set_lebesgue_integral CONST lborel A (\<lambda>x. f)"

abbreviation "set_integrable M A f \<equiv> integrable M (\<lambda>x. f x * indicator A x)"

definition interval_lebesgue_integral ::
"real measure \<Rightarrow> ereal \<Rightarrow> ereal \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real"
  where "interval_lebesgue_integral M a b f \<equiv>
    (if a \<le> b then set_lebesgue_integral M {r. a \<le> ereal r \<and> ereal r \<le> b} f
               else - set_lebesgue_integral M {r. b \<le> ereal r \<and> ereal r \<le> a} f)"

syntax
  "_ascii_interval_lebesgue_integral" ::
  "pttrn \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real measure \<Rightarrow> real \<Rightarrow> real"
  ("(5LINT _=_.._|_. _)" [0,60,60,110,61] 60)

translations
  "LINT x=a..b|M. f" ==
  "CONST interval_lebesgue_integral M (CONST ereal a) (CONST ereal b) (\<lambda>x. f)"

syntax
  "_ascii_interval_lebesgue_borel_integral" ::
  "pttrn \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" ("(4LBINT _=_.._. _)" [0,60,60,61] 60)

translations
  "LBINT x=a..b. f" == "CONST interval_lebesgue_integral CONST lborel
  (CONST ereal a) (CONST ereal b) (\<lambda>x. f)"

syntax
  "_ascii_interval_lebesgue_integral_Iic" ::
  "pttrn \<Rightarrow> real \<Rightarrow> real measure \<Rightarrow> real \<Rightarrow> real"
  ("(5LINT _ \<le> _|_. _)" [0,60,110,61] 60)

translations
  "LINT x \<le> b|M. f" == "CONST interval_lebesgue_integral M
  (CONST uminus (CONST infinity)) (CONST ereal b) (\<lambda>x. f)"

syntax
  "_ascii_interval_lebesgue_borel_integral_Iic" :: "pttrn \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
  ("(5LBINT _ \<le> _. _)" [0,60,61] 60)

translations
  "LBINT x \<le> b. f" == "LINT x \<le> b|(CONST lborel). f"

syntax
  "_ascii_interval_lebesgue_integral_Iio" ::
  "pttrn \<Rightarrow> real \<Rightarrow> real measure \<Rightarrow> real \<Rightarrow> real"
  ("(5LINT _ < _|_. _)" [0,60,110,61] 60)

translations
  "LINT x < b|M. f" == "LINT x:{..b}|M. f"

syntax
  "_ascii_interval_lebesgue_integral_Iio" ::
  "pttrn \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
  ("(5LBINT _ < _. _)" [0,60,61] 60)

translations
  "LBINT x < b. f" == "LBINT x:{..b}. f"

syntax
  "_ascii_interval_lebesgue_integral_Ici" ::
  "pttrn \<Rightarrow> real \<Rightarrow> real measure \<Rightarrow> real \<Rightarrow> real"
  ("(5LINT _ \<ge> _|_. _)" [0,60,110,61] 60)

translations
  "LINT x \<ge> a|M. f" ==
  "CONST interval_lebesgue_integral M (CONST ereal a) (CONST infinity) (\<lambda>x. f)"

syntax
  "_ascii_interval_lebesgue_integral_Ici" ::
  "pttrn \<Rightarrow> real \<Rightarrow> real measure \<Rightarrow> real \<Rightarrow> real"
  ("(5LBINT _ \<ge> _. _)" [0,60,61] 60)

translations
  "LBINT x \<ge> a. f" == "LINT x \<ge> a|(CONST lborel). f"

syntax
  "_ascii_interval_lebesgue_integral_Ioi" ::
  "pttrn \<Rightarrow> real \<Rightarrow> real measure \<Rightarrow> real \<Rightarrow> real"
  ("(5LINT _ > _|_. _)" [0,60,110,61] 60)

translations
  "LINT x > a|M. f" == "LINT x:{a..}|M. f"

syntax
  "_ascii_interval_lebesgue_integral_Iio" ::
  "pttrn \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
  ("(5LBINT _ > _. _)" [0,60,61] 60)

translations
  "LBINT x > a. f" == "LBINT x:{a..}. f"

(***** Almost Everywhere on a Set. *****)
abbreviation
  "set_almost_everywhere A M P \<equiv> AE x in M. x \<in> A \<longrightarrow> P x"

syntax
  "_set_almost_everywhere" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> bool"
("AE _\<in>_ in _. _" [0,0,0,10] 10)

translations
  "AE x\<in>A in M. P" == "CONST set_almost_everywhere A M (\<lambda>x. P)"

(** General Lebesgue integration. **)

lemma set_integral_Un:
  assumes "A \<inter> B = {}"
  and "set_integrable M A f"
  and "set_integrable M B f"
  shows "LINT x:A\<union>B|M. f x = (LINT x:A|M. f x) + (LINT x:B|M. f x)"
  by (auto simp add: indicator_union_arith indicator_inter_arith[symmetric]
      distrib_left assms)

lemma set_integrable_Un:
  assumes "set_integrable M A f" "set_integrable M B f"
  "A \<in> sets M" "B \<in> sets M" "f \<in> borel_measurable M"
  shows "set_integrable M (A \<union> B) f"

  apply (rule integrable_bound[of _ "\<lambda>x. \<bar>f x * indicator A x\<bar> +
      \<bar>f x * indicator B x\<bar>"])
  apply (rule integral_add(1))
  apply (auto intro: assms integrable_abs)
  apply (rule AE_I2)
  apply (subst abs_mult)+
  apply (metis (hide_lams, no_types) UnE abs_ge_zero add_increasing
    add_increasing2 comm_semiring_1_class.normalizing_semiring_rules(34)
    indicator_abs_eq indicator_def indicator_le_1 mult_left_mono)
  using assms apply auto
done
            
lemma set_integrable_finite_Union:
  assumes finI: "finite I" and 
    measAi: "\<And>i. i\<in>I \<Longrightarrow> (A i) \<in> sets M" and
    measf: "f \<in> borel_measurable M"
    "\<And>i. i\<in>I \<Longrightarrow> set_integrable M (A i) f"
  shows "set_integrable M (\<Union>i\<in>I. A i) f"
  using assms
  apply (induct I)
  apply force
  apply (subst UN_insert)
  apply (rule set_integrable_Un)
  apply auto
done

lemma set_integrable_finite_Union':
  assumes finI: "finite I" and 
    measAi: "\<And>i. i\<in>I \<Longrightarrow> (A i) \<in> sets M" and
    measf: "(\<lambda>x. f x * indicator (\<Union>i\<in>I. A i) x) \<in> borel_measurable M"
    "\<And>i. i\<in>I \<Longrightarrow> set_integrable M (A i) f"
  shows "set_integrable M (\<Union>i\<in>I. A i) f"

  apply (subst mult_indicator_subset [of "\<Union>i\<in>I. A i" "\<Union>i\<in>I. A i", symmetric])
  apply force
  apply (subst mult_assoc [symmetric])
  apply (rule set_integrable_finite_Union)
  using assms apply auto
  apply (subst mult_assoc)
  apply (subst mult_commute) back
  apply (subst mult_indicator_subset)
  apply auto
done

lemma indicator_finite_union:
  assumes "finite I" "disjoint_family_on A I"
  shows "(indicator (UN i : I. A i) x :: real) = (SUM i : I. indicator (A i) x)"

  using assms apply (induct I)
  apply auto
  apply (subst indicator_disj_union)
  apply (auto simp add: disjoint_family_on_def)
done

lemma set_integral_finite_union:
  assumes "finite I" "disjoint_family_on A I" and
    measAi: "\<And>i. i\<in>I \<Longrightarrow> (A i) \<in> sets M" and
    "\<And>i. i \<in> I \<Longrightarrow> set_integrable M (A i) f"
  shows "(LINT x:(\<Union>i\<in>I. A i)|M. f x) = (\<Sum>i\<in>I. LINT x:A i|M. f x)"
  using assms
  apply induct
  apply auto
  apply (subst set_integral_Un)
  apply (subst Int_UN_distrib) 
  apply (subst UNION_empty_conv(2))
  unfolding disjoint_family_on_def apply (metis insertCI)
  using assms apply auto
  apply (rule set_integrable_finite_Union')
  apply auto
  apply (subst indicator_finite_union)
  apply auto
  prefer 2
  apply (subst setsum_right_distrib)
  apply (rule borel_measurable_setsum)
  apply auto
  unfolding disjoint_family_on_def apply auto
done

lemma set_integrable_subset:
  assumes intgbl: "set_integrable M B f"
  and meas: "A \<in> sets M"
  and sub: "A \<subseteq> B"
  shows "set_integrable M A f"
  using sub apply (subst mult_indicator_subset[symmetric])
  apply simp
  apply (subst mult_commute) back
  apply (subst mult_assoc[symmetric])
  apply (rule integrable_mult_indicator)
  by (auto intro: assms)

lemma set_integral_cmult:
  assumes "set_integrable M A f"
  shows "set_integrable M A (\<lambda>t. a * f t)"
  and "LINT t:A|M. a * f t = a * (LINT t:A|M. f t)"
  (* Expressions which are the same up to rearrangement of parentheses should be easier to identify. *)
  apply (subst mult_assoc)
  apply (auto intro: assms)
  apply (subst mult_assoc)
  by (auto intro: assms)

(**
(* Generalize to more measures and more change-of-variable functions. *)
lemma lborel_cont_diff_change_variable:
  fixes a b :: real
  assumes "a \<le> b"
  and "\<And>x. x\<in>{a..b} \<Longrightarrow> g x \<in> {(g a)..(g b)} \<and> isCont g' x \<and> DERIV g x :> g' x"
  and "g a \<le> g b"
  and "\<And>x. x \<in> {(g a)..(g b)} \<Longrightarrow> DERIV F x :> f x"
  and "\<And>x. x \<in> {(g a)..(g b)} \<Longrightarrow> isCont f x"
  shows "LINT x:a..b|lborel. f (g x) * g' x = LINT y:(g a)..(g b)|lborel. f y"
proof-
  have "\<forall>x \<in> {a..b}. isCont (\<lambda>x. f (g x) * g' x) x"
  proof-
    have isCont_comp: "\<forall>x \<in> {a..b}. isCont f (g x)" using assms by auto
    have isCont_g: "\<forall>x \<in> {a..b}. isCont g x"
      using assms DERIV_isCont by blast
    hence "\<forall>x \<in> {a..b}. isCont (\<lambda>x. f (g x)) x"
      using isCont_comp isCont_g isCont_o2 by blast
    thus ?thesis using assms by simp
  qed
  hence "LINT x:a..b|lborel. f (g x) * g' x = (F o g) b - (F o g) a"
    using assms integral_FTC_atLeastAtMost[of a b "(F o g)"
      "\<lambda>x. f (g x) * g' x"] by (auto intro!: DERIV_chain)
  thus ?thesis using assms integral_FTC_atLeastAtMost[of "g a" "g b" F f]
    by auto
qed
**)

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

lemma set_integrable_abs: "set_integrable M A f \<Longrightarrow> set_integrable M A (\<lambda>x. \<bar>f x\<bar>)"
  using integrable_abs[of M "\<lambda>x. f x * indicator A x"] by (simp add: abs_mult)

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
      apply (subst set_integral_finite_union)
      apply (auto simp: disjoint_family_on_def disj atLeast0LessThan
                  intro!: set_integrable_abs)
      apply (rule set_integrable_subset[OF intgbl])
      apply auto
      done
    also have "\<dots> \<le> set_lebesgue_integral M (\<Union>i. A i) (\<lambda>x. \<bar>f x\<bar>)"
      apply (intro integral_mono set_integrable_abs intgbl)
      apply (rule integrable_bound[OF intgbl[THEN  set_integrable_abs]])
      apply (auto split: split_indicator)
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
    using set_integrable_subset[where A = "A i" and B = "\<Union>i. A i"] A intgbl by auto
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
    apply (subst indicator_abs_eq[symmetric])
    apply (subst abs_mult[symmetric])
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


(**    
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
      (*Need development version for next fact? *)
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
**)

lemma set_AE_func_int_eq:
  assumes "AE x \<in> A in M. f x = g x"
  shows "LINT x:A|M. f x = LINT x:A|M. g x"
proof-
  have "AE x in M. f x * indicator A x = g x * indicator A x"
    using assms by auto
  thus ?thesis using integral_cong_AE by metis
qed

lemma integral_at_point:
  fixes a :: real
  assumes "set_integrable M {a} f"
  and "{a} \<in> sets M" and "(emeasure M) {a} \<noteq> \<infinity>"
  shows "LINT x=a..a|M. f x = f a * real (emeasure M {a})"
proof-
  have eq: "{r. a \<le> r \<and> r \<le> a} = {a}" by auto
  have int_at: "LINT x:{a}|M. f x = LINT x:{a}|M. f a"
    by (metis (full_types) indicator_simps(2) mult_zero_right singletonE)
  also have "... = f a * real (emeasure M {a})" using assms by auto
  finally show ?thesis using int_at by (simp add: interval_lebesgue_integral_def eq)
qed

lemma integral_limits_inter_neg:
  fixes a b :: real
  assumes "a \<noteq> b"
  shows "LINT x=b..a|M. f x = -(LINT x=a..b|M. f x)"
  using assms by (auto simp: interval_lebesgue_integral_def)

(** Derivatives and integrals for CLT. **)

lemma exp_alpha_at_top:
  assumes pos: "0 < x"
  shows "LIM (u::real) at_top. exp (u * x) :> at_top"
  apply (rule filterlim_compose[of exp at_top at_top "\<lambda>u. u * x" at_top])
  apply (rule exp_at_top)
  apply (subst mult_commute)
  apply (rule filterlim_at_top_at_top[where Q = "\<lambda>x. True" and P = "\<lambda>x. True" and g = "op * (1/x)"])
  apply (rule mult_left_mono)
  apply simp apply (smt pos) apply simp
  apply (smt pos)
  apply simp
  by auto

lemma "((F \<circ> real) ---> T) (at_left (ereal a)) \<longleftrightarrow> (F ---> T) (at_left a)"
  sorry

lemma "((F \<circ> real) ---> T) (at_left \<infinity>) \<longleftrightarrow> (F ---> T) at_top"
  sorry

lemma "((F \<circ> real) ---> T) (at_left (-\<infinity>)) \<longleftrightarrow> (F ---> T) at_bot"
  sorry

lemma "((ereal \<circ> f) ---> ereal a) F \<longleftrightarrow> (f ---> a) F"
  sorry

lemma "((ereal \<circ> f) ---> \<infinity>) F \<longleftrightarrow> (LIM x F. f x :> at_top)"
  sorry

lemma "((ereal \<circ> f) ---> -\<infinity>) F \<longleftrightarrow> (LIM x F. f x :> at_bot)"
  sorry

definition "eint a b = {x. a \<le> ereal x \<and> ereal x \<le> b}"

lemma "eint (ereal a) (ereal b) = {a .. b}"
  by (auto simp: eint_def)

lemma integral_substitution:
  fixes f g g':: "real \<Rightarrow> real" and a b :: ereal
  assumes "a \<le> b"
  assumes deriv_g: "!!x. x \<in> eint a b \<Longrightarrow> (g has_vector_derivative (g' x)) (at x within X)"
  assumes contf: "continuous_on (g ` eint a b) f"
  assumes contg': "continuous_on (eint a b) g'"
  assumes "((ereal \<circ> g \<circ> real) ---> t) (at_left a)"
  assumes "((ereal \<circ> g \<circ> real) ---> b) (at_right b)"
  shows "interval_lebesgue_integral lborel a b (\<lambda>x. (f (g x) * g' x)) = interval_lebesgue_integral lborel t b f"
sorry

lemma interval_integral_FTC:
  fixes f F :: "real \<Rightarrow> real" and a b :: ereal
  assumes "a \<le> b"
  assumes f_borel: "f \<in> borel_measurable borel"
  assumes f: "\<And>x. a \<le> ereal x \<Longrightarrow> ereal x \<le> b \<Longrightarrow> DERIV F x :> f x" 
  assumes nonneg: "\<And>x. a \<le> ereal x \<Longrightarrow> ereal x \<le> b \<Longrightarrow> 0 \<le> f x"
  assumes T: "((F \<circ> real) ---> T) (at_left a)"
  assumes B: "((F \<circ> real) ---> B) (at_right b)"
  shows "interval_lebesgue_integral lborel a b f = T - B"
sorry

lemma interval_integrable_FTC:
  fixes f F :: "real \<Rightarrow> real" and a b :: ereal
  assumes "a \<le> b"
  assumes f_borel: "f \<in> borel_measurable borel"
  assumes f: "\<And>x. a \<le> ereal x \<Longrightarrow> ereal x \<le> b \<Longrightarrow> DERIV F x :> f x" 
  assumes nonneg: "\<And>x. a \<le> ereal x \<Longrightarrow> ereal x \<le> b \<Longrightarrow> 0 \<le> f x"
  assumes T: "((F \<circ> real) ---> T) (at_left a)"
  assumes B: "((F \<circ> real) ---> B) (at_right b)"
  shows "interval_lebesgue_integrable lborel a b f"
sorry

lemma positive_integral_eq_erealD:
  assumes "integral\<^isup>P M f = ereal x"
  assumes "f \<in> borel_measurable M"
  assumes "AE x in M. 0 \<le> f x"
  shows "integrable M f" "integral\<^isup>L M f = x"
  apply (metis PInfty_neq_ereal(1) integrable_nonneg assms)
  by (metis PInfty_neq_ereal(1) assms(1) assms(2) assms(3) integrable_nonneg positive_integral_eq_integral real_of_ereal(2))

(* Should be easier to conclude integrability from calculation of an integral. *)
(* Adapted from proof in Distributions.thy. *)
lemma integral_expneg_alpha_atLeast0:
  fixes x::real
  assumes pos: "0 < u"
  shows "LBINT x:{0..}. exp (- (x * u)) = 1/u" (is "?eq")
  and "set_integrable lborel {0..} (\<lambda>x. exp (- (x * u)))" (is ?int) thm interval_integral_FTC thm diff_0
  apply (subst diff_0[symmetric, where a = )

proof -
  have "(\<integral>\<^isup>+ x. ereal (exp (- (x * u)) * indicator {0..} x) \<partial>lborel) =
    (\<integral>\<^isup>+ x. ereal (exp (- (x * u))) * indicator {0..} x \<partial>lborel)"
    by (intro positive_integral_cong) (auto split: split_indicator)
  also have "\<dots> = ereal (0 - (- 1 / u * exp (- u * 0)))"
    apply (rule positive_integral_FTC_atLeast[where F="\<lambda>x. - 1 / u * exp (- u * x)"])
    apply measurable
    using `0 < u`
    apply (auto intro!: DERIV_intros)
    apply (rule tendsto_eq_intros)
    apply (subst filterlim_at_top_mirror)
    apply (rule tendsto_eq_intros)
    apply (rule filterlim_compose[of exp])
    apply (rule exp_at_bot)
    apply simp_all
    apply (rule filterlim_tendsto_pos_mult_at_bot)
    apply (rule tendsto_const)
    apply (rule `0 < u`)
    apply (rule filterlim_ident)
    apply auto
    done
  finally have *: "(\<integral>\<^isup>+x. ereal (exp (- (x * u)) * indicator {0..} x) \<partial>lborel) = ereal (1 / u)"
    by simp

  show ?eq
    by (rule positive_integral_eq_erealD[OF *]) (simp_all add: mult_nonneg_nonneg)
  show ?int
    by (rule positive_integral_eq_erealD[OF *]) (simp_all add: mult_nonneg_nonneg)
qed

lemma Collect_eq_Icc: "{r. t \<le> r \<and> r \<le> b} = {t .. b}"
  by auto

(* From Billingsley section 18. *)
lemma ex_18_4_1_deriv: "DERIV (\<lambda>x. (1/(1+u^2)) * (1 - exp (-u * x) *
(u * sin x + cos x))) x :> exp (-u * x) * sin x"
  apply (auto intro!: DERIV_intros)
  apply (simp_all add: power2_eq_square field_simps)
  by (metis mult_zero_left not_square_less_zero square_bound_lemma)+

lemma ex_18_4_1:
  assumes "t \<ge> 0"
  shows "LBINT x=0..t. exp (-u * x) * sin x = (1/(1+u^2)) *
  (1 - exp (-u * t) * (u * sin t + cos t))"
  unfolding interval_lebesgue_integral_def
  using integral_FTC_atLeastAtMost[of 0 t "\<lambda>x. (1/(1+u^2)) *
    (1 - exp (-u * x) * (u * sin x + cos x))" "\<lambda>x. exp (-u * x) * sin x"]
    ex_18_4_1_deriv assms by (simp add:  Collect_eq_Icc)

lemma ex_18_4_2_deriv:
  "DERIV (\<lambda>u. 1/x * (1 - exp (-u * x)) * \<bar>sin x\<bar>) u :> \<bar>exp (-u * x) * sin x\<bar>"
  apply (auto simp only: intro!: DERIV_intros)
  by (simp add: abs_mult)

lemma ex_18_4_2_bdd_integral:
  assumes "s \<ge> 0"
  shows "LBINT u=0..s. \<bar>exp (-u * x) * sin x\<bar> =
  1/x * (1 - exp (-s * x)) * \<bar>sin x\<bar>"
using integral_FTC_atLeastAtMost[of 0 s "\<lambda>u. 1/x * (1 - exp (-u * x)) * \<bar>sin x\<bar>" "\<lambda>u. \<bar>exp (-u * x) * sin x\<bar>"] assms
ex_18_4_2_deriv by simp

lemma ex_18_4_2_ubdd_integral:
  fixes x
  assumes pos: "0 < x"
  shows "LBINT u:{0..}. \<bar>exp (-(u * x)) * sin x\<bar> = \<bar>sin x\<bar> / x" (is "LBINT u:{0..}. ?f u = ?sx")
  apply (subst abs_mult)
  apply (subst mult_commute) back
  (* Would be nice not to need to do this explicitly. *)
  apply (subst divide_inverse)
  apply (subst inverse_eq_divide)
  apply (subst integral_expneg_alpha_atMost0[symmetric], rule pos)
  (* Automated tools should get this. *)
  apply (subst mult_assoc)
  apply (subst integral_cmult(2), simp_all)
  (* Want a theorem which says that if we can calculate the integral of something, it is integrable. *)
      

definition sinc :: "real \<Rightarrow> real" where
"sinc t \<equiv> LBINT x:0..t. sin x / x"

lemma sinc_at_top: "(sinc ---> \<pi>/2) at_top"
  sorry

lemma Billingsley_26_15:
  assumes "T \<ge> 0"
  shows "\<And>\<theta>. LBINT t:0..T. sin (t * \<theta>) / t = sgn \<theta> * sinc (T * \<bar>\<theta>\<bar>)"
  sorry

end