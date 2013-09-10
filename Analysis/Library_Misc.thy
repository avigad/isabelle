theory Library_Misc
imports Complex_Main Distributions

begin

(** General miscellaneous. **)

lemma rat_type_infinite: "infinite (UNIV :: rat set)"
  by (rule Finite_Set.infinite_UNIV_char_0)

lemma inj_on_infinite: "infinite A \<Longrightarrow> inj_on f A \<Longrightarrow> infinite (range f)"
  apply (simp add: infinite_iff_countable_subset)
  apply auto
  apply (rule_tac x = "f o fa" in exI)
  apply auto
  by (metis comp_inj_on_iff subset_inj_on)

lemma real_rats_infinite: "infinite \<rat>"
  apply (subst Rats_def)
  apply (rule inj_on_infinite)
  apply (rule Finite_Set.infinite_UNIV_char_0)
  unfolding inj_on_def by auto

lemma indicator_abs_eq[simp]:
  "\<bar>indicator A x\<bar> = ((indicator A x)::'a::linordered_idom)"
  by simp

lemma indicator_disj_union:
  assumes "A \<inter> B = {}"
  shows "indicator (A \<union> B) x = indicator A x + (indicator B x :: 'a::ring_1)"
  by (auto simp add: indicator_union_arith indicator_inter_arith[symmetric] assms)

lemma indicator_disj_un_fun:
  assumes "A \<inter> B = {}"
  shows "indicator (A \<union> B) = (\<lambda>x. indicator A x +
  (indicator B x :: 'a::ring_1))"
  by (auto simp add: indicator_union_arith indicator_inter_arith[symmetric] assms)

lemma mult_indicator_subset:
  assumes sub: "A \<subseteq> B"
  shows "\<And>x. indicator A x * indicator B x = ((indicator A x)::real)"
  apply (case_tac "x \<in> A")
  apply (subgoal_tac "x \<in> B")
  apply auto
  by (metis in_mono sub)

lemma setseq_inc:
  assumes inc: "\<And>i::nat. A i \<subseteq> A (i+1)"
  shows "\<And>i j::nat. i \<le> j \<Longrightarrow> A i \<subseteq> A j"
proof-
  fix j::nat
  show "\<And>i. i \<le> j \<Longrightarrow> A i \<subseteq> A j"
  proof (induct j)
    fix i::nat
    assume "i \<le> 0"
    hence "i = 0" by simp
    thus "A i \<subseteq> A 0" by simp
  next
    fix i j::nat
    assume mono: "\<And>i. i \<le> j \<Longrightarrow> A i \<subseteq> A j"
    assume i_le_sj: "i \<le> Suc j"
    show "A i \<subseteq> A (Suc j)"
    proof (cases "i = Suc j")
      assume "i = Suc j"
      thus "A i \<subseteq> A (Suc j)" by simp
    next
      assume "i \<noteq> Suc j"
      hence "i \<le> j" using i_le_sj by simp
      hence "A i \<subseteq> A j" using mono by simp
      moreover have "A j \<subseteq> A (j+1)" using inc by simp
      ultimately show "A i \<subseteq> A (Suc j)" by simp
    qed
  qed
qed

lemma setseq_dec:
  assumes dec: "\<And>i::nat. A (i+1) \<subseteq> A i"
  shows "\<And>i j::nat. i \<le> j \<Longrightarrow> A j \<subseteq> A i"
proof-
  fix j::nat
  show "\<And>i. i \<le> j \<Longrightarrow> A j \<subseteq> A i"
  proof (induct j)
    fix i::nat
    assume "i \<le> 0"
    hence "i = 0" by simp
    thus "A 0 \<subseteq> A i" by simp
  next
    fix i j::nat
    assume mono: "\<And>i. i \<le> j \<Longrightarrow> A j \<subseteq> A i"
    assume i_le_sj: "i \<le> Suc j"
    show "A (Suc j) \<subseteq> A i"
    proof (cases "i = Suc j")
      assume "i = Suc j"
      thus "A (Suc j) \<subseteq> A i" by simp
    next
      assume "i \<noteq> Suc j"
      hence "i \<le> j" using i_le_sj by simp
      hence "A j \<subseteq> A i" using mono by simp
      moreover have "A (j+1) \<subseteq> A j" using dec by simp
      ultimately show "A (Suc j) \<subseteq> A i" by simp
    qed
  qed
qed

lemma indicator_cont_up:
  assumes inc: "\<And>i::nat. A i \<subseteq> A (i+1)"
  shows "\<And>x. (\<lambda>i::nat. (indicator (A i) x)::real) ----> indicator (\<Union>i. A i) x"
proof -
  fix x
  show "(\<lambda>i::nat. (indicator (A i) x)::real) ----> indicator (\<Union>i. A i) x"
    apply (rule metric_LIMSEQ_I)
  proof (cases "x \<in> (\<Union>i. A i)")
    fix r::real assume pos: "0 < r"
    assume elem: "x \<in> (\<Union>i. A i)"
    obtain i where inAi: "x \<in> A i" using UN_E elem by auto
    hence inAj: "\<And>j. i \<le> j \<Longrightarrow> x \<in> A j" using setseq_inc inc by auto
    have "\<forall>j \<ge> i. dist (indicator (A j) x) (indicator (\<Union>i. A i) x) < r"
    proof -
      { fix j::nat assume ge: "j \<ge> i"
        hence "indicator (A j) x = (1::real)" using inAi inAj by simp
        moreover have "indicator (\<Union>i. A i) x = (1::real)" using elem by simp
        ultimately have "((indicator (A j) x)::real) = indicator (\<Union>i. A i) x" by simp
      }
      thus "\<forall>j \<ge> i. dist (indicator (A j) x) (indicator (\<Union>i. A i) x) < r"
        using pos by (metis (full_types) dist_self elem inAj indicator_simps(1))
    qed
    thus "\<exists>no. \<forall>n\<ge>no. dist (indicator (A n) x) (indicator (\<Union>i. A i) x) < r" by auto
  next
    fix r::real assume pos: "0 < r"
    assume nelem: "x \<notin> (\<Union>i. A i)"
    hence notin: "\<And>i::nat. x \<notin> A i" by auto
    have "indicator (\<Union>i. A i) x = (0::real)" using nelem by simp
    moreover have "\<And>i::nat. indicator (A i) x = (0::real)" using notin by simp
    ultimately show "\<exists>no. \<forall>n \<ge> no. dist (indicator (A n) x) (indicator (\<Union>i. A i) x) < r"
      using pos by (metis dist_self indicator_simps(2) nelem notin)
  qed
qed

(** Also prove indicator_cont_down. **)
              
lemma tendsto_const_add:
  fixes a b :: "'a::real_normed_vector"
  assumes lim: "((\<lambda>x. a + f x) ---> a + b) F"
  shows "(f ---> b) F"
proof (rule tendstoI)
  fix e::real assume pos: "0 < e"
  have "eventually (\<lambda>x. dist (a + f x) (a + b) < e) F"
    by (auto intro: lim pos tendstoD)
  thus "eventually (\<lambda>x. dist (f x) b < e) F"
    by (metis (lifting, mono_tags) ab_group_add_class.add_diff_cancel_left
      dist_norm eventually_rev_mono)
qed

lemma tendsto_const_mult:
  fixes a b :: real
  assumes nonzero: "a \<noteq> 0"
  and lim: "((\<lambda>x. a * f x) ---> a * b) F"
  shows "(f ---> b) F"
proof (rule tendstoI)
  fix e::real assume pos: "0 < e"
  have ev: "eventually (\<lambda>x. dist (a * f x) (a * b) < e * \<bar>a\<bar>) F"
    apply (rule tendstoD[where e = "e * \<bar>a\<bar>"])
    apply (rule lim)
    by (metis mult_pos_pos nonzero pos zero_less_abs_iff)
  thus "eventually (\<lambda>x. dist (f x) b < e) F"
  proof-
    have eq: "(\<lambda>x. dist (a * f x) (a * b) < e * \<bar>a\<bar>) = (\<lambda>x. dist (f x) b < e)"
      apply (rule ext)
      apply (unfold dist_real_def)
      apply (subst linordered_field_class.sign_simps(6)[symmetric])
      apply (subst abs_mult)
      apply (subst mult_commute)
      by (simp add: nonzero)
    thus ?thesis
      apply (subst eq[symmetric])
      by (rule ev)
  qed
qed

lemma real_of_ereal_neq_0:
fixes x::ereal
assumes "real x \<noteq> 0"
shows "x = ereal (real x)"
by (metis assms ereal_eq_0(1) ereal_real)

(* Why aren't these in Set_Interval.thy?? *)
lemma setprod_atMost_Suc[simp]: "(\<Prod>i \<le> Suc n. f i) = (\<Prod>i \<le> n. f i) * f(Suc n)"
by (simp add:atMost_Suc mult_ac)

lemma setprod_lessThan_Suc[simp]: "(\<Prod>i < Suc n. f i) = (\<Prod>i < n. f i) * f n"
by (simp add:lessThan_Suc mult_ac)

lemma norm_triangle_ineq_setsum: "norm (\<Sum> i \<in> A. f i) \<le> (\<Sum> i \<in> A. norm (f i))"
apply (case_tac "finite A", auto)
apply (erule finite_induct, auto)
apply (rule order_trans)
apply (rule norm_triangle_ineq)
apply auto
done

lemma norm_setprod: "norm (\<Prod>i \<in> A. f i) = 
  (\<Prod> i \<in> A. norm ((f i) :: 'a :: {real_normed_div_algebra,comm_monoid_mult}))"
apply (case_tac "finite A", auto)
apply (erule finite_induct, auto simp add: norm_mult)
done

end