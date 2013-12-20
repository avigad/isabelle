theory Library_Misc
imports Complex_Main Distributions

begin

(** General miscellaneous. **)

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

lemma norm_setprod: "norm (\<Prod>i \<in> A. f i) = 
  (\<Prod> i \<in> A. norm ((f i) :: 'a :: {real_normed_div_algebra,comm_monoid_mult}))"
apply (case_tac "finite A", auto)
apply (erule finite_induct, auto simp add: norm_mult)
done

(** Miscellany from Helly. **)

(* This should have been in the library, like convergent_limsup_cl. *)
lemma convergent_liminf_cl:
  fixes X :: "nat \<Rightarrow> 'a::{complete_linorder,linorder_topology}"
  shows "convergent X \<Longrightarrow> liminf X = lim X"
  by (auto simp: convergent_def limI lim_imp_Liminf)

primrec halfseq :: "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  "halfseq l a0 0 = a0"
| "halfseq l a0 (Suc n) = (halfseq l a0 n + l) / 2"

lemma halfseq_converges: "halfseq l a0 ----> l"
proof -
  let ?a = "halfseq l a0"
  {
    fix n
    have "dist (?a n) l = dist a0 l / 2^n"
      by (induct n, auto simp add: dist_real_def field_simps)
  } note dist_a = this
  show ?thesis
  proof (rule metric_LIMSEQ_I)
    fix r :: real
    assume [simp]: "r > 0"
    from reals_Archimedean2 [of "dist a0 l / r"] guess n .. 
    with `r > 0` have 2: "dist a0 l < r * n" by (simp add: field_simps)
    have "(dist a0 l) / 2^n < r"
      apply (auto simp add: field_simps)
      apply (rule order_less_trans, rule 2)
      by (rule mult_strict_left_mono, simp_all)
    hence "\<forall>m\<ge>n. dist (halfseq l a0 m) l < r"
      apply (auto simp add: dist_a)
      apply (rule order_le_less_trans)
      prefer 2 apply assumption
      by (auto simp add: field_simps intro!: mult_left_mono)
    thus "\<exists>n. \<forall>m\<ge>n. dist (halfseq l a0 m) l < r" ..
  qed
qed

lemma real_Inf_greatest': 
  fixes A and x :: real 
  assumes "A \<noteq> {}" "bdd_below A" and 1: "x > Inf A" 
  shows "\<exists>y \<in> A. y \<le> x"
apply (rule contrapos_pp [OF 1], simp add: not_less not_le)
using assms cInf_greatest le_less by metis

lemma bdd_below_closure:
  fixes A :: "real set"
  assumes "bdd_below A"
  shows "bdd_below (closure A)"
proof -
  from assms obtain m where "\<And>x. x \<in> A \<Longrightarrow> m \<le> x" unfolding bdd_below_def by auto
  hence "A \<subseteq> {m..}" by auto
  hence "closure A \<subseteq> {m..}" using closed_real_atLeast closure_minimal by auto
  thus ?thesis unfolding bdd_below_def by auto
qed

lemma real_closed_subset_contains_Inf:
  fixes A C :: "real set"
  assumes cl: "closed C" and A: "A \<subseteq> C"
  and nonempty: "A \<noteq> {}" and bdd_below: "bdd_below A"
  shows "Inf A \<in> C"
proof -
  have "closure A \<subseteq> C" using closure_minimal assms by auto
  thus ?thesis
    apply (elim subsetD)
    apply (rule closure_contains_Inf)
    using assms by auto
qed

(* Should this definition be eliminated? **)
definition rcont_inc :: "(real \<Rightarrow> real) \<Rightarrow> bool"
  where "rcont_inc f \<equiv> (\<forall>x. continuous (at_right x) f) \<and> mono f"

lemma real_atLeastAtMost_subset_contains_Inf:
  fixes A :: "real set" and a b :: real assumes "A \<noteq> {}" and "bdd_below A"
  and "a \<le> b" and "A \<subseteq> {a..b}"
  shows "Inf A \<in> {a..b}"
by (rule real_closed_subset_contains_Inf, rule closed_real_atLeastAtMost) (simp_all add: assms)

lemma rat_unbounded: "\<exists> q \<in> \<rat>. (x :: real) \<le> q"
  apply (rule_tac x = "of_nat (natceiling x)" in bexI, auto)
by (metis real_natceiling_ge real_of_nat_def)

lemma f_inv_f_surj_on: "f ` A = B \<Longrightarrow> x \<in> B \<Longrightarrow> f (inv f x) = x"
  apply auto
  unfolding inv_def by (rule someI_ex, auto)

lemma dist_epsilon: "\<forall>\<epsilon>>0. dist x y < \<epsilon> \<Longrightarrow> x = y" using dist_pos_lt less_irrefl by auto

lemma ereal_dist_epsilon:
  assumes "\<forall>(\<epsilon>::real)>0. \<bar>x - ereal r\<bar> < \<epsilon>"
  shows "x = ereal r"
proof (rule ereal_cases[of x])
  fix t assume x: "x = ereal t"
  { fix \<epsilon>::real assume \<epsilon>: "\<epsilon> > 0"
    hence "\<bar>ereal t - ereal r\<bar> < \<epsilon>" using assms x \<epsilon> by auto
    hence "dist t r < \<epsilon>" unfolding dist_real_def by auto
  }
  hence "ereal t = ereal r" using dist_epsilon by auto
  thus ?thesis using x by simp
next
  assume "x = \<infinity>"
  hence "\<bar>x - ereal r\<bar> = \<infinity>" by auto
  hence "\<not> \<bar>x - ereal r\<bar> < ereal 1" by auto
  hence False using assms by auto
  thus ?thesis ..
next (* Duplication; how to avoid? *)
  assume "x = -\<infinity>"
  hence "\<bar>x - ereal r\<bar> = \<infinity>" by auto
  hence "\<not> \<bar>x - ereal r\<bar> < ereal 1" by auto
  hence False using assms by auto
  thus ?thesis ..
qed

lemma lim_close_limsup_liminf:
  fixes a :: "nat \<Rightarrow> ereal" and L :: real
  assumes "\<forall>(e::real)>0. \<bar>limsup a - L\<bar> < e \<and> \<bar>L - liminf a\<bar> < e"
  shows "convergent a" and "lim a = L"
proof -
  have lsup: "limsup a = L" using ereal_dist_epsilon assms by auto
  also have "L = liminf a"
  proof -
    have "\<And>n::nat. n > 0 \<Longrightarrow> \<bar>L - liminf a\<bar> < inverse n" using assms
      by (metis inverse_positive_iff_positive real_of_nat_gt_zero_cancel_iff)
    hence 1: "\<bar>L - liminf a\<bar> = 0"
      using ereal_dist_epsilon by (metis abs_ereal_zero assms ereal_minus(7) zero_ereal_def)
    show ?thesis
    proof -
      have "\<bar>liminf a\<bar> < \<infinity>" using 1
        by (metis PInfty_neq_ereal(1) abs_eq_infinity_cases abs_ereal_uminus add_commute ereal_less_PInfty ereal_minus(3)
            minus_ereal_def plus_ereal.simps(2) zero_ereal_def)  
      then obtain linf where linf: "ereal linf = liminf a" by auto
      hence "\<bar>L - linf\<bar> = 0" using 1 by (metis abs_ereal.simps(1) ereal_eq_0(2) ereal_minus(1))
      hence "linf = L" by auto
      thus ?thesis using linf by auto
    qed
  qed
  finally have "limsup a = liminf a" by simp
  thus "convergent a" using convergent_ereal by auto
  hence "limsup a = lim a" using convergent_limsup_cl by auto
  thus "lim a = L" using lsup by simp
qed

lemma convergent_real_imp_convergent_ereal:
  assumes "convergent a"
  shows "convergent (\<lambda>n. ereal (a n))" and "lim (\<lambda>n. ereal (a n)) = ereal (lim a)"
proof -
  from assms obtain L where L: "a ----> L" unfolding convergent_def ..
  hence lim: "(\<lambda>n. ereal (a n)) ----> ereal L" using lim_ereal by auto
  thus "convergent (\<lambda>n. ereal (a n))" unfolding convergent_def ..
  thus "lim (\<lambda>n. ereal (a n)) = ereal (lim a)" using lim L limI by metis
qed

lemma ereal_not_infty:
  fixes x :: ereal and B :: real
  assumes "x \<le> ereal B"
  shows "x \<noteq> \<infinity>"
by (metis PInfty_neq_ereal(1) assms ereal_infty_less_eq(1))

lemma abs_bounds: "x \<le> y \<Longrightarrow> -x \<le> y \<Longrightarrow> abs (x :: ereal) \<le> y"
by (metis abs_ereal_ge0 abs_ereal_uminus ereal_0_le_uminus_iff linear)

(** From Weak_Convergence **)

(***
(* Want to port this from proof of Skorohod, but not clear what the right generalization is. *)
lemma bdd_rcont_inc_almost_inverse:
  fixes F :: "real \<Rightarrow> real"
  fixes M :: real
  assumes "rcont_inc F" and "\<And>x. \<bar>F x\<bar> \<le> M"
  defines "Y \<equiv> \<lambda>\<omega>. Inf {x. \<omega> \<le> F x}"
  shows "\<And>\<omega> x. (\<omega> \<le> F x) = (Y \<omega> \<le> x)"
  proof safe
    fix n::nat fix \<omega> x :: real
    {
      assume "\<omega> \<le> F x"
      hence "x \<in> {x. \<omega> \<le> F x}" by auto
      hence "Inf {x. \<omega> \<le> F x} \<le> x"
        using cInf_lower assms(2) 
      thus "Y_seq n \<omega> \<le> x" unfolding Y_seq_def by simp
    }
    {
      assume "Y_seq n \<omega> \<le> x"
      hence x_less: "\<forall>y \<in> {0<..<1}. x < y \<longrightarrow> \<omega> \<le> f n y"
        apply (unfold Y_seq_def)
        apply safe
      proof -
        fix y assume x: "Inf ({x. \<omega> \<le> f n x} \<inter> {0<..<1}) \<le> x" and y: "y \<in> {0<..<1}" "x < y"
        show "\<omega> \<le> f n y"
        proof (rule ccontr)
          assume "\<not> \<omega> \<le> f n y"
          hence "f n y < \<omega>" by simp
          hence le: "\<And>z. z \<le> y \<Longrightarrow> f n z < \<omega>" using f_inc le_less_trans unfolding mono_def by metis
          have "y \<le> Inf ({x. \<omega> \<le> f n x} \<inter> {0<..<1})"
            apply (rule cInf_greatest)
            prefer 2 using le
            apply (metis (lifting) Int_Collect inf_sup_aci(1) le_cases max.semilattice_strict_iff_order not_less_iff_gr_or_eq)
            using interval(1) real_distribution.cdf_lim_at_top_prob sorry
          hence "y \<le> x" using x by simp
          thus False using y by simp
        qed
      qed
      show "\<omega> \<le> f n x"
      proof (rule field_le_epsilon)
        fix e::real assume e: "0 < e"
        hence "\<exists>d>0. f n (x + d) - f n x < e"
          using continuous_at_right_real_increasing f_inc f_right_cts unfolding mono_def by auto
        then guess d .. note d = this
        have "\<exists>w. 0 < w \<and> w < 1 - x" using interval(2)
          (*by (metis diff_0 diff_less_iff(2) greaterThanLessThan_iff minus_diff_eq real_lbound_gt_zero)*)
        then guess w .. note w = this
        def \<delta> \<equiv> "min d w"
        have \<delta>: "\<delta> > 0" "f n (x + \<delta>) - f n x < e" "x + \<delta> \<in> {0<..<1}"
        proof -
          from d w show "\<delta> > 0" unfolding \<delta>_def by auto
          have "x + \<delta> \<le> x + d" unfolding \<delta>_def by auto
          hence "f n (x + \<delta>) \<le> f n (x + d)" using f_inc unfolding mono_def by auto
          thus "f n (x + \<delta>) - f n x < e" using d by simp
          from w have "x < x + w \<and> x + w < 1" by simp
          hence "x < x + \<delta> \<and> x + \<delta> < 1" using d w unfolding \<delta>_def by auto
          thus "x + \<delta> \<in> {0<..<1}" using interval(2) by auto
        qed
        hence "\<omega> \<le> f n (x + \<delta>)" using x_less \<delta> by auto
        thus "\<omega> \<le> f n x + e" using \<delta>(2) by simp
      qed
    }
  qed
***)

end