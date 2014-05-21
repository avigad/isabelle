theory Library_Misc
imports Distribution_Functions

begin

(** General miscellaneous. **)

(* This should be easy. *)
lemma ereal_le_epsilon_iff2: "(\<forall>\<epsilon>>0. x \<le> y + ereal \<epsilon>) = (x \<le> y)" using ereal_le_epsilon2
by (metis add_commute add_right_mono dual_order.trans ereal_less(2) less_eq_ereal_def
    monoid_add_class.add.left_neutral)

lemma inj_on_infinite: "infinite A \<Longrightarrow> inj_on f A \<Longrightarrow> infinite (range f)"
  by (metis finite_imageD image_mono rev_finite_subset top_greatest)

lemma real_rats_infinite: "infinite \<rat>"
  apply (subst Rats_def)
  apply (rule inj_on_infinite)
  apply (rule infinite_UNIV_char_0)
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

(*
lemma setseq_inc:
  "(\<And>i::nat. A i \<subseteq> A (i+1)) \<Longrightarrow> i \<le> j \<Longrightarrow> A i \<subseteq> A j"
  by (rule lift_Suc_mono_le) simp_all

lemma setseq_dec:
  assumes dec: "\<And>i::nat. A (i+1) \<subseteq> A i" "i \<le> j"
  shows "A j \<subseteq> A i"
  using assms(2,1)
  by (induct rule: dec_induct) auto
*)

lemma indicator_cont_up:
  assumes inc: "\<And>i::nat. A i \<subseteq> A (i+1)"
  shows "(\<lambda>i::nat. (indicator (A i) x)::real) ----> indicator (\<Union>i. A i) x"
  using LIMSEQ_indicator_UN
proof -
  have "\<And>i j. i \<le> j \<Longrightarrow> A i \<subseteq> A j"
    by (rule lift_Suc_mono_le, rule assms [simplified]) 
  then have "\<And>k. (\<Union> i<Suc k. A i) = A k"
    by (force simp: less_Suc_eq_le)
  with LIMSEQ_indicator_UN[of A x, THEN LIMSEQ_Suc]
  show ?thesis
    by simp
qed

(** Also prove indicator_cont_down. **)
              
lemma tendsto_const_add:
  fixes a b :: "'a::real_normed_vector"
  assumes "((\<lambda>x. a + f x) ---> a + b) F"
  shows "(f ---> b) F"
proof -
  have "((\<lambda>x. (a + f x) - a) ---> (a + b) - a) F"
    by (intro tendsto_diff tendsto_const assms)
  then show ?thesis
    by simp
qed

lemma tendsto_const_mult:
  fixes a b :: real
  assumes nonzero: "a \<noteq> 0"
  and lim: "((\<lambda>x. a * f x) ---> a * b) F"
  shows "(f ---> b) F"
proof -
  have "((\<lambda>x. (a * f x) / a) ---> (a * b) / a) F"
    by (intro tendsto_divide tendsto_const assms)
  with nonzero show ?thesis
    by simp
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

(* Perhaps generalize to arbitrary T1 spaces *)
lemma lborel_countable:
  fixes A M
  assumes "\<And>a. a\<in>A \<Longrightarrow> {a} \<in> sets M" "countable A"
  shows "A \<in> sets M"
proof -
  have "(\<Union>a\<in>A. {a}) \<in> sets M"
    using assms by (intro sets.countable_UN') auto
  also have "(\<Union>a\<in>A. {a}) = A" by auto
  finally show ?thesis by auto
qed

(* This should have been in the library, like convergent_limsup_cl. *)
lemma convergent_liminf_cl:
  fixes X :: "nat \<Rightarrow> 'a::{complete_linorder,linorder_topology}"
  shows "convergent X \<Longrightarrow> liminf X = lim X"
  by (auto simp: convergent_def limI lim_imp_Liminf)

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

lemma convergent_real_imp_convergent_ereal:
  assumes "convergent a"
  shows "convergent (\<lambda>n. ereal (a n))" and "lim (\<lambda>n. ereal (a n)) = ereal (lim a)"
proof -
  from assms obtain L where L: "a ----> L" unfolding convergent_def ..
  hence lim: "(\<lambda>n. ereal (a n)) ----> ereal L" using lim_ereal by auto
  thus "convergent (\<lambda>n. ereal (a n))" unfolding convergent_def ..
  thus "lim (\<lambda>n. ereal (a n)) = ereal (lim a)" using lim L limI by metis
qed

lemma abs_bounds: "x \<le> y \<Longrightarrow> -x \<le> y \<Longrightarrow> abs (x :: ereal) \<le> y"
by (metis abs_ereal_ge0 abs_ereal_uminus ereal_0_le_uminus_iff linear)

lemma interval_cases:
  fixes S :: "'a :: conditionally_complete_linorder set"
  assumes ivl: "\<And>a b x. a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> x \<in> S"
  shows "\<exists>a b. S = {} \<or> S = UNIV \<or> S = {..<b} \<or> S = {..b} \<or> S = {a<..} \<or> S = {a..} \<or>
    S = {a<..<b} \<or> S = {a<..b} \<or> S = {a..<b} \<or> S = {a..b}"
proof -
  def lower \<equiv> "{x. \<exists>s\<in>S. s \<le> x}" and upper \<equiv> "{x. \<exists>s\<in>S. x \<le> s}"
  with ivl have "S = lower \<inter> upper"
    by auto
  moreover 
  have "\<exists>a. upper = UNIV \<or> upper = {} \<or> upper = {.. a} \<or> upper = {..< a}"
  proof cases
    assume *: "bdd_above S \<and> S \<noteq> {}"
    from * have "upper \<subseteq> {.. Sup S}"
      by (auto simp: upper_def intro: cSup_upper2)
    moreover from * have "{..< Sup S} \<subseteq> upper"
      by (force simp add: less_cSup_iff upper_def subset_eq Ball_def)
    ultimately have "upper = {.. Sup S} \<or> upper = {..< Sup S}"
      unfolding ivl_disj_un(2)[symmetric] by auto
    then show ?thesis by auto
  next
    assume "\<not> (bdd_above S \<and> S \<noteq> {})"
    then have "upper = UNIV \<or> upper = {}"
      by (auto simp: upper_def bdd_above_def not_le dest: less_imp_le)
    then show ?thesis
      by auto
  qed
  moreover
  have "\<exists>b. lower = UNIV \<or> lower = {} \<or> lower = {b ..} \<or> lower = {b <..}"
  proof cases
    assume *: "bdd_below S \<and> S \<noteq> {}"
    from * have "lower \<subseteq> {Inf S ..}"
      by (auto simp: lower_def intro: cInf_lower2)
    moreover from * have "{Inf S <..} \<subseteq> lower"
      by (force simp add: cInf_less_iff lower_def subset_eq Ball_def)
    ultimately have "lower = {Inf S ..} \<or> lower = {Inf S <..}"
      unfolding ivl_disj_un(1)[symmetric] by auto
    then show ?thesis by auto
  next
    assume "\<not> (bdd_below S \<and> S \<noteq> {})"
    then have "lower = UNIV \<or> lower = {}"
      by (auto simp: lower_def bdd_below_def not_le dest: less_imp_le)
    then show ?thesis
      by auto
  qed
  ultimately show ?thesis
    unfolding greaterThanAtMost_def greaterThanLessThan_def atLeastAtMost_def atLeastLessThan_def
    by (elim exE disjE) auto
qed

lemma is_real_interval:
  assumes S: "is_interval S"
  shows "\<exists>a b::real. S = {} \<or> S = UNIV \<or> S = {..<b} \<or> S = {..b} \<or> S = {a<..} \<or> S = {a..} \<or>
    S = {a<..<b} \<or> S = {a<..b} \<or> S = {a..<b} \<or> S = {a..b}"
  using S unfolding is_interval_1 by (blast intro: interval_cases)

lemma real_interval_borel_measurable:
  assumes "is_interval (S::real set)"
  shows "S \<in> sets borel"
proof -
  from assms is_real_interval have "\<exists>a b::real. S = {} \<or> S = UNIV \<or> S = {..<b} \<or> S = {..b} \<or>
    S = {a<..} \<or> S = {a..} \<or> S = {a<..<b} \<or> S = {a<..b} \<or> S = {a..<b} \<or> S = {a..b}" by auto
  then guess a ..
  then guess b ..
  thus ?thesis by (metis atLeastAtMost_borel atLeastLessThan_borel atMost_borel eucl_ivals(5)
    greaterThanAtMost_borel greaterThanLessThan_borel greaterThan_borel lessThan_borel sets.empty_sets
    space_in_borel)
qed

(* Should work for more general types than reals? *)
lemma borel_measurable_mono_fnc:
  fixes f :: "real \<Rightarrow> real"
  assumes "mono f"
  shows "f \<in> borel_measurable borel"
proof (subst borel_measurable_iff_ge, auto simp add:)
  fix a :: real
  have "is_interval {w. a \<le> f w}" using is_interval_1 assms(1) order.trans unfolding mono_def
    by (auto simp add:,  metis)
  thus "{w. a \<le> f w} \<in> sets borel" using real_interval_borel_measurable by auto  
qed

(* Not needed for our formalization, but perhaps useful. *)
lemma lim_eventually_le: "convergent f \<Longrightarrow> (eventually (\<lambda>n. f n \<le> (x::'a::linorder_topology)) sequentially) \<Longrightarrow> lim f \<le> x"
proof (subst (asm) eventually_sequentially)
  assume cnv: "convergent f" and fx: "\<exists>N. \<forall>n\<ge>N. f n \<le> x"
  from fx guess N .. note N = this
  let ?g = "\<lambda>n. f (n + N)"
  have g: "convergent ?g" "lim ?g = lim f"
    using cnv unfolding convergent_def apply (metis LIMSEQ_ignore_initial_segment)
    using cnv unfolding lim_def by (metis LIMSEQ_ignore_initial_segment LIMSEQ_offset)
  moreover have "lim ?g \<le> x"
    by (rule lim_le) (auto simp add: g(1) N)
  ultimately show "lim f \<le> x" using g(2) by simp
qed

end