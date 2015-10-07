theory Library_Misc
imports Probability "~~/src/HOL/Library/ContNotDenum"
begin

abbreviation exterior :: "'a::{topological_space} set \<Rightarrow> 'a set" where
  "exterior A \<equiv> interior (-A)"

lemma partition_interior_frontier_exterior:
  fixes X :: "'a::{topological_space}"
    and A :: "'a set"
  shows "UNIV = interior A \<union> frontier A \<union> exterior A"
proof auto
  fix x
  assume ext: "x \<notin> exterior A" and fr: "x \<notin> frontier A"
  show "x \<in> interior A"
  proof -
    from ext closure_interior have "x \<in> closure A" by auto
    thus ?thesis using fr unfolding frontier_def by auto
  qed
qed

lemma isCont_indicator: 
  fixes x :: "'a::t2_space"
  shows "isCont (indicator A :: 'a \<Rightarrow> real) x = (x \<notin> frontier A)"
proof auto
  fix x
  assume cts_at: "isCont (indicator A :: 'a \<Rightarrow> real) x" and fr: "x \<in> frontier A"
  with continuous_at_open have 1: "\<forall>V::real set. open V \<and> indicator A x \<in> V \<longrightarrow>
    (\<exists>U::'a set. open U \<and> x \<in> U \<and> (\<forall>y\<in>U. indicator A y \<in> V))" by auto
  show False
  proof (cases "x \<in> A")
    assume x: "x \<in> A"
    hence "indicator A x \<in> ({0<..<2} :: real set)" by simp
    hence "\<exists>U. open U \<and> x \<in> U \<and> (\<forall>y\<in>U. indicator A y \<in> ({0<..<2} :: real set))"
      using 1 open_greaterThanLessThan by blast
    then guess U .. note U = this
    hence "\<forall>y\<in>U. indicator A y > (0::real)"
      unfolding greaterThanLessThan_def by auto
    hence "U \<subseteq> A" using indicator_eq_0_iff by force
    hence "x \<in> interior A" using U interiorI by auto
    thus ?thesis using fr unfolding frontier_def by simp
  next
    assume x: "x \<notin> A"
    hence "indicator A x \<in> ({-1<..<1} :: real set)" by simp
    hence "\<exists>U. open U \<and> x \<in> U \<and> (\<forall>y\<in>U. indicator A y \<in> ({-1<..<1} :: real set))"
      using 1 open_greaterThanLessThan by blast
    then guess U .. note U = this
    hence "\<forall>y\<in>U. indicator A y < (1::real)"
      unfolding greaterThanLessThan_def by auto
    hence "U \<subseteq> -A" by auto
    hence "x \<in> exterior A" using U interiorI by auto
    thus ?thesis using fr interior_complement unfolding frontier_def by auto
  qed
next
  assume nfr: "x \<notin> frontier A"
  hence "x \<in> interior A \<or> x \<in> exterior A" using partition_interior_frontier_exterior by auto
  thus "isCont ((indicator A)::'a \<Rightarrow> real) x"
  proof
    assume int: "x \<in> interior A"
    hence "\<exists>U. open U \<and> x \<in> U \<and> U \<subseteq> A" unfolding interior_def by auto
    then guess U .. note U = this
    hence "\<forall>y\<in>U. indicator A y = (1::real)" unfolding indicator_def by auto
    hence "continuous_on U (indicator A)" by (simp add: continuous_on_const indicator_eq_1_iff)
    thus ?thesis using U continuous_on_eq_continuous_at by auto
  next
    assume ext: "x \<in> exterior A"
    hence "\<exists>U. open U \<and> x \<in> U \<and> U \<subseteq> -A" unfolding interior_def by auto
    then guess U .. note U = this
    hence "\<forall>y\<in>U. indicator A y = (0::real)" unfolding indicator_def by auto
    hence "continuous_on U (indicator A)" by (smt U continuous_on_topological indicator_def)
    thus ?thesis using U continuous_on_eq_continuous_at by auto
  qed
qed

(* Should work for more general types than reals? *)

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
  thus ?thesis
    by auto
qed

lemma borel_measurable_mono:
  fixes f :: "real \<Rightarrow> real"
  assumes "mono f"
  shows "f \<in> borel_measurable borel"
proof (subst borel_measurable_iff_ge, auto simp add:)
  fix a :: real
  have "is_interval {w. a \<le> f w}"
    unfolding is_interval_1 using assms by (auto dest: monoD intro: order.trans)
  thus "{w. a \<le> f w} \<in> sets borel" using real_interval_borel_measurable by auto  
qed

lemma continuous_within_open: "a \<in> A \<Longrightarrow> open A \<Longrightarrow> (continuous (at a within A) f) = isCont f a"
  by (simp add: continuous_within, rule Lim_within_open)

lemma has_vector_derivative_weaken:
  fixes x D and f g s t
  assumes f: "(f has_vector_derivative D) (at x within t)"
    and "x \<in> s" "s \<subseteq> t" 
    and "\<And>x. x \<in> s \<Longrightarrow> f x = g x"
  shows "(g has_vector_derivative D) (at x within s)"
proof -
  have "(f has_vector_derivative D) (at x within s) \<longleftrightarrow> (g has_vector_derivative D) (at x within s)"
    unfolding has_vector_derivative_def has_derivative_iff_norm
    using assms by (intro conj_cong Lim_cong_within refl) auto
  then show ?thesis
    using has_vector_derivative_within_subset[OF f `s \<subseteq> t`] by simp
qed

lemma DERIV_image_chain': "(f has_field_derivative D) (at x within s) \<Longrightarrow> 
    (g has_field_derivative E) (at (f x) within (f ` s)) \<Longrightarrow> 
    ((\<lambda>x. g (f x)) has_field_derivative E * D) (at x within s)"
by (drule (1) DERIV_image_chain, simp add: comp_def)

(* This should have been in the library, like convergent_limsup_cl. *)
lemma convergent_liminf_cl:
  fixes X :: "nat \<Rightarrow> 'a::{complete_linorder,linorder_topology}"
  shows "convergent X \<Longrightarrow> liminf X = lim X"
  by (auto simp: convergent_def limI lim_imp_Liminf)

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

lemma closed_subset_contains_Inf:
  fixes A C :: "real set"
  shows "closed C \<Longrightarrow> A \<subseteq> C \<Longrightarrow> A \<noteq> {} \<Longrightarrow> bdd_below A \<Longrightarrow> Inf A \<in> C"
  by (metis closure_contains_Inf closure_minimal subset_eq)

lemma atLeastAtMost_subset_contains_Inf:
  fixes A :: "real set" and a b :: real 
  shows "A \<noteq> {} \<Longrightarrow> a \<le> b \<Longrightarrow> A \<subseteq> {a..b} \<Longrightarrow> Inf A \<in> {a..b}"
  by (rule closed_subset_contains_Inf) 
     (auto intro: closed_real_atLeastAtMost intro!: bdd_belowI[of A a])

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

lemma real_arbitrarily_close_eq:
  fixes x y :: real
  assumes "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> abs (x - y) \<le> \<epsilon>"
  shows "x = y"
by (metis abs_le_zero_iff assms dense_ge eq_iff_diff_eq_0)

lemma real_interval_avoid_countable_set:
  fixes a b :: real and A :: "real set"
  assumes "a < b" and "countable A"
  shows "\<exists>x. x \<in> {a<..<b} \<and> x \<notin> A"
proof -
  from `countable A` have "countable (A \<inter> {a<..<b})" by auto
  moreover with `a < b` have "\<not> countable {a<..<b}" 
    by (simp add: uncountable_open_interval)
  ultimately have "A \<inter> {a<..<b} \<noteq> {a<..<b}" by auto
  hence "A \<inter> {a<..<b} \<subset> {a<..<b}" 
    by (intro psubsetI, auto)
  hence "\<exists>x. x \<in> {a<..<b} - A \<inter> {a<..<b}"
    by (rule psubset_imp_ex_mem)
  thus ?thesis by auto
qed

lemma frontier_real_Iic:
  fixes a :: real
  shows "frontier {..a} = {a}"
  unfolding frontier_def by (auto simp add: interior_real_semiline')

end