theory Library_Misc
imports Probability "~~/src/HOL/Library/ContNotDenum"
begin

(* Should work for more general types than reals? *)

lemma continuous_within_open: "a \<in> A \<Longrightarrow> open A \<Longrightarrow> continuous (at a within A) f \<longleftrightarrow> isCont f a"
  by (simp add: at_within_open_NO_MATCH)

lemma DERIV_image_chain': "(f has_field_derivative D) (at x within s) \<Longrightarrow> 
    (g has_field_derivative E) (at (f x) within (f ` s)) \<Longrightarrow> 
    ((\<lambda>x. g (f x)) has_field_derivative E * D) (at x within s)"
by (drule (1) DERIV_image_chain, simp add: comp_def)

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

lemma abs_bounds: "x \<le> y \<Longrightarrow> -x \<le> y \<Longrightarrow> abs (x :: ereal) \<le> y"
by (metis abs_ereal_ge0 abs_ereal_uminus ereal_0_le_uminus_iff linear)

lemma real_arbitrarily_close_eq:
  fixes x y :: real
  assumes "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> abs (x - y) \<le> \<epsilon>"
  shows "x = y"
by (metis abs_le_zero_iff assms dense_ge eq_iff_diff_eq_0)

end
