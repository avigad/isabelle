theory Uncountable

imports Distribution_Functions "~~/src/HOL/Library/ContNotDenum"

begin

(* "Countable" is defined in terms of injections; may want to revise definition of uncountable to
be \<not>countable, and make an abbreviation rather than a definition. *)
definition uncountable :: "'a set \<Rightarrow> bool" where
  "uncountable A \<equiv> A \<noteq> {} \<and> \<not>(\<exists>f::(nat \<Rightarrow> 'a). range f = A)"

lemma reals_uncountable: "uncountable (UNIV::real set)"
  using real_non_denum unfolding uncountable_def by auto

lemma uncountable_image: "uncountable (f ` A) \<Longrightarrow> uncountable A"
unfolding uncountable_def proof auto
  fix g :: "nat \<Rightarrow> 'b" assume "\<forall>h::(nat \<Rightarrow> 'a). range h \<noteq> f ` range g"
  hence "range (f \<circ> g) \<noteq> f ` range g" by auto
  thus False unfolding image_def by auto
qed

lemma uncountable_bij_betw: "bij_betw f A B \<Longrightarrow> uncountable B \<Longrightarrow> uncountable A"
  unfolding bij_betw_def by (metis uncountable_image)
  
lemma uncountable_infinite: "uncountable A \<Longrightarrow> infinite A"
unfolding uncountable_def proof auto
  fix x
  assume fA: "\<forall>f::(nat \<Rightarrow> 'a). range f \<noteq> A" and A: "finite A" and x: "x \<in> A"
  hence nonempty: "A \<noteq> {}" by auto
  def f \<equiv> "from_nat_into A"
  have "range f = A"
    unfolding f_def using nonempty by (metis A countable_finite range_from_nat_into)
  thus False using fA by auto
qed

lemma uncountable_not_countable: "uncountable A = (\<not> countable A)"
  unfolding uncountable_def countable_def apply auto
  apply (metis all_not_in_conv inj_on_iff_surj subset_UNIV)
  by (metis image_subsetI inj_on_inv_into rangeI)
  
lemma uncountable_minus_countable:
  fixes A B
  assumes "uncountable A" "countable B"
  shows "uncountable (A - B)"
apply (subst uncountable_not_countable)
proof (rule ccontr, auto)
  assume "countable (A - B)"
  with assms(2) have "countable ((A - B) \<union> B)" using countable_Un by blast
  with assms(1) show False by (metis Un_Diff_cancel2 countable_Un_iff uncountable_not_countable)
qed

lemma bij_betw_open_intervals:
  fixes a b c d :: real
  assumes "a < b" "c < d"
  shows "\<exists>f. bij_betw f {a<..<b} {c<..<d}"
proof -
  def f \<equiv> "\<lambda>x::real. (d - c)/(b - a) * (x - a) + c"
  def g \<equiv> "\<lambda>x::real. (b - a)/(d - c) * (x - c) + a"
  have "bij_betw f {a<..<b} {c<..<d}"
    apply (unfold bij_betw_def)
    apply (unfold inj_on_def)
    apply auto
    unfolding f_def using assms apply simp_all
    using assms apply (metis comm_monoid_add_class.add.left_neutral divide_divide_eq_right
      linordered_field_class.sign_simps(3) zero_less_divide_iff)
    apply (subst add_less_cancel_right[of _ "-c" _, symmetric], simp)
    apply (subst mult_less_cancel_left_pos[of "b - a" _ _, symmetric])
    using assms(1) apply simp
    apply simp
    unfolding image_def apply auto
    apply (unfold Bex_def, subst greaterThanLessThan_iff)
    apply (rule_tac x = "g x" in exI)
    unfolding g_def apply (auto simp:)
    using assms apply (metis diff_less_iff(1) divide_pos_pos mult_pos_pos)
    apply (subst add_less_cancel_right[of _ "-a" _, symmetric], simp)
    apply (subst mult_less_cancel_left_pos[of "d - c" _ _, symmetric])
    using assms by auto
  thus ?thesis by auto
qed

lemma open_interval_uncountable: "\<And>a b::real. a < b \<Longrightarrow> uncountable {a<..<b}"
proof -
  fix a b :: real assume ab: "a < b"
  from ab bij_betw_open_intervals[of a b "-pi/2" "pi/2"] guess f by auto note f = this
  from lemma_tan_total1 have "tan ` {-pi/2<..<pi/2} = UNIV"
    unfolding image_def Bex_def apply (subst greaterThanLessThan_iff)
    by (metis (lifting, mono_tags) UNIV_eq_I mem_Collect_eq minus_divide_left)
  hence "uncountable {-pi/2<..<pi/2}" using uncountable_image reals_uncountable by metis
  with f uncountable_bij_betw show "uncountable {a<..<b}" by auto
qed

end
