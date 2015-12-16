(***************************************************************************************************

Title    : Distribution_Functions.thy
Authors  : Jeremy Avigad and Luke Serafin

Shows that the cumulative distribution function (cdf) of a distribution (a measure on the reals) is 
nondecreasing and right continuous, which tends to 0 and 1 in either direction.

Conversely, every such function is the cdf of a unique distribution. This direction defines the 
measure in the obvious way on half-open intervals, and then applies the Caratheodory extension 
theorem.

TODO: the locales "finite_borel_measure" and "real_distribution" are defined here, but maybe they
 should be somewhere else.

***************************************************************************************************)

theory Distribution_Functions

imports Probability Library_Misc

begin

subsection {* Properties of cdf's *}

definition
  cdf :: "real measure \<Rightarrow> real \<Rightarrow> real"
where
  "cdf M \<equiv> \<lambda>x. measure M {..x}"

lemma cdf_def2: "cdf M x = measure M {..x}" by (simp add: cdf_def)

locale finite_borel_measure = finite_measure M for M :: "real measure" +
  assumes M_super_borel: "sets borel \<subseteq> sets M"
begin

lemma [intro]: "a \<in> sets borel \<Longrightarrow> a \<in> sets M"
  using M_super_borel by auto

lemma cdf_diff_eq: 
  assumes "x < y"
  shows "cdf M y - cdf M x = measure M {x<..y}"
proof -
  from assms have *: "{..x} \<union> {x<..y} = {..y}" by auto
  have "measure M {..y} = measure M {..x} + measure M {x<..y}"
    by (subst finite_measure_Union [symmetric], auto simp add: *)
  thus ?thesis
    unfolding cdf_def by auto
qed

lemma cdf_nondecreasing [rule_format]: "(\<forall>x y. x \<le> y \<longrightarrow> cdf M x \<le> cdf M y)"
  unfolding cdf_def by (auto intro!: finite_measure_mono)

lemma borel_UNIV: "space M = UNIV"
 by (metis in_mono sets.sets_into_space space_in_borel top_le M_super_borel)
 
lemma cdf_nonneg: "cdf M x \<ge> 0"
  unfolding cdf_def by (rule measure_nonneg)

lemma cdf_bounded: "cdf M x \<le> measure M (space M)"
  unfolding cdf_def using assms by (intro bounded_measure)

lemma cdf_lim_infty:
  "((\<lambda>i. cdf M (real i)) ----> measure M (space M))"
proof -
  have "(%i. cdf M (real i)) ----> measure M (\<Union> i::nat. {..real i})"
    unfolding cdf_def by (rule finite_Lim_measure_incseq) (auto simp: incseq_def)
  also have "(\<Union> i::nat. {..real i}) = space M"
    by (auto simp: borel_UNIV intro: real_arch_simple)
  finally show ?thesis .
qed

lemma cdf_lim_at_top: "(cdf M ---> measure M (space M)) at_top" 
  apply (rule tendsto_at_topI_sequentially_real)
  apply (simp_all add: mono_def cdf_nondecreasing cdf_lim_infty)
  done

lemma cdf_lim_neg_infty: "((\<lambda>i. cdf M (- real i)) ----> 0)" 
proof -
  have "(\<lambda>i. cdf M (- real i)) ----> measure M (\<Inter> i::nat. {.. - real i })"
    unfolding cdf_def by (rule finite_Lim_measure_decseq) (auto simp: decseq_def)
  also have "(\<Inter> i::nat. {..- real i}) = {}"
    by auto (metis leD le_minus_iff reals_Archimedean2)
  finally show ?thesis
    by simp
qed

lemma cdf_lim_at_bot: "(cdf M ---> 0) at_bot"
proof - 
  have 1: "((%x :: real. - cdf M (- x)) ---> 0) at_top"
    apply (rule tendsto_at_topI_sequentially_real)
    apply (auto simp add: mono_def cdf_nondecreasing cdf_lim_neg_infty)
    using cdf_lim_neg_infty by (metis minus_zero tendsto_minus_cancel_left)
  from filterlim_compose [OF 1, OF filterlim_uminus_at_top_at_bot]
  show ?thesis
    by (metis "1" filterlim_at_bot_mirror minus_zero tendsto_minus_cancel_left)
qed

lemma cdf_is_right_cont: "continuous (at_right a) (cdf M)"
  unfolding continuous_within
proof (rule tendsto_at_right_sequentially[where b="a + 1"])
  fix f :: "nat \<Rightarrow> real" and x assume f: "decseq f" "f ----> a"
  then have "(\<lambda>n. cdf M (f n)) ----> measure M (\<Inter>i. {.. f i})"
    unfolding cdf_def 
    apply (intro finite_Lim_measure_decseq)
    using `decseq f` apply (auto simp: decseq_def)
    done
  also have "(\<Inter>i. {.. f i}) = {.. a}"
    using decseq_le[OF f] by (auto intro: order_trans LIMSEQ_le_const[OF f(2)])
  finally show "(\<lambda>n. cdf M (f n)) ----> cdf M a"
    by (simp add: cdf_def)
qed simp

lemma cdf_at_left: "(cdf M ---> measure M {..<a}) (at_left a)"
  apply (rule increasing_tendsto)
  apply (subst eventually_at_left[of "a - 1"])
  apply simp
  apply (rule_tac exI[of _ "a - 1"], auto)
  apply (simp add: cdf_def)
  apply (rule finite_measure_mono, auto)
  apply (rule_tac b="a - 1" in sequentially_imp_eventually_at_left, auto)
proof -
  fix f :: "nat \<Rightarrow> real" and x assume f: "incseq f" "f ----> a" "\<And>x. f x < a"
    and x: "measure M {..<a} > x"
  then have "(\<lambda>n. cdf M (f n)) ----> measure M (\<Union>i. {.. f i})"
    unfolding cdf_def 
    apply (intro finite_Lim_measure_incseq)
    using `incseq f` apply (auto simp: incseq_def)
    done
  also have "(\<Union>i. {.. f i}) = {..<a}"
    apply auto
    apply (erule order_le_less_trans, rule f)
    by (metis Lim_bounded_ereal f(2) linear not_less)
  finally have "(\<lambda>n. cdf M (f n)) ----> measure M {..<a}"
    by (simp add: cdf_def)
  from order_tendstoD(1)[OF this x]
  show "eventually (\<lambda>n. cdf M (f n) > x) sequentially" .
qed

lemma isCont_cdf:
  fixes x :: real
  shows  "isCont (cdf M) x = (measure M {x} = 0)"

  apply (simp add: continuous_at_split cdf_is_right_cont)
  apply (subst continuous_within)
  apply (rule trans [of _ "(cdf M x = measure M {..<x})"])
  apply auto[1]
  apply (rule tendsto_unique [OF _ _ cdf_at_left])
  apply auto[2]
  apply (rule cdf_at_left)
  apply (simp add: cdf_def)
  apply (subgoal_tac "{..x} = {..<x} \<union> {x}")
  apply (erule ssubst)
  apply (subst finite_measure_Union)
by auto

lemma ceiling_nonneg: "0 \<le> x \<Longrightarrow> 0 \<le> \<lceil>x\<rceil>"
  by simp

lemma countable_atoms: "countable {x. measure M {x} > 0}"
  using countable_support unfolding zero_less_measure_iff .
    
end

locale real_distribution = prob_space M for M :: "real measure" +
  assumes events_eq_borel [simp, measurable_cong]: "sets M = sets borel" and space_eq_univ [simp]: "space M = UNIV"
begin

sublocale finite_borel_measure M
  by standard auto

lemma cdf_bounded_prob: "\<And>x. cdf M x \<le> 1"
  by (subst prob_space [symmetric], rule cdf_bounded)

lemma cdf_lim_infty_prob: "(\<lambda>i. cdf M (real i)) ----> 1"
  by (subst prob_space [symmetric], rule cdf_lim_infty)

lemma cdf_lim_at_top_prob: "(cdf M ---> 1) at_top" 
  by (subst prob_space [symmetric], rule cdf_lim_at_top)

end

lemma (in prob_space) real_distribution_distr [intro, simp]:
  "random_variable borel X \<Longrightarrow> real_distribution (distr M borel X)"
  unfolding real_distribution_def real_distribution_axioms_def apply auto
by (rule prob_space_distr)  

subsection {* uniqueness *}

lemma (in real_distribution) emeasure_Ioc:
  assumes "a \<le> b" shows "emeasure M {a <.. b} = cdf M b - cdf M a"
proof -
  have "{a <.. b} = {..b} - {..a}"
    by auto
  with `a \<le> b` show ?thesis
    by (simp add: emeasure_eq_measure finite_measure_Diff cdf_def)
qed

lemma UN_Ioc_eq_UNIV: "(\<Union>i. {- real (i::nat)<..real i}) = UNIV"
  by auto
     (metis le_less_trans minus_minus neg_less_iff_less not_le real_arch_simple
            of_nat_0_le_iff reals_Archimedean2)

lemma cdf_unique:
  fixes M1 M2
  assumes "real_distribution M1" and "real_distribution M2"
  assumes "cdf M1 = cdf M2"
  shows "M1 = M2"
proof (rule measure_eqI_generator_eq[where \<Omega>=UNIV])
  fix X assume "X \<in> range (\<lambda>(a, b). {a<..b::real})"
  then obtain a b where Xeq: "X = {a<..b}" by auto
  then show "emeasure M1 X = emeasure M2 X"
    by (cases "a \<le> b")
       (simp_all add: assms(1,2)[THEN real_distribution.emeasure_Ioc] assms(3))
next
  show "(\<Union>i. {- real (i::nat)<..real i}) = UNIV"
    by (rule UN_Ioc_eq_UNIV)
qed (auto simp: real_distribution.emeasure_Ioc[OF assms(1)]
  assms(1,2)[THEN real_distribution.events_eq_borel] borel_sigma_sets_Ioc
  Int_stable_def)

lemma real_distribution_interval_measure:
  fixes F :: "real \<Rightarrow> real"
  assumes nondecF : "\<And> x y. x \<le> y \<Longrightarrow> F x \<le> F y" and
    right_cont_F : "\<And>a. continuous (at_right a) F" and 
    lim_F_at_bot : "(F ---> 0) at_bot" and
    lim_F_at_top : "(F ---> 1) at_top"
  shows "real_distribution (interval_measure F)"
proof -
  let ?F = "interval_measure F"
  interpret prob_space ?F
  proof
    have "ereal (1 - 0) = (SUP i::nat. ereal (F (real i) - F (- real i)))"
      by (intro LIMSEQ_unique[OF _ LIMSEQ_SUP] lim_ereal[THEN iffD2] tendsto_intros
         lim_F_at_bot[THEN filterlim_compose] lim_F_at_top[THEN filterlim_compose]
         lim_F_at_bot[THEN filterlim_compose] filterlim_real_sequentially
         filterlim_uminus_at_top[THEN iffD1])
         (auto simp: incseq_def intro!: diff_mono nondecF)
    also have "\<dots> = (SUP i::nat. emeasure ?F {- real i<..real i})"
      by (subst emeasure_interval_measure_Ioc) (simp_all add: nondecF right_cont_F)
    also have "\<dots> = emeasure ?F (\<Union>i::nat. {- real i<..real i})"
      by (rule SUP_emeasure_incseq) (auto simp: incseq_def)
    also have "(\<Union>i. {- real (i::nat)<..real i}) = space ?F"
      by (simp add: UN_Ioc_eq_UNIV)
    finally show "emeasure ?F (space ?F) = 1"
      by (simp add: one_ereal_def)
  qed
  show ?thesis
    proof qed simp_all
qed

lemma cdf_interval_measure:
  fixes F :: "real \<Rightarrow> real"
  assumes nondecF : "\<And> x y. x \<le> y \<Longrightarrow> F x \<le> F y" and
    right_cont_F : "\<And>a. continuous (at_right a) F" and 
    lim_F_at_bot : "(F ---> 0) at_bot" and
    lim_F_at_top : "(F ---> 1) at_top"
  shows "cdf (interval_measure F) = F"
  unfolding cdf_def
proof (intro ext)
  interpret real_distribution "interval_measure F"
    by (rule real_distribution_interval_measure) fact+
  fix x
  have "F x - 0 = measure (interval_measure F) (\<Union>i::nat. {-real i <.. x})"
  proof (intro LIMSEQ_unique[OF _ finite_Lim_measure_incseq])
    have "(\<lambda>i. F x - F (- real i)) ----> F x - 0"
      by (intro tendsto_intros lim_F_at_bot[THEN filterlim_compose] filterlim_real_sequentially
                filterlim_uminus_at_top[THEN iffD1])
    then show "(\<lambda>i. measure (interval_measure F) {- real i<..x}) ----> F x - 0"
      apply (rule filterlim_cong[OF refl refl, THEN iffD1, rotated])
      apply (rule eventually_sequentiallyI[where c="nat (ceiling (- x))"])
      apply (simp add: measure_interval_measure_Ioc right_cont_F nondecF)
      done
  qed (auto simp: incseq_def)
  also have "(\<Union>i::nat. {-real i <.. x}) = {..x}"
    by auto (metis minus_minus neg_less_iff_less reals_Archimedean2)
  finally show "measure (interval_measure F) {..x} = F x"
    by simp
qed

end

