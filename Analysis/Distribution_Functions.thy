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

imports Probability

begin

subsection {* Miscellany *}

lemma prob_space_simps [simp]:
  "prob_space M \<Longrightarrow> finite_measure M"
unfolding prob_space_def by simp

(* goes with atLeastLessThan_inj in SetInterval.thy *)
lemma (in linorder) greaterThanAtMost_subset_iff:
  "({a<..b} \<subseteq> {c<..d}) = (b <= a | c<=a & b<=d)"
apply (auto simp: subset_eq Ball_def)
by (metis less_le not_less)

lemma greaterThanAtMost_inj:
  fixes a b c d :: "'a::linorder"
  assumes eq: "{a<..b} = {c<..d}" and "a < b | c < d"
  shows "a = c & b = d"
using assms
by (metis greaterThanAtMost_empty greaterThanAtMost_empty_iff 
  greaterThanAtMost_subset_iff order_eq_iff)+

lemma greaterThanAtMost_disjoint:
  fixes a b c d :: "'a::linorder"
  shows "({a<..b} \<inter> {c<..d} = {}) = 
    (b \<le> a | d \<le> c | b \<le> c | d \<le> a)"
using assms by auto

lemma AtMost_real_inter: "{..x} = (\<Inter> i. {..x + inverse (real (Suc i))})"
  apply auto
  apply (metis add_increasing2 inverse_nonnegative_iff_nonnegative 
    real_of_nat_ge_zero)
  apply (subst not_less [symmetric], rule notI)
  apply (subgoal_tac "xa - x > 0", auto)
  apply (drule reals_Archimedean, auto)
  apply (drule_tac x = n in spec)
  apply auto
done

lemma dependent_choice:
  assumes  1: "\<exists> x. P x" and 
           2: "\<And>x (n:: nat). P x \<Longrightarrow> \<exists>y. P y \<and> Q n x y"
  shows "\<exists>f. \<forall>n. P (f n) \<and> Q n (f n) (f (Suc n))"
proof
  let ?f = "rec_nat (SOME x. P x) (%n x. SOME y. P y \<and> Q n x y)"
  show "\<forall>n. P (?f n) \<and> Q n (?f n) (?f (Suc n))"
  proof
    fix n
    show "P (?f n) \<and> Q n (?f n) (?f (Suc n))"
      apply (induct_tac n)
      apply auto
      apply (rule someI_ex, rule 1)
      apply (rule 2 [THEN someI_ex, THEN conjunct2])
      apply (rule someI_ex, rule 1)
      apply (rule 2 [THEN someI_ex, THEN conjunct1], assumption)
      apply (rule 2 [THEN someI_ex, THEN conjunct2])
      apply (rule 2 [THEN someI_ex, THEN conjunct1], assumption)
      done
  qed
qed

(* The next two theorems could be proved in greater generality  by replacing "real" with 
"{no_top, inner_dense_linorder, linorder_topology, first_countable_topology}".

Compare to  sequentially_imp_eventually_nhds_within. But it is not clear whether the greater 
generality is worth the effort. *)

lemma not_eventually_at_right_decseq: 
  fixes a b :: real and P
  assumes [arith]: "a < b" and h: "\<not> eventually P (at_right a)"
  shows "\<exists>f. decseq f \<and> f ----> a \<and> (\<forall>n. f n > a) \<and> (\<forall>n. f n < b) \<and>  
      (\<forall>n. \<not> P (f n))" (is "\<exists> f. ?conc f")
proof -
  from h have 1 [rule_format]: "(\<forall>b>a. \<exists>z. a < z \<and> z < b \<and> \<not> P z)"
    by (simp add: eventually_at_right)
  have [simp]: "b - a > 0" by arith
  let ?P = "\<lambda>x. a < x \<and> x < b \<and> \<not> P x"
  let ?Q = "\<lambda>n x y. y < min x (a + (b - a) * inverse (real (n+1)))"
  have "\<exists>f. \<forall>n. ?P (f n) \<and> ?Q n (f n) (f (Suc n))"
  proof (rule dependent_choice)
    show "\<exists>x>a. x < b \<and> \<not> P x"
      by (rule 1, rule assms)
    next
      fix n :: "nat" and x
      assume 2: "a < x \<and> x < b \<and> \<not> P x"
      hence "\<exists>z. a < z \<and> z < min x (a + (b - a) * inverse (real (n + 1))) \<and> \<not> P z"
        by (intro 1, force intro!: mult_pos_pos)
      then obtain z where "a < z \<and> z < min x (a + (b - a) * inverse (real (n + 1))) \<and> \<not> P z" ..
      hence "(a < z \<and> z < b \<and> \<not> P z) \<and> z < min x (a + (b - a) * inverse (real (n + 1)))"
        using 2 by auto
      thus "\<exists>y. (a < y \<and> y < b \<and> \<not> P y) \<and> y < min x (a + (b - a) * inverse (real (n + 1)))" ..
    qed
  then obtain f where 3: "\<And>n. ?P (f n)" and 4: "\<And>n. ?Q n (f n) (f (Suc n))" by auto
  hence 5: "\<And>n. f (n + 1) < (a + (b - a) * inverse (real (n+1)))" by auto
  from 3 have "\<And>n. f n > a" by auto 
  moreover from 3 have "\<And>n :: nat. f n < b" by auto
  moreover from 4 have decseqf: "decseq f" by (auto intro!: decseq_SucI less_imp_le)
  moreover have "f ----> a"
    apply (rule decreasing_tendsto)
    apply (rule eventually_sequentiallyI)
    apply (rule less_imp_le)
    using 3 apply force
    apply (rule eventually_sequentiallyI)
    (* this is a good example of a straightforward calculation which is a pain in the neck *)
    proof -
      fix x m
      assume "a < x" and 6: "m \<ge> natceiling ((b - a) / (x - a)) + 1"
      hence "real m > ((b - a) / (x - a))"
        by (metis Suc_eq_plus1 natceiling_le_eq natceiling_real_of_nat not_le not_less_eq 
        sup.semilattice_strict_iff_order)
      from less_imp_inverse_less [OF this] have 7: "inverse (real m) < ((x - a) / (b - a))"
        using `a < x` `a < b` by (auto simp add: field_simps)
      from 6 have "m = (m - 1) + 1" by arith
      hence "f m < a + (b - a) * inverse (real m)"
        apply (elim ssubst)
        by (rule 5)
      also have "... < a + (b - a) * ((x - a) / (b - a))"
        apply (rule add_strict_left_mono)
        using `a < b` apply (intro mult_strict_left_mono, auto)
        by (rule 7)
      also have "... = x" by auto
      finally show "f m < x" .
    qed
  moreover from 3 have "\<forall>n. \<not> P (f n)" by auto
  ultimately show "?thesis" by blast
qed

(* parallels version for ereal in Extended_Real.thy *)
lemma
  fixes f :: "nat \<Rightarrow> real"
  shows incseq_uminus_real[simp]: "incseq (\<lambda>x. - f x) \<longleftrightarrow> decseq f"
  and decseq_uminus_real[simp]: "decseq (\<lambda>x. - f x) \<longleftrightarrow> incseq f"
  unfolding decseq_def incseq_def by auto

lemma not_eventually_at_left_incseq: 
  fixes a b :: real and P
  assumes [arith]: "a > b" and h: "\<not> eventually P (at_left a)"
  shows "\<exists>f. incseq f \<and> f ----> a \<and> (\<forall>n. f n < a) \<and> (\<forall>n. f n > b) \<and> (\<forall>n. \<not> P (f n))"
proof -
  have "\<exists>f. decseq f \<and> f ----> -a \<and> (\<forall>n. f n > -a) \<and> (\<forall>n. f n < -b) \<and> (\<forall>n. \<not> P (- f n))"
    using assms by (intro not_eventually_at_right_decseq, 
        auto simp add: eventually_at_left_to_right)
  then guess f ..
  thus ?thesis
    apply (intro exI[of _ "\<lambda>x. - f x"], auto)
    apply (rule tendsto_minus_cancel, auto)
    by (drule_tac x = n in spec, auto)+
qed

lemma sequentially_imp_eventually_at_right:
  fixes a b :: real
  assumes "a < b"
  assumes *: "\<And>f. (\<And>n. f n > a) \<Longrightarrow> (\<And>n. f n < b) \<Longrightarrow> decseq f \<Longrightarrow> f ----> a \<Longrightarrow> 
    eventually (\<lambda>n. P (f n)) sequentially"
  shows "eventually P (at_right a)"

  apply (rule ccontr)
  apply (drule not_eventually_at_right_decseq [OF `a < b`])
  apply auto
  apply (subgoal_tac "eventually (\<lambda>n. P (f n)) sequentially")
  prefer 2
by (rule *, auto)

lemma sequentially_imp_eventually_at_left:
  fixes a b :: real
  assumes "a > b"
  assumes *: "\<And>f. (\<And>n. f n < a) \<Longrightarrow> (\<And>n. f n > b) \<Longrightarrow> incseq f \<Longrightarrow> f ----> a \<Longrightarrow> 
    eventually (\<lambda>n. P (f n)) sequentially"
  shows "eventually P (at_left a)"

  apply (rule ccontr)
  apply (drule not_eventually_at_left_incseq [OF `a > b`])
  apply auto
  apply (subgoal_tac "eventually (\<lambda>n. P (f n)) sequentially")
  prefer 2
by (rule *, auto)

lemma continuous_at_split: 
  "continuous (at (x::'a::linorder_topology)) f = 
    (continuous (at_left x) f \<and> continuous (at_right x) f)"
by (simp add: continuous_within filterlim_at_split)

lemma continuous_at_right_real_increasing:
  assumes nondecF: "\<And> x y. x \<le> y \<Longrightarrow> f x \<le> ((f y) :: real)"
  shows "(continuous (at_right (a :: real)) f) = (\<forall>e > 0. \<exists>delta > 0. f (a + delta) - f a < e)"

  apply (auto simp add: continuous_within_eps_delta dist_real_def greaterThan_def)
  apply (drule_tac x = e in spec, auto)
  apply (drule_tac x = "a + d / 2" in spec)
  apply (subst (asm) abs_of_nonneg)
  apply (auto intro: nondecF simp add: field_simps)
  apply (rule_tac x = "d / 2" in exI)
  apply (auto simp add: field_simps)
  apply (drule_tac x = e in spec, auto)
  apply (rule_tac x = delta in exI, auto)
  apply (subst abs_of_nonneg)
  apply (auto intro: nondecF simp add: field_simps)
  apply (rule le_less_trans)
  prefer 2 apply assumption
by (rule nondecF, auto)

lemma continuous_at_left_real_increasing:
  assumes nondecF: "\<And> x y. x \<le> y \<Longrightarrow> f x \<le> ((f y) :: real)"
  shows "(continuous (at_left (a :: real)) f) = (\<forall>e > 0. \<exists>delta > 0. f a - f (a - delta) < e)"

  apply (auto simp add: continuous_within_eps_delta dist_real_def lessThan_def)
  apply (drule_tac x = e in spec, auto)
  apply (drule_tac x = "a - d / 2" in spec)
  apply (subst (asm) abs_of_nonpos)
  apply (auto intro: nondecF simp add: field_simps)
  apply (rule_tac x = "d / 2" in exI)
  apply (auto simp add: field_simps)
  apply (drule_tac x = e in spec, auto)
  apply (rule_tac x = delta in exI, auto)
  apply (subst abs_of_nonpos)
  apply (auto intro: nondecF simp add: field_simps)
  apply (rule less_le_trans)
  apply assumption
  apply auto
by (rule nondecF, auto)

(* TODO: move this somewhere else *)
lemma infinite_arbitrarily_large:
  fixes n :: nat 
  assumes "infinite A"
  shows "\<exists>B. finite B \<and> card B = n \<and> B \<subseteq> A"

proof (induction n)
  case 0 show ?case by auto
next 
  case (Suc n)
  fix n
  assume "\<exists>B. finite B \<and> card B = n \<and> B \<subseteq> A"
  then guess B .. note B = this
  with `infinite A` have "A \<noteq> B" by auto
  with B have "B \<subset> A" by auto
  hence "\<exists>x. x \<in> A - B" by (elim psubset_imp_ex_mem)
  then guess x .. note x = this
  with B have "finite (insert x B) \<and> card (insert x B) = Suc n \<and> insert x B \<subseteq> A"
    by auto
  thus "\<exists>B. finite B \<and> card B = Suc n \<and> B \<subseteq> A" ..
qed

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
  "((%i. cdf M (real i)) ----> measure M (space M))"
proof -
  have "(%i. cdf M (real i)) ----> measure M (\<Union> i::nat. {..real i})"
    unfolding cdf_def by (rule finite_Lim_measure_incseq) (auto simp: incseq_def)
  also have "(\<Union> i::nat. {..real i}) = space M"
    by (auto simp: borel_UNIV intro: real_natceiling_ge)
  finally show ?thesis .
qed

lemma cdf_lim_at_top: "(cdf M ---> measure M (space M)) at_top" 
  by (rule tendsto_at_topI_sequentially) (simp_all add: mono_def cdf_nondecreasing cdf_lim_infty)

lemma cdf_lim_neg_infty: "((%i. cdf M (- real i)) ----> 0)" 
proof -
  have "(%i. cdf M (- real i)) ----> measure M (\<Inter> i::nat. {.. - real i })"
    unfolding cdf_def by (rule finite_Lim_measure_decseq) (auto simp: decseq_def)
  also have "(\<Inter> i::nat. {..- real i}) = {}"
    by auto (metis leD le_minus_iff reals_Archimedean2)
  finally show ?thesis
    by simp
qed

lemma cdf_lim_at_bot: "(cdf M ---> 0) at_bot"
proof - 
  have 1: "((%x :: real. - cdf M (- x)) ---> 0) at_top"
    apply (rule tendsto_at_topI_sequentially) 
    apply (auto simp add: mono_def cdf_nondecreasing cdf_lim_neg_infty)
    using cdf_lim_neg_infty by (metis minus_zero tendsto_minus_cancel_left)
  from filterlim_compose [OF 1, OF filterlim_uminus_at_top_at_bot]
  show ?thesis
    by (metis "1" filterlim_at_bot_mirror minus_zero tendsto_minus_cancel_left)
qed

lemma cdf_is_right_cont: "continuous (at_right a) (cdf M)"
  apply (subst continuous_within)
  apply (rule decreasing_tendsto)
  apply (auto simp add: eventually_at_right intro!: cdf_nondecreasing exI[of _ "a + 1"]) []
  apply (rule_tac b="a + 1" in sequentially_imp_eventually_at_right)
  apply simp
proof -
  fix f :: "nat \<Rightarrow> real" and x assume f: "decseq f" "f ----> a" and x: "cdf M a < x"
  then have "(\<lambda>n. cdf M (f n)) ----> measure M (\<Inter>i. {.. f i})"
    unfolding cdf_def 
    apply (intro finite_Lim_measure_decseq)
    using `decseq f` apply (auto simp: decseq_def)
    done
  also have "(\<Inter>i. {.. f i}) = {.. a}"
    using decseq_le[OF f] by (auto intro: order_trans LIMSEQ_le_const[OF f(2)])
  finally have "(\<lambda>n. cdf M (f n)) ----> cdf M a"
    by (simp add: cdf_def)
  from order_tendstoD(2)[OF this x]
  show "eventually (\<lambda>n. cdf M (f n) < x) sequentially" .
qed

lemma cdf_at_left: "(cdf M ---> measure M {..<a}) (at_left a)"
  apply (rule increasing_tendsto)
  apply (subst eventually_at_left)
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

lemma countable_atoms: "countable {x. measure M {x} > 0}"
proof -
  { fix B i
    assume finB: "finite B" and 
      subB: "B \<subseteq> {x. inverse (real (Suc i)) < Sigma_Algebra.measure M {x}}"
    have "measure M B = (\<Sum>x\<in>B. measure M {x})"
      by (rule measure_eq_setsum_singleton [OF finB], auto)
    also have "\<dots> \<ge> (\<Sum>x\<in>B. inverse (real (Suc i)))" (is "?lhs \<ge> ?rhs")
      using subB by (intro setsum_mono, auto)
    also (xtrans) have "?rhs = card B * inverse (real (Suc i))"
      (* this should be automatic! *)
      by (simp add: real_of_nat_def)
    finally have "measure M B \<ge> card B * inverse (real (Suc i))" .
  } note * = this
  have "measure M (space M) < real (Suc(natceiling (measure M (space M))))"
    apply (auto simp add: real_of_nat_Suc)
    apply (rule order_le_less_trans)
    by (rule real_natceiling_ge, auto)
  then obtain X :: nat where X: "measure M (space M) < X" ..
  (* it would be nice if this next calculation were automatic, with X replaced the particular
     value above *)
  { fix i
  have "finite {x. inverse (real (Suc i)) < Sigma_Algebra.measure M {x}}"
    apply (rule ccontr)
    apply (drule infinite_arbitrarily_large [of _ "X * Suc i"])
    apply clarify
    apply (drule *, assumption)
    apply (drule leD, erule notE, erule ssubst, subst real_of_nat_mult)
    apply (simp add: field_simps)
    by (rule order_le_less_trans [OF bounded_measure X])
  } note ** = this
  have "{x. measure M {x} > 0} = (\<Union>i :: nat. {x. measure M {x} > inverse (Suc i)})"
    apply auto
    apply (erule reals_Archimedean)
    by (metis inverse_positive_iff_positive less_trans real_of_nat_Suc_gt_zero)
  thus "countable {x. measure M {x} > 0}"
    apply (elim ssubst)
    apply (rule countable_UN, auto)
    apply (rule countable_finite)
    by (rule **)
qed
    
end

locale real_distribution = prob_space M for M :: "real measure" +
  assumes events_eq_borel [simp]: "sets M = sets borel" and space_eq_univ [simp]: "space M = UNIV"
begin

sublocale finite_borel_measure M
  by default auto

lemma cdf_bounded_prob: "\<And>x. cdf M x \<le> 1"
  by (subst prob_space [symmetric], rule cdf_bounded)

lemma cdf_lim_infty_prob: "(%i. cdf M (real i)) ----> 1"
  by (subst prob_space [symmetric], rule cdf_lim_infty)

lemma cdf_lim_at_top_prob: "(cdf M ---> 1) at_top" 
  by (subst prob_space [symmetric], rule cdf_lim_at_top)

end


subsection {* Every right continuous and nondecreasing function gives rise to a measure *}

abbreviation
  "half_open_intervals \<equiv>  {u :: real set. \<exists>a b. u = {a<..b}}"

lemma half_open_intervals: "half_open_intervals = range (\<lambda>(i, j). {i <.. j})"
  by auto

interpretation half_open_semiring: semiring_of_sets UNIV half_open_intervals
  apply (unfold_locales, force, force, force)
  apply clarsimp
proof -
  fix a b c d :: real
  show "\<exists>C \<subseteq> half_open_intervals. finite C \<and> disjoint C \<and> {a<..b} - {c<..d} = 
    \<Union>C"
  proof cases
    let ?C = "{{a<..b}}"
    assume "b < c | d \<le> a | d \<le> c"
    hence "?C \<subseteq> half_open_intervals \<and> finite ?C \<and> disjoint ?C \<and> 
        {a<..b} - {c<..d} = \<Union>?C"
      by (auto simp add: disjoint_def)
    thus ?thesis ..
  next
    let ?C = "{{a<..c}, {d<..b}}"
    assume "~(b < c | d \<le> a | d \<le> c)"
    hence "?C \<subseteq> half_open_intervals \<and> finite ?C \<and> disjoint ?C \<and> 
        {a<..b} - {c<..d} = \<Union>?C"
      by (auto simp add: disjoint_def)
    thus ?thesis ..
  qed
qed

lemma sigma_sets_half_open_intervals: "borel = sigma UNIV half_open_intervals"
  unfolding half_open_intervals
proof (rule borel_eq_sigmaI5[OF borel_eq_atMost])
  fix i :: real
  have "{..i} = (\<Union>j::nat. {-j <.. i})"
    by (auto simp: minus_less_iff reals_Archimedean2)
  also have "\<dots> \<in> sets (sigma UNIV (range (\<lambda>(i, j). {i<..j})))"
    by (intro sets.countable_nat_UN) auto 
  finally show "{..i} \<in> sets (sigma UNIV (range (\<lambda>(i, j). {i<..j})))" .
qed simp

definition
  interval_name :: "real set \<Rightarrow> real * real"
where
  "interval_name A = (SOME p. A = {fst p<..snd p})"

lemma interval_name_unique: "a < b \<Longrightarrow> interval_name {a<..b} = (a, b)"
  apply (unfold interval_name_def)
  apply (rule some1_equality) 
  apply (rule ex1I [where a = "(a, b)"])
  apply auto
  apply (frule greaterThanAtMost_inj, auto)+
done

lemma interval_name_sound: 
  fixes S
  assumes hoS: "S \<in> half_open_intervals"
  shows "S = {fst (interval_name S)<..snd (interval_name S)}"
using hoS apply -
  apply clarsimp
  apply (unfold interval_name_def)
  apply (rule_tac x = "(a, b)" in someI)
  apply auto
done

definition
  half_open_semiring_measure :: "(real \<Rightarrow> real) \<Rightarrow> real set \<Rightarrow> real"
where
  "half_open_semiring_measure F A \<equiv> 
    if A = {} then 0 else 
        F(snd (interval_name A)) - F(fst (interval_name A))"

lemma half_open_semiring_measure_empty [simp]:
  "half_open_semiring_measure F {} = 0"
  unfolding half_open_semiring_measure_def interval_name_def
by auto

lemma half_open_semiring_measure_nonempty [simp]:
  "a < b \<Longrightarrow> half_open_semiring_measure F {a<..b} = F b - F a"
  apply (unfold half_open_semiring_measure_def)
by (auto simp add: interval_name_unique)

lemma half_open_semiring_measure_positive:
  fixes F :: "real \<Rightarrow> real"
  assumes nondecF : "\<And> x y. x \<le> y \<Longrightarrow> F x \<le> F y"
  shows "positive half_open_intervals (half_open_semiring_measure F)"
  apply (auto simp add: positive_def)
  apply (case_tac "a < b")
by (auto simp add: diff_le_iff intro: nondecF)

lemma half_open_semiring_measure_countably_additive:
  fixes F :: "real \<Rightarrow> real"
  assumes nondecF : "\<And> x y. x \<le> y \<Longrightarrow> F x \<le> F y" 
  and right_cont_F : "\<And>a. continuous (at_right a) F" 
  shows "countably_additive half_open_intervals (half_open_semiring_measure F)"
proof (rule countably_additiveI)
  fix A :: "nat \<Rightarrow> real set"
  assume 
    rangeA: "range A \<subseteq> half_open_intervals" and
    disjA: "disjoint_family A" and 
    "(\<Union>i. A i) \<in> half_open_intervals"
  then obtain a b where unAeq: "(\<Union>i. A i) = {a<..b}" by auto
  hence Aisub: "\<And>i. A i \<subseteq> {a<..b}" by auto
  from rangeA have halfopenAi: "\<And>i. A i \<in> half_open_intervals"
    unfolding image_def by auto
  def left \<equiv> "%i. fst (interval_name (A i))"
  def right \<equiv> "%i. snd (interval_name (A i))"
  def x \<equiv> "%i. SOME x. x : A i"
  have Aieq: "\<And>i. A i = {left i<..right i}"
    unfolding left_def right_def apply (rule interval_name_sound)
    by (rule halfopenAi)
  have Aixi: "\<And>i. A i \<noteq> {} \<Longrightarrow> x i \<in> A i"
    unfolding x_def apply (rule someI_ex)
    by auto
  have lefti_less_xi: "\<And>i. A i \<noteq> {} \<Longrightarrow> left i < x i"
    using Aixi by (auto simp add: Aieq)
  have xi_le_righti: "\<And>i. A i \<noteq> {} \<Longrightarrow> x i \<le> right i"
    using Aixi by (auto simp add: Aieq)
  have lefti_less_righti: "\<And>i. A i \<noteq> {} \<Longrightarrow> left i < right i"
    using Aixi by (auto simp add: Aieq)
  have posF: "positive half_open_intervals (half_open_semiring_measure F)"
    using assms by (auto intro: half_open_semiring_measure_positive)
  with halfopenAi have [simp]: "!i. 0 \<le> half_open_semiring_measure F (A i)"
    by (auto simp add: positive_def)
  (* first key induction: a bound on the measures of any finite collection of Ai's
     contained in an interval {u<..v} *)
  have claim1: "\<And>S. finite S \<Longrightarrow> (\<forall>i\<in>S. A i \<noteq> {}) \<longrightarrow> 
      (\<forall>u v. u \<le> v \<longrightarrow> (\<forall>i\<in>S. A i \<subseteq> {u<..v}) \<longrightarrow>
        (\<Sum>i\<in>S. half_open_semiring_measure F (A i)) \<le> F v - F u)" (is "\<And>S. finite S \<Longrightarrow> ?P S")
  proof -
    fix S :: "nat set"
    show "finite S \<Longrightarrow> ?P S"
    proof (induct rule: finite_psubset_induct, clarify)
      fix S  :: "nat set"
      assume finS: "finite S"
      assume ih: "\<And>U. U \<subset> S \<Longrightarrow> ?P U"
      fix u v :: real
      assume nonemptyAi [rule_format]: "(\<forall>i\<in>S. A i \<noteq> {})"
      assume leuv : "u \<le> v"
      assume Aiuv [rule_format]: "(\<forall>i\<in>S. A i \<subseteq> {u<..v})"
      have lefti_less_righti_S: "\<And>i. i \<in> S \<Longrightarrow> left i < right i"
        by (rule lefti_less_righti, rule nonemptyAi)
      have u_le_lefti_S: "\<And>i. i \<in> S \<Longrightarrow> u \<le> left i"
        apply (frule Aiuv, frule lefti_less_righti_S)
        using leuv by (auto simp add: Aieq greaterThanAtMost_subset_iff)
      have righti_le_v_S: "\<And>i. i \<in> S \<Longrightarrow> right i \<le> v"
        apply (frule Aiuv, frule lefti_less_righti_S)
        using leuv by (auto simp add: Aieq greaterThanAtMost_subset_iff)
      show "(\<Sum>i\<in>S. half_open_semiring_measure F (A i)) \<le> F v - F u"
      proof (cases "S = {}")
        assume "S = {}"
        with nondecF [OF leuv] finS show ?thesis by auto
      next
        assume "S \<noteq> {}"
        hence "\<exists>i. i : S" by auto
        then obtain j where Sj: "j \<in> S" ..
        with lefti_less_righti_S have [arith]: "left j < right j" by auto
        from Sj have "A j \<subseteq> {u<..v}" by (rule Aiuv)
        hence [arith]: "u \<le> left j" and "right j \<le> v"
          by (auto simp add: Aieq greaterThanAtMost_subset_iff
            lefti_less_righti)
        let ?S1 = "{i \<in> S. right i \<le> left j}"
        let ?S2 = "{i \<in> S. right j \<le> left i}"
        from Sj have "?S1 \<subset> S" by force
        hence sumS1: "(SUM i : ?S1. half_open_semiring_measure F (A i)) \<le> 
            F (left j) - F u"
          apply (elim ih [rule_format])
          using finS nonemptyAi Aieq apply auto
          by (frule u_le_lefti_S, auto)
        from Sj have "?S2 \<subset> S" by force 
        hence sumS2: "(SUM i : ?S2. half_open_semiring_measure F (A i)) \<le> 
            F v - F (right j)"
          apply (elim ih [rule_format])
          using finS nonemptyAi Aieq apply auto
          using Sj apply (rule righti_le_v_S)
          by (frule righti_le_v_S, auto)
        from Sj disjA have Seq: "S = ?S1 \<union> ?S2 \<union> {j}"
          by (force simp add: disjoint_family_on_def Aieq intro: lefti_less_righti_S)
        show "(\<Sum>i\<in>S. half_open_semiring_measure F (A i)) \<le> F v - F u"
          apply (subst Seq)
          apply (subst setsum_Un_disjoint)
          using finS apply auto
          apply (subst setsum_Un_disjoint)
          using finS apply auto
          apply (frule lefti_less_righti_S, auto)
          using sumS1 sumS2 by (auto simp add: Aieq)
        qed    
      qed
    qed
  have aux: "\<And>n. (\<Sum>i<n. half_open_semiring_measure F (A i)) =
    (SUM i | i < n & A i \<noteq> {}. half_open_semiring_measure F (A i))"
    by (rule setsum_mono_zero_right, auto)
  from Aisub have unAicases: "(\<forall>i. A i = {}) \<or> a < b" by auto
  (* this gives us the first inequality *)
  have le_direction: "(\<Sum>i. ereal (half_open_semiring_measure F (A i))) <=
           ereal (half_open_semiring_measure F (\<Union>i. A i))"
    apply (rule suminf_bound, auto)
    using unAicases apply auto
    apply (subst aux)
    apply (rule order_trans)
    apply (rule claim1 [rule_format])
    prefer 4
    apply (rule Aisub)
    by (auto simp add: unAeq)
  (* second key induction: a lower bound on the measures of any finite collection of Ai's
     that cover an interval {u..v} *)
  have claim2: "\<And>l r S. finite S \<Longrightarrow> (\<forall>i \<in> S. l i < r i) \<longrightarrow> 
      (\<forall>u v. (\<Union> i \<in> S. {l i<..< r i}) \<supseteq> {u..v} \<longrightarrow>
      (\<Sum>i\<in>S. F (r i) - F (l i)) \<ge> F v - F u)"
      (is "\<And>l r S. finite S \<Longrightarrow> ?P l r S")
  proof -
    fix l r S
    show "finite S \<Longrightarrow> ?P l r S"
    proof (induct rule: finite_psubset_induct, clarify)
      fix S u v 
      assume finS: "finite S" and
        iSliri [rule_format]: "(\<forall> i \<in> S. l i < r i)" and 
        UNiS: "(UN i : S. {l i<..< r i}) \<supseteq> {u..v}"
      assume ih: "\<And>U. U \<subset> S \<Longrightarrow> ?P l r U"
      show "F v - F u \<le> (\<Sum>i\<in>S. F (r i) - F (l i))"
      proof (cases "S = {}")
        assume "S = {}"
        with finS UNiS nondecF show ?thesis by auto
      next
        fix n
        assume Sne: "S \<noteq> {}"
        hence "\<exists>i. i : S" by auto
        then obtain j where Sj: "j \<in> S" ..
        let ?R = "r j < u | l j > v |
              (\<exists>i \<in> S - {j}. l i \<le> l j & r j \<le> r i)"
        show ?thesis
          proof (cases ?R)
            assume hyp: ?R
            have "F v - F u \<le> (\<Sum>i\<in>S - {j}. F (r i) - F (l i))"
              apply (rule ih [rule_format])
              using Sj apply force
              apply (rule iSliri, auto)
              apply (subgoal_tac "x \<in> (\<Union>i\<in>S. {l i<..<r i})")
              prefer 2
              (* why didn't automated tools get this? *)
              apply (rule subsetD [OF UNiS], auto)
              using hyp UNiS apply auto
              apply (frule_tac x = "ia" in bspec)
              apply auto
              by (smt DiffI Set.set_insert hyp singleton_insert_inj_eq')
              (* The fact euclidean_trans seems to have been renamed; above are the results of
                 running sledgehammer. *)
              (*by (metis euclidean_trans(2) euclidean_trans(3)
                hyp le_less less_imp_triv mem_delete not_le)*)
            also have "(\<Sum>i\<in>S - {j}. F (r i) - F (l i)) \<le>
              (\<Sum>i\<in>S. F (r i) - F (l i))"
              apply (subgoal_tac "S = (S - {j}) Un {j}") 
              apply (erule ssubst) back
              apply (subst setsum_Un_disjoint)
              using finS Sj by (auto simp add: field_simps intro: nondecF less_imp_le iSliri)
            finally show ?thesis .
          next 
            assume hyp: "~?R"
            hence leurj: "u \<le> r j" and leljv: "l j \<le> v" and 
              aux4: "\<And>i. i \<in> S - {j} \<Longrightarrow> r i < r j | l i > l j"
              (* do better here *)
              apply auto
              apply (subgoal_tac "l j < r j")
              apply (subgoal_tac "l i < r i")
              apply (drule_tac x = i in bspec)
              using Sj iSliri by auto
            let ?S1 = "{i \<in> S. l i < l j}"
            let ?S2 = "{i \<in> S. r i > r j}"
            have S1sum: "F (l j) - F u \<le> (\<Sum>i\<in>?S1. F (r i) - F (l i))"
              apply (rule ih [rule_format])
              using finS Sj iSliri apply auto
              apply (subgoal_tac "l j < r j")
              prefer 2 apply (rule iSliri, assumption)
              apply (subgoal_tac "x \<in> (\<Union>i\<in>S. {l i<..<r i})")
              prefer 2
              apply (rule set_mp [OF UNiS])
              using `l j \<le> v` by auto
            have S2sum: "F v - F (r j) \<le> (\<Sum>i\<in>?S2. F (r i) - F (l i))"
              apply (rule ih [rule_format])
              using finS Sj iSliri apply auto
              apply (subgoal_tac "l j < r j")
              prefer 2 apply (rule iSliri, assumption)
              apply (subgoal_tac "x \<in> (\<Union>i\<in>S. {l i<..<r i})")
              prefer 2
              apply (rule set_mp [OF UNiS])
              using `u \<le> r j` by auto
            have "F v - F u \<le> (\<Sum>i\<in>?S1 \<union> ?S2 \<union> {j}. F (r i) - F (l i))"
              apply (subst setsum_Un_disjoint)
              using finS apply auto
              apply (subst setsum_Un_disjoint)
              using finS apply auto
              apply (subgoal_tac "x \<in> S - {j}")
              apply (frule aux4)
              using S1sum S2sum by auto
            also have "... \<le> (\<Sum>i\<in>S. F (r i) - F (l i))"
              apply (rule setsum_mono2)
              using finS Sj apply (auto simp add: field_simps)
              apply (rule nondecF)
              apply (frule iSliri) back
              by auto
            finally show ?thesis .
          qed
        qed
      qed
    qed
  (* now prove the inequality going the other way *)
  have "\<forall>epsilon > 0. ereal (half_open_semiring_measure F (\<Union>i. A i)) \<le> 
    (\<Sum>i. ereal (half_open_semiring_measure F (A i))) + (epsilon :: real)" 
    (is "\<forall>epsilon > 0. ?Q epsilon")
  proof (clarify)
    fix epsilon :: real 
    assume egt0: "epsilon > 0"
    have "\<forall>i. \<exists>d. d > 0 &  F(right i + d) < F(right i) + epsilon / 2^(i+2)"
    proof 
      fix i
      note right_cont_F [of "right i"]
      thus "\<exists>d. d > 0 &  F(right i + d) < F(right i) + epsilon / 2^(i+2)"
        apply -
        apply (subst (asm) continuous_at_right_real_increasing)
        apply (rule nondecF, assumption)
        apply (drule_tac x = "epsilon / 2 ^ (i + 2)" in spec)
        apply (erule impE)
        using egt0 by (auto simp add: field_simps)
    qed
    then obtain delta where 
        deltai_gt0: "\<And>i. delta i> 0" and
        deltai_prop: "\<And>i. F(right i + delta i) < F(right i) + epsilon / 2^(i+2)"
      by metis
    have "\<exists>a' > a. F a' - F a < epsilon / 2"
      apply (insert right_cont_F [of a])
      apply (subst (asm) continuous_at_right_real_increasing)
      using nondecF apply force
      apply (drule_tac x = "epsilon / 2" in spec)
      using egt0 apply (auto simp add: field_simps)
      by (metis add_less_cancel_left comm_monoid_add_class.add.right_neutral 
        comm_semiring_1_class.normalizing_semiring_rules(24) mult_2 mult_2_right)
    then obtain a' where a'lea [arith]: "a' > a" and 
      a_prop: "F a' - F a < epsilon / 2"
      by auto
    def S' \<equiv> "{i. left i < right i}"
    obtain S :: "nat set" where 
      "S \<subseteq> S'" and finS: "finite S" and 
      Sprop: "{a'..b} \<subseteq> (\<Union>i \<in> S. {left i<..<right i + delta i})"
    proof (rule compactE_image)
      show "compact {a'..b}" by (rule compact_interval)
      show "\<forall>i \<in> S'. open ({left i<..<right i + delta i})" by auto
      show "{a'..b} \<subseteq> (\<Union>i \<in> S'. {left i<..<right i + delta i})"
        apply auto
        apply (subgoal_tac "x \<in> (UN i. A i)")
        prefer 2
        apply (subst unAeq)
        apply auto
        apply (rule_tac x = "xa" in bexI)
        using a'lea apply (auto simp add: Aieq S'_def)
        apply (subgoal_tac "delta xa > 0")
        apply arith
        apply (rule deltai_gt0)
        done
    qed
    with S'_def have Sprop2: "\<And>i. i \<in> S \<Longrightarrow> left i < right i" by auto
    from finS have "\<exists>n. \<forall>i \<in> S. i \<le> n" 
      by (subst finite_nat_set_iff_bounded_le [symmetric])
    then obtain n where Sbound [rule_format]: "\<forall>i \<in> S. i \<le> n" ..
    have "F b - F a' \<le> (\<Sum>i\<in>S. F (right i + delta i) - F (left i))"
      apply (rule claim2 [rule_format])
      using finS Sprop apply auto
      apply (frule Sprop2)
      apply (subgoal_tac "delta i > 0")
      apply arith
      by (rule deltai_gt0)
    also have "... \<le> (SUM i : S. F(right i) - F(left i) + epsilon / 2^(i+2))"
      apply (rule setsum_mono)
      apply simp
      apply (rule order_trans)
      apply (rule less_imp_le)
      apply (rule deltai_prop)
      by auto
    also have "... = (SUM i : S. F(right i) - F(left i)) + 
        (epsilon / 4) * (SUM i : S. (1 / 2)^i)" (is "_ = ?t + _")
      apply (subst setsum_addf)
      apply (rule arg_cong) back
      apply (subst setsum_right_distrib)
      by (auto simp add: field_simps power_divide)
    also have "... \<le> ?t + (epsilon / 4) * (\<Sum> i < Suc n. (1 / 2)^i)"
      apply (rule add_left_mono)
      apply (rule mult_left_mono)
      apply (rule setsum_mono2)
      using egt0 apply auto 
      by (frule Sbound, auto)
    also have "... \<le> ?t + (epsilon / 2)"
      apply (rule add_left_mono)
      apply (subst geometric_sum)
      apply auto
      apply (rule mult_left_mono)
      using egt0 apply auto
      done
    finally have aux2: "F b - F a' \<le> (\<Sum>i\<in>S. F (right i) - F (left i)) + 
      epsilon / 2" .
    have "half_open_semiring_measure F (UNION UNIV A)
      \<le> (\<Sum>i \<le> n. half_open_semiring_measure F (A i)) + epsilon"
    proof cases
      assume "a < b"
      hence "half_open_semiring_measure F (UNION UNIV A) = F b - F a"
        apply (subst unAeq)
        by (erule half_open_semiring_measure_nonempty)
      also have "... = (F b - F a') + (F a' - F a)"
        by auto
      also have "... \<le> (F b - F a') + epsilon / 2"
        apply (rule add_left_mono)
        using a_prop by arith
      also have "... \<le> (\<Sum>i\<in>S. F (right i) - F (left i)) + epsilon / 2 +
          epsilon / 2"
        apply (rule add_right_mono)
        by (rule aux2)
      also have "... = (\<Sum>i\<in>S. F (right i) - F (left i)) + epsilon"
        by auto
      also have "... = (\<Sum>i \<in> S. half_open_semiring_measure F (A i)) + epsilon"
        apply (rule arg_cong) back
        apply (rule setsum_cong, auto)
        apply (subst Aieq)
        apply (rule half_open_semiring_measure_nonempty [symmetric])
        by (erule Sprop2)
      also have "... \<le> (\<Sum>i\<le>n. half_open_semiring_measure F (A i)) + epsilon"
        apply (rule add_right_mono)
        apply (rule setsum_mono2)
        using finS Sbound Sprop by auto
      finally show ?thesis .
    next
      assume "~ a < b"
      thus ?thesis
        apply (subst unAeq, auto)
        apply (rule add_nonneg_nonneg)
        apply (rule setsum_nonneg)
        using egt0 by auto
    qed  
    thus "?Q epsilon"
      apply (rule_tac order_trans)
      prefer 2
      apply (rule add_mono[where c="ereal epsilon"])
      apply (rule suminf_upper[of _ "Suc n"])
      by (simp_all add: lessThan_Suc_atMost)
    qed
  hence "ereal (half_open_semiring_measure F (\<Union>i. A i)) \<le> 
    (\<Sum>i. ereal (half_open_semiring_measure F (A i)))"
    by (elim ereal_le_epsilon2)
  with le_direction show "(\<Sum>i. ereal (half_open_semiring_measure F (A i))) =
      ereal (half_open_semiring_measure F (\<Union>i. A i))"
    by auto
qed

(* this should be easier *)
lemma open_union_greaterThanAtMost: 
  "{a<..<b} = (\<Union>i. {a<..b - inverse (real (Suc i))})"
proof auto
  fix x
  assume "a < x" and "x < b"
  have "(\<lambda>i. b - inverse (real (Suc i))) ----> b - 0"
    by (intro tendsto_intros LIMSEQ_inverse_real_of_nat)
  from order_tendstoD(1)[OF this, of x] `x < b`
  show "\<exists>i. x \<le> b - inverse (real (Suc i))"
    by (auto simp add: eventually_sequentially intro: less_imp_le)
next
  fix x i assume "x \<le> b - inverse (real (Suc i))"
  moreover have "0 < inverse (real (Suc i))"
    by simp
  ultimately show "x < b" by arith
qed

lemma cdf_to_measure:
  fixes F :: "real \<Rightarrow> real"
  assumes nondecF : "\<And> x y. x \<le> y \<Longrightarrow> F x \<le> F y" and
    right_cont_F : "\<And>a. continuous (at_right a) F" 
  shows "\<exists>\<mu> :: real set \<Rightarrow> ereal. (\<forall>(a::real) b. a < b \<longrightarrow> \<mu> {a<..b} = F b - F a) 
    \<and> measure_space UNIV (sets borel) \<mu>"
proof -
  let ?mu = "%s. ereal(half_open_semiring_measure F s)"
  from assms have pos: "positive half_open_intervals ?mu"
    by (intro half_open_semiring_measure_positive)
  from assms have ca: "countably_additive half_open_intervals ?mu"
    by (intro half_open_semiring_measure_countably_additive)
  note half_open_semiring.caratheodory [OF pos ca]
  then show "\<exists>\<mu>. (\<forall>a b. a < b \<longrightarrow> \<mu> {a<..b} = ereal (F b - F a)) \<and>
        measure_space UNIV (sets borel) \<mu>"
    apply (elim exE)
    apply (simp add: sigma_sets_half_open_intervals)
    apply (rule_tac x = \<mu>' in exI, auto)
    by (drule_tac x = "{a<..b}" in spec, auto)
qed


subsection {* uniqueness *}

lemma cdf_unique:
  fixes M1 M2
  assumes "real_distribution M1" and "real_distribution M2"
  assumes "cdf M1 = cdf M2"
  shows "M1 = M2"
proof (rule measure_eqI_generator_eq)
  show "Int_stable half_open_intervals" by (rule Int_stableI, force) 
  show "half_open_intervals \<subseteq> Pow UNIV" by auto
  {
    fix X
    assume "X \<in> half_open_intervals"
    then obtain a b where Xeq: "X = {a<..b}" by auto
    interpret M1: real_distribution M1
      by (rule assms)
    have [simp]: "finite_measure M1" by (auto intro: finite_measureI)
    interpret M2: real_distribution M2
      by (rule assms)
    have [simp]: "finite_measure M2" by (auto intro: finite_measureI)
    have abeq: "{a<..b} = {..b} - {..a}" by auto
    show "emeasure M1 X = emeasure M2 X"
      apply (auto simp add: Xeq intro: finite_measure.emeasure_eq_measure)
      apply (subst finite_measure.emeasure_eq_measure, auto)+
      apply (case_tac "a \<le> b", auto)
      apply (auto simp add: abeq)
      apply (subst Measure_Space.finite_measure.finite_measure_Diff, auto)+
      by (simp add: cdf_def2 [symmetric] assms)
  }
  show "sets M1 = sigma_sets UNIV half_open_intervals"
    apply (subst real_distribution.events_eq_borel, rule assms)
    apply (subst sigma_sets_half_open_intervals)
    by auto
  show "sets M2 = sigma_sets UNIV half_open_intervals"
    apply (subst real_distribution.events_eq_borel, rule assms)
    apply (subst sigma_sets_half_open_intervals)
    by auto
  show "range (\<lambda>i :: nat. {-real i<..real i}) \<subseteq> half_open_intervals" by auto
  show "(\<Union>i. {- real (i::nat)<..real i}) = UNIV"
    apply auto
    apply (rule exI, rule conjI)
    apply (subgoal_tac "-real (natceiling (abs x) + 1) < x")
    apply assumption
    apply (case_tac "x >= 0")
    apply auto
    apply (metis Suc_n_not_le_n le_minus_iff natceiling_mono natceiling_real_of_nat not_less)
    apply (case_tac "x >= 0")
    apply auto
    by (metis Suc_n_not_le_n linear natceiling_mono natceiling_real_of_nat)
  { 
    fix i :: "nat" 
    interpret M1: real_distribution M1
      by (rule assms)
    show "emeasure M1 {- real i<..real i} \<noteq> \<infinity>" by auto
  }
qed

lemma distrib_unique:
  fixes F G :: "real \<Rightarrow> real" and c :: "real"
  assumes h1: "\<forall>x y. x > y \<longrightarrow> F x - F y = G x - G y"
    and h2: "(F ---> c) at_bot" and h3: "(G ---> c) at_bot"
  shows "F = G"
proof
  fix x
  have 1: "F = (\<lambda>x. G x + (F 0 - G 0))"
    apply (rule ext)
    using h1 by (subgoal_tac "x < 0 | x = 0 | x > 0", auto, force, force)
  hence "(F ---> c + (F 0 - G 0)) at_bot"
    apply (elim ssubst) back back
    by (rule tendsto_add, rule h3, auto)
  with h2 have "c + (F 0 - G 0) = c"
    apply (intro tendsto_unique, auto)
    by (metis eventually_at_bot_linorder eventually_bot leD le_less)
  hence "F 0 = G 0" by auto
  with 1 show "F x = G x" by auto
qed

(* move these somewhere? *)
lemma sigma_algebra_borel [simp]: "sigma_algebra UNIV borel"
  by (auto simp add: borel_def intro: sigma_algebra_sigma_sets)

lemma sigma_sets_borel [simp]: "sigma_sets UNIV (sets borel) = sets borel"
  by (rule sigma_algebra.sigma_sets_eq, simp)

lemma cdf_to_real_distribution:
  fixes F :: "real \<Rightarrow> real"
  assumes nondecF : "\<And> x y. x \<le> y \<Longrightarrow> F x \<le> F y" and
    right_cont_F : "\<And>a. continuous (at_right a) F" and 
    lim_F_at_bot : "(F ---> 0) at_bot" and
    lim_F_at_top : "(F ---> 1) at_top"
  shows "\<exists>M. real_distribution M \<and> cdf M = F"
proof -
  have "\<exists>\<mu> :: real set \<Rightarrow> ereal. (\<forall>(a::real) b. a < b \<longrightarrow> \<mu> {a<..b} = F b - F a) 
    \<and> measure_space UNIV (sets borel) \<mu>"
    apply (rule cdf_to_measure)
    using assms by auto
  then obtain \<mu> :: "real set \<Rightarrow> ereal" where 
      1: "\<forall>(a::real) b. a < b \<longrightarrow> \<mu> {a<..b} = F b - F a" and 
      2: "measure_space UNIV (sets borel) \<mu>" by auto
  have UNIVeq: "UNIV = (\<Union>i. {-real (i + 1::nat)<..real (i + 1::nat)})"
    apply auto
    by (metis le_Suc_eq le_less_linear le_natfloor minus_less_iff natceiling_le_eq not_less_eq_eq)
  let ?M = "measure_of UNIV (sets borel) \<mu>"
  have [simp, intro]: "ring_of_sets UNIV (sets borel)"
    by (rule ring_of_setsI, auto)
  have cts_from_below [rule_format]: "(\<forall>A. range A \<subseteq> sets ?M \<longrightarrow>
       incseq A \<longrightarrow> (\<Union>i. A i) \<in> sets ?M \<longrightarrow> (\<lambda>i. \<mu> (A i)) ----> \<mu> (\<Union>i. A i))"
    apply (subst ring_of_sets.countably_additive_iff_continuous_from_below [symmetric])
    using 2 by (auto simp add: measure_space_def intro: ring_of_sets.countably_additive_additive)
  have 3: "real_distribution ?M" 
    unfolding real_distribution_def real_distribution_axioms_def
    apply (rule conjI)
    prefer 2 apply simp
(* apply (metis sets.sets_measure_of_eq space_borel) *)
    apply (rule prob_spaceI)
    apply (subst emeasure_measure_of_sigma, auto)
    using 2 apply (auto simp add: measure_space_def)
    apply (subst UNIVeq)
    apply (rule LIMSEQ_unique)
    apply (rule cts_from_below)
    unfolding incseq_def apply auto
    apply (subst 1)
    apply auto
    apply (subgoal_tac "(1 :: ereal) = ereal (1::real)")
    apply (erule ssubst)
    apply (rule isCont_tendsto_compose) back
    apply (auto simp add: one_ereal_def)
    apply (subgoal_tac "(1 :: real) = 1 - 0")
    apply (erule ssubst)
    apply (subst LIMSEQ_Suc_iff)
    apply (rule tendsto_diff)
    apply auto
    apply (rule filterlim_compose) back
    apply (rule lim_F_at_top)
    apply (rule filterlim_real_sequentially)
    apply (rule filterlim_compose) back
    apply (rule lim_F_at_bot)
    apply (subst filterlim_uminus_at_top [symmetric])
    by (rule filterlim_real_sequentially)
  then interpret M: real_distribution ?M .
  have "cdf ?M = F"
    apply (rule distrib_unique)
    prefer 3 apply (rule lim_F_at_bot)
    prefer 2 apply (rule M.cdf_lim_at_bot)
    apply (auto simp add: cdf_def M.finite_measure_Diff [symmetric])
    apply (subgoal_tac "{..x} - {..y} = {y<..x}")
    prefer 2 apply force
    apply (erule ssubst)
    apply (unfold measure_def)
    apply (subst emeasure_measure_of)
    apply (rule refl)
    apply auto
    using 2 apply (auto simp add: measure_space_def)
    apply (subst 1)
    by auto
  with 3 show ?thesis by blast 
qed

end



