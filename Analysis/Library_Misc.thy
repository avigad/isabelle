theory Library_Misc
imports Probability "~~/src/HOL/Library/ContNotDenum"
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

(* TODO: move these elsewhere *)

lemma (in prob_space) indep_vars_compose2:
  assumes "indep_vars M' X I"
  assumes rv: "\<And>i. i \<in> I \<Longrightarrow> Y i \<in> measurable (M' i) (N i)"
  shows "indep_vars N (\<lambda>i x. Y i (X i x)) I"
  using indep_vars_compose [OF assms] by (simp add: comp_def)

lemma (in prob_space) indep_vars_cmult:
  assumes "indep_vars (\<lambda>i. borel) X I" shows "indep_vars (\<lambda>i. borel) (\<lambda>i x. (c :: real) * X i x) I"
  using assms by (rule indep_vars_compose2) measurable

lemma (in prob_space) variance_mean_zero:
  "expectation X = 0 \<Longrightarrow> variance X = expectation (\<lambda>x. (X x)^2)"
by auto

lemma sqrt_at_top: "LIM x at_top. sqrt x :: real :> at_top"
  by (rule filterlim_at_top_at_top[where Q="\<lambda>x. True" and P="\<lambda>x. 0 < x" and g="power2"])
     (auto intro: eventually_gt_at_top)


(* it is funny that this isn't in the library! It could go in Transcendental *)
lemma exp_limit:
  fixes x :: real
  shows "((\<lambda>y.(1 + x * y) powr (1 / y)) ---> exp x) (at_right 0)"
proof - 
  have "((\<lambda>y. ln (1 + x * y)) has_real_derivative 1 * x) (at 0)"
    by (rule DERIV_chain'[where g=ln]) (auto intro!: derivative_eq_intros)
  hence 1: "((\<lambda>y. ln (1 + x * y) / y) ---> x) (at 0)"
    by (auto simp add: has_field_derivative_def field_has_derivative_at) 
  have 2: "(at_right 0) \<le> (at (0::real))"
    by (subst at_eq_sup_left_right, auto)
  have 3: "eventually (\<lambda>y. 0 < 1 + x * y) (at_right 0)"
    apply (case_tac "x = 0")
    apply auto
    apply (subst eventually_at_right)
    apply (rule_tac x = "1 / abs x" in exI)
    apply (auto simp add: field_simps)
    apply (case_tac "x >= 0")
    apply (auto simp add: field_simps)
    apply (rule add_pos_nonneg, auto)
    done
  have 4: "eventually (\<lambda>y. y > (0::real)) (at_right 0)"
    by (subst eventually_at_right, auto intro: gt_ex)
  have 5: "eventually (\<lambda>y. exp (ln ((1 + x * y) powr (1 / y))) =
         (1 + x * y) powr (1 / y)) (at_right 0)"
    apply (rule eventually_elim1 [OF eventually_conj [OF 3 4]])
    by (rule exp_ln, auto)
  have 6: "eventually (\<lambda>y. ln ((1 + x * y) powr (1 / y)) =
         ln (1 + x * y) / y) (at_right 0)"
    apply (rule eventually_elim1 [OF eventually_conj [OF 3 4]])
    apply (subst ln_powr)
    apply (case_tac "x = 0")
    by auto
  have "((\<lambda>y. ln ((1 + x * y) powr (1 / y))) ---> x) (at_right 0)"
    apply (subst filterlim_cong [OF refl refl 6])
    by (rule tendsto_mono [OF 2 1])
  hence "((\<lambda>y. exp (ln ((1 + x * y) powr (1 / y)))) ---> exp x) (at_right 0)"
    by (rule tendsto_exp)
  thus "((\<lambda>y.(1 + x * y) powr (1 / y)) ---> exp x) (at_right 0)"
    by (rule Lim_transform_eventually [OF 5])
qed

lemma exp_limit':
  fixes x :: real
  shows "((\<lambda>y. (1 + x / y) powr y) ---> exp x) at_top"

  apply (subst filterlim_at_top_to_right)
  apply (simp add: inverse_eq_divide)
by (rule exp_limit)

lemma exp_limit'':
  fixes x :: real
  shows "(\<lambda>n. (1 + x / n) ^ n) ----> exp x"
proof -
  from reals_Archimedean2 [of "abs x"] obtain n :: nat where *: "real n > abs x" ..
  hence "eventually (\<lambda>n :: nat. 0 < 1 + x / real n) at_top"
    apply (intro eventually_sequentiallyI [of n])
    apply (case_tac "x \<ge> 0")
    apply (rule add_pos_nonneg, auto intro: divide_nonneg_nonneg)
    apply (subgoal_tac "x / real xa > -1")
    by (auto simp add: field_simps)
  hence *: "eventually (\<lambda>n. (1 + x / n) powr n = (1 + x / n) ^ n) at_top"
    apply (rule eventually_elim1)
    by (erule powr_realpow)
  thus ?thesis
    apply (rule Lim_transform_eventually)
    by (rule filterlim_compose [OF exp_limit' filterlim_real_sequentially])
qed


(** Inequality for difference of complex products. **)
(* probably generalizes to real_normed_algebra_1,(comm_)monoid_mult *)
lemma complex_prod_diff [rule_format]:
  fixes 
    z :: "nat \<Rightarrow> complex" and
    w :: "nat \<Rightarrow> complex" and
    m :: nat
  shows "(\<forall> i < m. cmod (z i) \<le> 1) & (\<forall> i < m. cmod (w i) \<le> 1) \<longrightarrow> 
    norm ((\<Prod> i < m. z i) - (\<Prod> i < m. w i)) \<le> (\<Sum> i < m. cmod (z i - w i))" 
      (is "?H1 m & ?H2 m \<longrightarrow> ?P m") 
proof (induct m)
  let "?Q m" = "?H1 m & ?H2 m \<longrightarrow> ?P m"
  show "?Q 0" by auto
next
  let "?Q m" = "?H1 m & ?H2 m \<longrightarrow> ?P m"
  fix m
  assume ih: "?Q m"
  show "?Q (Suc m)"
  proof (clarify)
    assume zbnd: "?H1 (Suc m)"
       and wbnd : "?H2 (Suc m)"
    with ih have ih1: "?P m" by auto
    show "?P (Suc m)"
    proof -
      have "cmod ((\<Prod> i < Suc m. z i) - (\<Prod> i < Suc m. w i)) = 
        cmod ((\<Prod> i < Suc m. z i) - w m * (\<Prod> i < m. z i) + w m *
        (\<Prod> i < m. z i) - (\<Prod> i < Suc m. w i))"
        by auto
      also have "... = cmod ((\<Prod> i < m. z i) * (z m - w m) + 
        ((\<Prod> i < m. z i) - (\<Prod> i < m. w i)) * w m)"
        (is "?lhs = cmod (?t1 + ?t2)")
        by (auto simp add: field_simps)
      also have "... \<le> cmod(?t1) + cmod(?t2)"
        by (rule norm_triangle_ineq)
      also have "cmod(?t1) \<le> cmod(z m - w m)"
        apply (subst norm_mult)
        apply (rule mult_left_le_one_le, auto)
        apply (subst norm_setprod)
        apply (subst setprod_1 [symmetric])
        apply simp
        apply (rule order_trans)
        apply (rule setprod_mono[of "{..<m}" "\<lambda>i. cmod (z i)" "\<lambda>i. 1"])
        apply (auto intro: zbnd [rule_format])
        done
      also have "cmod(?t2) \<le> cmod((\<Prod> i < m. z i) - (\<Prod> i < m. w i))"
        apply (subst norm_mult)
        apply (rule mult_right_le_one_le)
        apply (auto simp add: wbnd)
        done
      also have "... \<le> (\<Sum> i < m. cmod (z i - w i))"
        by (rule ih1)
      finally show ?thesis
        by (auto simp add: add_ac)
    qed
  qed
qed

lemma complex_power_diff [rule_format]: 
  fixes z w :: complex and m :: nat
  assumes "cmod z \<le> 1" "cmod w \<le> 1"
  shows "cmod (z^m - w^m) \<le> m * cmod (z - w)"
proof -
  have "cmod (z^m - w^m) = cmod ((\<Prod> i < m. z) - (\<Prod> i < m. w))" by (simp add: setprod_constant)
  also have "\<dots> \<le> (\<Sum> i < m. cmod (z - w))" by (intro complex_prod_diff, simp add: assms)
  also have "\<dots> = m * cmod (z - w)" by (simp add: real_of_nat_def)
  finally show ?thesis .
qed

(*
  TODO: move elsewhere 
*)

lemma borel_measurable_sgn [measurable (raw)]:
  fixes f :: "real \<Rightarrow> real"
  assumes "f \<in> borel_measurable M"
  shows "(\<lambda>x. sgn (f x)) \<in> borel_measurable M"
proof -
  have "(\<lambda>x. sgn (f x)) = (\<lambda>x. indicator {0<..} (f x) - indicator {..<0} (f x))"
    unfolding indicator_def by auto
  thus ?thesis
    apply (elim ssubst) 
    using assms by measurable
qed

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


(* TODO: should this be a simp rule? *)
lemma complex_of_real_indicator: "complex_of_real (indicator A x) = indicator A x"
  by (simp split: split_indicator)

lemma sin_x_le_x: "x \<ge> 0 \<Longrightarrow> sin x \<le> x"
proof -
  fix x :: real 
  assume "x \<ge> 0"
  let ?f = "\<lambda>x. x - sin x"
  have "?f x \<ge> ?f 0"
    apply (rule DERIV_nonneg_imp_nondecreasing [OF `x \<ge> 0`])
    apply auto
    apply (rule_tac x = "1 - cos x" in exI)
    apply (auto intro!: derivative_intros)
    by (simp add: field_simps)
  thus "sin x \<le> x" by simp
qed

lemma sin_x_ge_neg_x: "x \<ge> 0 \<Longrightarrow> sin x \<ge> - x"
proof -
  fix x :: real 
  assume "x \<ge> 0"
  let ?f = "\<lambda>x. x + sin x"
  have "?f x \<ge> ?f 0"
    apply (rule DERIV_nonneg_imp_nondecreasing [OF `x \<ge> 0`])
    apply auto
    apply (rule_tac x = "1 + cos x" in exI)
    apply (auto intro!: derivative_intros)
    by (metis cos_ge_minus_one real_0_le_add_iff)
  thus "sin x \<ge> -x" by simp
qed

lemma abs_sin_x_le_abs_x: "abs (sin x) \<le> abs x"
  using sin_x_ge_neg_x [of x] sin_x_le_x [of x] sin_x_ge_neg_x [of "-x"] sin_x_le_x [of "-x"]
  by (case_tac "x \<ge> 0", auto)


lemma borel_measurable_root [measurable]: "(root n) \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_on1 continuous_intros)

lemma borel_measurable_sqrt [measurable]: "sqrt \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_on1 continuous_intros)

lemma borel_measurable_power [measurable (raw)]:
   fixes f :: "_ \<Rightarrow> 'b::{power,real_normed_algebra}"
   assumes f: "f \<in> borel_measurable M"
   shows "(\<lambda>x. (f x) ^ n) \<in> borel_measurable M"
   by (intro borel_measurable_continuous_on [OF _ f] continuous_intros)

lemma borel_measurable_Re [measurable]: "Re \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_on1 continuous_intros)

lemma borel_measurable_Im [measurable]: "Im \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_on1 continuous_intros)

lemma borel_measurable_of_real [measurable]: "(of_real :: _ \<Rightarrow> (_::real_normed_algebra)) \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_on1 continuous_intros)

(* 
    Things that belong somewhere else 
*)

(* TODO: Move and merge with has_integral_lebesgue_integral *)
lemma has_integral_lebesgue_integral:
  fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes f:"integrable lborel f"
  shows "(f has_integral (integral\<^sup>L lborel f)) UNIV"
proof -
  let ?F = "\<lambda>x. \<Sum>b\<in>Basis. (f x \<bullet> b) *\<^sub>R b"
  { fix b
    have "((\<lambda>x. f x \<bullet> b) has_integral (integral\<^sup>L lborel (\<lambda>x. f x \<bullet> b))) UNIV"
      by (intro has_integral_lebesgue_integral integrable_inner_left f) }
  then have "(?F has_integral (\<Sum>b\<in>Basis. integral\<^sup>L lborel (\<lambda>x. f x \<bullet> b) *\<^sub>R b)) UNIV"
    by (auto intro!: has_integral_setsum has_integral_scaleR_left)
  also have "(\<Sum>b\<in>Basis. integral\<^sup>L lborel (\<lambda>x. f x \<bullet> b) *\<^sub>R b) = integral\<^sup>L lborel ?F"
    using f by simp
  finally show ?thesis
    unfolding euclidean_representation .
qed

lemma continuous_image_closed_interval:
  fixes a b :: real and f :: "real \<Rightarrow> real"
  defines "S \<equiv> {a..b}"
  assumes "a \<le> b" and f: "continuous_on S f"
  shows "\<exists>c d. f`S = {c..d} \<and> c \<le> d"
proof -
  have S: "compact S" "S \<noteq> {}"
    using `a \<le> b` by (auto simp: S_def)
  obtain c where "c \<in> S" "\<forall>d\<in>S. f d \<le> f c"
    using continuous_attains_sup[OF S f] by auto
  moreover obtain d where "d \<in> S" "\<forall>c\<in>S. f d \<le> f c"
    using continuous_attains_inf[OF S f] by auto
  moreover have "connected (f`S)"
    using connected_continuous_image[OF f] connected_Icc by (auto simp: S_def)
  ultimately have "f ` S = {f d .. f c} \<and> f d \<le> f c"
    by (auto simp: connected_iff_interval)
  then show ?thesis
    by auto
qed

lemma tendsto_at_within_iff_tendsto_nhds:
  "(g ---> g l) (at l within S) \<longleftrightarrow> (g ---> g l) (inf (nhds l) (principal S))"
  unfolding tendsto_def eventually_at_filter eventually_inf_principal
  by (intro ext all_cong imp_cong) (auto elim!: eventually_elim1)

lemma tendsto_at_iff_sequentially:
  fixes f :: "'a :: first_countable_topology \<Rightarrow> _"
  shows "(f ---> a) (at x within s) \<longleftrightarrow> (\<forall>X. (\<forall>i. X i \<in> s - {x}) \<longrightarrow> X ----> x \<longrightarrow> ((f \<circ> X) ----> a))"
  unfolding filterlim_def[of _ "nhds a"] le_filter_def eventually_filtermap at_within_def eventually_nhds_within_iff_sequentially comp_def
  by metis

(* a slight generalization of eventually_at_right *)
lemma eventually_at_right':
  fixes x :: "'a :: linorder_topology"
  assumes gt_ex: "x < y"
  shows "eventually P (at_right x) \<longleftrightarrow> (\<exists>b. x < b \<and> (\<forall>z. x < z \<and> z < b \<longrightarrow> P z))"
  unfolding eventually_at_topological
proof safe
  note gt_ex
  moreover fix S assume "open S" "x \<in> S" note open_right[OF this, of y]
  moreover assume "\<forall>s\<in>S. s \<noteq> x \<longrightarrow> s \<in> {x<..} \<longrightarrow> P s"
  ultimately show "\<exists>b>x. \<forall>z. x < z \<and> z < b \<longrightarrow> P z"
    by (auto simp: subset_eq Ball_def)
next
  fix b assume "x < b" "\<forall>z. x < z \<and> z < b \<longrightarrow> P z"
  then show "\<exists>S. open S \<and> x \<in> S \<and> (\<forall>xa\<in>S. xa \<noteq> x \<longrightarrow> xa \<in> {x<..} \<longrightarrow> P xa)"
    by (intro exI[of _ "{..< b}"]) auto
qed

lemma eventually_at_left':
  fixes x :: "'a :: linorder_topology"
  assumes lt_ex: "y < x"
  shows "eventually P (at_left x) \<longleftrightarrow> (\<exists>b. x > b \<and> (\<forall>z. b < z \<and> z < x \<longrightarrow> P z))"
  unfolding eventually_at_topological
proof safe
  note lt_ex
  moreover fix S assume "open S" "x \<in> S" note open_left[OF this, of y]
  moreover assume "\<forall>s\<in>S. s \<noteq> x \<longrightarrow> s \<in> {..<x} \<longrightarrow> P s"
  ultimately show "\<exists>b<x. \<forall>z. b < z \<and> z < x \<longrightarrow> P z"
    by (auto simp: subset_eq Ball_def)
next
  fix b assume "b < x" "\<forall>z. b < z \<and> z < x \<longrightarrow> P z"
  then show "\<exists>S. open S \<and> x \<in> S \<and> (\<forall>s\<in>S. s \<noteq> x \<longrightarrow> s \<in> {..<x} \<longrightarrow> P s)"
    by (intro exI[of _ "{b <..}"]) auto
qed

lemma eventually_at_right_top: "at_right (top::_::{order_top, linorder_topology}) = bot"
  unfolding filter_eq_iff eventually_at_topological by auto

lemma eventually_at_left_bot: "at_left (bot::_::{order_bot, linorder_topology}) = bot"
  unfolding filter_eq_iff eventually_at_topological by auto

lemma integrable_mult_indicator:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  shows "A \<in> sets M \<Longrightarrow> integrable M f \<Longrightarrow> integrable M (\<lambda>x. indicator A x *\<^sub>R f x)"
  by (rule integrable_bound[of M f]) (auto split: split_indicator)

lemma integrable_abs_iff:
  fixes f :: "'a \<Rightarrow> real"
  shows "f \<in> borel_measurable M \<Longrightarrow> integrable M (\<lambda>x. \<bar>f x\<bar>) \<longleftrightarrow> integrable M f"
  by (auto intro: integrable_abs_cancel)

lemmas sums_scaleR_left = bounded_linear.sums[OF bounded_linear_scaleR_left]

lemmas suminf_scaleR_left = bounded_linear.suminf[OF bounded_linear_scaleR_left]

lemma indicator_sums: 
  assumes "\<And>i j. i \<noteq> j \<Longrightarrow> A i \<inter> A j = {}"
  shows "(\<lambda>i. indicator (A i) x::real) sums indicator (\<Union>i. A i) x"
proof cases
  assume "\<exists>i. x \<in> A i"
  then obtain i where i: "x \<in> A i" ..
  with assms have "(\<lambda>i. indicator (A i) x::real) sums (\<Sum>i\<in>{i}. indicator (A i) x)"
    by (intro sums_finite) (auto split: split_indicator)
  also have "(\<Sum>i\<in>{i}. indicator (A i) x) = indicator (\<Union>i. A i) x"
    using i by (auto split: split_indicator)
  finally show ?thesis .
qed simp

(* TODO: refactor *)
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
  case 0 show ?case by (intro exI[of _ "{}"]) auto
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

lemma continuous_on_vector_derivative:
  "(\<And>x. x \<in> S \<Longrightarrow> (f has_vector_derivative f' x) (at x within S)) \<Longrightarrow> continuous_on S f"
  by (auto simp: continuous_on_eq_continuous_within intro!: has_vector_derivative_continuous)


lemma measure_restrict_space:
    "\<Omega> \<in> sets M \<Longrightarrow> A \<subseteq> \<Omega> \<Longrightarrow> measure (restrict_space M \<Omega>) A = measure M A"
  unfolding measure_def by (subst emeasure_restrict_space, auto)

lemma lebesgue_measure_interval: "a \<le> b \<Longrightarrow> measure lborel {a..b} = b - a"
 unfolding measure_def by auto

lemma distr_cong_AE:
  assumes 1: "M = K" "sets N = sets L" and 
    2: "(AE x in M. f x = g x)" and "f \<in> measurable M N" and "g \<in> measurable K L"
  shows "distr M N f = distr K L g"
proof (rule measure_eqI)
  fix A assume "A \<in> sets (distr M N f)"
  with assms show "emeasure (distr M N f) A = emeasure (distr K L g) A"
    by (auto simp add: emeasure_distr intro!: emeasure_eq_AE measurable_sets)
qed (insert 1, simp)


lemma of_rat_dense:
  fixes x y :: real
  assumes "x < y"
  shows "\<exists>q :: rat. x < of_rat q \<and> of_rat q < y"
using Rats_dense_in_real [OF `x < y`]
by (auto elim: Rats_cases)


lemma continuous_within_open: "a \<in> A \<Longrightarrow> open A \<Longrightarrow> (continuous (at a within A) f) = isCont f a"
  by (simp add: continuous_within, rule Lim_within_open)


lemma emeasure_lborel_countable:
  fixes A :: "real set"
  assumes "countable A"
  shows "emeasure lborel A = 0"
proof -
  have "A \<subseteq> (\<Union>i. {from_nat_into A i})" using from_nat_into_surj assms by force
  moreover have "emeasure lborel (\<Union>i. {from_nat_into A i}) = 0"
    by (rule emeasure_UN_eq_0) auto
  ultimately have "emeasure lborel A \<le> 0" using emeasure_mono
    by (metis assms bot.extremum_unique emeasure_empty image_eq_UN range_from_nat_into sets.empty_sets)
  thus ?thesis by (auto simp add: emeasure_le_0_iff)
qed

lemma closed_Collect_imp: assumes "open {x. P x}" "closed {x. Q x}" shows "closed {x. P x \<longrightarrow> Q x}"
proof -
  have *: "{x. P x \<longrightarrow> Q x} = - {x. P x} \<union> {x. Q x}"
    by auto
  show ?thesis
    unfolding * by (intro closed_Un closed_Compl assms)
qed

lemma open_Collect_conj: assumes "open {x. P x}" "open {x. Q x}" shows "open {x. P x \<and> Q x}"
proof -
  have *: "{x. P x \<and> Q x} = {x. P x} \<inter> {x. Q x}"
    by auto
  show ?thesis
    unfolding * by (intro open_Int assms)
qed

lemma isCont_borel:
  fixes f :: "'b::metric_space \<Rightarrow> 'a::metric_space"
  shows "{x. isCont f x} \<in> sets borel"
proof -
  let ?I = "\<lambda>j. inverse(real (Suc j))"

  { fix x
    have "isCont f x = (\<forall>i. \<exists>j. \<forall>y z. dist x y < ?I j \<and> dist x z < ?I j \<longrightarrow> dist (f y) (f z) \<le> ?I i)"
      unfolding continuous_at_eps_delta
    proof safe
      fix i assume "\<forall>e>0. \<exists>d>0. \<forall>y. dist y x < d \<longrightarrow> dist (f y) (f x) < e"
      moreover have "0 < ?I i / 2"
        by simp
      ultimately obtain d where d: "0 < d" "\<And>y. dist x y < d \<Longrightarrow> dist (f y) (f x) < ?I i / 2"
        by (metis dist_commute)
      then obtain j where j: "?I j < d"
        by (metis reals_Archimedean)

      show "\<exists>j. \<forall>y z. dist x y < ?I j \<and> dist x z < ?I j \<longrightarrow> dist (f y) (f z) \<le> ?I i"
      proof (safe intro!: exI[where x=j])
        fix y z assume *: "dist x y < ?I j" "dist x z < ?I j"
        have "dist (f y) (f z) \<le> dist (f y) (f x) + dist (f z) (f x)"
          by (rule dist_triangle2)
        also have "\<dots> < ?I i / 2 + ?I i / 2"
          by (intro add_strict_mono d less_trans[OF _ j] *)
        also have "\<dots> \<le> ?I i"
          by (simp add: field_simps real_of_nat_Suc)
        finally show "dist (f y) (f z) \<le> ?I i"
          by simp
      qed
    next
      fix e::real assume "0 < e"
      then obtain n where n: "?I n < e"
        by (metis reals_Archimedean)
      assume "\<forall>i. \<exists>j. \<forall>y z. dist x y < ?I j \<and> dist x z < ?I j \<longrightarrow> dist (f y) (f z) \<le> ?I i"
      from this[THEN spec, of "Suc n"]
      obtain j where j: "\<And>y z. dist x y < ?I j \<Longrightarrow> dist x z < ?I j \<Longrightarrow> dist (f y) (f z) \<le> ?I (Suc n)"
        by auto
      
      show "\<exists>d>0. \<forall>y. dist y x < d \<longrightarrow> dist (f y) (f x) < e"
      proof (safe intro!: exI[of _ "?I j"])
        fix y assume "dist y x < ?I j"
        then have "dist (f y) (f x) \<le> ?I (Suc n)"
          by (intro j) (auto simp: dist_commute)
        also have "?I (Suc n) < ?I n"
          by simp
        also note n
        finally show "dist (f y) (f x) < e" .
      qed simp
    qed }
  note * = this

  have **: "\<And>e y. open {x. dist x y < e}"
    using open_ball by (simp_all add: ball_def dist_commute)

  have "{x\<in>space borel. isCont f x } \<in> sets borel"
    unfolding *
    apply (intro sets.sets_Collect_countable_All sets.sets_Collect_countable_Ex)
    apply (simp add: Collect_all_eq)
    apply (intro borel_closed closed_INT ballI closed_Collect_imp open_Collect_conj **)
    apply auto
    done
  then show ?thesis
    by simp
qed

lemma isCont_indicator: 
  fixes x :: "'a::{t2_space}"
  shows "isCont (indicator A :: 'a \<Rightarrow> real) x = (x \<notin> frontier A)"
proof -
  have *: "!! A x. (indicator A x > (0 :: real)) = (x \<in> A)"
    by (case_tac "x : A", auto)
  have **: "!! A x. (indicator A x < (1 :: real)) = (x \<notin> A)"
    by (case_tac "x : A", auto)
  show ?thesis
    apply (auto simp add: frontier_def)
    (* calling auto here produces a strange error message *)
    apply (subst (asm) continuous_at_open)
    apply (case_tac "x \<in> A", simp_all)
    apply (drule_tac x = "{0<..}" in spec, clarsimp simp add: *)
    apply (erule interiorI, assumption, force)
    apply (drule_tac x = "{..<1}" in spec, clarsimp simp add: **)
    apply (subst (asm) closure_interior, auto, erule notE)
    apply (erule interiorI, auto)
    apply (subst (asm) closure_interior, simp)
    apply (rule continuous_on_interior)
    prefer 2 apply assumption
    apply (rule continuous_on_eq [where f = "\<lambda>x. 0"], auto intro: continuous_on_const)
    apply (rule continuous_on_interior)
    prefer 2 apply assumption
    by (rule continuous_on_eq [where f = "\<lambda>x. 1"], auto intro: continuous_on_const)
qed


lemma AE_lborel_singleton: "AE x in lborel. x \<noteq> c"
  by (intro AE_I[where N="{c}"]) auto

lemma emeasure_insert':
  "A \<noteq> {} \<Longrightarrow> {x} \<in> sets M \<Longrightarrow> A \<in> sets M \<Longrightarrow> x \<notin> A \<Longrightarrow> emeasure M (insert x A) = emeasure M {x} + emeasure M A"
    by (rule emeasure_insert) 


(* the dual version is in Convex_Euclidean_Space.thy *)

lemma interior_real_semiline2:
  fixes a :: real
  shows "interior {..a} = {..<a}"
proof -
  {
    fix y
    assume "a > y"
    then have "y \<in> interior {..a}"
      apply (simp add: mem_interior)
      apply (rule_tac x="(a-y)" in exI)
      apply (auto simp add: dist_norm)
      done
  }
  moreover
  {
    fix y
    assume "y \<in> interior {..a}"
    then obtain e where e: "e > 0" "cball y e \<subseteq> {..a}"
      using mem_interior_cball[of y "{..a}"] by auto
    moreover from e have "y + e \<in> cball y e"
      by (auto simp add: cball_def dist_norm)
    ultimately have "a \<ge> y + e" by auto
    then have "a > y" using e by auto
  }
  ultimately show ?thesis by auto
qed

lemma frontier_real_atMost:
  fixes a :: real
  shows "frontier {..a} = {a}"
  unfolding frontier_def by (auto simp add: interior_real_semiline2)



(*
(*** NOTE: The following three lemmata are solved directly by theorems in Library_Misc. ***)
convergent_real_imp_convergent_ereal(2)

(* name clash with the version in Extended_Real_Limits *)
lemma convergent_ereal': "convergent (X :: nat \<Rightarrow> real) \<Longrightarrow> convergent (\<lambda>n. ereal (X n))"
  apply (drule convergentD, auto)
  apply (rule convergentI)
  by (subst lim_ereal, assumption)

lemma lim_ereal': "convergent X \<Longrightarrow> lim (\<lambda>n. ereal (X n)) = ereal (lim X)"
    by (rule limI, simp add: convergent_LIMSEQ_iff)
*)

(**************************************************)

lemma limsup_le_liminf_real:
  fixes X :: "nat \<Rightarrow> real" and L :: real
  assumes 1: "limsup X \<le> L" and 2: "L \<le> liminf X"
  shows "X ----> L"
proof -
  from 1 2 have "limsup X \<le> liminf X" by auto
  hence 3: "limsup X = liminf X"  
    apply (subst eq_iff, rule conjI)
    by (rule Liminf_le_Limsup, auto)
  hence 4: "convergent (\<lambda>n. ereal (X n))"
    by (subst convergent_ereal)
  hence "limsup X = lim (\<lambda>n. ereal(X n))"
    by (rule convergent_limsup_cl)
  also from 1 2 3 have "limsup X = L" by auto
  finally have "lim (\<lambda>n. ereal(X n)) = L" ..
  hence "(\<lambda>n. ereal (X n)) ----> L"
    apply (elim subst)
    by (subst convergent_LIMSEQ_iff [symmetric], rule 4) 
  thus ?thesis by simp
qed


lemma integrableI_bounded_set:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes [measurable]: "A \<in> sets M" "f \<in> borel_measurable M"
  assumes finite: "emeasure M A < \<infinity>"
    and bnd: "AE x in M. x \<in> A \<longrightarrow> norm (f x) \<le> B"
    and null: "AE x in M. x \<notin> A \<longrightarrow> f x = 0"
  shows "integrable M f"
proof (rule integrableI_bounded)
  { fix x :: 'b have "norm x \<le> B \<Longrightarrow> 0 \<le> B"
      using norm_ge_zero[of x] by arith }
  with bnd null have "(\<integral>\<^sup>+ x. ereal (norm (f x)) \<partial>M) \<le> (\<integral>\<^sup>+ x. ereal (max 0 B) * indicator A x \<partial>M)"
    by (intro nn_integral_mono_AE) (auto split: split_indicator split_max)
  also have "\<dots> < \<infinity>"
    using finite by (subst nn_integral_cmult_indicator) (auto simp: max_def)
  finally show "(\<integral>\<^sup>+ x. ereal (norm (f x)) \<partial>M) < \<infinity>" .
qed simp

lemma integrableI_bounded_set_indicator:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  shows "A \<in> sets M \<Longrightarrow> f \<in> borel_measurable M \<Longrightarrow>
    emeasure M A < \<infinity> \<Longrightarrow> (AE x in M. x \<in> A \<longrightarrow> norm (f x) \<le> B) \<Longrightarrow>
    integrable M (\<lambda>x. indicator A x *\<^sub>R f x)"
  by (rule integrableI_bounded_set[where A=A]) auto

end