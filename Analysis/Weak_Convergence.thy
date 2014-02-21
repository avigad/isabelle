(*
Theory: Weak_Convergence.thy
Authors: Jeremy Avigad, Luke Serafin

Properties of weak convergence of functions and measures, including the portmanteau theorem.
*)

theory Weak_Convergence

imports Distribution_Functions Library_Misc Uncountable

begin

(* weak convergence of distribution functions *)
definition
  weak_conv :: "(nat \<Rightarrow> (real \<Rightarrow> real)) \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> bool"
where
  "weak_conv F_seq F \<equiv> \<forall>x. isCont F x \<longrightarrow> (\<lambda>n. F_seq n x) ----> F x"

(* weak convergence of distributions *)
definition
  weak_conv_m :: "(nat \<Rightarrow> real measure) \<Rightarrow> real measure \<Rightarrow> bool"
where
  "weak_conv_m M_seq M \<equiv> weak_conv (\<lambda>n. cdf (M_seq n)) (cdf M)"

(* weak convergence of random variables *)
abbreviation (in prob_space)
  "weak_conv_r X_seq X \<equiv> weak_conv_m (\<lambda>n. distr M borel (X_seq n)) (distr M borel X)" 
  
definition mono_on :: "('a::order \<Rightarrow> 'b::order) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "mono_on f A = (\<forall>x\<in>A. \<forall>y\<in>A. x \<le> y \<longrightarrow> f x \<le> f y)"

lemma borel_measurable_mono_on_fnc:
  fixes f :: "real \<Rightarrow> real" and  A :: "real set"
  assumes "mono_on f A" "A \<in> sets borel" "A \<noteq> {}" "bdd_below A"
  shows "f \<in> borel_measurable (restrict_space lborel A)"
apply (subst borel_measurable_iff_ge)
apply (subst sets_restrict_space, auto)
apply (subst space_restrict_space)
proof -
  def F \<equiv> "\<lambda>a. Inf (ereal ` {w \<in> A. a \<le> f w})"
  fix a :: real
  have monoF: "mono F" unfolding mono_def F_def
    by auto (rule Inf_superset_mono, auto simp add: image_mono)
  hence "{w. a \<le> F w} \<in> sets borel" using borel_measurable_mono_fnc
    by (smt dual_order.trans is_interval_1 mem_Collect_eq mono_def real_interval_borel_measurable)
  moreover have "{w \<in> A. a \<le> f w} = {w. a \<le> F w} \<inter> A" using monoF unfolding F_def sorry
  ultimately show "{w \<in> A. a \<le> f w} \<in> op \<inter> A ` sets borel" by auto
qed

lemma measure_restrict_space:
    "\<Omega> \<in> sets M \<Longrightarrow> A \<subseteq> \<Omega> \<Longrightarrow> measure (restrict_space M \<Omega>) A = measure M A"
  unfolding measure_def by (subst emeasure_restrict_space, auto)

lemma lebesgue_measure_interval: "a \<le> b \<Longrightarrow> measure lborel {a..b} = b - a"
 unfolding measure_def by auto

thm distr_cong

lemma distr_cong_AE:
  "M = K \<Longrightarrow> sets N = sets L \<Longrightarrow> (AE x in M. f x = g x) \<Longrightarrow> distr M N f = distr K L g"
  using sets_eq_imp_space_eq[of N L] distr_cong sorry (*by (simp add: distr_def Int_def cong: rev_conj_cong)*)
 
(* state using obtains? *)
theorem Skorohod:
  fixes 
    \<mu> :: "nat \<Rightarrow> real measure" and
    M :: "real measure"
  assumes 
    "\<And>n. real_distribution (\<mu> n)" and 
    "real_distribution M" and 
    "weak_conv_m \<mu> M"
  shows "\<exists> (\<Omega> :: real measure) (Y_seq :: nat \<Rightarrow> real \<Rightarrow> real) (Y :: real \<Rightarrow> real). 
    prob_space \<Omega> \<and>
    (\<forall>n. Y_seq n \<in> measurable \<Omega> borel) \<and>
    (\<forall>n. distr \<Omega> borel (Y_seq n) = \<mu> n) \<and>
    Y \<in> measurable \<Omega> lborel \<and>
    distr \<Omega> borel Y = M \<and>
    (\<forall>x \<in> space \<Omega>. (\<lambda>n. Y_seq n x) ----> Y x)"
proof -
  def f \<equiv> "\<lambda>n. cdf (\<mu> n)"
  def F \<equiv> "cdf M"
  have fn_weak_conv: "weak_conv f F" using assms(3) unfolding weak_conv_m_def f_def F_def by auto
  {  fix n
     interpret \<mu>: real_distribution "\<mu> n" by (rule assms)
     have "mono (f n)" "\<And>a. continuous (at_right a) (f n)" "((f n) ---> 1) at_top" "((f n) ---> 0) at_bot"
       by (auto simp add: f_def mono_def \<mu>.cdf_nondecreasing \<mu>.cdf_is_right_cont \<mu>.cdf_lim_at_top_prob \<mu>.cdf_lim_at_bot)
  } 
  note f_inc = this(1) and f_right_cts = this(2) and f_at_top = this(3) and f_at_bot = this(4)
  interpret M: real_distribution M by (rule assms)
  have F_inc: "mono F" unfolding F_def mono_def using M.cdf_nondecreasing by auto
  have F_right_cts: "\<And>a. continuous (at_right a) F"
    unfolding F_def using assms(2) M.cdf_is_right_cont by auto
  have F_at_top: "(F ---> 1) at_top" unfolding F_def using M.cdf_lim_at_top_prob by auto
  have F_at_bot: "(F ---> 0) at_bot" unfolding F_def using M.cdf_lim_at_bot by auto
  def \<Omega> \<equiv> "restrict_space lborel {0::real<..<1}"
  have prob_\<Omega>: "prob_space \<Omega>" sorry
  def Y_seq \<equiv> "\<lambda>n \<omega>. Inf {x. \<omega> \<le> f n x}"
  def Y \<equiv> "\<lambda>\<omega>. Inf {x. \<omega> \<le> F x}"
  have f_meas: "\<And>n. f n \<in> borel_measurable borel" using f_inc borel_measurable_mono_fnc by auto
  have Y_seq_le_iff: "\<And>n. \<forall>\<omega>\<in>{0<..<1}. \<forall>x. (\<omega> \<le> f n x) = (Y_seq n \<omega> \<le> x)"
  proof -
    fix n :: nat
    show "\<forall>\<omega>\<in>{0<..<1}. \<forall>x. (\<omega> \<le> f n x) = (Y_seq n \<omega> \<le> x)"
      unfolding Y_seq_def apply (rule bdd_rcont_inc_pseudoinverse[of 0 1 "f n"])
      unfolding rcont_inc_def using f_inc f_right_cts f_at_top f_at_bot by auto
  qed
  have Y_seq_mono_on: "\<And>n. mono_on (Y_seq n) {0<..<1}" unfolding mono_on_def
    using Y_seq_le_iff by (metis order.trans order_refl)
  hence Y_seq_meas: "\<And>n. (Y_seq n) \<in> borel_measurable \<Omega>" using borel_measurable_mono_on_fnc 
      unfolding \<Omega>_def
    by simp
  have Y_seq_emeasure_distr_\<Omega>: "\<And>n. emeasure (distr \<Omega> borel (Y_seq n)) UNIV = 1"
     apply (subst emeasure_distr)
     using Y_seq_meas unfolding \<Omega>_def 
     by (auto simp add: emeasure_restrict_space space_restrict_space)
  have "\<And>n. cdf (distr \<Omega> borel (Y_seq n)) = cdf (\<mu> n)"
  proof -
    fix n
    interpret \<mu>: real_distribution "\<mu> n" by (rule assms)
    show "cdf (distr \<Omega> borel (Y_seq n)) = cdf (\<mu> n)"
      apply (unfold cdf_def, rule ext)
      apply (subst measure_distr)
      apply (rule Y_seq_meas, auto)
      unfolding \<Omega>_def vimage_def apply auto
      apply (subst space_restrict_space)
      apply (subst Int_commute)
      thm Y_seq_le_iff[rule_format]
      apply (subst Int_def, simp)
      apply (subgoal_tac "{xa. 0 < xa \<and> xa < 1 \<and> Y_seq n xa \<le> x} = {xa. 0 < xa \<and> xa < 1 \<and> xa \<le> f n x}")
      apply (erule ssubst)
      prefer 2
      using Y_seq_le_iff apply auto [1]
      apply (subst measure_restrict_space, auto)
      unfolding f_def cdf_def
      apply (subgoal_tac "Sigma_Algebra.measure (\<mu> n) {..x} =
         measure lborel {0..Sigma_Algebra.measure (\<mu> n) {..x}}")
      prefer 2
      apply (subst lebesgue_measure_interval, auto simp add: measure_nonneg)
      apply (erule ssubst) back
      unfolding measure_def apply (rule arg_cong) back
      apply (rule emeasure_eq_AE, auto)
      apply (rule AE_I [of _ _ "{0, 1}"])
      apply auto
      apply (subst (asm) measure_def [symmetric])
      apply (subst order_less_le, auto)
      apply (erule order_trans, auto)
      by (metis lmeasure_eq_0 negligible_insert negligible_sing)
    qed
  hence Y_seq_distr: "\<And>n. distr \<Omega> borel (Y_seq n) = \<mu> n"
    apply (intro cdf_unique, auto simp add: assms)
    unfolding real_distribution_def apply auto
    unfolding prob_space_def apply auto
    unfolding prob_space_axioms_def real_distribution_axioms_def apply auto
    by (rule finite_measureI, auto simp add: Y_seq_emeasure_distr_\<Omega>)
  have F_meas: "F \<in> borel_measurable borel" using F_inc borel_measurable_mono_fnc by auto
  have Y_le_iff: "\<forall>\<omega>\<in>{0<..<1}. \<forall>x. (\<omega> \<le> F x) = (Y \<omega> \<le> x)"
    unfolding Y_def apply (rule bdd_rcont_inc_pseudoinverse[of 0 1 F])
    unfolding rcont_inc_def using F_inc F_right_cts F_at_top F_at_bot by auto
  have Y_mono_on: "mono_on Y {0<..<1}" unfolding mono_on_def
    using Y_le_iff by (metis order.trans order_refl)
  hence Y_meas: "Y \<in> borel_measurable \<Omega>" using borel_measurable_mono_on_fnc unfolding \<Omega>_def
    by simp
  have Y_emeasure_distr_\<Omega>: "emeasure (distr \<Omega> borel Y) UNIV = 1"
     apply (subst emeasure_distr)
     using Y_meas unfolding \<Omega>_def 
     by (auto simp add: emeasure_restrict_space space_restrict_space)
  have "cdf (distr \<Omega> borel Y) = cdf M"
  proof -
    interpret M: real_distribution M by (rule assms)
    show "cdf (distr \<Omega> borel Y) = cdf M"
      apply (unfold cdf_def, rule ext)
      apply (subst measure_distr)
      apply (rule Y_meas, auto)
      unfolding \<Omega>_def vimage_def apply auto
      apply (subst space_restrict_space)
      apply (subst Int_commute)
      thm Y_seq_le_iff[rule_format]
      apply (subst Int_def, simp)
      apply (subgoal_tac "{xa. 0 < xa \<and> xa < 1 \<and> Y xa \<le> x} = {xa. 0 < xa \<and> xa < 1 \<and> xa \<le> F x}")
      apply (erule ssubst)
      prefer 2
      using Y_le_iff apply auto [1]
      apply (subst measure_restrict_space, auto)
      unfolding F_def cdf_def
      apply (subgoal_tac "Sigma_Algebra.measure M {..x} =
         measure lborel {0..Sigma_Algebra.measure M {..x}}")
      prefer 2
      apply (subst lebesgue_measure_interval, auto simp add: measure_nonneg)
      apply (erule ssubst) back
      unfolding measure_def apply (rule arg_cong) back
      apply (rule emeasure_eq_AE, auto)
      apply (rule AE_I [of _ _ "{0, 1}"])
      apply auto
      apply (subst (asm) measure_def [symmetric])
      apply (subst order_less_le, auto)
      apply (erule order_trans, auto)
      by (metis lmeasure_eq_0 negligible_insert negligible_sing)
    qed
  hence Y_distr: "distr \<Omega> borel Y = M"
    apply (intro cdf_unique, auto simp add: assms)
    unfolding real_distribution_def apply auto
    unfolding prob_space_def apply auto
    unfolding prob_space_axioms_def real_distribution_axioms_def apply auto
    by (rule finite_measureI, auto simp add: Y_emeasure_distr_\<Omega>)
  {
    fix \<omega>::real assume \<omega>: "\<omega> \<in> {0<..<1}" "continuous (at \<omega>) Y"
    have "liminf (\<lambda>n. Y_seq n \<omega>) \<ge> Y \<omega>"
    proof (subst liminf_bounded_iff, auto)
      fix B :: ereal assume B: "B < ereal (Y \<omega>)"
      show "\<exists>N. \<forall>n\<ge>N. B < ereal (Y_seq n \<omega>)"
        apply (rule ereal_cases[of B])
        prefer 2 using B less_ereal.simps(4) apply auto
        proof -
          fix r :: real assume r: "r < Y \<omega>"
          hence "uncountable {r<..<Y \<omega>}" using open_interval_uncountable by simp
          with M.countable_atoms uncountable_minus_countable
          have "uncountable ({r<..<Y \<omega>} - {x. measure M {x} > 0})" by auto
          then obtain x where *: "x \<in> {r<..<Y \<omega>} - {x. measure M {x} > 0}"
            unfolding uncountable_def by blast
          hence x: "r < x" "x < Y \<omega>" "measure M {x} = 0"
            using DiffD1 greaterThanLessThan_iff measure_nonneg[of M "{x}"] by (simp_all add: linorder_not_less)
          with Y_le_iff \<omega> have Fx_less: "F x < \<omega>" using not_less by blast
          from fn_weak_conv M.isCont_cdf x(3) have 1: "(\<lambda>n. f n x) ----> F x"
            unfolding F_def weak_conv_def by auto
          have "\<exists>N. \<forall>n\<ge>N. f n x < \<omega>"
            apply (insert 1)
            apply (drule LIMSEQ_D[of _ _ "\<omega> - F x"])
            using Fx_less apply auto by smt
          hence "\<exists>N. \<forall>n\<ge>N. x < Y_seq n \<omega>" using Y_seq_le_iff \<omega>(1) not_less by metis
          thus "\<exists>N. \<forall>n\<ge>N. r < Y_seq n \<omega>" using x(1) by (metis less_trans) 
        qed
    qed
    moreover have "limsup (\<lambda>n. Y_seq n \<omega>) \<le> Y \<omega>"
    proof -
      { fix \<omega>' :: real assume \<omega>': "0 < \<omega>'" "\<omega>' < 1" "\<omega> < \<omega>'"
        { fix \<epsilon> :: real assume \<epsilon>: "\<epsilon> > 0"
          hence "uncountable {Y \<omega>'<..<Y \<omega>' + \<epsilon>}" using open_interval_uncountable by simp
          with M.countable_atoms uncountable_minus_countable
          have "uncountable ({Y \<omega>'<..<Y \<omega>' + \<epsilon>} - {x. measure M {x} > 0})" by auto
          then obtain y where *: "y \<in> {Y \<omega>'<..<Y \<omega>' + \<epsilon>} - {x. measure M {x} > 0}"
            unfolding uncountable_def by blast
          hence y: "Y \<omega>' < y" "y < Y \<omega>' + \<epsilon>" "measure M {y} = 0"
            using DiffD1 greaterThanLessThan_iff measure_nonneg[of M "{y}"] by (simp_all add: linorder_not_less)
          with Y_le_iff \<omega>' have "\<omega>' \<le> F (Y \<omega>')" by (metis greaterThanLessThan_iff order_refl)
          also from y have "... \<le> F y" using F_inc unfolding mono_def by auto
          finally have Fy_gt: "\<omega> < F y" using \<omega>'(3) by simp
          from fn_weak_conv M.isCont_cdf y(3) have 1: "(\<lambda>n. f n y) ----> F y"
            unfolding F_def weak_conv_def by auto
          have "\<exists>N. \<forall>n\<ge>N. \<omega> \<le> f n y"
            apply (insert 1)
            apply (drule LIMSEQ_D[of _ _ "F y - \<omega>"])
            using Fy_gt apply auto by smt
          hence 2: "\<exists>N. \<forall>n\<ge>N. Y_seq n \<omega> \<le> y" using Y_seq_le_iff \<omega>(1) by metis
          hence "limsup (\<lambda>n. Y_seq n \<omega>) \<le> y"
            apply (subst (asm) eventually_sequentially[of "\<lambda>n. Y_seq n \<omega> \<le> y",symmetric])
            using Limsup_mono[of "\<lambda>n. Y_seq n \<omega>" "\<lambda>n. y" sequentially] apply auto
            by (metis Limsup_bounded eq_iff eventually_sequentiallyI order.trans trivial_limit_sequentially)
          hence "limsup (\<lambda>n. Y_seq n \<omega>) < Y \<omega>' + \<epsilon>" using y(2)
            by (smt dual_order.antisym dual_order.trans le_cases less_eq_ereal_def less_ereal.simps(1))
        }
        hence "limsup (\<lambda>n. Y_seq n \<omega>) \<le> Y \<omega>'"
          by (metis ereal_le_epsilon2 order.strict_implies_order plus_ereal.simps(1))
      } note * = this
      show "limsup (\<lambda>n. Y_seq n \<omega>) \<le> Y \<omega>" (*using \<omega> Y_mono_on bdd_rcont_inc_pseudoinverse unfolding Y_def
        using F_inc F_right_cts F_at_top F_at_bot *) (* These are probably not all needed. *)
      proof (rule ereal_le_epsilon2, auto)
        fix \<epsilon>::real assume \<epsilon>: "\<epsilon> > 0"
        from \<omega>(2) obtain \<omega>' where \<omega>': "\<omega>' \<in> {0<..<1}" "\<omega> < \<omega>'" "Y \<omega>' \<le> Y \<omega> + \<epsilon>" sorry
        with * have "limsup (\<lambda>n. Y_seq n \<omega>) \<le> Y \<omega>'" by auto
        with \<omega>'(3) show "limsup (\<lambda>n. Y_seq n \<omega>) \<le> Y \<omega> + \<epsilon>" by (metis ereal_less_eq(3) order.trans)
      qed
    qed
    ultimately have "(\<lambda>n. Y_seq n \<omega>) ----> Y \<omega>" using Liminf_le_Limsup
      by (metis Liminf_eq_Limsup dual_order.antisym dual_order.trans lim_ereal trivial_limit_sequentially)
  } note Y_cts_cnv = this
  have Y_cts_iff: "\<forall>\<omega>\<in>{0<..<1}. continuous (at \<omega>) Y = (emeasure M {\<omega>} = 0)" sorry
  let ?D = "{\<omega>\<in>{0<..<1}. \<not> continuous (at \<omega>) Y}"
  thm M.countable_atoms
  have D: "emeasure lborel ?D = 0" sorry
  def Y' \<equiv> "\<lambda>\<omega>. (case \<omega>\<in>?D of True => 0 | False => Y \<omega>)"
  have Y'_AE: "AE \<omega> in M. Y' \<omega> = Y \<omega>" sorry
  def Y_seq' \<equiv> "\<lambda>n \<omega>. (case \<omega>\<in>?D of True => 0 | False => Y_seq n \<omega>)"
  have Y_seq'_AE: "\<And>n. AE \<omega> in M. Y_seq' n \<omega> = Y_seq n \<omega>" sorry
  have Y'_cnv: "\<forall>\<omega>\<in>{0<..<1}. (\<lambda>n. Y_seq' n \<omega>) ----> Y' \<omega>"
  proof
    fix \<omega>::real assume \<omega>: "\<omega> \<in> {0<..<1}"
    show "(\<lambda>n. Y_seq' n \<omega>) ----> Y' \<omega>"
    proof (cases "\<omega> \<in> ?D")
      assume \<omega>D: "\<omega> \<in> ?D"
      hence "\<And>n. Y_seq' n \<omega> = 0" unfolding Y_seq'_def by auto
      moreover have "Y' \<omega> = 0" using \<omega>D unfolding Y'_def by auto
      ultimately show ?thesis by auto
    next
      assume \<omega>D: "\<omega> \<notin> ?D"
      hence "continuous (at \<omega>) Y" using \<omega> by auto
      moreover have "\<And>n. Y_seq' n \<omega> = Y_seq n \<omega>" using \<omega>D unfolding Y_seq'_def by auto
      moreover have "Y' \<omega> = Y \<omega>" using \<omega>D unfolding Y'_def by auto
      ultimately show ?thesis using Y_cts_cnv sorry
    qed
  qed
  have "\<And>n. Y_seq' n \<in> borel_measurable \<Omega>" using Y_seq_meas Y_seq'_AE sorry
  moreover have "\<And>n. distr \<Omega> borel (Y_seq' n) = \<mu> n"
    using Y_seq_distr Y_seq'_AE distr_cong_AE[where f = "Y_seq' n" and g = "Y_seq n"] sorry
  moreover have "Y \<in> borel_measurable \<Omega>" using Y_meas Y'_AE sorry
  moreover have "distr \<Omega> borel Y = M"
    using Y_distr Y'_AE distr_cong_AE[where f = Y' and g = Y] by auto
  ultimately show ?thesis using prob_\<Omega> Y'_cnv unfolding \<Omega>_def using space_restrict_space sorry
qed

lemma isCont_borel:
  fixes f :: "real \<Rightarrow> real"
  assumes "f \<in> borel_measurable borel"
  shows "{x. isCont f x} \<in> sets borel"
proof -
  {
    fix x
    have "isCont f x = (\<forall>(i::nat). \<exists>(j::nat). \<forall>y z. 
      abs(x - y) < inverse(real (j + 1)) \<and> abs(x - z) < inverse(real (j + 1)) \<longrightarrow>
        abs(f(y) - f(z)) \<le> inverse (real (i + 1)))"
      apply (subst continuous_at_real_range, auto)
      apply (drule_tac x = "inverse(2 * real(Suc i))" in spec, auto)
      apply (frule reals_Archimedean, auto)
      apply (rule_tac x = n in exI, auto)
      apply (frule_tac x = y in spec)
      apply (drule_tac x = z in spec, auto)
      (* gee, it would be nice if this could be done automatically *)
      apply (subgoal_tac "f y - f z = f y - f x + (f x - f z)")
      apply (erule ssubst)
      apply (rule order_trans)
      apply (rule abs_triangle_ineq)
      apply (auto simp add: abs_minus_commute)
      apply (frule reals_Archimedean, auto)
      apply (drule_tac x = n in spec, auto)
      apply (rule_tac x = "inverse (real (Suc j))" in exI, auto)
      apply (drule_tac x = x' in spec)
      by (drule_tac x = x in spec, auto)
  } note isCont_iff = this
  {
    fix i j :: nat
    have "open {x. (\<exists>y. \<bar>x - y\<bar> < inverse (real (Suc i)) \<and> 
        (\<exists>z. \<bar>x - z\<bar> < inverse (real (Suc i)) \<and> inverse (real (Suc j)) < \<bar>f y - f z\<bar>))}"
    proof (auto simp add: not_le open_real)
      fix x y z 
      assume 1: "\<bar>x - y\<bar> < inverse (real (Suc i))" and 2: "\<bar>x - z\<bar> < inverse (real (Suc i))"
        and 3: "inverse (real (Suc j)) < \<bar>f y - f z\<bar>"
      hence "\<exists>e > 0. abs(x - y) + e \<le> inverse (real (Suc i)) \<and> 
                     abs(x - z) + e \<le> inverse (real (Suc i))"
        apply (rule_tac x = "min (inverse (real (Suc i)) - abs(x - y)) 
             (inverse (real (Suc i)) - abs(x - z))" in exI)
        by (auto split: split_min)
      then obtain e where 4: "e > 0" and 5: "abs(x - y) + e \<le> inverse (real (Suc i))"
          and 6: "abs(x - z) + e \<le> inverse (real (Suc i))" by auto
      have "e > 0 \<and> (\<forall>x'. \<bar>x' - x\<bar> < e \<longrightarrow>
               (\<exists>y. \<bar>x' - y\<bar> < inverse (real (Suc i)) \<and>
               (\<exists>z. \<bar>x' - z\<bar> < inverse (real (Suc i)) \<and> inverse (real (Suc j)) < \<bar>f y - f z\<bar>)))"
           (is "?P e")
        using 1 2 3 4 5 6 apply auto
        apply (rule_tac x = y in exI, auto)
        by (rule_tac x = z in exI, auto)
      thus "\<exists>e. ?P e" ..
    qed
  } note * = this
  show ?thesis
    apply (subst isCont_iff)
    apply (subst Collect_all_eq)
    apply (rule countable_Un_Int, auto)
    apply (subst Collect_ex_eq)
    apply (rule countable_Un_Int, auto)
    apply (rule borel_closed)
    apply (subst closed_def)
    apply (subst Compl_eq, simp add: not_le)
    by (rule *)
qed

theorem weak_conv_imp_bdd_ae_continuous_conv:
  fixes 
    M_seq :: "nat \<Rightarrow> real measure" and
    M :: "real measure" and
    f :: "real \<Rightarrow> real"
  assumes 
    distr_M_seq: "\<And>n. real_distribution (M_seq n)" and 
    distr_M: "real_distribution M" and 
    wcM: "weak_conv_m M_seq M" and
    discont_null: "M ({x. \<not> isCont f x}) = 0" and
    f_bdd: "\<And>x. abs (f x) \<le> B" and
    [simp]: "f \<in> borel_measurable borel"
  shows 
    "(\<lambda> n. integral\<^sup>L (M_seq n) f) ----> integral\<^sup>L M f"
proof -
  note Skorohod [OF distr_M_seq distr_M wcM]
  then obtain Omega Y_seq Y where
    ps_Omega [simp]: "prob_space Omega" and
    Y_seq_measurable [simp]: "\<And>n. Y_seq n \<in> borel_measurable Omega" and
    distr_Y_seq: "\<And>n. distr Omega borel (Y_seq n) = M_seq n" and
    Y_measurable [simp]: "Y \<in> borel_measurable Omega" and
    distr_Y: "distr Omega borel Y = M" and
    YnY: "\<And>x :: real. x \<in> space Omega \<Longrightarrow> (\<lambda>n. Y_seq n x) ----> Y x"  by force
  have *: "emeasure Omega (Y -` {x. \<not> isCont f x} \<inter> space Omega) = 0"
    apply (subst emeasure_distr [symmetric])
    apply (rule Y_measurable)
    apply (subst double_complement [symmetric])
    apply (rule borel_comp)
    apply (subst Compl_eq, simp, rule isCont_borel, simp)
    by (subst distr_Y, rule discont_null)
    thm pred_Collect_borel
  show ?thesis
    apply (subst distr_Y_seq [symmetric])
    apply (subst distr_Y [symmetric])
    apply (subst integral_distr, simp_all)+
    apply (rule integral_dominated_convergence)
    apply (rule finite_measure.integrable_const_bound)
    apply force
    apply (rule always_eventually, rule allI, rule f_bdd)
    apply (rule measurable_compose) back
    apply (rule Y_seq_measurable, force)
    apply (rule always_eventually, rule allI, rule f_bdd)
    apply (rule finite_measure.lebesgue_integral_const, force)
    prefer 2    
    apply (rule measurable_compose) back
    apply (rule Y_measurable, simp)
    apply (rule AE_I [where N = "Y -` {x. \<not> isCont f x} \<inter> space Omega"])
    apply auto [1]
    apply (erule notE)
    apply (erule isCont_tendsto_compose)
    apply (erule YnY)
    apply (rule *)
    apply (rule measurable_sets)
    apply (rule Y_measurable)
    apply (subst double_complement [symmetric])
    apply (rule borel_comp)
    apply (subst Compl_eq, simp)
    by (rule isCont_borel, simp)
qed

theorem weak_conv_imp_integral_bdd_continuous_conv:
  fixes 
    M_seq :: "nat \<Rightarrow> real measure" and
    M :: "real measure" and
    f :: "real \<Rightarrow> real"
  assumes 
    "\<And>n. real_distribution (M_seq n)" and 
    "real_distribution M" and 
    "weak_conv_m M_seq M" and
    "\<And>x. isCont f x" and
    "\<And>x. abs (f x) \<le> B"
  shows 
    "(\<lambda> n. integral\<^sup>L (M_seq n) f) ----> integral\<^sup>L M f"

  using assms apply (intro weak_conv_imp_bdd_ae_continuous_conv, auto)
  apply (rule borel_measurable_continuous_on1)
by (rule continuous_at_imp_continuous_on, auto)

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

theorem weak_conv_imp_continuity_set_conv:
  fixes 
    M_seq :: "nat \<Rightarrow> real measure" and
    M :: "real measure" and
    f :: "real \<Rightarrow> real"
  assumes 
    real_dist_Mn [simp]: "\<And>n. real_distribution (M_seq n)" and 
    real_dist_M [simp]: "real_distribution M" and 
    "weak_conv_m M_seq M" and
    [simp]: "A \<in> sets borel" and
    "M (frontier A) = 0"
  shows 
    "(\<lambda> n. (measure (M_seq n) A)) ----> measure M A"

  (* this is a pain -- have to instantiate the locale (or fake it) to use facts
     about real distributions *)
  apply (subst measure_def)+
  apply (subst integral_indicator(1) [symmetric]) 
  apply (auto simp add: real_distribution.events_eq_borel)[1]
  apply (rule finite_measure.emeasure_finite, rule prob_space_simps)
  using real_dist_Mn unfolding real_distribution_def apply auto
  apply (subst integral_indicator(1) [symmetric]) 
  apply (auto simp add: real_distribution.events_eq_borel)[1]
  apply (rule finite_measure.emeasure_finite, rule prob_space_simps)
  using real_dist_M unfolding real_distribution_def apply auto
  apply (rule weak_conv_imp_bdd_ae_continuous_conv, auto simp add: assms)
  apply (subst isCont_indicator, simp add: assms)
by (rule borel_measurable_indicator, simp)

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

theorem continuity_set_conv_imp_weak_conv:
  fixes 
    M_seq :: "nat \<Rightarrow> real measure" and
    M :: "real measure" and
    f :: "real \<Rightarrow> real"
  assumes 
    real_dist_Mn [simp]: "\<And>n. real_distribution (M_seq n)" and 
    real_dist_M [simp]: "real_distribution M" and 
    *: "\<And>A. A \<in> sets borel \<Longrightarrow> M (frontier A) = 0 \<Longrightarrow>
        (\<lambda> n. (measure (M_seq n) A)) ----> measure M A"
  shows 
    "weak_conv_m M_seq M"

proof -
  interpret real_distribution M by simp
thm emeasure_eq_measure
  show ?thesis
   unfolding weak_conv_m_def weak_conv_def cdf_def2 apply auto
   by (rule *, auto simp add: frontier_real_atMost isCont_cdf emeasure_eq_measure)
qed

definition
  cts_step :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
where
  "cts_step a b x \<equiv> 
    if x \<le> a then 1
    else (if x \<ge> b then 0 else (b - x) / (b - a))"

lemma cts_step_uniformly_continuous:
  fixes a b
  assumes [arith]: "a < b"
  shows "uniformly_continuous_on UNIV (cts_step a b)"
unfolding uniformly_continuous_on_def 
proof (clarsimp)
  fix e :: real
  assume [arith]: "0 < e"
  let ?d = "min (e * (b - a)) (b - a)"
  have "?d > 0" by (auto simp add: field_simps)
  {
    fix x x'
    assume 1: "\<bar>x' - x\<bar> < e * (b - a)" and 2: "\<bar>x' - x\<bar> < b - a" and "x \<le> x'"
    hence "\<bar>cts_step a b x' - cts_step a b x\<bar> < e"
      unfolding cts_step_def apply auto
      apply (auto simp add: field_simps)[2]
      by (subst diff_divide_distrib [symmetric], simp add: field_simps)
  } note * = this
  have "\<forall>x x'. dist x' x < ?d \<longrightarrow> dist (cts_step a b x') (cts_step a b x) < e"
  proof (clarsimp simp add: dist_real_def)
    fix x x'
    assume "\<bar>x' - x\<bar> < e * (b - a)" and "\<bar>x' - x\<bar> < b - a" 
    thus "\<bar>cts_step a b x' - cts_step a b x\<bar> < e"
      apply (case_tac "x \<le> x'")
      apply (rule *, auto)
      apply (subst abs_minus_commute)
      by (rule *, auto)
  qed
  with `?d > 0` show 
    "\<exists>d > 0. \<forall>x x'. dist x' x < d \<longrightarrow> dist (cts_step a b x') (cts_step a b x) < e"
    by blast
qed

lemma (in real_distribution) measurable_finite_borel [simp]: "f \<in> borel_measurable borel \<Longrightarrow> 
  f \<in> borel_measurable M"
  apply (rule borel_measurable_subalgebra)
  prefer 3 apply assumption
  by auto

lemma (in real_distribution) integrable_cts_step: "a < b \<Longrightarrow> integrable M (cts_step a b)"
  apply (rule integrable_const_bound [of _ 1])
  apply (force simp add: cts_step_def)
  apply (rule measurable_finite_borel)
  apply (rule borel_measurable_continuous_on1)
  apply (rule uniformly_continuous_imp_continuous)
by (rule cts_step_uniformly_continuous)
  
lemma (in real_distribution) cdf_cts_step:
  fixes  
    x y :: real
  assumes 
    "x < y"
  shows 
    "cdf M x \<le> integral\<^sup>L M (cts_step x y)" and
    "integral\<^sup>L M (cts_step x y) \<le> cdf M y"
unfolding cdf_def 
proof -
  have "prob {..x} = integral\<^sup>L M (indicator {..x})"
    apply (subst measure_def)
    (* interesting -- this doesn't this work:
      apply (auto simp add: integral_indicator)
    *)
    by (subst integral_indicator, auto)
  thus "prob {..x} \<le> expectation (cts_step x y)"
    apply (elim ssubst)
    apply (rule integral_mono)
    apply (rule integral_indicator, auto)
    apply (rule integrable_cts_step, rule assms)
  unfolding cts_step_def indicator_def
  by (auto simp add: field_simps)
next
  have "prob {..y} = integral\<^sup>L M (indicator {..y})"
    apply (subst measure_def)
    by (subst integral_indicator, auto)
  thus "expectation (cts_step x y) \<le> prob {..y}"
    apply (elim ssubst)
    apply (rule integral_mono)
    apply (rule integrable_cts_step, rule assms)
    apply (rule integral_indicator, auto)
    unfolding cts_step_def indicator_def using `x < y`
      by (auto simp add: field_simps)
qed

(*** NOTE: The following three lemmata are solved directly by theorems in Library_Misc. ***)

(* name clash with the version in Extended_Real_Limits *)
lemma convergent_ereal': "convergent (X :: nat \<Rightarrow> real) \<Longrightarrow> convergent (\<lambda>n. ereal (X n))"
  apply (drule convergentD, auto)
  apply (rule convergentI)
  by (subst lim_ereal, assumption)

lemma lim_ereal': "convergent X \<Longrightarrow> lim (\<lambda>n. ereal (X n)) = ereal (lim X)"
    by (rule limI, simp add: convergent_LIMSEQ_iff)

(* complements liminf version in Extended_Real_Limits *)
lemma convergent_liminf_cl:
  fixes X :: "nat \<Rightarrow> 'a::{complete_linorder,linorder_topology}"
  shows "convergent X \<Longrightarrow> liminf X = lim X"
  by (auto simp: convergent_def limI lim_imp_Liminf)

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

theorem integral_cts_step_conv_imp_weak_conv:
  fixes 
    M_seq :: "nat \<Rightarrow> real measure" and
    M :: "real measure"
  assumes 
    distr_M_seq: "\<And>n. real_distribution (M_seq n)" and 
    distr_M: "real_distribution M" and 
    integral_conv: "\<And>x y. x < y \<Longrightarrow>
         (\<lambda>n. integral\<^sup>L (M_seq n) (cts_step x y)) ----> integral\<^sup>L M (cts_step x y)"
  shows 
    "weak_conv_m M_seq M"
unfolding weak_conv_m_def weak_conv_def 
proof (clarsimp)
  fix x
  assume "isCont (cdf M) x"
  hence left_cont: "continuous (at_left x) (cdf M)"
    by (subst (asm) continuous_at_split, auto)
  have conv: "\<And>a b. a < b \<Longrightarrow> convergent (\<lambda>n. integral\<^sup>L (M_seq n) (cts_step a b))"
    by (rule convergentI, rule integral_conv, simp)
  {
    fix y :: real
    assume [arith]: "x < y"
    have "limsup (\<lambda>n. cdf (M_seq n) x) \<le> 
        limsup (\<lambda>n. integral\<^sup>L (M_seq n) (cts_step x y))"
      apply (rule Limsup_mono)
      apply (rule always_eventually, auto)
      apply (rule real_distribution.cdf_cts_step)
      by (rule distr_M_seq, simp)
    also have "\<dots> = lim (\<lambda>n. ereal (integral\<^sup>L (M_seq n) (cts_step x y)))"
      apply (rule convergent_limsup_cl)
      by (rule convergent_ereal', rule conv, simp)
    also have "\<dots> = integral\<^sup>L M (cts_step x y)"
      apply (subst lim_ereal', rule conv, auto)
      by (rule limI, rule integral_conv, simp)
    also have "\<dots> \<le> cdf M y"
      by (simp, rule real_distribution.cdf_cts_step, rule assms, simp)
    finally have "limsup (\<lambda>n. cdf (M_seq n) x) \<le> cdf M y" .
  } note * = this
  {
    fix y :: real
    assume [arith]: "x > y"
    have "liminf (\<lambda>n. cdf (M_seq n) x) \<ge> 
        liminf (\<lambda>n. integral\<^sup>L (M_seq n) (cts_step y x))" (is "_ \<ge> ?rhs")
      apply (rule Liminf_mono)
      apply (rule always_eventually, auto)
      apply (rule real_distribution.cdf_cts_step)
      by (rule distr_M_seq, simp)
    also have "?rhs = lim (\<lambda>n. ereal (integral\<^sup>L (M_seq n) (cts_step y x)))"
      apply (rule convergent_liminf_cl)
      by (rule convergent_ereal', rule conv, simp)
    also have "\<dots> = integral\<^sup>L M (cts_step y x)"
      apply (subst lim_ereal', rule conv, auto)
      by (rule limI, rule integral_conv, simp)
    also have "\<dots> \<ge> cdf M y"
      by (simp, rule real_distribution.cdf_cts_step, rule assms, simp)
    finally (xtrans) have "liminf (\<lambda>n. cdf (M_seq n) x) \<ge> cdf M y" .
  } note ** = this
  have le: "limsup (\<lambda>n. cdf (M_seq n) x) \<le> cdf M x"
  proof -
    interpret real_distribution M by (rule assms) 
    have 1: "((\<lambda>x. ereal (cdf M x)) ---> cdf M x) (at_right x)"
      by (simp add: continuous_within [symmetric], rule cdf_is_right_cont)
    have 2: "((\<lambda>t. limsup (\<lambda>n. cdf (M_seq n) x)) ---> 
        limsup (\<lambda>n. cdf (M_seq n) x)) (at_right x)" by (rule tendsto_const)
    show ?thesis
      apply (rule tendsto_le [OF _ 1 2], auto, subst eventually_at_right)
      apply (rule exI [of _ "x+1"], auto)
      by (rule *)
  qed
  moreover have ge: "cdf M x \<le> liminf (\<lambda>n. cdf (M_seq n) x)"
  proof -
    interpret real_distribution M by (rule assms) 
    have 1: "((\<lambda>x. ereal (cdf M x)) ---> cdf M x) (at_left x)"
      by (simp add: continuous_within [symmetric] left_cont) 
    have 2: "((\<lambda>t. liminf (\<lambda>n. cdf (M_seq n) x)) ---> 
        liminf (\<lambda>n. cdf (M_seq n) x)) (at_left x)" by (rule tendsto_const)
    show ?thesis
      apply (rule tendsto_le [OF _ 2 1], auto, subst eventually_at_left)
      apply (rule exI [of _ "x - 1"], auto)
      by (rule **)
  qed
  ultimately show "(\<lambda>n. cdf (M_seq n) x) ----> cdf M x"
    by (elim limsup_le_liminf_real) 
qed

theorem integral_bdd_continuous_conv_imp_weak_conv:
  fixes 
    M_seq :: "nat \<Rightarrow> real measure" and
    M :: "real measure"
  assumes 
    "\<And>n. real_distribution (M_seq n)" and 
    "real_distribution M" and 
    "\<And>f B. (\<And>x. isCont f x) \<Longrightarrow> (\<And>x. abs (f x) \<le> B) \<Longrightarrow>
         (\<lambda>n. integral\<^sup>L (M_seq n) f) ----> integral\<^sup>L M f"
  shows 
    "weak_conv_m M_seq M"

  apply (rule integral_cts_step_conv_imp_weak_conv [OF assms])
  apply (rule continuous_on_interior)
  apply (rule uniformly_continuous_imp_continuous)
  apply (rule cts_step_uniformly_continuous, auto)
  apply (subgoal_tac "abs(cts_step x y xa) \<le> 1")
  apply assumption
unfolding cts_step_def by auto

end



