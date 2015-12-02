(*
Theory: Weak_Convergence.thy
Authors: Jeremy Avigad, Luke Serafin

Properties of weak convergence of functions and measures, including the portmanteau theorem.
*)

theory Weak_Convergence

imports Distribution_Functions

begin

(* weak convergence of functions *)
definition
  weak_conv :: "(nat \<Rightarrow> (real \<Rightarrow> real)) \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> bool"
where
  "weak_conv F_seq F \<equiv> \<forall>x. isCont F x \<longrightarrow> (\<lambda>n. F_seq n x) ----> F x"

(* weak convergence of distributions *)
definition
  weak_conv_m :: "(nat \<Rightarrow> real measure) \<Rightarrow> real measure \<Rightarrow> bool"
where
  "weak_conv_m M_seq M \<equiv> weak_conv (\<lambda>n. cdf (M_seq n)) (cdf M)"

(* TODO: we never use this; delete? *)
(* weak convergence of random variables *)
abbreviation (in prob_space)
  "weak_conv_r X_seq X \<equiv> weak_conv_m (\<lambda>n. distr M borel (X_seq n)) (distr M borel X)" 
  

(* 
  general stuff - move elsewhere 
*)

lemma restrict_space_sets_cong:
  "A = B \<Longrightarrow> sets M = sets N \<Longrightarrow> sets (restrict_space M A) = sets (restrict_space N B)"
  by (auto simp: sets_restrict_space)

definition mono_on :: "('a::order \<Rightarrow> 'b::order) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "mono_on f A = (\<forall>x\<in>A. \<forall>y\<in>A. x \<le> y \<longrightarrow> f x \<le> f y)"

lemma mono_onD: "mono_on f A \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
  unfolding mono_on_def by auto
(* Show such a function is an ereal-valued measurable function times the indicator function of the
   complement of A. *)
lemma mono_on_ctble_discont:
  fixes f :: "real \<Rightarrow> real"
  fixes A :: "real set"
  assumes "mono_on f A"
  shows "countable {a\<in>A. \<not> continuous (at a within A) f}"
proof -

  have "\<forall>a \<in> {a\<in>A. \<not> continuous (at a within A) f}. \<exists>q :: nat \<times> rat.
      (fst q = 0 \<and> of_rat (snd q) < f a \<and> (\<forall>x \<in> A. x < a \<longrightarrow> f x < of_rat (snd q))) |
      (fst q = 1 \<and> of_rat (snd q) > f a \<and> (\<forall>x \<in> A. x > a \<longrightarrow> f x > of_rat (snd q)))"
  proof auto
    from `mono_on f A` have mono: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
      by (simp add: mono_on_def)
    fix a
    assume "a \<in> A"
    assume "\<not> continuous (at a within A) f"
    thus "\<exists>q1 q2.
            q1 = 0 \<and> real_of_rat q2 < f a \<and> (\<forall>x\<in>A. x < a \<longrightarrow> f x < real_of_rat q2) \<or>
            q1 = Suc 0 \<and> f a < real_of_rat q2 \<and> (\<forall>x\<in>A. a < x \<longrightarrow> real_of_rat q2 < f x)"
    proof (auto simp add: continuous_within order_tendsto_iff eventually_at)
      fix l
      assume "l < f a"
      hence "\<exists>q :: rat. l < of_rat q \<and> of_rat q < f a"
        by (rule of_rat_dense)
      then guess q2 .. note 1 = this
      assume 2 [rule_format]: "\<forall>d>0. \<exists>x\<in>A. x \<noteq> a \<and> dist x a < d \<and> \<not> l < f x"
      from 1 have "real_of_rat q2 < f a \<and> (\<forall>x\<in>A. x < a \<longrightarrow> f x < real_of_rat q2)"
      proof auto
        fix x 
        assume "x \<in> A" "x < a"
        with 1 2 [of "a - x"] show "f x < real_of_rat q2"
          apply (auto simp add: dist_real_def)
          apply (subgoal_tac "f x \<le> f xa")
          by (auto intro: mono)
      qed 
      thus ?thesis by auto
    next
      fix u
      assume "u > f a"
      hence "\<exists>q :: rat. f a < of_rat q \<and> of_rat q < u"
        by (rule of_rat_dense)
      then guess q2 .. note 1 = this
      assume 2 [rule_format]: "\<forall>d>0. \<exists>x\<in>A. x \<noteq> a \<and> dist x a < d \<and> \<not> u > f x"
      from 1 have "real_of_rat q2 > f a \<and> (\<forall>x\<in>A. x > a \<longrightarrow> f x > real_of_rat q2)"
      proof auto
        fix x 
        assume "x \<in> A" "x > a"
        with 1 2 [of "x - a"] show "f x > real_of_rat q2"
          apply (auto simp add: dist_real_def)
          apply (subgoal_tac "f x \<ge> f xa")
          by (auto intro: mono)
      qed 
      thus ?thesis by auto
    qed
  qed
  hence "\<exists>g :: real \<Rightarrow> nat \<times> rat . \<forall>a \<in> {a\<in>A. \<not> continuous (at a within A) f}. 
      (fst (g a) = 0 \<and> of_rat (snd (g a)) < f a \<and> (\<forall>x \<in> A. x < a \<longrightarrow> f x < of_rat (snd (g a)))) |
      (fst (g a) = 1 \<and> of_rat (snd (g a)) > f a \<and> (\<forall>x \<in> A. x > a \<longrightarrow> f x > of_rat (snd (g a))))"
    by (rule bchoice)
  then guess g ..
  hence g: "\<And>a x. a \<in> A \<Longrightarrow> \<not> continuous (at a within A) f \<Longrightarrow> x \<in> A \<Longrightarrow>
      (fst (g a) = 0 \<and> of_rat (snd (g a)) < f a \<and> (x < a \<longrightarrow> f x < of_rat (snd (g a)))) |
      (fst (g a) = 1 \<and> of_rat (snd (g a)) > f a \<and> (x > a \<longrightarrow> f x > of_rat (snd (g a))))"
    by auto
  have "inj_on (\<lambda>x. g x) {a\<in>A. \<not> continuous (at a within A) f}"
  proof (auto simp add: inj_on_def)
    fix w z
    assume 1: "w \<in> A" and 2: "\<not> continuous (at w within A) f" and
           3: "z \<in> A" and 4: "\<not> continuous (at z within A) f" and
           5: "g w = g z"
    from g [OF 1 2 3] g [OF 3 4 1] 5 
    show "w = z" by auto
  qed
  thus ?thesis 
    by (rule countableI') 
qed

lemma borel_measurable_mono_on_fnc:
  fixes f :: "real \<Rightarrow> real" and A :: "real set"
  assumes "mono_on f A"
  shows "f \<in> borel_measurable (restrict_space borel A)"
  apply (rule measurable_restrict_countable[OF mono_on_ctble_discont[OF assms]])
  apply (auto intro!: image_eqI[where x="{x}" for x] simp: sets_restrict_space)
  apply (auto simp add: sets_restrict_restrict_space continuous_on_eq_continuous_within
              cong: measurable_cong_sets 
              intro!: borel_measurable_continuous_on_restrict intro: continuous_within_subset)
  done

(* TODO: turn this into an iff by weakening the hypothesis *)
(* compare to continuous_at_right_real_mono *)
lemma continuous_at_right_real_mono_on_open:
  fixes f :: "real \<Rightarrow> real" and U a
  assumes "open U" "a \<in> U" and mono: "mono_on f U"
  shows "continuous (at_right a) f \<Longrightarrow> (\<forall>\<epsilon>>0. \<exists>\<delta>>0. a + \<delta> \<in> U \<and> f (a + \<delta>) - f a < \<epsilon>)"
proof (auto simp add: continuous_within_eps_delta dist_real_def greaterThan_def)
  from mono have nondec: "\<And>x y. x \<in> U \<Longrightarrow> y \<in> U \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> ((f y) :: real)"
    unfolding mono_on_def by auto
  from `a \<in> U` `open U` have "\<exists>e>0. \<forall>x'. \<bar>x' - a\<bar> < e \<longrightarrow> x' \<in> U"
    by (auto simp add: open_real_def dist_real_def)
  then obtain d' where "d' > 0 \<and> (\<forall>x'. \<bar>x' - a\<bar> < d' \<longrightarrow> x' \<in> U)" ..
  hence "d' > 0" and d': "\<And>x'. \<bar>x' - a\<bar> < d' \<Longrightarrow> x' \<in> U" by auto
  {
    fix \<epsilon> :: real
    assume "\<epsilon> > 0" and
      hyp: "\<forall>e>0. \<exists>d>0. \<forall>x'>a. x' - a < d \<longrightarrow> \<bar>f x' - f a\<bar> < e"
    hence "\<exists>d>0. \<forall>x'>a. x' - a < d \<longrightarrow> \<bar>f x' - f a\<bar> < \<epsilon>" by auto
    then obtain d where "d > 0 \<and> (\<forall>x'>a. x' - a < d \<longrightarrow> \<bar>f x' - f a\<bar> < \<epsilon>)" ..
    hence "d > 0" and d: "\<And>x'. x'>a \<Longrightarrow> x' - a < d \<Longrightarrow> \<bar>f x' - f a\<bar> < \<epsilon>" by auto
    let ?delta = "min (d / 2) (d' / 2)"
    from `d > 0` `d' > 0` have "?delta >0 \<and> a + ?delta \<in> U \<and> f (a + ?delta) - f a < \<epsilon>"
      apply (auto intro: d')
      by (rule order_le_less_trans [OF abs_ge_self d], auto)
    thus "\<exists>\<delta>>0. a + \<delta> \<in> U \<and> f (a + \<delta>) - f a < \<epsilon>" ..
  }

qed

(* TODO: make mono_on primitive, and define mono f to be an abbreviation for mono_on f UNIV? *)
lemma "mono f = mono_on f UNIV"
  unfolding mono_def mono_on_def by auto


lemma mono_on_ctble_discont_open:
  fixes f :: "real \<Rightarrow> real"
  fixes A :: "real set"
  assumes "open A" "mono_on f A"
  shows "countable {a\<in>A. \<not>isCont f a}"
proof -
  have "{a\<in>A. \<not>isCont f a} = {a\<in>A. \<not>(continuous (at a within A) f)}"
    by (auto simp add: continuous_within_open [OF _ `open A`])
  thus ?thesis
    apply (elim ssubst)
    by (rule mono_on_ctble_discont, rule assms)
qed

lemma mono_ctble_discont:
  fixes f :: "real \<Rightarrow> real"
  assumes "mono f"
  shows "countable {a. \<not> isCont f a}"
using assms mono_on_ctble_discont [of f UNIV] unfolding mono_on_def mono_def by auto

(*

  Skorohod's theorem

*)

(* TODO: should this definition be eliminated? **)
definition rcont_inc :: "(real \<Rightarrow> real) \<Rightarrow> bool"
  where "rcont_inc f \<equiv> (\<forall>x. continuous (at_right x) f) \<and> mono f"

lemma bdd_rcont_inc_pseudoinverse:
  fixes F :: "real \<Rightarrow> real"
  fixes M a b :: real
  assumes "a < b" and rcont_inc: "rcont_inc F"
    and F_at_bot: "(F ---> a) at_bot" and F_at_top: "(F ---> b) at_top"
  shows "\<forall>\<omega>\<in>{a<..<b}. \<forall>x. (\<omega> \<le> F x) = (Inf {x. \<omega> \<le> F x} \<le> x)"
proof safe
  fix \<omega> x :: real assume interval: "\<omega> \<in> {a<..<b}"
  def Y \<equiv> "\<lambda>\<omega>. Inf {x. \<omega> \<le> F x}"
  {
    assume "\<omega> \<le> F x"
    hence "x \<in> {x. \<omega> \<le> F x}" using interval by auto
    thus "Y \<omega> \<le> x" unfolding Y_def
      apply (rule cInf_lower)
      proof (unfold bdd_below_def Ball_def, auto)
        from F_at_bot have "\<exists>y. F y < \<omega>" unfolding filterlim_def le_filter_def
          apply (subst (asm) eventually_filtermap)
          apply (subst (asm) eventually_at_bot_linorder)
          apply (drule_tac x = "\<lambda>z. z < \<omega>" in allE[where R = "\<exists>y. F y < \<omega>"], auto)
          using interval by (metis F_at_bot eventually_at_bot_linorder greaterThanLessThan_iff order_refl order_tendsto_iff) 
      then guess y .. note y = this
      hence "\<forall>x. \<omega> \<le> F x \<longrightarrow> y \<le> x" using rcont_inc unfolding rcont_inc_def mono_def
        by (metis dual_order.irrefl le_cases le_less_trans)
      thus "\<exists>m. \<forall>x. \<omega> \<le> F x \<longrightarrow> m \<le> x" by auto
    qed
  }
  {
    assume "Y \<omega> \<le> x"
    hence x_less: "\<And>y. x < y \<Longrightarrow> \<omega> \<le> F y"
    proof (unfold Y_def)
      fix y assume x: "Inf {x. \<omega> \<le> F x} \<le> x" and y: "x < y"
      show "\<omega> \<le> F y"
      proof (rule ccontr)
        assume "\<not> \<omega> \<le> F y"
        hence "F y < \<omega>" by simp
        hence le: "\<And>z. z \<le> y \<Longrightarrow> F z < \<omega>" using rcont_inc le_less_trans unfolding rcont_inc_def mono_def by metis
        have "y \<le> Inf {x. \<omega> \<le> F x}"
        proof (rule cInf_greatest)
          have "(\<lambda>k::nat. F (real k)) ----> b"
            by (metis F_at_top filterlim_compose filterlim_real_sequentially)
          then have "\<exists>no::nat. \<forall>k\<ge>no. norm (F (real k) - b) < b - \<omega>"
            by (rule LIMSEQ_D) (insert interval, simp)
          then guess no .. note no = this
          hence "norm (F (real no) - b) < b - \<omega>" by simp
          hence "\<omega> \<le> F (real no)" by auto
          thus "{x. \<omega> \<le> F x} \<noteq> {}" by auto
        qed (meson le_cases mem_Collect_eq not_le le)
        hence "y \<le> x" using x by simp
        thus False using y by simp
      qed
    qed
    show "\<omega> \<le> F x"
    proof (rule field_le_epsilon)
      fix e::real assume e: "0 < e"
      hence "\<exists>\<delta>>0. F (x + \<delta>) - F x < e"
        using continuous_at_right_real_increasing rcont_inc unfolding rcont_inc_def mono_def by auto
      then guess \<delta> .. note \<delta> = this
      have \<delta>: "\<delta> > 0" "F (x + \<delta>) - F x < e" using \<delta> by simp_all
      hence "\<omega> \<le> F (x + \<delta>)" using x_less \<delta> by auto
      thus "\<omega> \<le> F x + e" using \<delta>(2) by simp
    qed
  }
qed

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
  have prob_\<Omega>: "prob_space \<Omega>"
    apply (rule prob_spaceI)
    unfolding \<Omega>_def apply (subst space_restrict_space)
    by (subst emeasure_restrict_space, auto)
  def Y_seq \<equiv> "\<lambda>n \<omega>. Inf {x. \<omega> \<le> f n x}"
  def Y \<equiv> "\<lambda>\<omega>. Inf {x. \<omega> \<le> F x}"
  have f_meas: "\<And>n. f n \<in> borel_measurable borel" using f_inc borel_measurable_mono by auto
  have Y_seq_le_iff: "\<And>n. \<forall>\<omega>\<in>{0<..<1}. \<forall>x. (\<omega> \<le> f n x) = (Y_seq n \<omega> \<le> x)"
  proof -
    fix n :: nat
    show "\<forall>\<omega>\<in>{0<..<1}. \<forall>x. (\<omega> \<le> f n x) = (Y_seq n \<omega> \<le> x)"
      unfolding Y_seq_def apply (rule bdd_rcont_inc_pseudoinverse[of 0 1 "f n"])
      unfolding rcont_inc_def using f_inc f_right_cts f_at_top f_at_bot by auto
  qed
  have Y_seq_mono_on: "\<And>n. mono_on (Y_seq n) {0<..<1}" unfolding mono_on_def
    using Y_seq_le_iff by (metis order.trans order_refl)
  hence Y_seq_meas [measurable]: "\<And>n. (Y_seq n) \<in> borel_measurable \<Omega>" using borel_measurable_mono_on_fnc 
      unfolding \<Omega>_def
    by (simp cong: measurable_cong_sets restrict_space_sets_cong)
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
      apply (subst Int_def, simp)
      apply (subgoal_tac "{xa. 0 < xa \<and> xa < 1} \<inter> {xa. Y_seq n xa \<le> x} = {xa. 0 < xa \<and> xa < 1 \<and> xa \<le> f n x}")
      apply (erule ssubst)
      prefer 2
      using Y_seq_le_iff apply auto [1]
      apply (subst measure_restrict_space, simp)
      apply (auto simp del: measure_lborel_Ioc)
      apply (subgoal_tac "Sigma_Algebra.measure (\<mu> n) {..x} =
         measure lborel {0..Sigma_Algebra.measure (\<mu> n) {..x}}")
      prefer 2
      apply (subst measure_lborel_Icc)
      apply (rule measure_nonneg)
      apply simp
      apply (erule ssubst)
      unfolding measure_def
      apply (rule arg_cong[where f=real_of_ereal])
      unfolding f_def cdf_def
      apply (rule emeasure_eq_AE)
      apply (rule AE_I [of _ _ "{0, 1}"])
      apply (subst measure_def [symmetric])
      apply auto []
      apply (subst order_less_le, simp)
      apply (erule order_trans, auto)
      apply (simp add: emeasure_insert_ne)
      done
    qed
  hence Y_seq_distr: "\<And>n. distr \<Omega> borel (Y_seq n) = \<mu> n"
    apply (intro cdf_unique, auto simp add: assms)
    unfolding real_distribution_def apply auto
    unfolding prob_space_def apply auto
    unfolding prob_space_axioms_def real_distribution_axioms_def apply auto
    by (rule finite_measureI, auto simp add: Y_seq_emeasure_distr_\<Omega>)
  have F_meas: "F \<in> borel_measurable borel" using F_inc borel_measurable_mono by auto
  have Y_le_iff: "\<forall>\<omega>\<in>{0<..<1}. \<forall>x. (\<omega> \<le> F x) = (Y \<omega> \<le> x)"
    unfolding Y_def apply (rule bdd_rcont_inc_pseudoinverse[of 0 1 F])
    unfolding rcont_inc_def using F_inc F_right_cts F_at_top F_at_bot by auto
  have Y_mono_on: "mono_on Y {0<..<1}" unfolding mono_on_def
    using Y_le_iff by (metis order.trans order_refl)
  hence Y_meas[measurable]: "Y \<in> borel_measurable \<Omega>" using borel_measurable_mono_on_fnc unfolding \<Omega>_def
    by (simp cong: measurable_cong_sets restrict_space_sets_cong)
  have Y_emeasure_distr_\<Omega>: "emeasure (distr \<Omega> borel Y) UNIV = 1"
     apply (subst emeasure_distr)
     using Y_meas unfolding \<Omega>_def 
     by (auto simp add: emeasure_restrict_space space_restrict_space)
  interpret M: real_distribution M by (rule assms)
  { fix x 
    have "cdf (distr \<Omega> borel Y) x = measure \<Omega> (Y -` {..x} \<inter> space \<Omega>)"
      by (simp add: cdf_def measure_distr)
    also have "(Y -` {..x} \<inter> space \<Omega>) = ({.. F x} \<inter> {0 <..< 1})"
      using Y_le_iff by (auto simp: Ball_def \<Omega>_def space_restrict_space)
    also have "measure \<Omega> ({.. F x} \<inter> {0 <..< 1}) = measure lborel ({.. F x} \<inter> {0 <..< 1})"
      by (simp add: \<Omega>_def measure_restrict_space)
    also have "\<dots> = measure lborel {0 .. F x}"
      unfolding measure_def using M.cdf_bounded_prob[of x]
      by (intro arg_cong[where f=real_of_ereal] emeasure_eq_AE)
         (auto intro!: AE_I[where N="{0, 1}"] simp: emeasure_insert_ne less_le F_def)
    also have "\<dots> = cdf M x"
      using M.cdf_nonneg[of x] by (simp add: measure_def F_def)
    finally have "cdf (distr \<Omega> borel Y) x = cdf M x" . }
  then have "cdf (distr \<Omega> borel Y) = cdf M" ..
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
          hence "uncountable {r<..<Y \<omega>}" using uncountable_open_interval by simp
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
          hence "uncountable {Y \<omega>'<..<Y \<omega>' + \<epsilon>}" using uncountable_open_interval by simp
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
      show "limsup (\<lambda>n. Y_seq n \<omega>) \<le> Y \<omega>"
      proof (rule ereal_le_epsilon2, auto)
        fix \<epsilon>::real assume \<epsilon>: "\<epsilon> > 0"
        thm continuous_at_right_real_increasing
        have "\<exists>\<delta>>0. \<omega> + \<delta> \<in> {0<..<1} \<and> Y (\<omega> + \<delta>) - Y \<omega> < \<epsilon>"
          using continuous_at_right_real_mono_on_open \<omega> continuous_at_split Y_mono_on \<epsilon>
            open_greaterThanLessThan by metis
        then guess \<delta> .. note \<delta> = this
        hence "\<exists>\<omega>'\<in>{0<..<1}. \<omega> < \<omega>' \<and> Y \<omega>' \<le> Y \<omega> + \<epsilon>"
        proof -
          def d \<equiv> "min \<delta> ((1 - \<omega>)/2)"
          def \<omega>' \<equiv> "\<omega> + d"
          have \<omega>': "\<omega>' \<in> {0<..<1}" unfolding \<omega>'_def d_def using \<omega>(1) \<delta>
            by (auto split: split_min simp: field_simps)
          moreover have "\<omega> < \<omega>'" unfolding \<omega>'_def d_def using \<delta> \<omega>(1) by auto
          moreover with \<omega>' have "Y \<omega>' \<le> Y \<omega> + \<epsilon>"
            using Y_mono_on \<omega>(1) \<delta> unfolding mono_on_def \<omega>'_def d_def by smt
          ultimately show ?thesis by auto
        qed
        then obtain \<omega>' where \<omega>': "\<omega>' \<in> {0<..<1}" "\<omega> < \<omega>'" "Y \<omega>' \<le> Y \<omega> + \<epsilon>" by auto
        with * have "limsup (\<lambda>n. Y_seq n \<omega>) \<le> Y \<omega>'" by auto
        with \<omega>'(3) show "limsup (\<lambda>n. Y_seq n \<omega>) \<le> Y \<omega> + \<epsilon>" by (metis ereal_less_eq(3) order.trans)
      qed
    qed
    ultimately have "(\<lambda>n. Y_seq n \<omega>) ----> Y \<omega>" using Liminf_le_Limsup
      by (metis Liminf_eq_Limsup dual_order.antisym dual_order.trans lim_ereal trivial_limit_sequentially)
  } note Y_cts_cnv = this
  let ?D = "{\<omega>\<in>{0<..<1}. \<not> isCont Y \<omega>}"
  have D_countable: "countable ?D" using Y_mono_on mono_on_ctble_discont
    by (metis (poly_guards_query) mono_on_ctble_discont_open open_greaterThanLessThan)
  hence D: "emeasure lborel ?D = 0" using emeasure_lborel_countable by (metis (full_types))
  def Y' \<equiv> "\<lambda>\<omega>. (case \<omega>\<in>?D of True => 0 | False => Y \<omega>)"
  have Y'_AE: "AE \<omega> in \<Omega>. Y' \<omega> = Y \<omega>"
    apply (rule AE_I [where N = "?D"])
    apply (auto simp add: \<Omega>_def space_restrict_space) [1]
    unfolding Y'_def apply auto [1]
    apply (subst \<Omega>_def, subst emeasure_restrict_space, force)
    apply force
    using D apply force
    apply (rule sets.countable)
    unfolding \<Omega>_def using D_countable by (subst sets_restrict_space, auto)
  def Y_seq' \<equiv> "\<lambda>n \<omega>. (case \<omega>\<in>?D of True => 0 | False => Y_seq n \<omega>)"
  have Y_seq'_AE: "\<And>n. AE \<omega> in \<Omega>. Y_seq' n \<omega> = Y_seq n \<omega>"
    apply (rule AE_I[where N = "?D"])
    apply (auto simp add: \<Omega>_def space_restrict_space) [1]
    unfolding Y_seq'_def apply auto [1]
    apply (subst \<Omega>_def, subst emeasure_restrict_space, force)
    apply force
    using D apply force
    apply (rule sets.countable)
    unfolding \<Omega>_def using D_countable by (subst sets_restrict_space, auto)
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
      ultimately show ?thesis using Y_cts_cnv \<omega> by auto
    qed
  qed
  have [simp]: "\<And>n. Y_seq' n \<in> borel_measurable \<Omega>"
    using Y_seq_meas D_countable
    by (rule measurable_discrete_difference) (auto simp: Y_seq'_def \<Omega>_def sets_restrict_space)
  moreover {fix n  have "distr \<Omega> borel (Y_seq' n) = \<mu> n" using Y_seq_distr [of n] 
      Y_seq'_AE [of n]
    by (subst distr_cong_AE[where f = "Y_seq' n" and g = "Y_seq n"], auto) }
  moreover have [simp]: "Y' \<in> borel_measurable \<Omega>"
    using Y_meas D_countable
    by (rule measurable_discrete_difference) (auto simp: Y'_def \<Omega>_def sets_restrict_space)
  moreover have "distr \<Omega> borel Y' = M"
    apply (subst Y_distr [symmetric])
    apply (rule distr_cong_AE, auto)
    by (rule Y'_AE)
  ultimately have "prob_space \<Omega> \<and> (\<forall>n. Y_seq' n \<in> borel_measurable \<Omega>) \<and>
    (\<forall>n. distr \<Omega> borel (Y_seq' n) = \<mu> n) \<and> Y' \<in> measurable \<Omega> lborel \<and> distr \<Omega> borel Y' = M \<and>
    (\<forall>x\<in>space \<Omega>. (\<lambda>n. Y_seq' n x) ----> Y' x)" using prob_\<Omega> Y'_cnv
    unfolding \<Omega>_def by (auto simp add: space_restrict_space)
  thus ?thesis by metis
qed

(*
  The Portmanteau theorem, that is, the equivalence of various definitions of weak convergence.
*)

theorem weak_conv_imp_bdd_ae_continuous_conv:
  fixes 
    M_seq :: "nat \<Rightarrow> real measure" and
    M :: "real measure" and
    f :: "real \<Rightarrow> 'a::{banach, second_countable_topology}"
  assumes 
    distr_M_seq: "\<And>n. real_distribution (M_seq n)" and 
    distr_M: "real_distribution M" and 
    wcM: "weak_conv_m M_seq M" and
    discont_null: "M ({x. \<not> isCont f x}) = 0" and
    f_bdd: "\<And>x. norm (f x) \<le> B" and
    [measurable]: "f \<in> borel_measurable borel"
  shows 
    "(\<lambda> n. integral\<^sup>L (M_seq n) f) ----> integral\<^sup>L M f"
proof -
  have "0 \<le> B"
    using norm_ge_zero f_bdd by (rule order_trans)
  note Skorohod [OF distr_M_seq distr_M wcM]
  then obtain Omega Y_seq Y where
    ps_Omega [simp]: "prob_space Omega" and
    Y_seq_measurable [measurable]: "\<And>n. Y_seq n \<in> borel_measurable Omega" and
    distr_Y_seq: "\<And>n. distr Omega borel (Y_seq n) = M_seq n" and
    Y_measurable [measurable]: "Y \<in> borel_measurable Omega" and
    distr_Y: "distr Omega borel Y = M" and
    YnY: "\<And>x :: real. x \<in> space Omega \<Longrightarrow> (\<lambda>n. Y_seq n x) ----> Y x"  by force
  interpret prob_space Omega by fact
  have *: "emeasure Omega (Y -` {x. \<not> isCont f x} \<inter> space Omega) = 0"
    apply (subst emeasure_distr [symmetric])
    apply (rule Y_measurable)
    apply (subst double_complement [symmetric])
    apply (rule borel_comp)
    apply (subst Compl_eq, simp, rule isCont_borel)
    by (subst distr_Y, rule discont_null)
  show ?thesis
    apply (subst distr_Y_seq [symmetric])
    apply (subst distr_Y [symmetric])
    apply (subst integral_distr, simp_all)+
    apply (rule integral_dominated_convergence)
    apply measurable
    apply (rule integrable_const_bound[where B=B and f="\<lambda>x. B"])
    apply simp
    using `0 \<le> B` apply simp
    apply simp
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
    apply (rule isCont_borel)
    using f_bdd
    apply simp
    done
qed

theorem weak_conv_imp_integral_bdd_continuous_conv:
  fixes 
    M_seq :: "nat \<Rightarrow> real measure" and
    M :: "real measure" and
    f :: "real \<Rightarrow> 'a::{banach, second_countable_topology}"
  assumes 
    "\<And>n. real_distribution (M_seq n)" and 
    "real_distribution M" and 
    "weak_conv_m M_seq M" and
    "\<And>x. isCont f x" and
    "\<And>x. norm (f x) \<le> B"
  shows 
    "(\<lambda> n. integral\<^sup>L (M_seq n) f) ----> integral\<^sup>L M f"

  using assms apply (intro weak_conv_imp_bdd_ae_continuous_conv, auto)
  apply (rule borel_measurable_continuous_on1)
by (rule continuous_at_imp_continuous_on, auto)

theorem weak_conv_imp_continuity_set_conv:
  fixes 
    M_seq :: "nat \<Rightarrow> real measure" and
    M :: "real measure" and
    f :: "real \<Rightarrow> real"
  assumes 
    "\<And>n. real_distribution (M_seq n)" "real_distribution M" and 
    "weak_conv_m M_seq M" and
    [measurable]: "A \<in> sets borel" and
    "M (frontier A) = 0"
  shows 
    "(\<lambda> n. (measure (M_seq n) A)) ----> measure M A"
proof -
  interpret M: real_distribution M by fact
  interpret M_seq: real_distribution "M_seq n" for n by fact
  
  have "(\<lambda>n. (\<integral>x. indicator A x \<partial>M_seq n) :: real) ----> (\<integral>x. indicator A x \<partial>M)"
    by (intro weak_conv_imp_bdd_ae_continuous_conv[where B=1])
       (auto intro: assms simp: isCont_indicator)
  then show ?thesis
    by simp
qed

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
  show ?thesis
   unfolding weak_conv_m_def weak_conv_def cdf_def2 apply auto
   by (rule *, auto simp add: frontier_real_Iic isCont_cdf emeasure_eq_measure)
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
    by simp
  thus "prob {..x} \<le> expectation (cts_step x y)"
    apply (elim ssubst)
    apply (rule integral_mono)
    apply simp
    apply (auto intro!: integrable_cts_step assms) []
    apply (auto simp add: cts_step_def indicator_def field_simps)
    done
next
  have "prob {..y} = integral\<^sup>L M (indicator {..y})"
    by simp
  thus "expectation (cts_step x y) \<le> prob {..y}"
    apply (elim ssubst)
    apply (rule integral_mono)
    apply (rule integrable_cts_step, rule assms)
    unfolding cts_step_def indicator_def using `x < y`
    by (auto simp add: field_simps)
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
      by (rule convergent_real_imp_convergent_ereal, rule conv, simp)
    also have "\<dots> = integral\<^sup>L M (cts_step x y)"
      apply (subst convergent_real_imp_convergent_ereal, rule conv, auto)
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
      by (rule convergent_real_imp_convergent_ereal, rule conv, simp)
    also have "\<dots> = integral\<^sup>L M (cts_step y x)"
      apply (subst convergent_real_imp_convergent_ereal, rule conv, auto)
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
      apply (rule tendsto_le [OF _ 1 2], auto)
      apply (subst eventually_at_right[of _ "x + 1"])
      apply simp
      apply (rule exI [of _ "x+1"])
      apply auto
      apply (rule *)
      apply assumption
      done
  qed
  moreover have ge: "cdf M x \<le> liminf (\<lambda>n. cdf (M_seq n) x)"
  proof -
    interpret real_distribution M by (rule assms) 
    have 1: "((\<lambda>x. ereal (cdf M x)) ---> cdf M x) (at_left x)"
      by (simp add: continuous_within [symmetric] left_cont) 
    have 2: "((\<lambda>t. liminf (\<lambda>n. cdf (M_seq n) x)) ---> 
        liminf (\<lambda>n. cdf (M_seq n) x)) (at_left x)" by (rule tendsto_const)
    show ?thesis
      apply (rule tendsto_le [OF _ 2 1])
      apply auto
      apply (subst eventually_at_left[of "x - 1"])
      apply simp
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
         (\<lambda>n. integral\<^sup>L (M_seq n) f::real) ----> integral\<^sup>L M f"
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

