(*
  Theory: Helly_Selection.thy
  Authors: Jeremy Avigad, Luke Serafin
*)

section \<open>Helly's selection theorem\<close>

text \<open>The set of bounded, monotone, right continuous functions is sequentially compact\<close>

theory Helly_Selection
  imports Diagonal_Subsequence Weak_Convergence Library_Misc
begin

lemma ereal_Inf:
  assumes *: "bdd_below A" "A \<noteq> {}"
  shows "ereal (Inf A) = (INF a:A. ereal a)"
proof (rule ereal_Inf)
  from * obtain l u where "\<And>x. x \<in> A \<Longrightarrow> l \<le> x" "u \<in> A"
    by (auto simp: bdd_below_def)
  then have "l \<le> (INF x:A. ereal x)" "(INF x:A. ereal x) \<le> u"
    by (auto intro!: INF_greatest INF_lower)
  then show "\<bar>INF a:A. ereal a\<bar> \<noteq> \<infinity>"
    by auto
qed

lemma setcompr_eq_image: "{f x |x. P x} = f ` {x. P x}"
  by auto

lemma minus_one_less: "a - 1 < (a::real)"
  by simp

lemma ereal_dist_eq: "\<forall>e>0. \<bar>a - b\<bar> < ereal e \<Longrightarrow> a = b"
  apply (cases a b rule: ereal2_cases)
  apply (auto elim: allE[of _ 1])
  apply (metis eq_iff_diff_eq_0 less_irrefl zero_less_abs_iff)
  done

theorem Helly_selection:
  fixes f :: "nat \<Rightarrow> real \<Rightarrow> real"
  assumes rcont: "\<And>n x. continuous (at_right x) (f n)"
  assumes mono: "\<And>n. mono (f n)"
  assumes bdd: "\<And>n x. \<bar>f n x\<bar> \<le> M"
  shows "\<exists>s. subseq s \<and> (\<exists>F. (\<forall>x. continuous (at_right x) F) \<and> mono F \<and> (\<forall>x. \<bar>F x\<bar> \<le> M) \<and>
    (\<forall>x. continuous (at x) F \<longrightarrow> (\<lambda>n. f (s n) x) ----> F x))"
proof -
  obtain m :: "real \<Rightarrow> nat" where "bij_betw m \<rat> UNIV"
    using countable_rat Rats_infinite by (erule countableE_infinite)
  then obtain r :: "nat \<Rightarrow> real" where bij: "bij_betw r UNIV \<rat>"
    using bij_betw_inv by blast

  have dense_r: "\<And>x y. x < y \<Longrightarrow> \<exists>n. x < r n \<and> r n < y"
    by (metis Rats_dense_in_real bij f_the_inv_into_f bij_betw_def)

  let ?P = "\<lambda>n. \<lambda>s. convergent (\<lambda>k. f (s k) (r n))"
  interpret nat: subseqs ?P
  proof (unfold convergent_def, unfold subseqs_def, auto)
    fix n :: nat and s :: "nat \<Rightarrow> nat" assume s: "subseq s"
    have "bounded {-M..M}"
      using bounded_closed_interval by auto
    moreover have "\<And>k. f (s k) (r n) \<in> {-M..M}" 
      using bdd by (simp add: abs_le_iff minus_le_iff)
    ultimately have "\<exists>l s'. subseq s' \<and> ((\<lambda>k. f (s k) (r n)) \<circ> s') ----> l"
      using compact_Icc compact_imp_seq_compact seq_compactE by metis
    thus "\<exists>s'. subseq s' \<and> (\<exists>l. (\<lambda>k. f (s (s' k)) (r n)) ----> l)"
      by (auto simp: comp_def)
  qed
  def d \<equiv> "nat.diagseq"
  have subseq: "subseq d"
    unfolding d_def using nat.subseq_diagseq by auto
  have rat_cnv: "?P n d" for n
  proof -
    have Pn_seqseq: "?P n (nat.seqseq (Suc n))"
      by (rule nat.seqseq_holds)
    have 1: "(\<lambda>k. f ((nat.seqseq (Suc n) \<circ> (\<lambda>k. nat.fold_reduce (Suc n) k
      (Suc n + k))) k) (r n)) = (\<lambda>k. f (nat.seqseq (Suc n) k) (r n)) \<circ>
      (\<lambda>k. nat.fold_reduce (Suc n) k (Suc n + k))"
      by auto
    have 2: "?P n (d \<circ> (op + (Suc n)))"
      unfolding d_def
      apply (subst nat.diagseq_seqseq)
      apply (subst 1)
      apply (rule convergent_subseq_convergent[of "\<lambda>k. f (nat.seqseq (Suc n) k) (r n)"
        "\<lambda>k. nat.fold_reduce (Suc n) k (Suc n + k)"])
      by (rule Pn_seqseq) (rule nat.subseq_diagonal_rest)
    then obtain L where 3: "(\<lambda>k. f ((d \<circ> (op + (Suc n))) k) (r n)) ----> L"
      using convergentD by auto
    have 4: "(\<lambda>k. f (d (k + (Suc n))) (r n)) = (\<lambda>k. f ((d \<circ> (op + (Suc n))) k) (r n))"
      by (auto simp: add.commute)
    have "(\<lambda>k. f (d k) (r n)) ----> L" 
      apply (rule LIMSEQ_offset[of _ "Suc n"])
      by (subst 4) (rule 3)
    thus ?thesis unfolding convergent_def by auto
  qed
  let ?f = "\<lambda>n. \<lambda>k. f (d k) (r n)"
  have lim_f: "?f n ----> lim (?f n)" for n
    using rat_cnv convergent_LIMSEQ_iff by auto
  have lim_bdd: "lim (?f n) \<in> {-M..M}" for n
  proof -
    have "closed {-M..M}" using closed_real_atLeastAtMost by auto
    hence "(\<forall>i. ?f n i \<in> {-M..M}) \<and> ?f n ----> lim (?f n) \<longrightarrow> lim (?f n) \<in> {-M..M}"
      unfolding closed_sequential_limits by (drule_tac x = "\<lambda>k. f (d k) (r n)" in spec) blast
    moreover have "\<forall>i. ?f n i \<in> {-M..M}"
      using bdd by (simp add: abs_le_iff minus_le_iff)
    ultimately show "lim (?f n) \<in> {-M..M}"
      using lim_f by auto
  qed
  then have limset_bdd: "\<And>x. {lim (?f n) |n. x < r n} \<subseteq> {-M..M}"
    by auto
  then have bdd_below: "bdd_below {lim (?f n) |n. x < r n}" for x
    by (metis (mono_tags) bdd_below_Icc bdd_below_mono)
  have r_unbdd: "\<exists>n. x < r n" for x
    using dense_r[OF less_add_one, of x] by auto
  then have nonempty: "{lim (?f n) |n. x < r n} \<noteq> {}" for x
    by auto

  def F \<equiv> "\<lambda>x. Inf {lim (?f n) |n. x < r n}"
  have F_eq: "ereal (F x) = (INF n:{n. x < r n}. ereal (lim (?f n)))" for x
    unfolding F_def by (subst ereal_Inf[OF bdd_below nonempty]) (simp add: setcompr_eq_image)
  have mono_F: "mono F"
    using nonempty by (auto intro!: cInf_superset_mono simp: F_def bdd_below mono_def)
  moreover have "\<And>x. continuous (at_right x) F"
    unfolding continuous_within order_tendsto_iff eventually_at_right[OF less_add_one]
  proof safe
    show "F x < u \<Longrightarrow> \<exists>b>x. \<forall>y>x. y < b \<longrightarrow> F y < u" for x u
      unfolding F_def cInf_less_iff[OF nonempty bdd_below] by auto
  next
    show "\<exists>b>x. \<forall>y>x. y < b \<longrightarrow> l < F y" if l: "l < F x" for x l
      using less_le_trans[OF l mono_F[THEN monoD, of x]] by (auto intro: less_add_one)
  qed
  moreover
  { fix x
    have "F x \<in> {-M..M}"
      unfolding F_def using limset_bdd bdd_below r_unbdd by (intro closed_subset_contains_Inf) auto
    then have "\<bar>F x\<bar> \<le> M" by auto }
  moreover have "(\<lambda>n. f (d n) x) ----> F x" if cts: "continuous (at x) F" for x
  proof (rule limsup_le_liminf_real)
    show "limsup (\<lambda>n. f (d n) x) \<le> F x"
    proof (rule tendsto_le_const)
      show "(F ---> ereal (F x)) (at_right x)"
        using cts unfolding continuous_at_split by (auto simp: continuous_within)
      show "\<forall>\<^sub>F i in at_right x. limsup (\<lambda>n. f (d n) x) \<le> F i"
        unfolding eventually_at_right[OF less_add_one]
      proof (rule, rule, rule less_add_one, safe)
        fix y assume y: "x < y"
        with dense_r obtain N where "x < r N" "r N < y" by auto
        have *: "y < r n' \<Longrightarrow> lim (?f N) \<le> lim (?f n')" for n'
          using \<open>r N < y\<close> by (intro LIMSEQ_le[OF lim_f lim_f]) (auto intro!: mono[THEN monoD])
        have "limsup (\<lambda>n. f (d n) x) \<le> limsup (?f N)"
          using \<open>x < r N\<close> by (auto intro!: Limsup_mono always_eventually mono[THEN monoD])
        also have "\<dots> = lim (\<lambda>n. ereal (?f N n))"
          using rat_cnv[of N] by (force intro!: convergent_limsup_cl simp: convergent_def)
        also have "\<dots> \<le> F y"
          by (auto intro!: INF_greatest * simp: convergent_real_imp_convergent_ereal rat_cnv F_eq)
        finally show "limsup (\<lambda>n. f (d n) x) \<le> F y" .
      qed
    qed simp
    show "F x \<le> liminf (\<lambda>n. f (d n) x)"
    proof (rule tendsto_ge_const)
      show "(F ---> ereal (F x)) (at_left x)"
        using cts unfolding continuous_at_split by (auto simp: continuous_within)
      show "\<forall>\<^sub>F i in at_left x. F i \<le> liminf (\<lambda>n. f (d n) x)"
        unfolding eventually_at_left[OF minus_one_less]
      proof (rule, rule, rule minus_one_less, safe)
        fix y assume y: "y < x"
        with dense_r obtain N where "y < r N" "r N < x" by auto
        have "F y \<le> liminf (?f N)"
          using \<open>y < r N\<close> by (auto simp: F_eq convergent_real_imp_convergent_ereal
            rat_cnv convergent_liminf_cl intro!: INF_lower2)
        also have "\<dots> \<le> liminf (\<lambda>n. f (d n) x)"
          using \<open>r N < x\<close> by (auto intro!: Liminf_mono monoD[OF mono] always_eventually)
        finally show "F y \<le> liminf (\<lambda>n. f (d n) x)" .
      qed
    qed simp
  qed
  ultimately show ?thesis using subseq by auto
qed

(** Weak convergence corollaries to Helly's theorem. **)

definition
  tight :: "(nat \<Rightarrow> real measure) \<Rightarrow> bool"
where
  "tight \<mu> \<equiv> (\<forall>n. real_distribution (\<mu> n)) \<and> (\<forall>(\<epsilon>::real)>0. \<exists>a b::real. a < b \<and> (\<forall>n. measure (\<mu> n) {a<..b} > 1 - \<epsilon>))"

(* Can strengthen to equivalence. *)
theorem tight_iff_convergent_subsubsequence:
  assumes \<mu>: "tight \<mu>"
  shows "\<forall>s. subseq s \<longrightarrow> (\<exists>r. \<exists>M.  subseq r \<and> real_distribution M \<and> weak_conv_m (\<mu> \<circ> s \<circ> r) M)"
proof safe
  fix s assume s: "subseq s"
  def f \<equiv> "\<lambda>k. cdf (\<mu> (s k))"
  interpret \<mu>: real_distribution "\<mu> k" for k
    using \<mu> unfolding tight_def by auto

  have rcont: "\<And>x. continuous (at_right x) (f k)"
    and mono: "mono (f k)"
    and top: "(f k ---> 1) at_top"
    and bot: "(f k ---> 0) at_bot" for k
    unfolding f_def mono_def
    using \<mu>.cdf_nondecreasing \<mu>.cdf_is_right_cont \<mu>.cdf_lim_at_top_prob \<mu>.cdf_lim_at_bot by auto
  have bdd: "\<bar>f k x\<bar> \<le> 1" for k x
    by (auto simp add: abs_le_iff minus_le_iff f_def \<mu>.cdf_nonneg \<mu>.cdf_bounded_prob)

  from Helly_selection[OF rcont mono bdd, of "\<lambda>x. x"] obtain r F
    where F: "subseq r" "\<And>x. continuous (at_right x) F" "mono F" "\<And>x. \<bar>F x\<bar> \<le> 1"
    and lim_F: "\<And>x. continuous (at x) F \<Longrightarrow> (\<lambda>n. f (r n) x) ----> F x"
    by blast

  have "0 \<le> f n x" for n x
    unfolding f_def by (rule \<mu>.cdf_nonneg)
  have F_nonneg: "0 \<le> F x" for x
  proof -
    obtain y where "y < x" "isCont F y"
      using open_minus_countable[OF mono_ctble_discont[OF \<open>mono F\<close>], of "{..< x}"] by auto
    then have "0 \<le> F y"
      by (intro LIMSEQ_le_const[OF lim_F]) (auto simp: f_def \<mu>.cdf_nonneg)
    also have "\<dots> \<le> F x"
      using \<open>y < x\<close> by (auto intro!: monoD[OF \<open>mono F\<close>])
    finally show "0 \<le> F x" .
  qed

  have Fab: "\<exists>a b. (\<forall>x\<ge>b. F x \<ge> 1 - \<epsilon>) \<and> (\<forall>x\<le>a. F x \<le> \<epsilon>)" if \<epsilon>: "0 < \<epsilon>" for \<epsilon>
  proof auto
    from \<epsilon> \<mu> have "\<exists>a' b'. a' < b' \<and> (\<forall>k. measure (\<mu> k) {a'<..b'} > 1 - \<epsilon>)" unfolding tight_def by auto
    then obtain a' b' where a'b': "a' < b'" "\<And>k. measure (\<mu> k) {a'<..b'} > 1 - \<epsilon>" by auto
    obtain a where a: "a < a'" "isCont F a"
      using open_minus_countable[OF mono_ctble_discont[OF \<open>mono F\<close>], of "{..< a'}"] by auto
    obtain b where b: "b' < b" "isCont F b"
      using open_minus_countable[OF mono_ctble_discont[OF \<open>mono F\<close>], of "{b' <..}"] by auto
    from a b a'b' have ab: "a < b" "\<And>k. measure (\<mu> k) {a<..b} > 1 - \<epsilon>"
    proof simp
      fix k
      have "{a'<..b'} \<subseteq> {a<..b}" using a b by auto
      hence "measure (\<mu> k) {a'<..b'} \<le> measure (\<mu> k) {a<..b}" using \<mu>.finite_measure_mono by auto
      thus "measure (\<mu> k) {a<..b} > 1 - \<epsilon>" using a'b'(2) by (metis less_eq_real_def less_trans)
    qed
    from b(2) lim_F have "(\<lambda>k. f (r k) b) ----> F b" by auto
    hence subsubseq_lim: "(\<lambda>k. measure ((\<mu> \<circ> s \<circ> r) k) {..b}) ----> F b"
      unfolding f_def cdf_def o_def by auto
    have "\<And>k. measure ((\<mu> \<circ> s \<circ> r) k) {..b} =
      measure ((\<mu> \<circ> s \<circ> r) k) {..a} + measure ((\<mu> \<circ> s \<circ> r) k) {a<..b}"
      by (subst ivl_disj_un(9)[symmetric,of a b])
         (auto simp add: ab less_imp_le intro: \<mu>.finite_measure_Union)
    hence "\<And>k. measure ((\<mu> \<circ> s \<circ> r) k) {a<..b} =
      measure ((\<mu> \<circ> s \<circ> r) k) {..b} - measure ((\<mu> \<circ> s \<circ> r) k) {..a}" by simp
    hence *: "\<And>k. measure ((\<mu> \<circ> s \<circ> r) k) {a<..b} = f (r k) b - f (r k) a"
      unfolding f_def cdf_def o_def by auto
    have "lim (\<lambda>k. measure ((\<mu> \<circ> s \<circ> r) k) {a<..b}) \<le> F b"
      apply (rule tendsto_le[of sequentially "\<lambda>k. measure ((\<mu> \<circ> s \<circ> r) k) {..b}" "F b"
        "\<lambda>k. measure ((\<mu> \<circ> s \<circ> r) k) {a<..b}"  "lim (\<lambda>k. measure ((\<mu> \<circ> s \<circ> r) k) {a<..b})"])
      using subsubseq_lim apply auto
      apply (subst convergent_LIMSEQ_iff[symmetric])
      apply (unfold convergent_def)
      using * unfolding o_def apply simp
      apply (rule exI)
      apply (rule tendsto_diff)
      using F lim_F b(2) a(2) apply auto
      apply (rule eventually_sequentiallyI)
      by (rule \<mu>.finite_measure_mono) auto
    moreover have "1 - \<epsilon> \<le> lim (\<lambda>k. measure ((\<mu> \<circ> s \<circ> r) k) {a<..b})"
      apply (rule tendsto_le[of sequentially "\<lambda>k. measure ((\<mu> \<circ> s \<circ> r) k) {a<..b}"
        "lim (\<lambda>k. measure ((\<mu> \<circ> s \<circ> r) k) {a<..b})" "\<lambda>k. 1 - \<epsilon>" "1 - \<epsilon>"], auto)
      apply (subst convergent_LIMSEQ_iff[symmetric])
      apply (unfold convergent_def)
      apply (rule exI)
      using * unfolding o_def apply simp
      apply (rule tendsto_diff)
      using a b lim_F apply auto
      apply (rule eventually_sequentiallyI)
      using ab(2) less_imp_le by metis
    ultimately have "1 - \<epsilon> \<le> F b" by (metis order.trans)
    hence "\<forall>x\<ge>b. F x \<ge> 1 - \<epsilon>" using F unfolding mono_def by (metis order.trans)
    thus "\<exists>b. \<forall>x\<ge>b. 1 - \<epsilon> \<le> F x" by auto
    from a(2) lim_F have "(\<lambda>k. f (r k) a) ----> F a" by auto
    hence "(\<lambda>k. measure ((\<mu> \<circ> s \<circ> r) k) {..a}) ----> F a" unfolding f_def cdf_def o_def by auto
    hence "lim (\<lambda>k. measure ((\<mu> \<circ> s \<circ> r) k) {..a}) = F a" using limI by auto
    have 1: "\<And>n. measure (\<mu> n) {..a} < \<epsilon>"
    proof-
      fix n
      have "measure (\<mu> n) {..a} + measure (\<mu> n) {a<..b} \<le> 1"
        by (subst \<mu>.finite_measure_Union[symmetric]) auto
      thus "measure (\<mu> n) {..a} < \<epsilon>" using ab(2)[of n] by simp
    qed
    have Fa: "F a \<le> \<epsilon>"
      apply (rule tendsto_le[of sequentially "\<lambda>k. \<epsilon>" \<epsilon> "\<lambda>k. f (r k) a" "F a"], auto)
      using lim_F a apply auto
      apply (rule eventually_sequentiallyI)
      apply (unfold f_def cdf_def)
      using 1 less_imp_le by metis
    hence  "\<forall>x\<le>a. F x \<le> \<epsilon>" using F unfolding mono_def by (metis order.trans)
    thus "\<exists>a. \<forall>x\<le>a. F x \<le> \<epsilon>" by auto
  qed
  have "(F ---> 1) at_top" "(F ---> 0) at_bot"
  unfolding tendsto_def proof (auto simp add: eventually_at_top_linorder eventually_at_bot_linorder)
    fix S :: "real set" assume S: "open S" "1 \<in> S"
    show "\<exists>N. \<forall>n\<ge>N. F n \<in> S"
    proof (rule openE[of _ 1], auto intro: S)
      fix \<epsilon> assume \<epsilon>: "\<epsilon> > 0" "ball 1 \<epsilon> \<subseteq> S"
      with Fab have "\<exists>b. (\<forall>x\<ge>b. 1 - \<epsilon>/2 \<le> F x)" by auto
      then guess b .. note b = this
      hence "\<forall>n\<ge>b. 1 - \<epsilon> < F n"
        apply (subgoal_tac "1 - \<epsilon> < 1 - \<epsilon>/2")
        apply (metis less_le_trans)
        by (simp add: \<epsilon>(1))
      hence "\<forall>n\<ge>b. F n \<in> ball 1 \<epsilon>"
        unfolding ball_def dist_real_def apply auto
        apply (subgoal_tac "\<bar>F n\<bar> = F n")
        apply (erule ssubst)
        using F_nonneg F abs_of_nonneg
        apply (auto simp: field_simps)
        done
      hence "\<forall>n\<ge>b. F n \<in> S" using \<epsilon> by auto
      thus "\<exists>N. \<forall>n\<ge>N. F n \<in> S" by auto
    qed
  (* Duplication to be removed. *)
  next fix S :: "real set" assume S: "open S" "0 \<in> S"
    show "\<exists>N. \<forall>n\<le>N. F n \<in> S"
    proof (rule openE[of _ 0], auto intro: S)
      fix \<epsilon> assume \<epsilon>: "\<epsilon> > 0" "ball 0 \<epsilon> \<subseteq> S"
      with Fab[rule_format, of "\<epsilon>/2"] have "\<exists>a. (\<forall>x\<le>a. F x \<le> \<epsilon>/2)" by auto
      then guess a .. note a = this
      hence "\<forall>n\<le>a. F n < \<epsilon>" using \<epsilon>(1) by auto
      hence "\<forall>n\<le>a. F n \<in> ball 0 \<epsilon>"
        unfolding ball_def dist_real_def apply auto
        apply (subgoal_tac "\<bar>F n\<bar> = F n")
        apply (erule ssubst)
        using F_nonneg F abs_of_nonneg by auto
      hence "\<forall>n\<le>a. F n \<in> S" using \<epsilon> by auto
      thus "\<exists>N. \<forall>n\<le>N. F n \<in> S" by auto
    qed
  qed
  with F have M: "real_distribution (interval_measure F)" "cdf (interval_measure F) = F"
    by (auto intro!: real_distribution_interval_measure cdf_interval_measure simp: mono_def)
  with lim_F have "weak_conv (f \<circ> r) F" unfolding weak_conv_def f_def using lim_subseq by auto
  hence "weak_conv_m (\<mu> \<circ> s \<circ> r) (interval_measure F)" using M unfolding weak_conv_m_def f_def o_def by auto
  hence "\<exists>M. real_distribution M \<and> weak_conv_m (\<mu> \<circ> s \<circ> r) M" using M by auto
  thus "\<exists>r M. subseq r \<and> (real_distribution M \<and> weak_conv_m (\<mu> \<circ> s \<circ> r) M)" using F by auto
(*
next
  assume sseq: "\<forall>s. subseq s \<longrightarrow> (\<exists>r. subseq r \<and> (\<exists>M. real_distribution M \<and> weak_conv_m (\<mu> \<circ> s \<circ> r) M))"
  show "tight \<mu>" unfolding tight_def
  proof (rule ccontr, auto simp add: assms not_less)
    fix \<epsilon> :: real assume \<epsilon>: "\<epsilon> > 0"
    assume ntight: "\<forall>a b. b \<le> a \<or> (\<exists>n. Sigma_Algebra.measure (\<mu> n) {a<..b} \<le> 1 - \<epsilon>)"
    show False
    proof (cases "\<epsilon> \<le> 1")
      assume \<epsilon>1: "\<epsilon> \<le> 1"
      have "\<forall>k :: nat. \<exists>n. Sigma_Algebra.measure (\<mu> n) {-real k<..real k} \<le> 1 - \<epsilon>"
      proof
        fix k :: nat
        show "\<exists>n. Sigma_Algebra.measure (\<mu> n) {- real k<..real k} \<le> 1 - \<epsilon>"
        proof (cases "k = 0")
          assume "k = 0"
          hence "{-k<..k} = {}" by simp
          thus ?thesis using \<epsilon>1 by auto
        next
          assume "k \<noteq> 0"
          hence "\<not>real k \<le> - real k" by simp
          thus ?thesis using ntight by blast
        qed
      qed
      hence "\<exists>s. subseq s \<and> (\<forall>k::nat. measure (\<mu> (s k)) {-real k<..k} \<le> 1 - \<epsilon>)"
        using choice[of "\<lambda>k n::nat. measure (\<mu> n) {-real k<..k} \<le> 1 - \<epsilon>"] sorry
      then guess s .. note s = this
      with sseq have "\<exists>r. subseq r \<and> (\<exists>M. real_distribution M \<and> weak_conv_m (\<mu> \<circ> s \<circ> r) M)" by auto
      then guess r .. note r = this
      hence "\<exists>M. real_distribution M \<and> weak_conv_m (\<mu> \<circ> s \<circ> r) M" by auto
      then guess M .. note M = this
      hence "\<exists>a b. measure M {a} = 0 \<and> measure M {b} = 0 \<and> measure M {a<..b} > 1 - \<epsilon>" sorry
      then obtain a b where "measure M {a} = 0 \<and> measure M {b} = 0 \<and> measure M {a<..b} > 1 - \<epsilon>" by auto
      hence cnv: "(\<lambda>k. measure (\<mu> (s (r k))) {a<..b}) ----> measure M {a<..b}" using M sorry
      have "\<exists>j. {a<..b} \<subseteq> {-real (r j)..r j}" sorry
      then guess j .. note j = this
      hence "measure (\<mu> (s (r j))) {a<..b} \<le> measure (\<mu> (s (r j))) {-real (r j)..r j}"
        using finite_measure.finite_measure_mono sorry
      also have "measure (\<mu> (s (r j))) {-real (r j)..r j} \<le> 1 - \<epsilon>" sorry
      thus False sorry
    next
      assume "\<not>\<epsilon>\<le>1"
      hence "1 - \<epsilon> < 0" by simp
      thus False using ntight[rule_format,where a = 0 and b = 1] measure_nonneg
        by (metis dual_order.strict_trans2 less_le_not_le not_one_le_zero)
    qed
  qed
*)
qed

corollary tight_subseq_weak_converge:
  fixes \<mu> :: "nat \<Rightarrow> real measure" and M :: "real measure"
  assumes "\<And>n. real_distribution (\<mu> n)" "real_distribution M" and tight: "tight \<mu>" and
    subseq: "\<And>s \<nu>. subseq s \<Longrightarrow> real_distribution \<nu> \<Longrightarrow> weak_conv_m (\<mu> \<circ> s) \<nu> \<Longrightarrow> weak_conv_m (\<mu> \<circ> s) M"
  shows "weak_conv_m \<mu> M"
proof (rule ccontr)
  from tight tight_iff_convergent_subsubsequence
  have subsubseq: "\<forall>s. subseq s \<longrightarrow> (\<exists>r M. subseq r \<and> real_distribution M \<and> weak_conv_m (\<mu> \<circ> s \<circ> r) M)"
    using assms by simp
  {
    fix s assume s: "subseq s"
    with subsubseq subseq have "\<exists>r M. subseq r \<and> real_distribution M \<and> weak_conv_m (\<mu> \<circ> s \<circ> r) M"
      by simp
    then guess r .. note r = this
    then guess \<nu> .. note \<nu> = this
    hence subsubseq_conv: "weak_conv_m (\<mu> \<circ> (s \<circ> r)) \<nu>" by (auto simp add: o_assoc)
    from s r have sr: "subseq (s \<circ> r)" using subseq_o by auto
    with subsubseq_conv subseq \<nu> have "weak_conv_m (\<mu> \<circ> (s \<circ> r)) M" by auto
    with r have "\<exists>r. subseq r \<and> weak_conv_m (\<mu> \<circ> (s \<circ> r)) M" by auto
  }
  hence *: "\<And>s. subseq s \<Longrightarrow> \<exists>r. subseq r \<and> weak_conv_m (\<mu> \<circ> (s \<circ> r)) M" by auto
  def f \<equiv> "\<lambda>n. cdf (\<mu> n)"
  def F \<equiv> "cdf M"
  assume CH: "\<not> weak_conv_m \<mu> M"
  hence "\<exists>x. isCont F x \<and> \<not>((\<lambda>n. f n x) ----> F x)"
    unfolding weak_conv_m_def weak_conv_def f_def F_def by auto
  then guess x .. note x = this
  hence "\<exists>\<epsilon>>0. \<exists>s. subseq s \<and> (\<forall>n. \<bar>f (s n) x - F x\<bar> \<ge> \<epsilon>)"
    apply (subst (asm) tendsto_iff, auto simp add: not_less)
    apply (subst (asm) eventually_sequentially, auto)
    unfolding dist_real_def apply (simp add: not_less)
    apply (subst subseq_Suc_iff)
    apply (rule_tac x = e in exI, safe)
    proof -
      fix e assume e: "0 < e" "\<forall>N. \<exists>n\<ge>N. e \<le> \<bar>f n x - F x\<bar>"
      then obtain n where n: "\<And>N. N \<le> n N" "\<And>N. e \<le> \<bar>f (n N) x - F x\<bar>" by metis
      def s \<equiv> "rec_nat (n 0) (\<lambda>_ i. n (Suc i))"
      then have s[simp]: "s 0 = n 0" "\<And>i. s (Suc i) = n (Suc (s i))"
        by simp_all
      { fix i have "s i < s (Suc i)"
          using n(1)[of "Suc (s i)"] n(2)[of 0]  by simp_all }
      moreover { fix i have "e \<le> \<bar>f (s i) x - F x\<bar>"
        by (cases i) (simp_all add: n) }
      ultimately show "\<exists>s. (\<forall>n. s n < s (Suc n)) \<and> (\<forall>n. e \<le> \<bar>f (s n) x - F x\<bar>)"
        by metis
    qed
  then obtain \<epsilon> s where \<epsilon>: "\<epsilon> > 0" and s: "subseq s \<and> (\<forall>n. \<bar>f (s n) x - F x\<bar> \<ge> \<epsilon>)" by auto
  hence "\<And>r. subseq r \<Longrightarrow> \<not>weak_conv_m (\<mu> \<circ> s \<circ> r) M"
    apply (unfold weak_conv_m_def weak_conv_def, auto)
    apply (rule_tac x = x in exI)
    apply (subst tendsto_iff)
    unfolding dist_real_def apply (subst eventually_sequentially)
    using x unfolding F_def apply auto
    apply (subst not_less)
    apply (subgoal_tac "(\<lambda>n. cdf (\<mu> (s (r n))) x) = (\<lambda>n. f (s (r n)) x)")
    apply (erule ssubst)
    apply (rule_tac x = \<epsilon> in exI)
    unfolding f_def by auto
  thus False using subseq * by (metis fun.map_comp s) 
qed

end
