theory Helly_Selection
imports Diagonal_Subsequence Weak_Convergence Library_Misc

begin

theorem Helly_selection:
  fixes f :: "nat \<Rightarrow> real \<Rightarrow> real"
  assumes rcont_inc: "\<And>n. rcont_inc (f n)"
  and unif_bdd: "\<forall>n x. \<bar>f n x\<bar> \<le> M"
  shows "\<exists>s. subseq s \<and> (\<exists>F. rcont_inc F \<and> (\<forall>x. \<bar>F x\<bar> \<le> M) \<and>
    (\<forall>x.  continuous (at x) F \<longrightarrow> (\<lambda>n. f (s n) x) ----> F x))"
proof -
  obtain m :: "real \<Rightarrow> nat" where "bij_betw m \<rat> UNIV"
    apply (rule countableE_infinite)
    apply (rule countable_rat)
    apply (rule real_rats_infinite)
    by auto
  then obtain r :: "nat \<Rightarrow> real" where bij: "bij_betw r UNIV \<rat>" using bij_betw_inv by blast
  let ?P = "\<lambda>n. \<lambda>s. convergent (\<lambda>k. f (s k) (r n))"
  interpret nat: subseqs ?P
  proof (unfold convergent_def, unfold subseqs_def, auto)
    fix n :: nat fix s :: "nat \<Rightarrow> nat" assume s: "subseq s"
    have "bounded {-M..M}" using bounded_closed_interval by auto
    moreover have "\<And>k. f (s k) (r n) \<in> {-M..M}" using unif_bdd abs_le_interval_iff by auto
    ultimately have "\<exists>l s'. subseq s' \<and> ((\<lambda>k. f (s k) (r n)) \<circ> s') ----> l"
      using compact_Icc compact_imp_seq_compact seq_compactE by metis
    thus "\<exists>s'. subseq s' \<and> (\<exists>l. (\<lambda>k. f (s (s' k)) (r n)) ----> l)" unfolding o_def by auto
  qed
  def d \<equiv> "nat.diagseq"
  have subseq: "subseq d" unfolding d_def using nat.subseq_diagseq by auto
  have rat_cnv: "\<And>n. ?P n d"
  proof -
    fix n::nat show "?P n d"
    proof -
      have Pn_seqseq: "?P n (nat.seqseq (Suc n))"
        by (rule nat.seqseq_holds)
      have 1: "(\<lambda>k. f ((nat.seqseq (Suc n) \<circ> (\<lambda>k. nat.fold_reduce (Suc n) k
        (Suc n + k))) k) (r n)) = (\<lambda>k. f (nat.seqseq (Suc n) k) (r n)) \<circ>
        (\<lambda>k. nat.fold_reduce (Suc n) k (Suc n + k))"
        by auto
      have 2: "?P n (d \<circ> (op + (Suc n)))"
        unfolding d_def apply (subst nat.diagseq_seqseq)
        apply (subst 1)
        apply (rule convergent_subseq_convergent[of "\<lambda>k. f (nat.seqseq (Suc n) k) (r n)"
          "\<lambda>k. nat.fold_reduce (Suc n) k (Suc n + k)"])
        by (rule Pn_seqseq) (rule nat.subseq_diagonal_rest)
      then obtain L where 3: "(\<lambda>k. f ((d \<circ> (op + (Suc n))) k) (r n)) ----> L"
        using convergentD by auto
      have 4: "(\<lambda>k. f (d (k + (Suc n))) (r n)) =
      (\<lambda>k. f ((d \<circ> (op + (Suc n))) k) (r n))"
        by (auto simp: add_commute)
      have "(\<lambda>k. f (d k) (r n)) ----> L" 
        apply (rule LIMSEQ_offset[of _ "Suc n"])
        by (subst 4) (rule 3)
      thus ?thesis unfolding convergent_def by auto
    qed
  qed
  have M_nonneg: "0 \<le> M" using unif_bdd by (metis abs_minus_le_zero less_le less_trans neg_le_0_iff_le)
  have lim_bdd: "\<And>n. lim (\<lambda>k. f (d k) (r n)) \<in> {-M..M}"
  proof -
    fix n::nat
    have "closed {-M..M}" using closed_real_atLeastAtMost by auto
    hence "(\<forall>i. (\<lambda>k. f (d k) (r n)) i \<in> {-M..M}) \<and> (\<lambda>k. f (d k) (r n)) ----> lim (\<lambda>k. f (d k) (r n))
      \<longrightarrow> lim (\<lambda>k. f (d k) (r n)) \<in> {-M..M}"
      apply (subst (asm) closed_sequential_limits)
      by (drule_tac x = "\<lambda>k. f (d k) (r n)" in spec) blast
    moreover have "\<forall>i. (\<lambda>k. f (d k) (r n)) i \<in> {-M..M}" using unif_bdd abs_le_interval_iff by auto
    moreover have "(\<lambda>k. f (d k) (r n)) ----> lim (\<lambda>k. f (d k) (r n))"
      using rat_cnv convergent_LIMSEQ_iff by auto
    ultimately show "lim (\<lambda>k. f (d k) (r n)) \<in> {-M..M}" by auto
  qed
  hence limset_bdd: "\<And>x. {lim (\<lambda>k. f (d k) (r n)) |n. x < r n} \<subseteq> {-M..M}" by auto
  hence bdd_below: "\<And>x. bdd_below {lim (\<lambda>k. f (d k) (r n)) |n. x < r n}"
    (* Why does auto not get this? (auto intro: subset_bdd_below bdd_below_at_LeastAtMost limset_bdd) *)
  proof -
    fix x show " bdd_below {lim (\<lambda>k. f (d k) (r n)) |n. x < r n}"
    by (metis (mono_tags) bdd_below_Icc bdd_below_mono limset_bdd) 
  qed
  have nonempty: "\<And>x::real. {lim (\<lambda>k. f (d k) (r n)) |n. x < r n} \<noteq> {}"
  proof -
    fix x :: real
    obtain q where q: "q \<in> \<rat> \<and> x < q" by (metis (full_types) Rats_dense_in_real linordered_field_no_ub)
    let ?n = "the_inv_into UNIV r q"
    let ?y = "lim (\<lambda>k. f (d k) (r ?n))"
    have "x < r ?n" using f_the_inv_into_f bij q by (metis bij_betw_def)
    then have "?y \<in> {lim (\<lambda>k. f (d k) (r n)) |n. x < r n}" by auto
    thus "{lim (\<lambda>k. f (d k) (r n)) |n. x < r n} \<noteq> {}" by auto
  qed
  { fix x :: real
    from rat_unbounded [of "x + 1"] guess q ..
    with bij have "x < r (inv r q)" apply (subst f_inv_f_surj_on [of r])
      unfolding bij_betw_def by (erule conjE, assumption, auto)
    hence "\<exists>n. x < r n" ..
  } note r_unbdd = this
  def F \<equiv> "\<lambda>x. Inf {lim (\<lambda>k. f (d k) (r n)) |n. x < r n}"
  have "\<And>x. F x \<in> {-M..M}"
    unfolding F_def apply (rule real_closed_subset_contains_Inf)
    using limset_bdd apply auto
    prefer 2 apply (rule bdd_below_mono)
    apply (rule bdd_below_Ici [of "-M"])
    apply (rule subset_trans, assumption, force)
    by (rule r_unbdd)
  have mono: "mono F"
  proof (unfold mono_def, auto)
    fix x y::real assume le: "x \<le> y"
    hence subset: "{lim (\<lambda>k. f (d k) (r n)) |n. y < r n} \<subseteq> {lim (\<lambda>k. f (d k) (r n)) |n. x < r n}"
      by auto
    show "F x \<le> F y"
      unfolding F_def apply (rule cInf_superset_mono[of "{lim (\<lambda>k. f (d k) (r n)) |n. y < r n}"
        "{lim (\<lambda>k. f (d k) (r n)) |n. x < r n}"])
      apply (rule nonempty)
      apply (rule bdd_below)
      by (rule subset)
  qed
  moreover have "\<And>x. continuous (at_right x) F" 
    apply (unfold Topological_Spaces.continuous_def)
    apply (unfold tendsto_def, auto)
    apply (subst eventually_at_right)
    proof -
      fix x::real fix S::"real set" assume openS: "open S"
      assume ntlim_inS: "F (netlimit (at_right x)) \<in> S"
      have "netlimit (at_right x) = x" by (auto intro: netlimit_within)
      with F_def have "F x \<in> S" using ntlim_inS by simp
      then obtain e where e_pos: "e > 0" and e: "ball (F x) e \<subseteq> S" using openE openS by auto
      have "\<exists>y \<in> {lim (\<lambda>k. f (d k) (r n)) |n. x < r n}. y < F x + e"
      proof -
        from e_pos have "F x < F x + e / 2" by simp
        from nonempty bdd_below this real_Inf_greatest'[of "{lim (\<lambda>k. f (d k) (r n)) |n. x < r n}" "F x + e/2"]
        have "\<exists>y\<in>{lim (\<lambda>k. f (d k) (r n)) |n. x < r n}. y \<le> F x + e / 2" by (auto simp add: F_def)
        then guess y .. note y = this
        hence "y < F x + e" using e_pos by auto
        moreover have "y \<in> {lim (\<lambda>k. f (d k) (r n)) |n. x < r n}" using y by auto
        ultimately show ?thesis ..
      qed
      then guess y .. note y = this
      then obtain n where n: "y = lim (\<lambda>k. f (d k) (r n)) \<and> x < r n" by auto
      have "\<forall>z. x < z \<and> z < r n \<longrightarrow> F z \<in> S"
      proof auto
        fix z assume gr: "x < z" and ls: "z < r n"
        have 1: "F x \<le> F z" using gr mono unfolding mono_def by auto
        have "F z \<le> y"
        proof -
          have "F z \<le> lim (\<lambda>k. f (d k) (r n))"
            unfolding F_def apply (rule cInf_lower)
            using bdd_below ls by auto
          thus ?thesis using n by simp
        qed
        hence "F z < F x + e" using y by auto
        hence "F z \<in> ball (F x) e" unfolding ball_def dist_real_def using 1 by auto
        thus "F z \<in> S" using e by auto
      qed
      thus "\<exists>b>x. \<forall>z. x < z \<and> z < b \<longrightarrow> F z \<in> S" using n by auto
    qed
  ultimately have rcont_inc_lim: "rcont_inc F" unfolding rcont_inc_def by auto
  moreover have bdd: "\<forall>x. \<bar>F x\<bar> \<le> M"
  proof auto
    fix x
    have "F x \<in> {-M..M}"
      unfolding F_def apply (rule real_atLeastAtMost_subset_contains_Inf)
      apply (rule nonempty)
      apply (rule bdd_below)
      apply (simp add: M_nonneg)
      apply (rule limset_bdd)
      done
    thus "\<bar>F x\<bar> \<le> M" by auto
  qed
  moreover have lim: "\<forall>x.  continuous (at x) F \<longrightarrow> (\<lambda>n. f (d n) x) ----> F x"
  proof auto
    fix x::real assume cts: "continuous (at x) F"
    show "(\<lambda>n. f (d n) x) ----> F x"
    proof -
      have "\<forall>(e::real)>0. 
        \<bar>limsup (\<lambda>n. ereal (f (d n) x)) - ereal (F x)\<bar> < e \<and> \<bar>ereal (F x) - liminf (\<lambda>n. ereal (f (d n) x))\<bar> < e"
      proof auto
        fix e::real assume e: "0 < e"
        have "F -- x --> F x" using cts continuous_at by auto
          hence "\<exists>d>0. \<forall>y. y \<noteq> x \<and> norm (y - x) < d \<longrightarrow> norm (F y - F x) < e"
            by (rule LIM_D) (rule e) (* Why did auto not work here? *)
        then obtain d' where d: "d' > 0" and cts': "\<forall>y. y \<noteq> x \<and> norm (y - x) < d' \<longrightarrow> norm (F y - F x) < e"
          by auto
        have "\<exists>y<x. norm (y - x) < d'"
        proof -
          have "\<bar>(x - d'/2) - x\<bar> < d'"
            by (metis abs_divide abs_minus_commute abs_numeral abs_of_pos add_diff_cancel comm_monoid_add_class.add.left_neutral d diff_add_cancel
                linordered_field_class.sign_simps(16) real_gt_half_sum)
          moreover have "x - d'/2 < x" using d by simp
          ultimately show ?thesis using exI[of _ "x - d'/2"] by auto
        qed
        then guess y .. note y = this
        then have "norm (F y - F x) < e" using cts' by auto
        hence 1: "F x - e < F y" using y mono by auto
        have "\<exists>n. y < r n \<and> r n < x"
        proof -
          obtain q where q: "q \<in> \<rat> \<and> y < q \<and> q < x" using y Rats_dense_in_real by auto
          let ?n = "the_inv_into UNIV r q"
          have "y < r ?n \<and> r ?n < x" using q bij f_the_inv_into_f unfolding bij_betw_def by metis
          thus ?thesis by auto
        qed
        then guess n.. note n = this
        have "F y \<le> lim (\<lambda>k. f (d k) (r n))"
          unfolding F_def apply (rule cInf_lower)
          using bdd_below n by auto
        hence 2: "F x - e < lim (\<lambda>k. f (d k) (r n))" using 1 by auto
        have "\<exists>m. x < r m \<and> lim (\<lambda>k. f (d k) (r m)) < F x + e"
        proof - (* Contains duplication from proof of right-continuity--fix. *)
          have "\<exists>z \<in> {lim (\<lambda>k. f (d k) (r n)) |n. x < r n}. z < F x + e"
          proof -
            from e have "F x < F x + e / 2" by simp
            from nonempty bdd_below this real_Inf_greatest'[of "{lim (\<lambda>k. f (d k) (r n)) |n. x < r n}" "F x + e/2"]
            have z: "\<exists>z\<in>{lim (\<lambda>k. f (d k) (r n)) |n. x < r n}. z \<le> F x + e / 2" by (auto simp add: F_def)
            then guess z .. note 1 = this
            hence "z < F x + e" using e by auto
            moreover have "z \<in> {lim (\<lambda>k. f (d k) (r n)) |n. x < r n}" using 1 by auto
            ultimately show ?thesis ..
          qed
          then guess z .. note z = this
          then obtain m where m: "z = lim (\<lambda>k. f (d k) (r m)) \<and> x < r m" by auto
          thus ?thesis using z by auto
        qed
        then guess m .. note m = this
        from n m have nm: "r n < r m" by auto
        have 3: "lim (\<lambda>k. f (d k) (r n)) \<le> lim (\<lambda>k. f (d k) (r m))"
        proof -
          have le: "\<And>k. f (d k) (r n) \<le> f (d k) (r m)" using y assms nm unfolding rcont_inc_def mono_def by auto
          have "convergent (\<lambda>k. f (d k) (r n))" using Bseq_mono_convergent rcont_inc rat_cnv
            unfolding rcont_inc_def mono_def by auto
          hence L1: "(\<lambda>k. f (d k) (r n)) ----> lim (\<lambda>k. f(d k) (r n))" (is "_ ----> ?L1")
            using convergent_LIMSEQ_iff by auto
          have "convergent (\<lambda>k. f (d k) (r m))" using Bseq_mono_convergent rcont_inc rat_cnv
            unfolding rcont_inc_def mono_def by auto
          hence L2: "(\<lambda>k. f (d k) (r m)) ----> lim (\<lambda>k. f (d k) (r m))" (is "_ ----> ?L2")
            using convergent_LIMSEQ_iff by auto
          show "?L1 \<le> ?L2"
          proof -
            have "ereal ?L1 \<le> ereal ?L2"
              apply (rule ereal_lim_mono[of 0 "\<lambda>k. ereal (f (d k) (r n))" "\<lambda>k. ereal (f (d k) (r m))"])
              apply (force intro: le)
              by (auto intro: L1 L2)
            thus ?thesis by auto
          qed  
        qed
        have 4: "lim (\<lambda>k. f (d k) (r m)) < F x + e" using m by simp
        have 5: "\<And>k. f k (r n) \<le> f k x"  using n rcont_inc unfolding rcont_inc_def mono_def by auto
        have 6: "\<And>k. f k x \<le> f k (r m)" using m rcont_inc unfolding rcont_inc_def mono_def by auto
        have 7: "limsup (\<lambda>n. f (d n) x) < F x + e"
        proof -
          from 6 have "limsup (\<lambda>k. f (d k) x) \<le> limsup (\<lambda>k. f (d k) (r m))" using Limsup_mono
            by (smt ereal_less_eq(3) eventually_sequentially)
          also have "... = lim (\<lambda>k. f (d k) (r m))"
            apply (subst convergent_limsup_cl)
            using rat_cnv convergent_real_imp_convergent_ereal by auto
          also have "ereal (lim (\<lambda>k. f (d k) (r m))) < ereal (F x + e)" using 4 less_ereal.simps(1) by simp
          finally show ?thesis by simp
        qed
        have "\<bar>limsup (\<lambda>k. f (d k) x)\<bar> \<le> ereal M"
          apply (rule abs_bounds)
          apply (subst Limsup_const[symmetric, of sequentially "ereal M"], simp)
          apply (rule Limsup_mono[of "\<lambda>k. ereal (f (d k) x)" "\<lambda>k. ereal M" sequentially])
          apply eventually_elim
          apply (subst ereal_less_eq(3))
          apply (metis abs_ge_self order.trans unif_bdd)
          apply (subst ereal_uminus_le_reorder)
          apply (subst uminus_ereal.simps(1))
          apply (subst Limsup_const[symmetric, of sequentially "ereal (-M)"], simp)
          apply (rule Limsup_mono[of "\<lambda>k. ereal (-M)" "\<lambda>k. ereal (f (d k) x)" sequentially])
          apply eventually_elim
          apply (subst ereal_less_eq(3))
          by (metis abs_le_interval_iff unif_bdd)
        hence "\<bar>limsup (\<lambda>k. f (d k) x)\<bar> \<noteq> \<infinity>" by auto
        then obtain lsup where lsup: "limsup (\<lambda>n. f (d n) x) = ereal lsup" by auto
        have lsup_e: "lsup - F x < e" using 7
          by (smt lsup add_commute diff_less_eq less_ereal.simps(1))
        have 8: "F x - e < liminf (\<lambda>k. f (d k) x)"
        proof -
          from 5 have ineq: "liminf (\<lambda>k. f (d k) (r n)) \<le> liminf (\<lambda>k. f (d k) x)" using Liminf_mono
            by (smt ereal_less_eq(3) eventually_sequentially)
          have eq: "liminf (\<lambda>k. f (d k) (r n)) = lim (\<lambda>k. f (d k) (r n))"
            apply (subst convergent_liminf_cl)
            using rat_cnv convergent_real_imp_convergent_ereal by auto
          have "ereal (F x - e) < ereal (lim (\<lambda>k. f (d k) (r n)))" using 2 less_ereal.simps(1) by simp
          hence "ereal (F x - e) < liminf (\<lambda>k. f (d k) (r n))" using eq by simp
          thus ?thesis using ineq by simp
        qed
        (* Here I just copied the proof for limsup and replaced 'sup' by 'inf'; is there a better
           way exploiting duality of these operations? *)
        have "\<bar>liminf (\<lambda>k. f (d k) x)\<bar> \<le> ereal M"
          apply (rule abs_bounds)
          apply (subst Liminf_const[symmetric, of sequentially "ereal M"], simp)
          apply (rule Liminf_mono[of "\<lambda>k. ereal (f (d k) x)" "\<lambda>k. ereal M" sequentially])
          apply eventually_elim
          apply (subst ereal_less_eq(3))
          apply (metis abs_ge_self order.trans unif_bdd)
          apply (subst ereal_uminus_le_reorder)
          apply (subst uminus_ereal.simps(1))
          apply (subst Liminf_const[symmetric, of sequentially "ereal (-M)"], simp)
          apply (rule Liminf_mono[of "\<lambda>k. ereal (-M)" "\<lambda>k. ereal (f (d k) x)" sequentially])
          apply eventually_elim
          apply (subst ereal_less_eq(3))
          by (metis abs_le_interval_iff unif_bdd)
        hence "\<bar>liminf (\<lambda>k. f (d k) x)\<bar> \<noteq> \<infinity>" by auto
        then obtain linf where linf: "liminf (\<lambda>k. f (d k) x) = ereal linf" by auto
        have linf_e: "F x - linf < e" using 8
          by (smt linf add_commute diff_less_eq less_ereal.simps(1))
        have "ereal linf \<le> ereal lsup"
          apply (subst linf [symmetric], subst lsup [symmetric])
          by (auto intro: Liminf_le_Limsup)
        hence *: "linf \<le> lsup" by auto
        have "\<bar> lsup - F x \<bar> < e"
          apply (auto split: abs_split intro: lsup_e)
          using * linf_e by arith
        thus "\<bar>limsup (\<lambda>k. (f (d k) x)) - F x\<bar> < e"
          by (auto simp add: lsup)
        have "\<bar> linf - F x \<bar> < e"
          apply (auto split: abs_split)
          using * lsup_e apply arith
          by (auto intro: linf_e)
        thus "\<bar>F x - liminf (\<lambda>k. (f (d k) x))\<bar> < e"
          by (auto simp add: linf)
     qed
    hence *: "lim (\<lambda>k. ereal (f (d k) x)) = F x" "convergent (\<lambda>k. ereal (f (d k) x))"
      by (intro lim_close_limsup_liminf, auto)+
    have "(\<lambda>k. ereal (f (d k) x)) ----> F x"
      apply (subst *(1) [symmetric])
      apply (subst convergent_LIMSEQ_iff [symmetric])
      by (rule *)
    thus ?thesis by (subst lim_ereal [symmetric])
    qed
  qed
  ultimately show ?thesis using subseq by auto
qed

(** Weak convergence corollaries to Helly's theorem. **)

definition tight :: "(nat \<Rightarrow> real measure) \<Rightarrow> bool"
where "tight \<mu> \<equiv> (\<forall>n. real_distribution (\<mu> n)) \<and> (\<forall>(\<epsilon>::real)>0. \<exists>a b::real. a < b \<and> (\<forall>n. measure (\<mu> n) {a<..b} > 1 - \<epsilon>))"

(* Can strengthen to equivalence. *)
theorem tight_imp_convergent_subsubsequence:
  "\<And>\<mu>. tight \<mu> \<Longrightarrow> (\<forall>s. subseq s \<longrightarrow> (\<exists>r. \<exists>M.  subseq r \<and> real_distribution M \<and> weak_conv_m (\<mu> \<circ> s \<circ> r) M))"
proof auto
  fix \<mu> :: "nat \<Rightarrow> real measure" assume \<mu>: "tight \<mu>"
  fix s assume s: "subseq s"
  def f \<equiv> "\<lambda>k. cdf (\<mu> (s k))"
  {  fix k
     interpret \<mu>: real_distribution "\<mu> k" using \<mu> unfolding tight_def by auto
     interpret \<mu>_s: real_distribution "(\<mu> (s k))" using \<mu> unfolding tight_def by auto
     have "rcont_inc (f k)" "((f k) ---> 1) at_top" "((f k) ---> 0) at_bot" "\<forall>x. \<bar>f k x\<bar> \<le> 1"
      "\<And>A B. A \<subseteq> B \<Longrightarrow> B \<in> sets borel \<Longrightarrow> measure (\<mu> k) A \<le> measure (\<mu> k) B"
      "\<And>A B. A \<in> sets (\<mu> k) \<Longrightarrow> B \<in> sets (\<mu> k) \<Longrightarrow> A \<inter> B = {} \<Longrightarrow> measure (\<mu> k) (A \<union> B) =
        measure (\<mu> k) A + measure (\<mu> k) B" "\<And>A. measure (\<mu> k) A \<le> 1"
      unfolding rcont_inc_def f_def mono_def
      using \<mu>_s.cdf_nondecreasing \<mu>_s.cdf_is_right_cont \<mu>_s.cdf_lim_at_top_prob \<mu>_s.cdf_lim_at_bot
      apply auto
      apply (subst abs_le_interval_iff)
      using \<mu>_s.cdf_nonneg apply (metis \<mu>_s.cdf_bounded_prob dual_order.trans le_minus_one_simps(1))
      using \<mu>.finite_measure_mono apply force
      using \<mu>.finite_measure_Union by auto
  } note f_rcont_inc = this(1) and f_at_top = this(2) and f_at_bot = this(3) and f_bdd = this(4)
    and \<mu>_mono = this(5) and \<mu>_disj_un = this(6) and \<mu>_le_1 = this(7)
  from f_rcont_inc f_bdd Helly_selection obtain r
  where "subseq r \<and> (\<exists>F. rcont_inc F \<and> (\<forall>x. \<bar>F x\<bar> \<le> 1) \<and>
    (\<forall>x.  continuous (at x) F \<longrightarrow> (\<lambda>n. f (r n) x) ----> F x))" by blast
  then guess F by auto note F = this
  have F_nonneg: "\<And>x. F x \<ge> 0"
  proof -
    thm field_le_epsilon
    from f_rcont_inc f_at_bot have "\<And>n x. f n x \<ge> 0" unfolding rcont_inc_def mono_def tendsto_def
      apply (subst (asm) eventually_at_bot_linorder)
      apply (rule field_le_epsilon)
      apply (subst add_le_cancel_right[symmetric, where c = "-e"], simp)
      apply (subgoal_tac "\<And>k. \<exists>N. \<forall>n\<le>N. f k n \<in> {-e<..<e}")
      prefer 2 using open_real_greaterThanLessThan
      apply (metis greaterThanLessThan_iff neg_less_0_iff_less)
      by (metis greaterThanLessThan_iff less_le_trans linear not_less)
    hence cts_nonneg: "\<And>x. isCont F x \<Longrightarrow> F x \<ge> 0" using F by (metis LIMSEQ_le_const)
    (* Want general lemma to the effect that if a property holds at continuity points of a right
      continuous increasing function, then it holds everywhere. *)
    show "\<And>x. F x \<ge> 0" 
      apply (rule ccontr)
    proof (subst (asm) not_le)
      fix x assume x: "F x < 0"
      (* Should have made this a general lemma. *)
      have "uncountable {x - 1<..<x}" using open_interval_uncountable by simp
      hence "uncountable ({x - 1<..<x} - {x. \<not> isCont F x})"
        using uncountable_minus_countable mono_ctble_discont F unfolding rcont_inc_def by auto
      then obtain y where "y \<in> {x - 1<..<x} - {x. \<not> isCont F x}" unfolding uncountable_def by blast
      hence y: "y < x" "isCont F y"
        using DiffD1 greaterThanLessThan_iff by (simp_all add: linorder_not_less)
      with F have "F y \<le> F x" unfolding rcont_inc_def mono_def by auto
      hence "F y < 0" using x by auto
      thus False using y(2) cts_nonneg leD by auto
    qed
  qed
  have Fab: "\<forall>\<epsilon>>0. \<exists>a b. (\<forall>x\<ge>b. F x \<ge> 1 - \<epsilon>) \<and> (\<forall>x\<le>a. F x \<le> \<epsilon>)"
  proof auto
    fix \<epsilon>::real assume \<epsilon>: "\<epsilon> > 0"
    with \<mu> have "\<exists>a' b'. a' < b' \<and> (\<forall>k. measure (\<mu> k) {a'<..b'} > 1 - \<epsilon>)" unfolding tight_def by auto
    then obtain a' b' where a'b': "a' < b'" "\<And>k. measure (\<mu> k) {a'<..b'} > 1 - \<epsilon>" by auto
    have "uncountable {a' - 1<..<a'}" using open_interval_uncountable by simp
    hence "uncountable ({a' - 1<..<a'} - {x. \<not> isCont F x})"
      using uncountable_minus_countable mono_ctble_discont F unfolding rcont_inc_def by auto
    then obtain a where "a \<in> {a' - 1<..<a'} - {x. \<not> isCont F x}" unfolding uncountable_def by blast
    hence a: "a < a'" "isCont F a"
      using DiffD1 greaterThanLessThan_iff by (simp_all add: linorder_not_less)
    have "uncountable {b'<..<b' + 1}" using open_interval_uncountable by simp
    hence "uncountable ({b'<..<b' + 1} - {x. \<not> isCont F x})"
      using uncountable_minus_countable mono_ctble_discont F unfolding rcont_inc_def by auto
    then obtain b where "b \<in> ({b'<..<b' + 1} - {x. \<not> isCont F x})" unfolding uncountable_def by blast
    hence b: "b' < b" "isCont F b"
      using DiffD1 greaterThanLessThan_iff by (simp_all add: linorder_not_less)
    from a b a'b' have ab: "a < b" "\<And>k. measure (\<mu> k) {a<..b} > 1 - \<epsilon>"
    proof simp
      fix k
      have "{a'<..b'} \<subseteq> {a<..b}" using a b by auto
      hence "measure (\<mu> k) {a'<..b'} \<le> measure (\<mu> k) {a<..b}" using \<mu>_mono by auto
      thus "measure (\<mu> k) {a<..b} > 1 - \<epsilon>" using a'b'(2) by (metis less_eq_real_def less_trans)
    qed
    from b(2) F have "(\<lambda>k. f (r k) b) ----> F b" by auto
    hence subsubseq_lim: "(\<lambda>k. measure ((\<mu> \<circ> s \<circ> r) k) {..b}) ----> F b"
      unfolding f_def cdf_def o_def by auto
    have "\<And>k. measure ((\<mu> \<circ> s \<circ> r) k) {..b} =
      measure ((\<mu> \<circ> s \<circ> r) k) {..a} + measure ((\<mu> \<circ> s \<circ> r) k) {a<..b}"
      apply (subst ivl_disj_un(9)[symmetric,of a b], simp add: ab less_imp_le)
      apply auto apply (rule \<mu>_disj_un) apply auto
      apply (metis \<mu> atMost_borel real_distribution.events_eq_borel tight_def)
      by (metis \<mu> greaterThanAtMost_borel real_distribution.events_eq_borel tight_def)
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
      using F b(2) a(2) apply auto
      apply (rule eventually_sequentiallyI)
      by (rule \<mu>_mono) auto
    moreover have "1 - \<epsilon> \<le> lim (\<lambda>k. measure ((\<mu> \<circ> s \<circ> r) k) {a<..b})"
      apply (rule tendsto_le[of sequentially "\<lambda>k. measure ((\<mu> \<circ> s \<circ> r) k) {a<..b}"
        "lim (\<lambda>k. measure ((\<mu> \<circ> s \<circ> r) k) {a<..b})" "\<lambda>k. 1 - \<epsilon>" "1 - \<epsilon>"], auto)
      apply (subst convergent_LIMSEQ_iff[symmetric])
      apply (unfold convergent_def)
      apply (rule exI)
      using * unfolding o_def apply simp
      apply (rule tendsto_diff)
      using a b F apply auto
      apply (rule eventually_sequentiallyI)
      using ab(2) less_imp_le by metis
    ultimately have "1 - \<epsilon> \<le> F b" by (metis order.trans)
    hence "\<forall>x\<ge>b. F x \<ge> 1 - \<epsilon>" using F unfolding rcont_inc_def mono_def by (metis order.trans)
    thus "\<exists>b. \<forall>x\<ge>b. 1 - \<epsilon> \<le> F x" by auto
    from a(2) F have "(\<lambda>k. f (r k) a) ----> F a" by auto
    hence "(\<lambda>k. measure ((\<mu> \<circ> s \<circ> r) k) {..a}) ----> F a" unfolding f_def cdf_def o_def by auto
    hence "lim (\<lambda>k. measure ((\<mu> \<circ> s \<circ> r) k) {..a}) = F a" using limI by auto
    have 1: "\<And>n. measure (\<mu> n) {..a} < \<epsilon>"
    proof-
      fix n
      have "measure (\<mu> n) {..a} + measure (\<mu> n) {a<..b} \<le> 1"
        apply (subst \<mu>_disj_un[symmetric], auto)
        apply (metis \<mu> atMost_borel real_distribution.events_eq_borel tight_def)
        apply (metis \<mu> greaterThanAtMost_borel real_distribution.events_eq_borel tight_def)
        by (rule \<mu>_le_1)
      thus "measure (\<mu> n) {..a} < \<epsilon>" using ab(2)[of n] by simp
    qed
    have Fa: "F a \<le> \<epsilon>"
      apply (rule tendsto_le[of sequentially "\<lambda>k. \<epsilon>" \<epsilon> "\<lambda>k. f (r k) a" "F a"], auto)
      using F a apply auto
      apply (rule eventually_sequentiallyI)
      apply (unfold f_def cdf_def)
      using 1 less_imp_le by metis
    hence  "\<forall>x\<le>a. F x \<le> \<epsilon>" using F unfolding rcont_inc_def mono_def by (metis order.trans)
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
        using F_nonneg F abs_of_nonneg apply auto
        apply (subgoal_tac "\<bar>1 - F n\<bar> = 1 - F n")
        apply (erule ssubst)
        apply (erule_tac x=n in allE)
        apply simp
        by (metis abs_of_nonneg diff_le_iff(1))
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
  with F have "\<exists>M. real_distribution M \<and> cdf M = F" using cdf_to_real_distribution
    unfolding rcont_inc_def mono_def by auto
  then guess M .. note M = this
  with F have "weak_conv (f \<circ> r) F" unfolding weak_conv_def f_def using lim_subseq by auto
  hence "weak_conv_m (\<mu> \<circ> s \<circ> r) M" using M unfolding weak_conv_m_def f_def o_def by auto
  hence "\<exists>M. real_distribution M \<and> weak_conv_m (\<mu> \<circ> s \<circ> r) M" using M by auto
  thus "\<exists>r. subseq r \<and> (\<exists>M. real_distribution M \<and> weak_conv_m (\<mu> \<circ> s \<circ> r) M)" using F by auto
qed

corollary tight_subseq_weak_converge:
  fixes \<mu> :: "nat \<Rightarrow> real measure" and M :: "real measure"
  assumes "\<And>n. real_distribution (\<mu> n)" "real_distribution M" and tight: "tight \<mu>" and
    subseq: "\<And>s \<nu>. subseq s \<Longrightarrow> real_distribution \<nu> \<Longrightarrow> weak_conv_m (\<mu> \<circ> s) \<nu> \<Longrightarrow> weak_conv_m (\<mu> \<circ> s) M"
  shows "weak_conv_m \<mu> M"
proof (rule ccontr)
  from tight tight_imp_convergent_subsubsequence
  have subsubseq: "\<forall>s. subseq s \<longrightarrow> (\<exists>r M. subseq r \<and> real_distribution M \<and> weak_conv_m (\<mu> \<circ> s \<circ> r) M)"
    by simp
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