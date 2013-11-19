theory Helly_Selection
imports Diagonal_Subsequence Conditionally_Complete_Lattices Library_Misc

begin

(* This should have been in the library, like convergent_limsup_cl. *)
lemma convergent_liminf_cl:
  fixes X :: "nat \<Rightarrow> 'a::{complete_linorder,linorder_topology}"
  shows "convergent X \<Longrightarrow> liminf X = lim X"
  by (auto simp: convergent_def limI lim_imp_Liminf)

primrec halfseq :: "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  "halfseq l a0 0 = a0"
| "halfseq l a0 (Suc n) = (halfseq l a0 n + l) / 2"

lemma halfseq_converges: "halfseq l a0 ----> l"
proof -
  let ?a = "halfseq l a0"
  {
    fix n
    have "dist (?a n) l = dist a0 l / 2^n"
      by (induct n, auto simp add: dist_real_def field_simps)
  } note dist_a = this
  show ?thesis
  proof (rule metric_LIMSEQ_I)
    fix r :: real
    assume [simp]: "r > 0"
    from reals_Archimedean2 [of "dist a0 l / r"] guess n .. 
    with `r > 0` have 2: "dist a0 l < r * n" by (simp add: field_simps)
    have "(dist a0 l) / 2^n < r"
      apply (auto simp add: field_simps)
      apply (rule order_less_trans, rule 2)
      by (rule mult_strict_left_mono, simp_all)
    hence "\<forall>m\<ge>n. dist (halfseq l a0 m) l < r"
      apply (auto simp add: dist_a)
      apply (rule order_le_less_trans)
      prefer 2 apply assumption
      by (auto simp add: field_simps intro!: mult_left_mono)
    thus "\<exists>n. \<forall>m\<ge>n. dist (halfseq l a0 m) l < r" ..
  qed
qed

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

definition rcont_inc :: "(real \<Rightarrow> real) \<Rightarrow> bool"
  where "rcont_inc f \<equiv> (\<forall>x. continuous (at_right x) f) \<and> mono f"

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

lemma lim_close_limsup_liminf:
  fixes a :: "nat \<Rightarrow> ereal" and L :: real
  assumes "\<forall>(e::real)>0. \<bar>limsup a - L\<bar> < e \<and> \<bar>L - liminf a\<bar> < e"
  shows "convergent a" and "lim a = L"
proof -
  have lsup: "limsup a = L" using assms
    by (metis abs_ereal.simps(1) dual_order.irrefl ereal.distinct(1) ereal_less(2) ereal_less(3) ereal_less_minus
        ereal_minus_less ereal_real' infinity_ereal_def linorder_cases monoid_add_class.add.left_neutral zero_ereal_def
        zero_less_abs_iff)
  also have "L = liminf a"
  proof -
    have "\<And>n::nat. n > 0 \<Longrightarrow> \<bar>L - liminf a\<bar> < inverse n" using assms
      by (metis ereal_less(2) inverse_positive_iff_positive real_of_nat_gt_zero_cancel_iff)
    hence 1: "\<bar>L - liminf a\<bar> = 0"
      by (metis abs_ereal.simps(1) abs_real_of_ereal abs_zero assms ereal_real' less_ereal.simps(4) less_irrefl zero_ereal_def
          zero_less_abs_iff zero_less_real_of_ereal)
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

lemma convergent_real_imp_convergent_ereal:
  assumes "convergent a"
  shows "convergent (\<lambda>n. ereal (a n))" and "lim (\<lambda>n. ereal (a n)) = ereal (lim a)"
proof -
  from assms obtain L where L: "a ----> L" unfolding convergent_def ..
  hence lim: "(\<lambda>n. ereal (a n)) ----> ereal L" using lim_ereal by auto
  thus "convergent (\<lambda>n. ereal (a n))" unfolding convergent_def ..
  thus "lim (\<lambda>n. ereal (a n)) = ereal (lim a)" using lim L limI by metis
qed

(*
lemma limsup_not_infty: 
  fixes f :: "nat \<Rightarrow> ereal"
  assumes "\<And>x. f x \<le> ereal M"
*)

lemma ereal_not_infty:
  fixes x :: ereal and B :: real
  assumes "x \<le> ereal B"
  shows "x \<noteq> \<infinity>"
by (metis PInfty_neq_ereal(1) assms ereal_infty_less_eq(1))

lemma blah: "x \<le> y \<Longrightarrow> -x \<le> y \<Longrightarrow> abs (x :: ereal) \<le> y"
by (metis abs_ereal_ge0 abs_ereal_uminus ereal_0_le_uminus_iff linear)
thm ereal_infty_less_eq
thm PInfty_neq_ereal

theorem Helley_selection:
  fixes f :: "nat \<Rightarrow> real \<Rightarrow> real"
  assumes rcont_inc: "\<And>n. rcont_inc (f n)"
  and unif_bdd: "\<forall>n x. \<bar>f n x\<bar> \<le> M"
  shows "\<exists>s. subseq s \<and> (\<exists>F. rcont_inc F \<and> (\<forall>n x. \<bar>F x\<bar> \<le> M) \<and>
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
  def d == "nat.diagseq"
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
  def F == "\<lambda>x. Inf {lim (\<lambda>k. f (d k) (r n)) |n. x < r n}"
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
    apply (unfold continuous_def)
    apply (unfold tendsto_def, auto)
    apply (subst eventually_at_right)
    proof -
      fix x::real fix S::"real set" assume openS: "open S"
(*      assume ntlim_inS: "(Inf {lim (\<lambda>k. f (d k) (r n)) |n. netlimit (at_right x) < r n}) \<in> S" *)
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
  moreover have bdd: "\<forall>n x. \<bar>F x\<bar> \<le> M"
  proof auto
    fix x
    have "F x \<in> {-M..M}"
      unfolding F_def apply (rule real_atLeastAtMost_subset_contains_Inf)
      apply (rule nonempty)
      apply (rule bdd_below)
      apply (simp add: M_nonneg)
      apply (rule limset_bdd)
      done
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
          apply (rule blah)
          sorry
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
        hence "\<bar>liminf (\<lambda>k. f (d k) x)\<bar> \<noteq> \<infinity>" sorry
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
  thus ?thesis
    by (subst lim_ereal [symmetric])
  qed
  qed
  show "\<bar> F x \<bar> \<le> M"
  proof -
    have "F x \<in> {-M..M}"
      unfolding F_def apply (rule real_atLeastAtMost_subset_contains_Inf)
      apply (rule nonempty)
      apply (rule bdd_below)
      apply (simp add: M_nonneg)
      apply (rule limset_bdd)
      done    
    thus ?thesis by auto
qed
qed
  show "\<exists>s. subseq s \<and>
        (\<exists>F. rcont_inc F \<and>
             (\<forall>n x. \<bar>F x\<bar> \<le> M) \<and>
             (\<forall>x. isCont F x \<longrightarrow>
                  (\<lambda>n. f (s n) x) ----> F x))"
    apply (rule_tac x = d in exI)
    apply auto
    unfolding d_def apply (rule nat.subseq_diagseq)
    apply (rule_tac x = F in exI)
    apply auto
    prefer 2
    sorry
qed



(*



Backup copy 



*)





theorem Helley_selection:
  fixes f :: "nat \<Rightarrow> real \<Rightarrow> real"
  assumes rcont_inc: "\<And>n. rcont_inc (f n)"
  and unif_bdd: "\<forall>n x. \<bar>f n x\<bar> \<le> M"
  shows "\<exists>s. subseq s \<and> (\<exists>F. rcont_inc F \<and> (\<forall>n x. \<bar>F x\<bar> \<le> M) \<and>
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
  let ?d = "nat.diagseq"
  have rat_cnv: "\<And>n. ?P n ?d"
  proof -
    fix n::nat show "?P n ?d"
    proof -
      have Pn_seqseq: "?P n (nat.seqseq (Suc n))"
        by (rule nat.seqseq_holds)
      have 1: "(\<lambda>k. f ((nat.seqseq (Suc n) \<circ> (\<lambda>k. nat.fold_reduce (Suc n) k
        (Suc n + k))) k) (r n)) = (\<lambda>k. f (nat.seqseq (Suc n) k) (r n)) \<circ>
        (\<lambda>k. nat.fold_reduce (Suc n) k (Suc n + k))"
        by auto
      have 2: "?P n (?d \<circ> (op + (Suc n)))"
        apply (subst nat.diagseq_seqseq)
        apply (subst 1)
        apply (rule convergent_subseq_convergent[of "\<lambda>k. f (nat.seqseq (Suc n) k) (r n)"
          "\<lambda>k. nat.fold_reduce (Suc n) k (Suc n + k)"])
        by (rule Pn_seqseq) (rule nat.subseq_diagonal_rest)
      then obtain L where 3: "(\<lambda>k. f ((?d \<circ> (op + (Suc n))) k) (r n)) ----> L"
        using convergentD by auto
      have 4: "(\<lambda>k. f (?d (k + (Suc n))) (r n)) =
      (\<lambda>k. f ((?d \<circ> (op + (Suc n))) k) (r n))"
        by (auto simp: add_commute)
      have "(\<lambda>k. f (?d k) (r n)) ----> L" 
        apply (rule LIMSEQ_offset[of _ "Suc n"])
        by (subst 4) (rule 3)
      thus ?thesis unfolding convergent_def by auto
    qed
  qed
  have M_nonneg: "0 \<le> M" using unif_bdd by (metis abs_minus_le_zero less_le less_trans neg_le_0_iff_le)
  have lim_bdd: "\<And>n. lim (\<lambda>k. f (?d k) (r n)) \<in> {-M..M}"
  proof -
    fix n::nat
    have "closed {-M..M}" using closed_real_atLeastAtMost by auto
    hence "(\<forall>i. (\<lambda>k. f (?d k) (r n)) i \<in> {-M..M}) \<and> (\<lambda>k. f (?d k) (r n)) ----> lim (\<lambda>k. f (?d k) (r n))
      \<longrightarrow> lim (\<lambda>k. f (?d k) (r n)) \<in> {-M..M}"
      apply (subst (asm) closed_sequential_limits)
      by (drule_tac x = "\<lambda>k. f (?d k) (r n)" in spec) blast
    moreover have "\<forall>i. (\<lambda>k. f (?d k) (r n)) i \<in> {-M..M}" using unif_bdd abs_le_interval_iff by auto
    moreover have "(\<lambda>k. f (?d k) (r n)) ----> lim (\<lambda>k. f (?d k) (r n))"
      using rat_cnv convergent_LIMSEQ_iff by auto
    ultimately show "lim (\<lambda>k. f (?d k) (r n)) \<in> {-M..M}" by auto
  qed
  hence limset_bdd: "\<And>x. {lim (\<lambda>k. f (?d k) (r n)) |n. x < r n} \<subseteq> {-M..M}" by auto
  hence bdd_below: "\<And>x. bdd_below {lim (\<lambda>k. f (?d k) (r n)) |n. x < r n}"
    (* Why does auto not get this? (auto intro: subset_bdd_below bdd_below_at_LeastAtMost limset_bdd) *)
  proof -
    fix x show " bdd_below {lim (\<lambda>k. f (?d k) (r n)) |n. x < r n}"
    by (metis (mono_tags) bdd_below_Icc bdd_below_mono limset_bdd) 
  qed
  have nonempty: "\<And>x::real. {lim (\<lambda>k. f (?d k) (r n)) |n. x < r n} \<noteq> {}"
  proof -
    fix x :: real
    obtain q where q: "q \<in> \<rat> \<and> x < q" by (metis (full_types) Rats_dense_in_real linordered_field_no_ub)
    let ?n = "the_inv_into UNIV r q"
    let ?y = "lim (\<lambda>k. f (?d k) (r ?n))"
    have "x < r ?n" using f_the_inv_into_f bij q by (metis bij_betw_def)
    then have "?y \<in> {lim (\<lambda>k. f (?d k) (r n)) |n. x < r n}" by auto
    thus "{lim (\<lambda>k. f (?d k) (r n)) |n. x < r n} \<noteq> {}" by auto
  qed
  { fix x :: real
    from rat_unbounded [of "x + 1"] guess q ..
    with bij have "x < r (inv r q)" apply (subst f_inv_f_surj_on [of r])
      unfolding bij_betw_def by (erule conjE, assumption, auto)
    hence "\<exists>n. x < r n" ..
  } note r_unbdd = this
  let ?F = "\<lambda>x. Inf {lim (\<lambda>k. f (?d k) (r n)) |n. x < r n}"
  have "\<And>x. ?F x \<in> {-M..M}"
    apply (rule real_closed_subset_contains_Inf)
    using limset_bdd apply auto
    prefer 2 apply (rule bdd_below_mono)
    apply (rule bdd_below_Ici [of "-M"])
    apply (rule subset_trans, assumption, force)
    by (rule r_unbdd)
  have mono: "mono ?F"
  proof (unfold mono_def, auto)
    fix x y::real assume le: "x \<le> y"
    hence subset: "{lim (\<lambda>k. f (?d k) (r n)) |n. y < r n} \<subseteq> {lim (\<lambda>k. f (?d k) (r n)) |n. x < r n}"
      by auto
    show "?F x \<le> ?F y"
      apply (rule cInf_superset_mono[of "{lim (\<lambda>k. f (?d k) (r n)) |n. y < r n}"
        "{lim (\<lambda>k. f (?d k) (r n)) |n. x < r n}"])
      apply (rule nonempty)
      apply (rule bdd_below)
      by (rule subset)
  qed
  moreover have "\<And>x. continuous (at_right x) ?F"
    apply (unfold continuous_def)
    apply (unfold tendsto_def, auto)
    apply (subst eventually_at_right)
    proof -
      fix x::real fix S::"real set" assume openS: "open S"
      assume ntlim_inS: "(Inf {lim (\<lambda>k. f (?d k) (r n)) |n. netlimit (at_right x) < r n}) \<in> S"
      have "netlimit (at_right x) = x" by (auto intro: netlimit_within)
      hence "?F x \<in> S" using ntlim_inS by simp
      then obtain e where e_pos: "e > 0" and e: "ball (?F x) e \<subseteq> S" using openE openS by auto
      have "\<exists>y \<in> {lim (\<lambda>k. f (?d k) (r n)) |n. x < r n}. y < ?F x + e"
      proof -
        from e_pos have "?F x < ?F x + e / 2" by simp
        from nonempty bdd_below this real_Inf_greatest'[of "{lim (\<lambda>k. f (?d k) (r n)) |n. x < r n}" "?F x + e/2"]
        have "\<exists>y\<in>{lim (\<lambda>k. f (?d k) (r n)) |n. x < r n}. y \<le> ?F x + e / 2" by auto
        then guess y .. note y = this
        hence "y < ?F x + e" using e_pos by auto
        moreover have "y \<in> {lim (\<lambda>k. f (?d k) (r n)) |n. x < r n}" using y by auto
        ultimately show ?thesis ..
      qed
      then guess y .. note y = this
      then obtain n where n: "y = lim (\<lambda>k. f (?d k) (r n)) \<and> x < r n" by auto
      have "\<forall>z. x < z \<and> z < r n \<longrightarrow> ?F z \<in> S"
      proof auto
        fix z assume gr: "x < z" and ls: "z < r n"
        have 1: "?F x \<le> ?F z" using gr mono unfolding mono_def by auto
        have "?F z \<le> y"
        proof -
          have "?F z \<le> lim (\<lambda>k. f (?d k) (r n))"
            apply (rule cInf_lower)
            using bdd_below ls by auto
          thus ?thesis using n by simp
        qed
        hence "?F z < ?F x + e" using y by auto
        hence "?F z \<in> ball (?F x) e" unfolding ball_def dist_real_def using 1 by auto
        thus "?F z \<in> S" using e by auto
      qed
      thus "\<exists>b>x. \<forall>z. x < z \<and> z < b \<longrightarrow> ?F z \<in> S" using n by auto
    qed
  ultimately have rcont_inc_lim: "rcont_inc ?F" unfolding rcont_inc_def by auto
  moreover have bdd: "\<forall>n x. \<bar>?F x\<bar> \<le> M"
  proof auto
    fix x
    have "?F x \<in> {-M..M}"
      apply (rule real_atLeastAtMost_subset_contains_Inf)
      apply (rule nonempty)
      apply (rule bdd_below)
      apply (simp add: M_nonneg)
      apply (rule limset_bdd)
      done
  moreover have lim: "\<forall>x.  continuous (at x) ?F \<longrightarrow> (\<lambda>n. f (?d n) x) ----> ?F x"
  proof auto
    fix x::real assume cts: "continuous (at x) ?F"
    show "(\<lambda>n. f (?d n) x) ----> ?F x"
    proof -
      have "\<forall>(e::real)>0. 
        \<bar>limsup (\<lambda>n. ereal (f (?d n) x)) - ereal (?F x)\<bar> < e \<and> \<bar>ereal (?F x) - liminf (\<lambda>n. ereal (f (?d n) x))\<bar> < e"
      proof auto
        fix e::real assume e: "0 < e"
        have "?F -- x --> ?F x" using cts continuous_at by auto
          hence "\<exists>d>0. \<forall>y. y \<noteq> x \<and> norm (y - x) < d \<longrightarrow> norm (?F y - ?F x) < e"
            by (rule LIM_D) (rule e) (* Why did auto not work here? *)
        then obtain d where d: "d > 0" and cts': "\<forall>y. y \<noteq> x \<and> norm (y - x) < d \<longrightarrow> norm (?F y - ?F x) < e"
          by auto
        have "\<exists>y<x. norm (y - x) < d"
        proof -
          have "\<bar>(x - d/2) - x\<bar> < d"
            by (metis abs_divide abs_minus_commute abs_numeral abs_of_pos add_diff_cancel comm_monoid_add_class.add.left_neutral d diff_add_cancel
                linordered_field_class.sign_simps(16) real_gt_half_sum)
          moreover have "x - d/2 < x" using d by simp
          ultimately show ?thesis using exI[of _ "x - d/2"] by auto
        qed
        then guess y .. note y = this
        then have "norm (?F y - ?F x) < e" using cts' by auto
        hence 1: "?F x - e < ?F y" using y mono by auto
        have "\<exists>n. y < r n \<and> r n < x"
        proof -
          obtain q where q: "q \<in> \<rat> \<and> y < q \<and> q < x" using y Rats_dense_in_real by auto
          let ?n = "the_inv_into UNIV r q"
          have "y < r ?n \<and> r ?n < x" using q bij f_the_inv_into_f unfolding bij_betw_def by metis
          thus ?thesis by auto
        qed
        then guess n.. note n = this
        have "?F y \<le> lim (\<lambda>k. f (?d k) (r n))"
          apply (rule cInf_lower)
          using bdd_below n by auto
        hence 2: "?F x - e < lim (\<lambda>k. f (?d k) (r n))" using 1 by auto
        have "\<exists>m. x < r m \<and> lim (\<lambda>k. f (?d k) (r m)) < ?F x + e"
        proof - (* Contains duplication from proof of right-continuity--fix. *)
          have "\<exists>z \<in> {lim (\<lambda>k. f (?d k) (r n)) |n. x < r n}. z < ?F x + e"
          proof -
            from e have "?F x < ?F x + e / 2" by simp
            from nonempty bdd_below this real_Inf_greatest'[of "{lim (\<lambda>k. f (?d k) (r n)) |n. x < r n}" "?F x + e/2"]
            have z: "\<exists>z\<in>{lim (\<lambda>k. f (?d k) (r n)) |n. x < r n}. z \<le> ?F x + e / 2" by auto
            then guess z .. note 1 = this
            hence "z < ?F x + e" using e by auto
            moreover have "z \<in> {lim (\<lambda>k. f (?d k) (r n)) |n. x < r n}" using 1 by auto
            ultimately show ?thesis ..
          qed
          then guess z .. note z = this
          then obtain m where m: "z = lim (\<lambda>k. f (?d k) (r m)) \<and> x < r m" by auto
          thus ?thesis using z by auto
        qed
        then guess m .. note m = this
        from n m have nm: "r n < r m" by auto
        have 3: "lim (\<lambda>k. f (?d k) (r n)) \<le> lim (\<lambda>k. f (?d k) (r m))"
        proof -
          have le: "\<And>k. f (?d k) (r n) \<le> f (?d k) (r m)" using y assms nm unfolding rcont_inc_def mono_def by auto
          have "convergent (\<lambda>k. f (?d k) (r n))" using Bseq_mono_convergent rcont_inc rat_cnv
            unfolding rcont_inc_def mono_def by auto
          hence L1: "(\<lambda>k. f (?d k) (r n)) ----> lim (\<lambda>k. f(?d k) (r n))" (is "_ ----> ?L1")
            using convergent_LIMSEQ_iff by auto
          have "convergent (\<lambda>k. f (?d k) (r m))" using Bseq_mono_convergent rcont_inc rat_cnv
            unfolding rcont_inc_def mono_def by auto
          hence L2: "(\<lambda>k. f (?d k) (r m)) ----> lim (\<lambda>k. f (?d k) (r m))" (is "_ ----> ?L2")
            using convergent_LIMSEQ_iff by auto
          show "?L1 \<le> ?L2"
          proof -
            have "ereal ?L1 \<le> ereal ?L2"
              apply (rule ereal_lim_mono[of 0 "\<lambda>k. ereal (f (?d k) (r n))" "\<lambda>k. ereal (f (?d k) (r m))"])
              apply (force intro: le)
              by (auto intro: L1 L2)
            thus ?thesis by auto
          qed  
        qed
        have 4: "lim (\<lambda>k. f (?d k) (r m)) < ?F x + e" using m by simp
        have 5: "\<And>k. f k (r n) \<le> f k x"  using n rcont_inc unfolding rcont_inc_def mono_def by auto
        have 6: "\<And>k. f k x \<le> f k (r m)" using m rcont_inc unfolding rcont_inc_def mono_def by auto
        have 7: "limsup (\<lambda>n. f (?d n) x) < ?F x + e"
        proof -
          from 6 have "limsup (\<lambda>k. f (?d k) x) \<le> limsup (\<lambda>k. f (?d k) (r m))" using Limsup_mono
            by (smt ereal_less_eq(3) eventually_sequentially)
          also have "... = lim (\<lambda>k. f (?d k) (r m))"
            apply (subst convergent_limsup_cl)
            using rat_cnv convergent_real_imp_convergent_ereal by auto
          also have "ereal (lim (\<lambda>k. f (?d k) (r m))) < ereal (?F x + e)" using 4 less_ereal.simps(1) by simp
          finally show ?thesis by simp
        qed
        hence "\<bar>limsup (\<lambda>k. f (?d k) x)\<bar> \<noteq> \<infinity>" using unif_bdd sorry
        then obtain lsup where lsup: "limsup (\<lambda>n. f (?d n) x) = ereal lsup" by auto
        have lsup_e: "lsup - ?F x < e" using 7
          by (smt lsup add_commute diff_less_eq less_ereal.simps(1))
        have 8: "?F x - e < liminf (\<lambda>k. f (?d k) x)"
        proof -
          from 5 have ineq: "liminf (\<lambda>k. f (?d k) (r n)) \<le> liminf (\<lambda>k. f (?d k) x)" using Liminf_mono
            by (smt ereal_less_eq(3) eventually_sequentially)
          have eq: "liminf (\<lambda>k. f (?d k) (r n)) = lim (\<lambda>k. f (?d k) (r n))"
            apply (subst convergent_liminf_cl)
            using rat_cnv convergent_real_imp_convergent_ereal by auto
          have "ereal (?F x - e) < ereal (lim (\<lambda>k. f (?d k) (r n)))" using 2 less_ereal.simps(1) by simp
          hence "ereal (?F x - e) < liminf (\<lambda>k. f (?d k) (r n))" using eq by simp
          thus ?thesis using ineq by simp
        qed
        hence "\<bar>liminf (\<lambda>k. f (?d k) x)\<bar> \<noteq> \<infinity>" sorry
        then obtain linf where linf: "liminf (\<lambda>k. f (?d k) x) = ereal linf" by auto
        have linf_e: "?F x - linf < e" using 8
          by (smt linf add_commute diff_less_eq less_ereal.simps(1))
        have "ereal linf \<le> ereal lsup"
          apply (subst linf [symmetric], subst lsup [symmetric])
          by (auto intro: Liminf_le_Limsup)
        hence *: "linf \<le> lsup" by auto
        have "\<bar> lsup - ?F x \<bar> < e"
          apply (auto split: abs_split intro: lsup_e)
          using * linf_e by arith
        thus "\<bar>limsup (\<lambda>k. (f (?d k) x)) - ?F x\<bar> < e"
          by (auto simp add: lsup)
        have "\<bar> linf - ?F x \<bar> < e"
          apply (auto split: abs_split)
          using * lsup_e apply arith
          by (auto intro: linf_e)
        thus "\<bar>?F x - liminf (\<lambda>k. (f (?d k) x))\<bar> < e"
          by (auto simp add: linf)
   qed
  hence *: "lim (\<lambda>k. ereal (f (?d k) x)) = ?F x" "convergent (\<lambda>k. ereal (f (?d k) x))"
    by (intro lim_close_limsup_liminf, auto)+
  have "(\<lambda>k. ereal (f (?d k) x)) ----> ?F x"
    apply (subst *(1) [symmetric])
    apply (subst convergent_LIMSEQ_iff [symmetric])
    by (rule *)
  thus ?thesis
    by (auto simp add: lim_ereal [symmetric])
  qed
  qed
  show "\<bar> ?F x \<bar> \<le> M"
  proof -
    have "?F x \<in> {-M..M}"
      apply (rule real_atLeastAtMost_subset_contains_Inf)
      apply (rule nonempty)
      apply (rule bdd_below)
      apply (simp add: M_nonneg)
      apply (rule limset_bdd)
      done    
    thus ?thesis by auto
qed
qed
  show "\<exists>s. subseq s \<and>
        (\<exists>F. rcont_inc F \<and>
             (\<forall>n x. \<bar>F x\<bar> \<le> M) \<and>
             (\<forall>x. isCont F x \<longrightarrow>
                  (\<lambda>n. f (s n) x) ----> F x))"
    apply (rule_tac x = ?d in exI)
    apply auto
    apply (rule nat.subseq_diagseq)
    apply (rule_tac x = ?F in exI)
    apply auto
    prefer 2
    sorry
qed



end