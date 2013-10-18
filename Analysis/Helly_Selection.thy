theory Helly_Selection
imports Diagonal_Subsequence Conditionally_Complete_Lattice Library_Misc

begin

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
using assms by (intro Inf_greatest, auto)

lemma bdd_below_closure:
  fixes A :: "real set"
  assumes "bdd_below A"
  shows "bdd_below (closure A)"
proof -
  from assms obtain m where "\<And>x. x \<in> A \<Longrightarrow> m \<le> x" unfolding bdd_below_def by auto
  hence "A \<subseteq> {m..}" by auto
  find_theorems "closed _" "{_..}"
  hence "closure A \<subseteq> {m..}" using closed_real_atLeast closure_minimal by auto
  thus ?thesis unfolding bdd_below_def by auto
qed

lemma real_closure_contains_Inf:
  fixes A :: "real set"
  assumes  nonempty: "A \<noteq> {}" and bdd: "bdd_below A"
  shows "Inf A \<in> closure A"
proof -
  from nonempty obtain a0 where a0: "a0 \<in> A" by auto
  note 1 = tendsto_const [of "Inf A" sequentially]
  note 2 = halfseq_converges [of "Inf A" a0]
  let ?a = "halfseq (Inf A) a0"
  have a_above_Inf: "\<forall>i. ?a i \<ge> Inf A"
  proof
    fix i :: nat show "?a i \<ge> Inf A"
      by (induct i, auto intro: assms a0 Inf_lower)
  qed
  have 3: "\<forall>i. \<exists>b \<le> ?a i. b \<ge> Inf A \<and> b \<in> A"
  proof
    fix i :: nat show "\<exists>b \<le> ?a i. b \<ge> Inf A \<and> b \<in> A"
    proof (cases "Inf A \<in> A")
      assume "Inf A \<in> A" thus "\<exists>b \<le> ?a i. b \<ge> Inf A \<and> b \<in> A" using a_above_Inf by auto
      next assume notin: "Inf A \<notin> A"
      hence neq: "a0 \<noteq> Inf A" using a0 by auto
      have a_gr_Inf: "\<And>k. ?a k > Inf A"
      proof -
        fix k :: nat show "?a k > Inf A"
          by (induct k, auto intro: a0 bdd Inf_lower) (metis (full_types) a0 bdd Inf_lower le_neq_trans neq)
      qed
      thus "\<exists>b \<le> ?a i. b \<ge> Inf A \<and> b \<in> A" using real_Inf_greatest' Inf_lower assms by metis
    qed
  qed
  have dist_a: "\<And>n. dist (?a n) (Inf A) = dist a0 (Inf A) / 2^n"
  proof -
    fix n :: nat show "dist (?a n) (Inf A) = dist a0 (Inf A) / 2^n"
    apply (induct n, auto)
    apply (subst divide_inverse)
    apply (subst mult_commute)
    apply (subst real_scaleR_def[symmetric])
    apply (subst midpoint_def[symmetric])
    by (simp add: dist_midpoint)
  qed
  have lbd_a: "\<And>n. Inf A \<le> ?a n"
  proof -
    fix n show "Inf A \<le> ?a n" by (induct n, auto intro: assms Inf_lower a0)
  qed
  have "?a ----> Inf A" using halfseq_converges by auto
  have "\<forall>n. \<exists>x. x \<le> ?a n \<and> x \<in> A"
  proof
    fix n show "\<exists>x. x \<le> ?a n \<and> x \<in> A"
    proof (cases "?a n = Inf A")
      assume an: "?a n = Inf A"
      hence "dist a0 (Inf A) = 0" using dist_a dist_self
        by (metis divide_le_0_iff less_le not_less power_eq_0_iff zero_le_divide_iff zero_neq_numeral)
      hence "a0 = Inf A" by auto
      hence "a0 \<le> ?a n \<and> a0 \<in> A" using a0 an by auto
      thus ?thesis by auto
    next
      assume "?a n \<noteq> Inf A" hence an: "?a n > Inf A" using a_above_Inf le_neq_trans by metis
      show ?thesis
      proof (rule ccontr, auto)
        assume "\<forall>x\<le>?a n. x \<notin> A"
        hence "\<And>x. x \<in> A \<Longrightarrow> ?a n \<le> x" using 3 by auto
        then have "?a n \<le> Inf A" using Inf_greatest assms by auto
        thus False using an by auto
      qed
    qed
  qed
  from choice[OF this] guess b .. note b = this
  hence "b ----> Inf A" using real_tendsto_sandwich
    by (smt "1" bdd conditionally_complete_lattice_class.Inf_lower eventually_sequentially halfseq_converges)
  thus ?thesis using closure_sequential b by auto
qed

lemma real_closed_subset_contains_Inf:
  fixes A C :: "real set"
  assumes cl: "closed C" and A: "A \<subseteq> C"
  and nonempty: "A \<noteq> {}" and bdd_below: "bdd_below A"
  shows "Inf A \<in> C"
proof -
  find_theorems (68) closure
  have "closure A \<subseteq> C" using closure_minimal assms by auto
  thus ?thesis
    apply (elim subsetD)
    apply (rule real_closure_contains_Inf)
    using assms by auto
qed

definition rcont_inc :: "(real \<Rightarrow> real) \<Rightarrow> bool"
  where "rcont_inc f \<equiv> (\<forall>x. continuous (at_right x) f) \<and> mono f"

theorem bdd_below_atLeast: "bdd_below {a..}"
  unfolding bdd_below_def by auto

theorem rat_unbounded: "\<exists> q \<in> \<rat>. q >= (x :: real)"
  apply (rule_tac x = "of_nat (natceiling x)" in bexI, auto)
by (metis real_natceiling_ge real_of_nat_def)

lemma f_inv_f_surj_on: "f ` A = B \<Longrightarrow> x \<in> B \<Longrightarrow> f (inv f x) = x"
  apply auto
  unfolding inv_def by (rule someI_ex, auto)

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
      using bounded_imp_convergent_subsequence[of "{-M..M}"] by auto
    thus "\<exists>s'. subseq s' \<and> (\<exists>l. (\<lambda>k. f (s (s' k)) (r n)) ----> l)" unfolding o_def by auto
  qed
  let ?d = "nat.diagseq"
  have rat_cnv: "\<And>n. ?P n ?d"
  proof -
    fix n::nat show "?P n ?d"
    proof -
      have Pn_seqseq: "?P n (nat.seqseq (Suc n))"
        by (subst nat.seqseq_reducer) (rule nat.reducer_reduces)
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
  (* Is this needed? *)
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
    using bdd_below_atLeast subset_bdd_below sorry
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
  let ?F = "\<lambda>x. \<Sqinter>{lim (\<lambda>k. f (?d k) (r n)) |n. x < r n}"
  have "\<And>x. ?F x \<in> {-M..M}"
    apply (rule real_closed_subset_contains_Inf)
    using limset_bdd apply auto
    prefer 2 apply (rule subset_bdd_below)
    apply (rule bdd_below_atLeast [of "-M"])
    apply (rule subset_trans, assumption, force)
    by (rule r_unbdd)
  have mono: "mono ?F"
  proof (unfold mono_def, auto)
    fix x y::real assume le: "x \<le> y"
    hence subset: "{lim (\<lambda>k. f (?d k) (r n)) |n. y < r n} \<subseteq> {lim (\<lambda>k. f (?d k) (r n)) |n. x < r n}"
      by auto
    show "?F x \<le> ?F y"
      apply (rule bdd_nonempty_Inf_superset_mono[of "{lim (\<lambda>k. f (?d k) (r n)) |n. y < r n}"
        "{lim (\<lambda>k. f (?d k) (r n)) |n. x < r n}"])
      apply (rule nonempty)
      apply (rule bdd_below)
      by (rule subset)
  qed
  moreover have "\<And>x. continuous (at_right x) ?F"
    (*apply (unfold continuous_def)
    apply (unfold tendsto_def, auto)
    apply (subst eventually_within)
    proof -
      fix x::real fix S::"real set" assume opnS: "open S"
      assume ntlim_inS: "(Inf {lim (\<lambda>k. f (?d k) (r n)) |n. netlimit (at_right x) < r n}) \<in> S"
      have "netlimit (at_right x) = x" by (auto intro: netlimit_within)
      hence "?F x \<in> S" using ntlim_inS by simp
      (* Use S to get epsilon; r from the book is now d. *)*) sorry
  ultimately have rcont_inc: "rcont_inc ?F" unfolding rcont_inc_def by auto
  moreover have bdd: "\<forall>n x. \<bar>?F x\<bar> \<le> M" sorry
  moreover have lim: "\<forall>x.  continuous (at x) ?F \<longrightarrow> (\<lambda>n. f (?d n) x) ----> ?F x"
  proof auto
    fix x::real assume cnt: "continuous (at x) ?F"
    fix e::real assume e: "0 < e"
    have "?F -- x --> ?F x" using cnt continuous_at by auto
    hence "\<exists>d>0. \<forall>y. y \<noteq> x \<and> norm (y - x) < d \<longrightarrow> norm (?F y - ?F x) < e"
      by (rule LIM_D) (rule e) (* Why did auto not work here? *)
    then obtain d where "d > 0" and cnt': "\<forall>y. y \<noteq> x \<and> norm (y - x) < d \<longrightarrow> norm (?F y - ?F x) < e"
      by auto
    fix y::real assume less: "y < x" and "norm (y - x) < d"
    then have "norm (?F y - ?F x) < e" using cnt' by auto
    hence 1: "?F x - e < ?F y" using less mono by auto
    obtain n where n: "y < r n \<and> r n < x"
    proof -
      obtain q where q: "q \<in> \<rat> \<and> y < q \<and> q < x" using less Rats_dense_in_real by auto
      then obtain n where "r n = q" using bij sorry
      thus ?thesis sorry
    qed
    obtain m where m: "x < r m \<and> lim (\<lambda>k. f (?d k) (r m)) < ?F x + e" sorry
    have "?F x - e < lim (\<lambda>k. f (?d k) (r m))" sorry
  
  ultimately show ?thesis
    apply (rule_tac x = ?d in exI)
    apply (rule conjI)
    apply (rule nat.subseq_diagseq)
    by (rule_tac x = ?F in exI) auto
qed

end