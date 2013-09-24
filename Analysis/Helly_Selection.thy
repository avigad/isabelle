theory Helly_Selection
imports Diagonal_Subsequence Conditionally_Complete_Lattice Library_Misc

begin

primrec halfseq :: "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  "halfseq l a0 0 = a0"
| "halfseq l a0 (Suc n) = (halfseq l a0 n - l) / 2"

lemma closed_contains_Inf:
  assumes cl: "closed A" and nonempty: "A \<noteq> {}" and bdd: "bdd_below A"
  shows "Inf A \<in> (A::real set)"
proof -
  from nonempty obtain a0 where a0: "a0 \<in> A" by auto
  let ?a = "halfseq (Inf A) a0"
  have dist_a: "\<And>n. dist (?a n) (Inf A) = dist a0 (Inf A) / 2^n"
  proof -
    fix n :: nat show "dist (?a n) (Inf A) = dist a0 (Inf A) / 2^n"
    apply (induct n, auto)
    sorry
  qed
  have lbd_a: "\<And>n. Inf A \<le> ?a n"
  proof -
    fix n show "Inf A \<le> ?a n"
      apply (induct n, auto intro: assms Inf_lower a0)
      sorry
  qed
  have "?a ----> Inf A"
  proof (rule metric_LIMSEQ_I)
    fix r :: real assume r: "0 < r"
    obtain n0 where n0: "dist a0 (Inf A) / 2^n0 < r"
    sorry
    (* proof (cases "a0 = Inf A")
      assume "a0 = Inf A"
      then have "dist a0 (Inf A) = 0" by auto *)
    have "\<forall>n\<ge>n0. dist (?a n) (Inf A) < r"
    proof (auto)
      fix n assume le: "n0 \<le> n"
      from dist_a have "dist (?a n) (Inf A) = dist a0 (Inf A) / 2^n" by simp
      also have "... = (dist a0 (Inf A) / 2^n0) / 2^(n - n0)" using le sorry
      also have "... < r" using r le sorry
      finally show "dist (?a n) (Inf A) < r" by simp
    qed
    thus "\<exists>n0. \<forall>n\<ge>n0. dist (?a n) (Inf A) < r" by auto
  qed
  have "\<forall>n. \<exists>x. x \<le> ?a n \<and> x \<in> A" sorry
  then obtain b where "\<forall>n. b n \<le> ?a n \<and> b n \<in> A" sorry
  hence "b ----> Inf A"
  thus ?thesis using closed_sequential_limits
qed

definition rcont_inc :: "(real \<Rightarrow> real) \<Rightarrow> bool"
  where "rcont_inc f \<equiv> (\<forall>x. continuous (at_right x) f) \<and> mono f"

theorem Helley_selection:
  fixes f :: "nat \<Rightarrow> real \<Rightarrow> real"
  assumes rcont_inc: "\<And>n. rcont_inc (f n)"
  and ubdd: "\<forall>n x. \<bar>f n x\<bar> \<le> M"
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
    moreover have "\<And>k. f (s k) (r n) \<in> {-M..M}" using ubdd abs_le_interval_iff by auto
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
  have M_nonneg: "0 \<le> M" using ubdd by (metis abs_minus_le_zero less_le less_trans neg_le_0_iff_le)
  have lim_bdd: "\<And>n. lim (\<lambda>k. f (?d k) (r n)) \<in> {-M..M}"
  proof -
    fix n::nat
    have "closed {-M..M}" using closed_real_atLeastAtMost by auto
    hence "(\<forall>i. (\<lambda>k. f (?d k) (r n)) i \<in> {-M..M}) \<and> (\<lambda>k. f (?d k) (r n)) ----> lim (\<lambda>k. f (?d k) (r n))
      \<longrightarrow> lim (\<lambda>k. f (?d k) (r n)) \<in> {-M..M}"
      apply (subst (asm) closed_sequential_limits)
      by (drule_tac x = "\<lambda>k. f (?d k) (r n)" in spec) blast
    moreover have "\<forall>i. (\<lambda>k. f (?d k) (r n)) i \<in> {-M..M}" using ubdd abs_le_interval_iff by auto
    moreover have "(\<lambda>k. f (?d k) (r n)) ----> lim (\<lambda>k. f (?d k) (r n))"
      using rat_cnv convergent_LIMSEQ_iff by auto
    ultimately show "lim (\<lambda>k. f (?d k) (r n)) \<in> {-M..M}" by auto
  qed
  hence bdd_below: "\<And>x::real. bdd_below {lim (\<lambda>k. f (?d k) (r n)) |n. x < r n}"
    unfolding bdd_below_def by auto
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
  let ?F = "\<lambda>x::real. \<Sqinter>{lim (\<lambda>k. f (?d k) (r n)) |n. x < r n}"
  from lim_bdd have "\<And>x::real. ?F x \<in> {-M..M}"
  proof -
    find_theorems name: Inf "closed _"
    fix x::real
    have M: "-M \<le> M" using M_nonneg by simp
    have bd_limset: "{lim (\<lambda>k. f (?d k) (r n)) |n. x < r n} \<subseteq> {-M..M}" using lim_bdd by auto
    hence 1: "\<forall>y \<in> {lim (\<lambda>k. f (?d k) (r n)) |n. x < r n}. \<bar>y - 0\<bar> \<le> M"
    proof -
      have "(\<forall>y \<in> {lim (\<lambda>k. f (?d k) (r n)) |n. x < r n}. \<bar>y - 0\<bar> \<le> M) =
        (\<forall>y \<in> {lim (\<lambda>k. f (?d k) (r n)) |n. x < r n}. y \<in> {-M..M})" by auto
      thus ?thesis using bd_limset by blast
    qed
    have "\<bar>Inf {lim (\<lambda>k. f (?d k) (r n)) |n. x < r n} - 0\<bar> \<le> M"
      apply (rule Inf_asclose) by (rule nonempty) (rule 1)
    thus "Inf {lim (\<lambda>k. f (?d k) (r n)) |n. x < r n} \<in> {-M..M}" by auto
  qed
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