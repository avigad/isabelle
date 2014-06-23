theory Library_Misc
imports Probability "~~/src/HOL/Library/ContNotDenum"
begin

lemma distr_cong_AE:
  assumes 1: "M = K" "sets N = sets L" and 
    2: "(AE x in M. f x = g x)" and "f \<in> measurable M N" and "g \<in> measurable K L"
  shows "distr M N f = distr K L g"
proof (rule measure_eqI)
  fix A assume "A \<in> sets (distr M N f)"
  with assms show "emeasure (distr M N f) A = emeasure (distr K L g) A"
    by (auto simp add: emeasure_distr intro!: emeasure_eq_AE measurable_sets)
qed (insert 1, simp)

lemma not_eventually_impI: "eventually P F \<Longrightarrow> \<not> eventually Q F \<Longrightarrow> \<not> eventually (\<lambda>x. P x \<longrightarrow> Q x) F"
  by (auto intro: eventually_mp)

lemma not_eventuallyD: "\<not> eventually P F \<Longrightarrow> \<exists>x. \<not> P x"
  by (metis always_eventually)

lemma sequentially_imp_eventually_at_right:
  fixes a :: "'a :: {dense_linorder, linorder_topology, first_countable_topology}"
  assumes b[simp]: "a < b"
  assumes *: "\<And>f. (\<And>n. a < f n) \<Longrightarrow> (\<And>n. f n < b) \<Longrightarrow> decseq f \<Longrightarrow> f ----> a \<Longrightarrow> eventually (\<lambda>n. P (f n)) sequentially"
  shows "eventually P (at_right a)"
proof (safe intro!: sequentially_imp_eventually_within)
  fix X assume X: "\<forall>n. X n \<in> {a <..} \<and> X n \<noteq> a" "X ----> a"
  show "eventually (\<lambda>n. P (X n)) sequentially"
  proof (rule ccontr)
    assume neg: "\<not> eventually (\<lambda>n. P (X n)) sequentially"
    have "\<exists>s. \<forall>n. (\<not> P (X (s n)) \<and> X (s n) < b) \<and> (X (s (Suc n)) \<le> X (s n) \<and> Suc (s n) \<le> s (Suc n))"
    proof (rule dependent_nat_choice)
      have "\<not> eventually (\<lambda>n. X n < b \<longrightarrow> P (X n)) sequentially"
        by (intro not_eventually_impI neg order_tendstoD(2) [OF X(2) b])
      then show "\<exists>x. \<not> P (X x) \<and> X x < b"
        by (auto dest!: not_eventuallyD)
    next
      fix x n
      have "\<not> eventually (\<lambda>n. Suc x \<le> n \<longrightarrow> X n < b \<longrightarrow> X n < X x \<longrightarrow> P (X n)) sequentially"
        using X by (intro not_eventually_impI order_tendstoD(2)[OF X(2)] eventually_ge_at_top neg) auto
      then show "\<exists>n. (\<not> P (X n) \<and> X n < b) \<and> (X n \<le> X x \<and> Suc x \<le> n)"
        by (auto dest!: not_eventuallyD)
    qed
    then guess s ..
    then have "\<And>n. a < X (s n)" "\<And>n. X (s n) < b" "decseq (\<lambda>n. X (s n))" "(\<lambda>n. X (s n)) ----> a" "\<And>n. \<not> P (X (s n))"
      using X by (auto simp: subseq_Suc_iff Suc_le_eq decseq_Suc_iff intro!: LIMSEQ_subseq_LIMSEQ[OF `X ----> a`, unfolded comp_def])
    from *[OF this(1,2,3,4)] this(5) show False by auto
  qed
qed

lemma tendsto_at_right_sequentially:
  fixes a :: "_ :: {dense_linorder, linorder_topology, first_countable_topology}"
  assumes "a < b"
  assumes *: "\<And>S. (\<And>n. a < S n) \<Longrightarrow> (\<And>n. S n < b) \<Longrightarrow> decseq S \<Longrightarrow> S ----> a \<Longrightarrow> (\<lambda>n. X (S n)) ----> L"
  shows "(X ---> L) (at_right a)"
  using assms unfolding tendsto_def [where l=L]
  by (simp add: sequentially_imp_eventually_at_right)


(*
  Some useful things, that should be moved elsewhere.
*)

lemma has_vector_derivative_weaken:
  fixes x D and f g s t
  assumes f: "(f has_vector_derivative D) (at x within t)"
    and "x \<in> s" "s \<subseteq> t" 
    and "\<And>x. x \<in> s \<Longrightarrow> f x = g x"
  shows "(g has_vector_derivative D) (at x within s)"
proof -
  have "(f has_vector_derivative D) (at x within s) \<longleftrightarrow> (g has_vector_derivative D) (at x within s)"
    unfolding has_vector_derivative_def has_derivative_iff_norm
    using assms by (intro conj_cong Lim_cong_within refl) auto
  then show ?thesis
    using has_vector_derivative_within_subset[OF f `s \<subseteq> t`] by simp
qed

lemma DERIV_image_chain': "(f has_field_derivative D) (at x within s) \<Longrightarrow> 
    (g has_field_derivative E) (at (f x) within (f ` s)) \<Longrightarrow> 
    ((\<lambda>x. g (f x)) has_field_derivative E * D) (at x within s)"
by (drule (1) DERIV_image_chain, simp add: comp_def)

lemma AE_lborel_singleton:
  fixes a :: "'a::ordered_euclidean_space" shows "AE x in lborel. x \<noteq> a"
  by (rule AE_I[where N="{a}"]) auto

lemma (in linorder) linorder_wlog[case_names le sym]:
  fixes a b
  shows "(\<And>a b. a \<le> b \<Longrightarrow> P a b) \<Longrightarrow> (\<And>a b. P b a \<Longrightarrow> P a b) \<Longrightarrow> P a b"
  by (metis linear)

lemma open_Collect_conj: assumes "open {x. P x}" "open {x. Q x}" shows "open {x. P x \<and> Q x}"
  using open_Int[OF assms] by (simp add: Int_def)

lemma filterlim_sup1: "(LIM x F. f x :> G1) \<Longrightarrow> (LIM x F. f x :> (sup G1 G2))"
 unfolding filterlim_def by (auto intro: le_supI1)

lemma eventually_sequentially_Suc: "eventually (\<lambda>i. P (Suc i)) sequentially \<longleftrightarrow> eventually P sequentially"
  unfolding eventually_sequentially by (metis Suc_le_D Suc_le_mono le_Suc_eq)

lemma filterlim_sequentially_Suc:
  "(LIM x sequentially. f (Suc x) :> F) \<longleftrightarrow> (LIM x sequentially. f x :> F)"
  unfolding filterlim_iff
  by (subst eventually_sequentially_Suc) simp

lemma filtermap_nhds_open_map:
  assumes cont: "isCont f a" and open_map: "\<And>S. open S \<Longrightarrow> open (f`S)"
  shows "filtermap f (nhds a) = nhds (f a)"
  unfolding filter_eq_iff
proof safe
  fix P assume "eventually P (filtermap f (nhds a))"
  then guess S unfolding eventually_filtermap eventually_nhds ..
  then show "eventually P (nhds (f a))"
    unfolding eventually_nhds by (intro exI[of _ "f`S"]) (auto intro!: open_map)
qed (metis filterlim_iff tendsto_at_iff_tendsto_nhds isCont_def eventually_filtermap cont)

lemma filtermap_mono_strong: "inj f \<Longrightarrow> filtermap f F \<le> filtermap f G \<longleftrightarrow> F \<le> G"
  apply (auto intro!: filtermap_mono) []
  apply (auto simp: le_filter_def eventually_filtermap)
  apply (erule_tac x="\<lambda>x. P (inv f x)" in allE)
  apply auto
  done

lemma filtermap_eq_strong: "inj f \<Longrightarrow> filtermap f F = filtermap f G \<longleftrightarrow> F = G"
  by (simp add: filtermap_mono_strong eq_iff)

lemma ereal_all_split: "\<And>P. (\<forall>x::ereal. P x) \<longleftrightarrow> P \<infinity> \<and> (\<forall>x. P (ereal x)) \<and> P (-\<infinity>)"
  by (metis ereal_cases)

lemma ereal_ex_split: "\<And>P. (\<exists>x::ereal. P x) \<longleftrightarrow> P \<infinity> \<or> (\<exists>x. P (ereal x)) \<or> P (-\<infinity>)"
  by (metis ereal_cases)

lemma nhds_ereal: "nhds (ereal r) = filtermap ereal (nhds r)"
  by (simp add: filtermap_nhds_open_map open_ereal continuous_at_of_ereal)

lemma at_ereal: "at (ereal r) = filtermap ereal (at r)"
  by (simp add: filter_eq_iff eventually_at_filter nhds_ereal eventually_filtermap)

lemma at_left_ereal: "at_left (ereal r) = filtermap ereal (at_left r)"
  by (simp add: filter_eq_iff eventually_at_filter nhds_ereal eventually_filtermap)

lemma at_right_ereal: "at_right (ereal r) = filtermap ereal (at_right r)"
  by (simp add: filter_eq_iff eventually_at_filter nhds_ereal eventually_filtermap)

lemma
  shows at_left_PInf: "at_left \<infinity> = filtermap ereal at_top"
    and at_right_MInf: "at_right (-\<infinity>) = filtermap ereal at_bot"
  unfolding filter_eq_iff eventually_filtermap eventually_at_top_dense eventually_at_bot_dense
    eventually_at_left[OF ereal_less(5)] eventually_at_right[OF ereal_less(6)]
  by (auto simp add: ereal_all_split ereal_ex_split)

lemma tendsto_compose_filtermap: "((g \<circ> f) ---> T) F \<longleftrightarrow> (g ---> T) (filtermap f F)"
  by (simp add: filterlim_def filtermap_filtermap comp_def)

lemma ereal_tendsto_simps1:
  "((f \<circ> real) ---> y) (at_left (ereal x)) \<longleftrightarrow> (f ---> y) (at_left x)"
  "((f \<circ> real) ---> y) (at_right (ereal x)) \<longleftrightarrow> (f ---> y) (at_right x)"
  "((f \<circ> real) ---> y) (at_left (\<infinity>::ereal)) \<longleftrightarrow> (f ---> y) at_top"
  "((f \<circ> real) ---> y) (at_right (-\<infinity>::ereal)) \<longleftrightarrow> (f ---> y) at_bot"
  unfolding tendsto_compose_filtermap at_left_ereal at_right_ereal at_left_PInf at_right_MInf
  by (auto simp: filtermap_filtermap filtermap_ident)

lemma filterlim_at_bot_dense:
  fixes f :: "'a \<Rightarrow> ('b::{dense_linorder, no_bot})"
  shows "(LIM x F. f x :> at_bot) \<longleftrightarrow> (\<forall>Z. eventually (\<lambda>x. f x < Z) F)"
proof (auto simp add: filterlim_at_bot[of f F])
  fix Z :: 'b
  from lt_ex [of Z] obtain Z' where 1: "Z' < Z" ..
  assume "\<forall>Z. eventually (\<lambda>x. f x \<le> Z) F"
  hence "eventually (\<lambda>x. f x \<le> Z') F" by auto
  thus "eventually (\<lambda>x. f x < Z) F" 
    apply (rule eventually_rev_mono)
    using 1 by auto
  next 
    fix Z :: 'b 
    show "\<forall>Z. eventually (\<lambda>x. f x < Z) F \<Longrightarrow> eventually (\<lambda>x. f x \<le> Z) F"
      by (drule spec [of _ Z], erule eventually_rev_mono, auto simp add: less_imp_le)
qed

lemma ereal_tendsto_simps2:
  "((ereal \<circ> f) ---> ereal a) F \<longleftrightarrow> (f ---> a) F"
  "((ereal \<circ> f) ---> \<infinity>) F \<longleftrightarrow> (LIM x F. f x :> at_top)"
  "((ereal \<circ> f) ---> -\<infinity>) F \<longleftrightarrow> (LIM x F. f x :> at_bot)"
  unfolding tendsto_PInfty filterlim_at_top_dense tendsto_MInfty filterlim_at_bot_dense
  using lim_ereal by (simp_all add: comp_def)

lemmas ereal_tendsto_simps = ereal_tendsto_simps1 ereal_tendsto_simps2

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

lemma mult_indicator_subset:
  "A \<subseteq> B \<Longrightarrow> indicator A x * indicator B x = (indicator A x :: real)"
  by (auto split: split_indicator simp: fun_eq_iff)

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


(** General miscellaneous. **)

(* This should be easy. *)
lemma ereal_le_epsilon_iff2: "(\<forall>\<epsilon>>0. x \<le> y + ereal \<epsilon>) = (x \<le> y)" using ereal_le_epsilon2
by (metis add_commute add_right_mono dual_order.trans ereal_less(2) less_eq_ereal_def
    monoid_add_class.add.left_neutral)

lemma real_of_ereal_neq_0: "real x \<noteq> 0 \<Longrightarrow> x = ereal (real x)"
  by (metis assms ereal_eq_0(1) ereal_real)

(* Why aren't these in Set_Interval.thy?? *)
lemma setprod_atMost_Suc[simp]: "(\<Prod>i \<le> Suc n. f i) = (\<Prod>i \<le> n. f i) * f (Suc n)"
  by (simp add:atMost_Suc mult_ac)

lemma setprod_lessThan_Suc[simp]: "(\<Prod>i < Suc n. f i) = (\<Prod>i < n. f i) * f n"
  by (simp add:lessThan_Suc mult_ac)

(** Miscellany from Helly. **)

(* This should have been in the library, like convergent_limsup_cl. *)
lemma convergent_liminf_cl:
  fixes X :: "nat \<Rightarrow> 'a::{complete_linorder,linorder_topology}"
  shows "convergent X \<Longrightarrow> liminf X = lim X"
  by (auto simp: convergent_def limI lim_imp_Liminf)

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

lemma closed_subset_contains_Inf:
  fixes A C :: "real set"
  shows "closed C \<Longrightarrow> A \<subseteq> C \<Longrightarrow> A \<noteq> {} \<Longrightarrow> bdd_below A \<Longrightarrow> Inf A \<in> C"
  by (metis closure_contains_Inf closure_minimal subset_eq)

lemma atLeastAtMost_subset_contains_Inf:
  fixes A :: "real set" and a b :: real 
  shows "A \<noteq> {} \<Longrightarrow> a \<le> b \<Longrightarrow> A \<subseteq> {a..b} \<Longrightarrow> Inf A \<in> {a..b}"
  by (rule closed_subset_contains_Inf) 
     (auto intro: closed_real_atLeastAtMost intro!: bdd_belowI[of A a])

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
(* There is a generalized function using mono_on A f, and restrict_space A borel  *)
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
  by (intro LIMSEQ_le_const2) (auto simp: eventually_sequentially convergent_LIMSEQ_iff)

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

(*
  TODO: move elsewhere 
*)

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

(* 
    Things that belong somewhere else 
*)

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
  assumes eq: "{a<..b} = {c<..d}" and "a < b \<or> c < d"
  shows "a = c \<and> b = d"
using assms
by (metis greaterThanAtMost_empty greaterThanAtMost_empty_iff 
  greaterThanAtMost_subset_iff order_eq_iff)+

lemma (in linorder) greaterThanAtMost_disjoint:
  shows "{a<..b} \<inter> {c<..d} = {} \<longleftrightarrow> b \<le> a \<or> d \<le> c \<or> b \<le> c \<or> d \<le> a"
  using assms by auto

lemma continuous_at_split: 
  "continuous (at (x::'a::linorder_topology)) f = (continuous (at_left x) f \<and> continuous (at_right x) f)"
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

lemma emeasure_insert':
  "A \<noteq> {} \<Longrightarrow> {x} \<in> sets M \<Longrightarrow> A \<in> sets M \<Longrightarrow> x \<notin> A \<Longrightarrow> emeasure M (insert x A) = emeasure M {x} + emeasure M A"
    by (rule emeasure_insert) 

(* the dual version is in Convex_Euclidean_Space.thy *)

lemma interior_real_Iic:
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

lemma frontier_real_Iic:
  fixes a :: real
  shows "frontier {..a} = {a}"
  unfolding frontier_def by (auto simp add: interior_real_Iic)

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


lemma (in dense_linorder) Ioc_inject:
  "{a <.. b} = {c <.. d} \<longleftrightarrow> (b \<le> a \<and> d \<le> c) \<or> a = c \<and> b = d"
proof -
  { fix a b c d :: 'a assume *: "{a<..b} = {c<..d}" "c < d" "a < b"
    have "a \<le> c"
    proof (rule dense_ge_bounded[OF `c < d`])
      fix w assume "c < w" "w < d"
      then have "w \<in> {c <.. d}"
        by auto
      then have "w \<in> {a<..b}"
        unfolding * by auto
      then show "a \<le> w"
        by auto
    qed }
  from this[of a b c d] this[of c d a b] show ?thesis
    by (cases "b \<le> a" "d \<le> c" rule: bool.exhaust[case_product bool.exhaust])
       (auto intro!: antisym)
qed

lemma cInf_Ioc[simp]:
  fixes a b :: "'a::{conditionally_complete_linorder, dense_linorder}"
  shows "a < b \<Longrightarrow> Inf {a <.. b} = a"
  by (auto intro!: cInf_eq_non_empty intro: dense_ge_bounded)

lemma (in conditionally_complete_lattice) cInf_le_cSup:
  "A \<noteq> {} \<Longrightarrow> bdd_above A \<Longrightarrow> bdd_below A \<Longrightarrow> Inf A \<le> Sup A"
  by (auto intro!: cSup_upper2[of "SOME a. a \<in> A"] intro: someI cInf_lower)

lemma disjoint_family_onD: "disjoint_family_on A I \<Longrightarrow> i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> i \<noteq> j \<Longrightarrow> A i \<inter> A j = {}"
  by (auto simp: disjoint_family_on_def)

lemma extend_measure_caratheodory:
  fixes G :: "'i \<Rightarrow> 'a set"
  assumes M: "M = extend_measure \<Omega> I G \<mu>"
  assumes "i \<in> I"
  assumes "semiring_of_sets \<Omega> (G ` I)"
  assumes empty: "\<And>i. i \<in> I \<Longrightarrow> G i = {} \<Longrightarrow> \<mu> i = 0"
  assumes inj: "\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> G i = G j \<Longrightarrow> \<mu> i = \<mu> j"
  assumes nonneg: "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> \<mu> i"
  assumes add: "\<And>A::nat \<Rightarrow> 'i. \<And>j. A \<in> UNIV \<rightarrow> I \<Longrightarrow> j \<in> I \<Longrightarrow> disjoint_family (G \<circ> A) \<Longrightarrow>
    (\<Union>i. G (A i)) = G j \<Longrightarrow> (\<Sum>n. \<mu> (A n)) = \<mu> j"
  shows "emeasure M (G i) = \<mu> i"
proof -
  interpret semiring_of_sets \<Omega> "G ` I"
    by fact
  have "\<forall>g\<in>G`I. \<exists>i\<in>I. g = G i"
    by auto
  then obtain sel where sel: "\<And>g. g \<in> G ` I \<Longrightarrow> sel g \<in> I" "\<And>g. g \<in> G ` I \<Longrightarrow> G (sel g) = g"
    by metis

  have "\<exists>\<mu>'. (\<forall>s\<in>G ` I. \<mu>' s = \<mu> (sel s)) \<and> measure_space \<Omega> (sigma_sets \<Omega> (G ` I)) \<mu>'"
  proof (rule caratheodory)
    show "positive (G ` I) (\<lambda>s. \<mu> (sel s))"
      by (auto simp: positive_def intro!: empty sel nonneg)
    show "countably_additive (G ` I) (\<lambda>s. \<mu> (sel s))"
    proof (rule countably_additiveI)
      fix A :: "nat \<Rightarrow> 'a set" assume "range A \<subseteq> G ` I" "disjoint_family A" "(\<Union>i. A i) \<in> G ` I"
      then show "(\<Sum>i. \<mu> (sel (A i))) = \<mu> (sel (\<Union>i. A i))"
        by (intro add) (auto simp: sel image_subset_iff_funcset comp_def Pi_iff intro!: sel)
    qed
  qed
  then obtain \<mu>' where \<mu>': "\<forall>s\<in>G ` I. \<mu>' s = \<mu> (sel s)" "measure_space \<Omega> (sigma_sets \<Omega> (G ` I)) \<mu>'"
    by metis

  show ?thesis
  proof (rule emeasure_extend_measure[OF M])
    { fix i assume "i \<in> I" then show "\<mu>' (G i) = \<mu> i"
      using \<mu>' by (auto intro!: inj sel) }
    show "G ` I \<subseteq> Pow \<Omega>"
      by fact
    then show "positive (sets M) \<mu>'" "countably_additive (sets M) \<mu>'"
      using \<mu>' by (simp_all add: M sets_extend_measure measure_space_def)
  qed fact
qed
  
lemma extend_measure_caratheodory_pair:
  fixes G :: "'i \<Rightarrow> 'j \<Rightarrow> 'a set"
  assumes M: "M = extend_measure \<Omega> {(a, b). P a b} (\<lambda>(a, b). G a b) (\<lambda>(a, b). \<mu> a b)"
  assumes "P i j"
  assumes semiring: "semiring_of_sets \<Omega> {G a b | a b. P a b}"
  assumes empty: "\<And>i j. P i j \<Longrightarrow> G i j = {} \<Longrightarrow> \<mu> i j = 0"
  assumes inj: "\<And>i j k l. P i j \<Longrightarrow> P k l \<Longrightarrow> G i j = G k l \<Longrightarrow> \<mu> i j = \<mu> k l"
  assumes nonneg: "\<And>i j. P i j \<Longrightarrow> 0 \<le> \<mu> i j"
  assumes add: "\<And>A::nat \<Rightarrow> 'i. \<And>B::nat \<Rightarrow> 'j. \<And>j k.
    (\<And>n. P (A n) (B n)) \<Longrightarrow> P j k \<Longrightarrow> disjoint_family (\<lambda>n. G (A n) (B n)) \<Longrightarrow>
    (\<Union>i. G (A i) (B i)) = G j k \<Longrightarrow> (\<Sum>n. \<mu> (A n) (B n)) = \<mu> j k"
  shows "emeasure M (G i j) = \<mu> i j"
proof -
  have "emeasure M ((\<lambda>(a, b). G a b) (i, j)) = (\<lambda>(a, b). \<mu> a b) (i, j)"
  proof (rule extend_measure_caratheodory[OF M])
    show "semiring_of_sets \<Omega> ((\<lambda>(a, b). G a b) ` {(a, b). P a b})"
      using semiring by (simp add: image_def conj_commute)
  next
    fix A :: "nat \<Rightarrow> ('i \<times> 'j)" and j assume "A \<in> UNIV \<rightarrow> {(a, b). P a b}" "j \<in> {(a, b). P a b}"
      "disjoint_family ((\<lambda>(a, b). G a b) \<circ> A)"
      "(\<Union>i. case A i of (a, b) \<Rightarrow> G a b) = (case j of (a, b) \<Rightarrow> G a b)"
    then show "(\<Sum>n. case A n of (a, b) \<Rightarrow> \<mu> a b) = (case j of (a, b) \<Rightarrow> \<mu> a b)"
      using add[of "\<lambda>i. fst (A i)" "\<lambda>i. snd (A i)" "fst j" "snd j"]
      by (simp add: split_beta' comp_def Pi_iff)
  qed (auto split: prod.splits intro: assms)
  then show ?thesis by simp
qed

subsection {* Every right continuous and nondecreasing function gives rise to a measure *}

definition interval_measure :: "(real \<Rightarrow> real) \<Rightarrow> real measure" where
  "interval_measure F = extend_measure UNIV {(a, b). a \<le> b} (\<lambda>(a, b). {a <.. b}) (\<lambda>(a, b). ereal (F b - F a))"

lemma emeasure_interval_measure:
  assumes "a \<le> b"
  assumes mono_F: "\<And>x y. x \<le> y \<Longrightarrow> F x \<le> F y"
  assumes right_cont_F : "\<And>a. continuous (at_right a) F" 
  shows "emeasure (interval_measure F) {a <.. b} = F b - F a"
proof (rule extend_measure_caratheodory_pair[OF interval_measure_def `a \<le> b`])
  show "semiring_of_sets UNIV {{a<..b} |a b :: real. a \<le> b}"
  proof (unfold_locales, safe)
    fix a b c d :: real assume *: "a \<le> b" "c \<le> d"
    then show "\<exists>C\<subseteq>{{a<..b} |a b. a \<le> b}. finite C \<and> disjoint C \<and> {a<..b} - {c<..d} = \<Union>C"
    proof cases
      let ?C = "{{a<..b}}"
      assume "b < c \<or> d \<le> a \<or> d \<le> c"
      with * have "?C \<subseteq> {{a<..b} |a b. a \<le> b} \<and> finite ?C \<and> disjoint ?C \<and> {a<..b} - {c<..d} = \<Union>?C"
        by (auto simp add: disjoint_def)
      thus ?thesis ..
    next
      let ?C = "{{a<..c}, {d<..b}}"
      assume "\<not> (b < c \<or> d \<le> a \<or> d \<le> c)"
      with * have "?C \<subseteq> {{a<..b} |a b. a \<le> b} \<and> finite ?C \<and> disjoint ?C \<and> {a<..b} - {c<..d} = \<Union>?C"
        by (auto simp add: disjoint_def Ioc_inject) (metis linear)+
      thus ?thesis ..
    qed
  qed (auto simp: Ioc_inject, metis linear)
next
  fix l r :: "nat \<Rightarrow> real" and a b :: real
  assume l_r[simp]: "\<And>n. l n \<le> r n" and "a \<le> b" and disj: "disjoint_family (\<lambda>n. {l n<..r n})" 
  assume lr_eq_ab: "(\<Union>i. {l i<..r i}) = {a<..b}"

  have [intro, simp]: "\<And>a b. a \<le> b \<Longrightarrow> 0 \<le> F b - F a"
    by (auto intro!: l_r mono_F simp: diff_le_iff)

  { fix S :: "nat set" assume "finite S"
    moreover note `a \<le> b`
    moreover have "\<And>i. i \<in> S \<Longrightarrow> {l i <.. r i} \<subseteq> {a <.. b}"
      unfolding lr_eq_ab[symmetric] by auto
    ultimately have "(\<Sum>i\<in>S. F (r i) - F (l i)) \<le> F b - F a"
    proof (induction S arbitrary: a rule: finite_psubset_induct)
      case (psubset S)
      show ?case
      proof cases
        assume "\<exists>i\<in>S. l i < r i"
        with `finite S` have "Min (l ` {i\<in>S. l i < r i}) \<in> l ` {i\<in>S. l i < r i}"
          by (intro Min_in) auto
        then obtain m where m: "m \<in> S" "l m < r m" "l m = Min (l ` {i\<in>S. l i < r i})"
          by fastforce

        have "(\<Sum>i\<in>S. F (r i) - F (l i)) = (F (r m) - F (l m)) + (\<Sum>i\<in>S - {m}. F (r i) - F (l i))"
          using m psubset by (intro setsum.remove) auto
        also have "(\<Sum>i\<in>S - {m}. F (r i) - F (l i)) \<le> F b - F (r m)"
        proof (intro psubset.IH)
          show "S - {m} \<subset> S"
            using `m\<in>S` by auto
          show "r m \<le> b"
            using psubset.prems(2)[OF `m\<in>S`] `l m < r m` by auto
        next
          fix i assume "i \<in> S - {m}"
          then have i: "i \<in> S" "i \<noteq> m" by auto
          { assume i': "l i < r i" "l i < r m"
            moreover with `finite S` i m have "l m \<le> l i"
              by auto
            ultimately have "{l i <.. r i} \<inter> {l m <.. r m} \<noteq> {}"
              by auto
            then have False
              using disjoint_family_onD[OF disj, of i m] i by auto }
          then have "l i \<noteq> r i \<Longrightarrow> r m \<le> l i"
            unfolding not_less[symmetric] using l_r[of i] by auto
          then show "{l i <.. r i} \<subseteq> {r m <.. b}"
            using psubset.prems(2)[OF `i\<in>S`] by auto
        qed
        also have "F (r m) - F (l m) \<le> F (r m) - F a"
          using psubset.prems(2)[OF `m \<in> S`] `l m < r m` by (auto simp add: greaterThanAtMost_subset_iff intro!: mono_F)
        finally show ?case
          by (auto intro: add_mono)
      qed (simp add: `a \<le> b` less_le)
    qed }
  note claim1 = this

  (* second key induction: a lower bound on the measures of any finite collection of Ai's
     that cover an interval {u..v} *)

  { fix S u v and l r :: "nat \<Rightarrow> real"
    assume "finite S" "\<And>i. i\<in>S \<Longrightarrow> l i < r i" "{u..v} \<subseteq> (\<Union>i\<in>S. {l i<..< r i})"
    then have "F v - F u \<le> (\<Sum>i\<in>S. F (r i) - F (l i))"
    proof (induction arbitrary: v u rule: finite_psubset_induct)
      case (psubset S)
      show ?case
      proof cases
        assume "S = {}" then show ?case
          using psubset by (simp add: mono_F)
      next
        assume "S \<noteq> {}"
        then obtain j where "j \<in> S"
          by auto

        let ?R = "r j < u \<or> l j > v \<or> (\<exists>i\<in>S-{j}. l i \<le> l j \<and> r j \<le> r i)"
        show ?case
        proof cases
          assume "?R"
          with `j \<in> S` psubset.prems have "{u..v} \<subseteq> (\<Union>i\<in>S-{j}. {l i<..< r i})"
            apply (auto simp: subset_eq Ball_def)
            apply (metis Diff_iff less_le_trans leD linear singletonD)
            apply (metis Diff_iff less_le_trans leD linear singletonD)
            apply (metis order_trans less_le_not_le linear)
            done
          with `j \<in> S` have "F v - F u \<le> (\<Sum>i\<in>S - {j}. F (r i) - F (l i))"
            by (intro psubset) auto
          also have "\<dots> \<le> (\<Sum>i\<in>S. F (r i) - F (l i))"
            using psubset.prems
            by (intro setsum_mono2 psubset) (auto intro: less_imp_le)
          finally show ?thesis .
        next
          assume "\<not> ?R"
          then have j: "u \<le> r j" "l j \<le> v" "\<And>i. i \<in> S - {j} \<Longrightarrow> r i < r j \<or> l i > l j"
            by (auto simp: not_less)
          let ?S1 = "{i \<in> S. l i < l j}"
          let ?S2 = "{i \<in> S. r i > r j}"

          have "(\<Sum>i\<in>S. F (r i) - F (l i)) \<ge> (\<Sum>i\<in>?S1 \<union> ?S2 \<union> {j}. F (r i) - F (l i))"
            using `j \<in> S` `finite S` psubset.prems j
            by (intro setsum_mono2) (auto intro: less_imp_le)
          also have "(\<Sum>i\<in>?S1 \<union> ?S2 \<union> {j}. F (r i) - F (l i)) =
            (\<Sum>i\<in>?S1. F (r i) - F (l i)) + (\<Sum>i\<in>?S2 . F (r i) - F (l i)) + (F (r j) - F (l j))"
            using psubset(1) psubset.prems(1) j
            apply (subst setsum_Un_disjoint)
            apply simp_all
            apply (subst setsum_Un_disjoint)
            apply auto
            apply (metis less_le_not_le)
            done
          also (xtrans) have "(\<Sum>i\<in>?S1. F (r i) - F (l i)) \<ge> F (l j) - F u"
            using `j \<in> S` `finite S` psubset.prems j
            apply (intro psubset.IH psubset)
            apply (auto simp: subset_eq Ball_def)
            apply (metis less_le_trans not_le)
            done
          also (xtrans) have "(\<Sum>i\<in>?S2. F (r i) - F (l i)) \<ge> F v - F (r j)"
            using `j \<in> S` `finite S` psubset.prems j
            apply (intro psubset.IH psubset)
            apply (auto simp: subset_eq Ball_def)
            apply (metis le_less_trans not_le)
            done
          finally (xtrans) show ?case
            by (auto simp: add_mono)
        qed
      qed
    qed }
  note claim2 = this

  (* now prove the inequality going the other way *)

  { fix epsilon :: real assume egt0: "epsilon > 0"
    have "\<forall>i. \<exists>d. d > 0 &  F (r i + d) < F (r i) + epsilon / 2^(i+2)"
    proof 
      fix i
      note right_cont_F [of "r i"]
      thus "\<exists>d. d > 0 \<and> F (r i + d) < F (r i) + epsilon / 2^(i+2)"
        apply -
        apply (subst (asm) continuous_at_right_real_increasing)
        apply (rule mono_F, assumption)
        apply (drule_tac x = "epsilon / 2 ^ (i + 2)" in spec)
        apply (erule impE)
        using egt0 by (auto simp add: field_simps)
    qed
    then obtain delta where 
        deltai_gt0: "\<And>i. delta i > 0" and
        deltai_prop: "\<And>i. F (r i + delta i) < F (r i) + epsilon / 2^(i+2)"
      by metis
    have "\<exists>a' > a. F a' - F a < epsilon / 2"
      apply (insert right_cont_F [of a])
      apply (subst (asm) continuous_at_right_real_increasing)
      using mono_F apply force
      apply (drule_tac x = "epsilon / 2" in spec)
      using egt0 apply (auto simp add: field_simps)
      by (metis add_less_cancel_left comm_monoid_add_class.add.right_neutral 
        comm_semiring_1_class.normalizing_semiring_rules(24) mult_2 mult_2_right)
    then obtain a' where a'lea [arith]: "a' > a" and 
      a_prop: "F a' - F a < epsilon / 2"
      by auto
    def S' \<equiv> "{i. l i < r i}"
    obtain S :: "nat set" where 
      "S \<subseteq> S'" and finS: "finite S" and 
      Sprop: "{a'..b} \<subseteq> (\<Union>i \<in> S. {l i<..<r i + delta i})"
    proof (rule compactE_image)
      show "compact {a'..b}"
        by (rule compact_Icc)
      show "\<forall>i \<in> S'. open ({l i<..<r i + delta i})" by auto
      have "{a'..b} \<subseteq> {a <.. b}"
        by auto
      also have "{a <.. b} = (\<Union>i\<in>S'. {l i<..r i})"
        unfolding lr_eq_ab[symmetric] by (fastforce simp add: S'_def intro: less_le_trans)
      also have "\<dots> \<subseteq> (\<Union>i \<in> S'. {l i<..<r i + delta i})"
        apply (intro UN_mono)
        apply (auto simp: S'_def)
        apply (cut_tac i=i in deltai_gt0)
        apply simp
        done
      finally show "{a'..b} \<subseteq> (\<Union>i \<in> S'. {l i<..<r i + delta i})" .
    qed
    with S'_def have Sprop2: "\<And>i. i \<in> S \<Longrightarrow> l i < r i" by auto
    from finS have "\<exists>n. \<forall>i \<in> S. i \<le> n" 
      by (subst finite_nat_set_iff_bounded_le [symmetric])
    then obtain n where Sbound [rule_format]: "\<forall>i \<in> S. i \<le> n" ..
    have "F b - F a' \<le> (\<Sum>i\<in>S. F (r i + delta i) - F (l i))"
      apply (rule claim2 [rule_format])
      using finS Sprop apply auto
      apply (frule Sprop2)
      apply (subgoal_tac "delta i > 0")
      apply arith
      by (rule deltai_gt0)
    also have "... \<le> (SUM i : S. F(r i) - F(l i) + epsilon / 2^(i+2))"
      apply (rule setsum_mono)
      apply simp
      apply (rule order_trans)
      apply (rule less_imp_le)
      apply (rule deltai_prop)
      by auto
    also have "... = (SUM i : S. F(r i) - F(l i)) + 
        (epsilon / 4) * (SUM i : S. (1 / 2)^i)" (is "_ = ?t + _")
      by (subst setsum_addf) (simp add: field_simps setsum_right_distrib)
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
    finally have aux2: "F b - F a' \<le> (\<Sum>i\<in>S. F (r i) - F (l i)) + epsilon / 2"
      by simp

    have "F b - F a = (F b - F a') + (F a' - F a)"
      by auto
    also have "... \<le> (F b - F a') + epsilon / 2"
      using a_prop by (intro add_left_mono) simp
    also have "... \<le> (\<Sum>i\<in>S. F (r i) - F (l i)) + epsilon / 2 + epsilon / 2"
      apply (intro add_right_mono)
      apply (rule aux2)
      done
    also have "... = (\<Sum>i\<in>S. F (r i) - F (l i)) + epsilon"
      by auto
    also have "... \<le> (\<Sum>i\<le>n. F (r i) - F (l i)) + epsilon"
      using finS Sbound Sprop by (auto intro!: add_right_mono setsum_mono3)
    finally have "ereal (F b - F a) \<le> (\<Sum>i\<le>n. ereal (F (r i) - F (l i))) + epsilon"
      by simp
    then have "ereal (F b - F a) \<le> (\<Sum>i. ereal (F (r i) - F (l i))) + (epsilon :: real)"
      apply (rule_tac order_trans)
      prefer 2
      apply (rule add_mono[where c="ereal epsilon"])
      apply (rule suminf_upper[of _ "Suc n"])
      apply (auto simp add: lessThan_Suc_atMost)
      done }
  hence "ereal (F b - F a) \<le> (\<Sum>i. ereal (F (r i) - F (l i)))"
    by (auto intro: ereal_le_epsilon2)
  moreover
  have "(\<Sum>i. ereal (F (r i) - F (l i))) \<le> ereal (F b - F a)"
    by (auto simp add: claim1 intro!: suminf_bound)
  ultimately show "(\<Sum>n. ereal (F (r n) - F (l n))) = ereal (F b - F a)"
    by simp
qed (auto simp: Ioc_inject diff_le_iff mono_F)

lemma measure_interval_measure:
  assumes "a \<le> b"
  assumes mono_F: "\<And>x y. x \<le> y \<Longrightarrow> F x \<le> F y"
  assumes right_cont_F : "\<And>a. continuous (at_right a) F" 
  shows "measure (interval_measure F) {a <.. b} = F b - F a"
  unfolding measure_def
  apply (subst emeasure_interval_measure)
  apply fact+
  apply simp
  done

lemma Int_stable_Ioc: "Int_stable (range (\<lambda>(a, b). {a <.. b::real}))"
  by (rule Int_stableI) force

lemma borel_sigma_sets_Ioc: "borel = sigma UNIV (range (\<lambda>(a, b). {a <.. b::real}))"
proof (rule borel_eq_sigmaI5[OF borel_eq_atMost])
  fix i :: real
  have "{..i} = (\<Union>j::nat. {-j <.. i})"
    by (auto simp: minus_less_iff reals_Archimedean2)
  also have "\<dots> \<in> sets (sigma UNIV (range (\<lambda>(i, j). {i<..j})))"
    by (intro sets.countable_nat_UN) auto 
  finally show "{..i} \<in> sets (sigma UNIV (range (\<lambda>(i, j). {i<..j})))" .
qed simp

lemma sets_interval_measure [simp]: "sets (interval_measure F) = sets borel"
  apply (simp add: sets_extend_measure interval_measure_def borel_sigma_sets_Ioc)
  apply (rule sigma_sets_eqI)
  apply auto
  apply (case_tac "a \<le> ba")
  apply (auto intro: sigma_sets.Empty)
  done

lemma space_interval_measure [simp]: "space (interval_measure F) = UNIV"
  by (simp add: interval_measure_def space_extend_measure)

end