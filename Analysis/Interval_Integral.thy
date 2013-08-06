theory Interval_Integral
  imports Probability
begin

lemma tendsto_at_within_iff_tendsto_nhds:
  "(g ---> g l) (at l within S) \<longleftrightarrow> (g ---> g l) (inf (nhds l) (principal S))"
  unfolding tendsto_def eventually_at_filter eventually_inf_principal
  by (intro ext all_cong imp_cong) (auto elim!: eventually_elim1)

lemma tendsto_at_iff_sequentially:
  fixes f :: "'a :: first_countable_topology \<Rightarrow> _"
  shows "(f ---> a) (at x within s) \<longleftrightarrow> (\<forall>X. (\<forall>i. X i \<in> s - {x}) \<longrightarrow> X ----> x \<longrightarrow> ((f \<circ> X) ----> a))"
  unfolding filterlim_def[of _ "nhds a"] le_filter_def eventually_filtermap at_within_def eventually_nhds_within_iff_sequentially comp_def
  by metis

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

definition "einterval a b = {x. a < ereal x \<and> ereal x < b}"

lemma einterval_eq[simp]:
  shows einterval_eq_Icc: "einterval (ereal a) (ereal b) = {a <..< b}"
    and einterval_eq_Ici: "einterval (ereal a) \<infinity> = {a <..}"
    and einterval_eq_Iic: "einterval (- \<infinity>) (ereal b) = {..< b}"
    and einterval_eq_UNIV: "einterval (- \<infinity>) \<infinity> = UNIV"
  by (auto simp: einterval_def)

lemma einterval_iff: "x \<in> einterval a b \<longleftrightarrow> a < ereal x \<and> ereal x < b"
  by (simp add: einterval_def)

lemma open_Collect_conj: assumes "open {x. P x}" "open {x. Q x}" shows "open {x. P x \<and> Q x}"
  using open_Int[OF assms] by (simp add: Int_def)

lemma open_einterval[simp]: "open (einterval a b)"
  by (cases a b rule: ereal2_cases)
     (auto simp: einterval_def intro!: open_Collect_conj open_Collect_less continuous_on_intros)

lemma filterlim_sup1: "(LIM x F. f x :> G1) \<Longrightarrow> (LIM x F. f x :> (sup G1 G2))"
 unfolding filterlim_def by (auto intro: le_supI1)

lemma eventually_sequentially_Suc: "eventually (\<lambda>i. P (Suc i)) sequentially \<longleftrightarrow> eventually P sequentially"
  apply (auto simp: eventually_sequentially)
  apply (metis Suc_le_D Suc_le_mono)
  apply (metis le_Suc_eq)
  done

lemma filterlim_sequentially_Suc:
  "(LIM x sequentially. f (Suc x) :> F) \<longleftrightarrow> (LIM x sequentially. f x :> F)"
  unfolding filterlim_def le_filter_def eventually_filtermap
  by (subst eventually_sequentially_Suc) simp

lemma ereal_incseq_appox:
  fixes a b :: ereal
  assumes "a < b"
  obtains X :: "nat \<Rightarrow> real" where 
    "incseq X" "\<And>i. a < X i" "\<And>i. X i < b" "X ----> b"
proof (cases b)
  case PInf
  with `a < b` have "a = -\<infinity> \<or> (\<exists>r. a = ereal r)"
    by (cases a) auto
  moreover have " (\<lambda>x. ereal (real (Suc x))) ----> \<infinity>"
    using natceiling_le_eq by (subst LIMSEQ_Suc_iff) (auto simp: Lim_PInfty)
  moreover have "\<And>r. (\<lambda>x. ereal (r + real (Suc x))) ----> \<infinity>"
    apply (subst LIMSEQ_Suc_iff)
    apply (subst Lim_PInfty)
    apply (metis add_commute diff_le_eq natceiling_le_eq ereal_less_eq(3))
    done
  ultimately show thesis
    by (intro that[of "\<lambda>i. real a + Suc i"])
       (auto simp: incseq_def PInf)
next
  case (real b')
  def d \<equiv> "b' - (if a = -\<infinity> then b' - 1 else real a)"
  with `a < b` have a': "0 < d"
    by (cases a) (auto simp: real)
  moreover
  have "\<And>i r. r < b' \<Longrightarrow> (b' - r) * 1 < (b' - r) * real (Suc (Suc i))"
    by (intro mult_strict_left_mono) auto
  with `a < b` a' have "\<And>i. a < ereal (b' - d / real (Suc (Suc i)))"
    by (cases a) (auto simp: real d_def field_simps)
  moreover have "(\<lambda>i. b' - d / Suc (Suc i)) ----> b'"
    apply (subst filterlim_sequentially_Suc)
    apply (subst filterlim_sequentially_Suc)
    apply (rule tendsto_eq_intros)
    apply (auto intro!: tendsto_divide_0[OF tendsto_const] filterlim_sup1
                simp: at_infinity_eq_at_top_bot filterlim_real_sequentially)
    done
  ultimately show thesis
    by (intro that[of "\<lambda>i. b' - d / Suc (Suc i)"])
       (auto simp add: real incseq_def divide_pos_pos mult_pos_pos intro!: divide_left_mono)
qed (insert `a < b`, auto)

lemma ereal_decseq_appox:
  fixes a b :: ereal
  assumes "a < b"
  obtains X :: "nat \<Rightarrow> real" where 
    "decseq X" "\<And>i. a < X i" "\<And>i. X i < b" "X ----> a"
proof -
  have "-b < -a" using `a < b` by simp
  from ereal_incseq_appox[OF this] guess X .
  then show thesis
    apply (intro that[of "\<lambda>i. - X i"])
    apply (auto simp add: uminus_ereal.simps[symmetric] decseq_def incseq_def
                simp del: uminus_ereal.simps)
    apply (metis ereal_minus_less_minus ereal_uminus_uminus ereal_Lim_uminus)+
    done
qed

lemma einterval_Icc_approximation:
  fixes a b :: ereal
  assumes "a < b"
  obtains u l :: "nat \<Rightarrow> real" where 
    "einterval a b = (\<Union>i. {l i .. u i})"
    "incseq u" "decseq l" "\<And>i. l i < u i" "\<And>i. a < l i" "\<And>i. u i < b"
    "l ----> a" "u ----> b"
proof -
  from dense[OF `a < b`] obtain c where "a < c" "c < b" by safe
  from ereal_incseq_appox[OF `c < b`] guess u . note u = this
  from ereal_decseq_appox[OF `a < c`] guess l . note l = this
  { fix i from less_trans[OF `l i < c` `c < u i`] have "l i < u i" by simp }
  have "einterval a b = (\<Union>i. {l i .. u i})"
  proof (auto simp: einterval_iff)
    fix x assume "a < ereal x" "ereal x < b"
    have "eventually (\<lambda>i. ereal (l i) < ereal x) sequentially"
      using l(4) `a < ereal x` by (rule order_tendstoD)
    moreover 
    have "eventually (\<lambda>i. ereal x < ereal (u i)) sequentially"
      using u(4) `ereal x< b` by (rule order_tendstoD)
    ultimately have "eventually (\<lambda>i. l i < x \<and> x < u i) sequentially"
      by eventually_elim auto
    then show "\<exists>i. l i \<le> x \<and> x \<le> u i"
      by (auto intro: less_imp_le simp: eventually_sequentially)
  next
    fix x i assume "l i \<le> x" "x \<le> u i" 
    with `a < ereal (l i)` `ereal (u i) < b`
    show "a < ereal x" "ereal x < b"
      by (auto simp del: ereal_less_eq(3) simp add: ereal_less_eq(3)[symmetric])
  qed
  show thesis
    by (intro that) fact+
qed

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
  unfolding filter_eq_iff eventually_filtermap
    eventually_at_left'[OF ereal_less(3)] eventually_at_top_dense
    eventually_at_right'[OF ereal_less(4)] eventually_at_bot_dense
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
  fixes f :: "'a \<Rightarrow> ('b::dense_linorder)"
  shows "(LIM x F. f x :> at_bot) \<longleftrightarrow> (\<forall>Z. eventually (\<lambda>x. f x < Z) F)"
  by (metis eventually_elim1[of _ F] order_less_imp_le eventually_gt_at_bot
            filterlim_at_bot[of f F] filterlim_iff[of f at_bot F]) (* FIXME! *)

lemma ereal_tendsto_simps2:
  "((ereal \<circ> f) ---> ereal a) F \<longleftrightarrow> (f ---> a) F"
  "((ereal \<circ> f) ---> \<infinity>) F \<longleftrightarrow> (LIM x F. f x :> at_top)"
  "((ereal \<circ> f) ---> -\<infinity>) F \<longleftrightarrow> (LIM x F. f x :> at_bot)"
  unfolding tendsto_PInfty filterlim_at_top_dense tendsto_MInfty filterlim_at_bot_dense
  using lim_ereal by (simp_all add: comp_def)

lemmas ereal_tendsto_simps = ereal_tendsto_simps1 ereal_tendsto_simps2

definition interval_lebesgue_integral :: "real measure \<Rightarrow> ereal \<Rightarrow> ereal \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real" where
  "interval_lebesgue_integral M a b f = (if a \<le> b
    then (\<integral>x. f x * indicator (einterval a b) x \<partial>M)
    else - (\<integral>x. f x * indicator (einterval b a) x \<partial>M))"

definition interval_lebesgue_integrable :: "real measure \<Rightarrow> ereal \<Rightarrow> ereal \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> bool" where
  "interval_lebesgue_integrable M a b f = (if a \<le> b
    then integrable M (\<lambda>x. f x * indicator (einterval a b) x)
    else integrable M (\<lambda>x. f x * indicator (einterval b a) x))"

syntax
  "_interval_lebesgue_borel_integral" :: "pttrn \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
  ("(4LBINT _=_.._. _)" [0,60,60,61] 60)

translations
  "LBINT x=a..b. f" == "CONST interval_lebesgue_integral CONST lborel (CONST ereal a) (CONST ereal b) (\<lambda>x. f)"

lemma interval_integral_FTC_nonneg:
  fixes f F :: "real \<Rightarrow> real" and a b :: ereal
  assumes "a < b"
  assumes F: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> DERIV F x :> f x" 
  assumes f: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> isCont f x" 
  assumes f_nonneg: "AE x in lborel. a < ereal x \<longrightarrow> ereal x < b \<longrightarrow> 0 \<le> f x"
  assumes T: "((F \<circ> real) ---> T) (at_right a)"
  assumes B: "((F \<circ> real) ---> B) (at_left b)"
  shows "interval_lebesgue_integral lborel a b f = B - T"
proof -
  from einterval_Icc_approximation[OF `a < b`] guess u l . note approx = this
  have "integral\<^isup>L lborel (\<lambda>x. f x * indicator (einterval a b) x) = B - T"
  proof (rule integral_monotone_convergence)
    fix i show "integrable lborel (\<lambda>x. f x * indicator {l i .. u i} x)"
      using `a < l i` `u i < b`
      by (intro borel_integrable_atLeastAtMost f)
         (auto simp del: ereal_less_eq simp add: ereal_less_eq(3)[symmetric])
  next
    from f_nonneg have "AE x in lborel. \<forall>i. l i \<le> x \<longrightarrow> x \<le> u i \<longrightarrow> 0 \<le> f x"
      by eventually_elim
         (metis approx(5) approx(6) dual_order.strict_trans1 ereal_less_eq(3) le_less_trans)
    then show "AE x in lborel. mono (\<lambda>n. f x * indicator {l n..u n} x)"
      apply eventually_elim
      apply (auto simp: mono_def split: split_indicator)
      apply (metis approx(3) decseqD order_trans)
      apply (metis approx(2) incseqD order_trans)
      done
  next
    { fix x i assume "l i \<le> x" "x \<le> u i"
      then have "eventually (\<lambda>i. l i \<le> x \<and> x \<le> u i) sequentially"
        apply (auto simp: eventually_sequentially intro!: exI[of _ i])
        apply (metis approx(3) decseqD order_trans)
        apply (metis approx(2) incseqD order_trans)
        done
      then have "eventually (\<lambda>i. f x * indicator {l i..u i} x = f x) sequentially"
        by eventually_elim auto }
    then show "AE x in lborel. (\<lambda>i. f x * indicator {l i..u i} x) ----> f x * indicator (einterval a b) x"
      unfolding approx(1) by (auto intro!: AE_I2 Lim_eventually split: split_indicator)
  next
    { fix i 
      have "(\<integral>x. f x * indicator {l i..u i} x \<partial>lborel) = F (u i) - F (l i)"
        using approx(1,4)
        by (intro integral_FTC_atLeastAtMost)
           (auto intro!: F f intro: less_imp_le simp: einterval_def set_eq_iff) }
    moreover have "(\<lambda>i. F (u i)) ----> B"
      using B approx unfolding tendsto_at_iff_sequentially comp_def
      by (elim allE[of _ "\<lambda>i. ereal (u i)"]) auto
    moreover have "(\<lambda>i. F (l i)) ----> T"
      using T approx unfolding tendsto_at_iff_sequentially comp_def
      by (elim allE[of _ "\<lambda>i. ereal (l i)"]) auto
    ultimately show "(\<lambda>i. \<integral> x. f x * indicator {l i..u i} x \<partial>lborel) ----> B - T"
      by (simp add: tendsto_intros)
  next
    have "(\<lambda>x. if x \<in> einterval a b then f x else 0) \<in> borel_measurable borel"
      by (rule borel_measurable_continuous_on_open')
         (auto simp add: continuous_on_eq_continuous_at einterval_iff f)
    also have "(\<lambda>x. if x \<in> einterval a b then f x else 0) = (\<lambda>x. f x * indicator (einterval a b) x)"
      by auto
    finally show "(\<lambda>x. f x * indicator (einterval a b) x) \<in> borel_measurable lborel"
      by simp
  qed
  then show ?thesis
    using `a < b` by (simp add: interval_lebesgue_integral_def less_imp_le)
qed

thm integral_has_vector_derivative

lemma integral_substitution:
  fixes f g g':: "real \<Rightarrow> real" and a b :: ereal
  assumes "a \<le> b"
  assumes deriv_g: "!!x. x \<in> einterval a b \<Longrightarrow> (g has_vector_derivative (g' x)) (at x within X)"
  assumes contf: "continuous_on (g ` einterval a b) f"
  assumes contg': "continuous_on (einterval a b) g'"
  assumes "((ereal \<circ> g \<circ> real) ---> t) (at_left a)"
  assumes "((ereal \<circ> g \<circ> real) ---> b) (at_right b)"
  shows "interval_lebesgue_integral lborel a b (\<lambda>x. (f (g x) * g' x)) = interval_lebesgue_integral lborel t b f"
sorry

(** Integral notations. **)

(* TODO: Fix precedences so parentheses are not required around integrals too
often. *)

syntax
"_ascii_lebesgue_integral" :: "pttrn \<Rightarrow> 'a measure \<Rightarrow> real \<Rightarrow> real"
("(3LINT _|_. _)" [0,110,60] 60)

translations
"LINT x|M. f" == "CONST lebesgue_integral M (\<lambda>x. f)"

syntax
"_lebesgue_borel_integral" :: "pttrn \<Rightarrow> real \<Rightarrow> real"
("(2LBINT _. _)" [0,60] 60)

translations
"LBINT x. f" == "CONST lebesgue_integral CONST lborel (\<lambda>x. f)"

(* maybe use indicator A x *\<^sub>R f x *)
abbreviation
"set_lebesgue_integral M A f \<equiv> lebesgue_integral M (\<lambda>x. f x * indicator A x)"

syntax
"_set_lebesgue_integral" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'a measure \<Rightarrow> real \<Rightarrow> real"
("(4LINT _:_|_. _)" [0,60,110,61] 60)

translations
"LINT x:A|M. f" == "CONST set_lebesgue_integral M A (\<lambda>x. f)"

syntax
"_set_lebesgue_borel_integral" :: "pttrn \<Rightarrow> real set \<Rightarrow> real \<Rightarrow> real"
("(3LBINT _:_. _)" [0,60,61] 60)

translations
"LBINT x:A. f" == "CONST set_lebesgue_integral CONST lborel A (\<lambda>x. f)"

abbreviation "set_integrable M A f \<equiv> integrable M (\<lambda>x. f x * indicator A x)"

(* abbreviation (* Maybe make a definition out of this? *)
"cmp_conn_lebesgue_integral M a b f \<equiv> (if a \<le> b then 
set_lebesgue_integral M {a..b} f else - set_lebesgue_integral M {b..a} f)" *)

definition interval_lebesgue_integral :: "real measure \<Rightarrow> ereal \<Rightarrow> ereal \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real" where
  "interval_lebesgue_integral M a b f \<equiv>
    (if a \<le> b then set_lebesgue_integral M {r. a \<le> ereal r \<and> ereal r \<le> b} f
               else - set_lebesgue_integral M {r. b \<le> ereal r \<and> ereal r \<le> a} f)"

syntax
  "_interval_lebesgue_integral" ::
  "pttrn \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real measure \<Rightarrow> real \<Rightarrow> real"
  ("(5LINT _=_.._|_. _)" [0,60,60,110,61] 60)

translations
  "LINT x=a..b|M. f" == "CONST interval_lebesgue_integral M (CONST ereal a) (CONST ereal b) (\<lambda>x. f)"

syntax
  "_interval_lebesgue_integral_Iic" ::
  "pttrn \<Rightarrow> real \<Rightarrow> real measure \<Rightarrow> real \<Rightarrow> real"
  ("(5LINT _ \<le> _|_. _)" [0,60,110,61] 60)

translations
  "LINT x \<le> b|M. f" == "CONST interval_lebesgue_integral M (CONST uminus (CONST infinity)) (CONST ereal b) (\<lambda>x. f)"

syntax
  "_interval_lebesgue_integral_Iic" ::
  "pttrn \<Rightarrow> real \<Rightarrow> real measure \<Rightarrow> real \<Rightarrow> real"
  ("(5LINT _ \<ge> _|_. _)" [0,60,110,61] 60)

translations
  "LINT x \<ge> a|M. f" == "CONST interval_lebesgue_integral M (CONST ereal a) (CONST infinity) (\<lambda>x. f)"

syntax
  "_interval_lebesgue_borel_integral" :: "pttrn \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
  ("(4LBINT _=_.._. _)" [0,60,60,61] 60)

translations
  "LBINT x=a..b. f" == "CONST interval_lebesgue_integral CONST lborel (CONST ereal a) (CONST ereal b) (\<lambda>x. f)"

(* LBINT x < a. f x, LBINT x > b. f x, LBINT x = a .. b. f x *)
(* LINT x < a | M. f x, LINT x = a .. b | M. f x, LINT x > b | M. f x *)

(***** Almost Everywhere on a Set. *****)
abbreviation
  "set_almost_everywhere A M P \<equiv> AE x in M. x \<in> A \<longrightarrow> P x"

syntax
  "_set_almost_everywhere" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> bool"
("AE _\<in>_ in _. _" [0,0,0,10] 10)

translations
  "AE x\<in>A in M. P" == "CONST set_almost_everywhere A M (\<lambda>x. P)"

(** General Lebesgue integration. **)

lemma set_integrable_Un:
  assumes "set_integrable M A f" "set_integrable M B f"
  shows "set_integrable M (A \<union> B) f"
  using integrable_max
  sorry
  (* This gets it in development version? *)
  (*by (auto simp add: indicator_union_arith indicator_inter_arith[symmetric]
      distrib_left assms)*)

lemma set_integrable_UN:
  assumes "finite I" "\<And>i. i\<in>I \<Longrightarrow> set_integrable M (A i) f"
  shows "set_integrable M (\<Union>i\<in>I. A i) f"
  using assms
  by (induct I) (auto simp: set_integrable_Un)

lemma set_integral_Un:
  assumes "A \<inter> B = {}"
  and "set_integrable M A f"
  and "set_integrable M B f"
  shows "LINT x:A\<union>B|M. f x = (LINT x:A|M. f x) + (LINT x:B|M. f x)"
  by (auto simp add: indicator_union_arith indicator_inter_arith[symmetric]
      distrib_left assms)

lemma set_integral_finite_Union:
  assumes "finite I" "disjoint_family_on A I"
    and "\<And>i. i \<in> I \<Longrightarrow> set_integrable M (A i) f"
  shows "(LINT x:(\<Union>i\<in>I. A i)|M. f x) = (\<Sum>i\<in>I. LINT x:A i|M. f x)"
  using assms
  apply induct
  apply (auto intro!: set_integral_Un set_integrable_Un set_integrable_UN simp: disjoint_family_on_def)
  done
  sorry

lemma set_integrable_subset:
  assumes intgbl: "set_integrable M B f"
  and meas: "A \<in> sets M"
  and sub: "A \<subseteq> B"
  shows "set_integrable M A f"
  using sub apply (subst mult_indicator_subset[symmetric])
  apply simp
  apply (subst mult_commute) back
  apply (subst mult_assoc[symmetric])
  apply (rule integrable_mult_indicator)
  by (auto intro: assms)

lemma set_integral_cmult:
  assumes "set_integrable M A f"
  shows "set_integrable M A (\<lambda>t. a * f t)"
  and "LINT t:A|M. a * f t = a * (LINT t:A|M. f t)"
  (* Expressions which are the same up to rearrangement of parentheses should be easier to identify. *)
  apply (subst mult_assoc)
  apply (auto intro: integral_cmult assms)
  apply (subst mult_assoc)
  by (auto intro: integral_cmult assms)

(**
(* Generalize to more measures and more change-of-variable functions. *)
lemma lborel_cont_diff_change_variable:
  fixes a b :: real
  assumes "a \<le> b"
  and "\<And>x. x\<in>{a..b} \<Longrightarrow> g x \<in> {(g a)..(g b)} \<and> isCont g' x \<and> DERIV g x :> g' x"
  and "g a \<le> g b"
  and "\<And>x. x \<in> {(g a)..(g b)} \<Longrightarrow> DERIV F x :> f x"
  and "\<And>x. x \<in> {(g a)..(g b)} \<Longrightarrow> isCont f x"
  shows "LINT x:a..b|lborel. f (g x) * g' x = LINT y:(g a)..(g b)|lborel. f y"
proof-
  have "\<forall>x \<in> {a..b}. isCont (\<lambda>x. f (g x) * g' x) x"
  proof-
    have isCont_comp: "\<forall>x \<in> {a..b}. isCont f (g x)" using assms by auto
    have isCont_g: "\<forall>x \<in> {a..b}. isCont g x"
      using assms DERIV_isCont by blast
    hence "\<forall>x \<in> {a..b}. isCont (\<lambda>x. f (g x)) x"
      using isCont_comp isCont_g isCont_o2 by blast
    thus ?thesis using assms by simp
  qed
  hence "LINT x:a..b|lborel. f (g x) * g' x = (F o g) b - (F o g) a"
    using assms integral_FTC_atLeastAtMost[of a b "(F o g)"
      "\<lambda>x. f (g x) * g' x"] by (auto intro!: DERIV_chain)
  thus ?thesis using assms integral_FTC_atLeastAtMost[of "g a" "g b" F f]
    by auto
qed
**)

lemma pos_integrable_to_top:
  fixes l::real
  assumes "\<And>i. A i \<in> sets M" "mono A"
  assumes nneg: "\<And>x i. x \<in> A i \<Longrightarrow> 0 \<le> f x"
  and intgbl: "\<And>i::nat. set_integrable M (A i) f"
  and lim: "(\<lambda>i::nat. LINT x:A i|M. f x) ----> l"
  shows "set_integrable M (\<Union>i. A i) f"
  apply (rule integral_monotone_convergence_pos[where f = "\<lambda>i::nat. \<lambda>x. f x * indicator (A i) x" and x = l])
  apply (rule intgbl)
  prefer 4 apply (rule lim)
  apply (rule AE_I2)
  using `mono A` apply (auto simp: mono_def nneg split: split_indicator) []
  apply (auto intro!: AE_I2 nneg split: split_indicator) []
proof (rule AE_I2)
  { fix x assume "x \<in> space M"
    show "(\<lambda>i. f x * indicator (A i) x) ----> f x * indicator (\<Union>i. A i) x"
    proof cases
      assume "\<exists>i. x \<in> A i"
      then guess i ..
      then have *: "eventually (\<lambda>i. x \<in> A i) sequentially"
        using `x \<in> A i` `mono A` by (auto simp: eventually_sequentially mono_def)
      show ?thesis
        apply (intro Lim_eventually)
        using *
        apply eventually_elim
        apply (auto split: split_indicator)
        done
    qed auto }
  then show "(\<lambda>x. f x * indicator (\<Union>i. A i) x) \<in> borel_measurable M"
    by (rule borel_measurable_LIMSEQ) (auto intro: borel_measurable_integrable intgbl)
qed

lemma set_integrable_abs: "set_integrable M A f \<Longrightarrow> set_integrable M A (\<lambda>x. \<bar>f x\<bar>)"
  using integrable_abs[of M "\<lambda>x. f x * indicator A x"] by (simp add: abs_mult)

(* Proof from Royden Real Analysis, p. 91. *)
lemma lebesgue_integral_countable_add:
  assumes meas[intro]: "\<And>i::nat. A i \<in> sets M"
  and disj: "\<And>i j. i \<noteq> j \<Longrightarrow> A i \<inter> A j = {}"
  and intgbl: "set_integrable M (\<Union>i. A i) f"
  shows "LINT x:(\<Union>i. A i)|M. f x = (\<Sum>i. (LINT x:(A i)|M. f x))"
  apply (subst integral_sums(2)[THEN sums_unique, symmetric])
  apply (rule set_integrable_subset[OF intgbl])
  apply auto []
  apply auto []
proof -
  { fix x assume "x \<in> space M"
    have "(\<lambda>i. indicator (A i) x::real) sums (if \<exists>i. x \<in> A i then 1 else (0::real))"
    proof auto
      fix i assume "x \<in> A i"
      then have "\<And>j. j \<noteq> i \<Longrightarrow> indicator (A j) x = (0::real)"
        using disj[of _ i] by (auto split: split_indicator)
      with `x \<in> A i` have "(\<lambda>i. indicator (A i) x) sums (\<Sum>j\<in>{i}. indicator (A j) x)"
        by (intro sums_finite) (auto dest!: disj split: split_indicator)
      then show "(\<lambda>i. indicator (A i) x) sums 1"
        using `x \<in> A i` by simp
    qed }
  note sums = this
  from sums_summable[OF this]
  show "\<And>x. x \<in> space M \<Longrightarrow> summable (\<lambda>i. \<bar>f x * indicator (A i) x\<bar>)"
    by (simp add: abs_mult summable_mult)

  show "summable (\<lambda>i. LINT x|M. \<bar>f x * indicator (A i) x\<bar>)"
  proof (rule pos_summable)
    fix n
    show "0 \<le> LINT x|M. \<bar>f x * indicator (A n) x\<bar>"
      by (auto intro!: lebesgue_integral_nonneg)
    have "(\<Sum>i = 0..<n. LINT x|M. \<bar>f x * indicator (A i) x\<bar>) =
      (\<Sum>i = 0..<n. set_lebesgue_integral M (A i) (\<lambda>x. \<bar>f x\<bar>))"
      by (simp add: abs_mult)
    also have "\<dots> = set_lebesgue_integral M (\<Union>i<n. A i) (\<lambda>x. \<bar>f x\<bar>)"
      apply (subst set_integral_finite_Union)
      apply (auto simp: disjoint_family_on_def disj atLeast0LessThan
                  intro!: set_integrable_abs)
      apply (rule set_integrable_subset[OF intgbl])
      apply auto
      done
    also have "\<dots> \<le> set_lebesgue_integral M (\<Union>i. A i) (\<lambda>x. \<bar>f x\<bar>)"
      apply (intro integral_mono set_integrable_abs intgbl)
      apply (rule integrable_bound[OF intgbl[THEN  set_integrable_abs]])
      apply (auto intro!: AE_I2 split: split_indicator)
      apply (rule borel_measurable_integrable)
      apply (rule set_integrable_subset[OF intgbl])
      apply auto
      done
    finally show "(\<Sum>i = 0..<n. LINT x|M. \<bar>f x * indicator (A i) x\<bar>) \<le>
      set_lebesgue_integral M (\<Union>i. A i) (\<lambda>x. \<bar>f x \<bar>)"
      by simp
  qed
  show "set_lebesgue_integral M (UNION UNIV A) f = LINT x|M. (\<Sum>i. f x * indicator (A i) x)"
    apply (rule integral_cong)
    apply (subst suminf_mult[OF sums_summable[OF sums]])
  proof -
    fix x assume x: "x \<in> space M"
    from sums_unique[OF sums, OF this, symmetric]
    have "indicator (UNION UNIV A) x = (\<Sum>i. indicator (A i) x :: real)"
      by (simp split: split_indicator)
    then show "f x * indicator (UNION UNIV A) x = f x * (\<Sum>i. indicator (A i) x)"
      by simp
  qed
qed

lemma set_integral_cont_up:
  assumes A: "\<And>i. A i \<in> sets M" "incseq A"
  and intgbl: "set_integrable M (\<Union>i. A i) f"
  shows "(\<lambda>i. LINT x:(A i)|M. f x) ----> LINT x:(\<Union>i. A i)|M. f x"
proof (intro integral_dominated_convergence[of M
    "\<lambda>i. \<lambda>x. f x * indicator (A i) x"
    "\<lambda>x. \<bar>f x\<bar> * indicator (\<Union>i. A i) x"
    "\<lambda>x. f x * indicator (\<Union>i. A i) x"])
  fix i::nat show "set_integrable M (A i) f"
    using set_integrable_subset[where A = "A i" and B = "\<Union>i. A i"] A intgbl by auto
next
  fix j::nat show "AE x in M. \<bar>f x * indicator (A j) x\<bar> \<le>
    \<bar>f x\<bar> * indicator (\<Union>i. A i) x"
    apply (rule AE_I2)
    apply (subst abs_mult)
    apply (case_tac "x \<in> A j")
    apply simp
    apply (subgoal_tac "x \<in> (\<Union>i. A i)")
    apply simp apply auto
    apply (case_tac "x \<in> (\<Union>i. A i)")
    by simp_all
next
  show "set_integrable M (\<Union>i. A i) (\<lambda>x. \<bar>f x\<bar>)"
    apply (subst indicator_abs_eq[symmetric])
    apply (subst abs_mult[symmetric])
    apply (rule integrable_abs)
    using assms by auto
next
  show "AE x in M. (\<lambda>i. f x * indicator (A i) x) ---->
    f x * indicator  (\<Union>i. A i) x"
    proof (rule AE_I2)
    fix x
    assume Mx: "x \<in> space M"
    show "(\<lambda>i. f x * indicator (A i) x) ---->
      f x * indicator (\<Union>i. A i) x"
      apply (rule tendsto_mult, auto)
      apply (rule increasing_LIMSEQ)
      unfolding indicator_def using assms A by (auto simp: incseq_Suc_iff)
  qed
next
  show "(\<lambda>x. f x * indicator (\<Union>i. A i) x) \<in> borel_measurable M"
    unfolding integrable_def using assms by simp
qed
        
(* Can the int0 hypothesis be dropped? *)
lemma set_integral_cont_down:
  assumes A: "\<And>i. A i \<in> sets M" "decseq A"
  and int0: "set_integrable M (A 0) f"
  shows "(\<lambda>i::nat. LINT x:(A i)|M. f x) ----> LINT x:(\<Inter>i. A i)|M. f x"
proof (rule integral_dominated_convergence(3))
  have A_super: "\<And>i. A i \<subseteq> A 0"
    using A by (auto simp add: decseq_def)
  with A show int: "\<And>i. set_integrable M (A i) f"
    by (intro set_integrable_subset[OF int0]) auto
  show "set_integrable M (A 0) (\<lambda>x. \<bar>f x\<bar>)"
    using int0 by (rule set_integrable_abs)
  show "\<And>j. AE x in M. \<bar>f x * indicator (A j) x\<bar> \<le> \<bar>f x\<bar> * indicator (A 0) x"
    using A_super by (auto simp: abs_mult split: split_indicator)
  { fix x assume "x \<in> space M"
    have "(\<lambda>i. f x * indicator (A i) x) ----> f x * indicator (\<Inter>i. A i) x"
      apply (intro tendsto_intros)
      apply (cases "\<forall>i. x \<in> A i")
      apply auto
      apply (rule decreasing_tendsto)
      apply (simp_all add: eventually_sequentially)
      apply (rule_tac x=i in exI)
      using `decseq A`
      apply (auto split: split_indicator simp: decseq_def)
      done }
  note LIMSEQ = this
  then show "AE x in M. (\<lambda>i. f x * indicator (A i) x) ----> f x * indicator (\<Inter>i. A i) x"
    by simp
  show "(\<lambda>x. f x * indicator (\<Inter>i. A i) x) \<in> borel_measurable M"
    using LIMSEQ by (rule borel_measurable_LIMSEQ) (auto intro: borel_measurable_integrable int)
qed

lemma set_AE_func_int_eq:
  assumes "AE x \<in> A in M. f x = g x"
  shows "LINT x:A|M. f x = LINT x:A|M. g x"
proof-
  have "AE x in M. f x * indicator A x = g x * indicator A x"
    using assms by auto
  thus ?thesis using integral_cong_AE by metis
qed

lemma integral_at_point:
  fixes a :: real
  assumes "set_integrable M {a} f"
  and "{a} \<in> sets M" and "(emeasure M) {a} \<noteq> \<infinity>"
  shows "LINT x=a..a|M. f x = f a * real (emeasure M {a})"
proof-
  have eq: "{r. a \<le> r \<and> r \<le> a} = {a}" by auto
  have int_at: "LINT x:{a}|M. f x = LINT x:{a}|M. f a"
    by (metis (full_types) indicator_simps(2) mult_zero_right singletonE)
  also have "... = f a * real (emeasure M {a})" using assms by auto
  finally show ?thesis using int_at by (simp add: interval_lebesgue_integral_def eq)
qed

lemma integral_limits_inter_neg:
  fixes a b :: real
  assumes "a \<noteq> b"
  shows "LINT x=b..a|M. f x = -(LINT x=a..b|M. f x)"
  using assms by (auto simp: interval_lebesgue_integral_def)

(** Derivatives and integrals for CLT. **)

lemma exp_alpha_at_top:
  assumes pos: "0 < x"
  shows "LIM (u::real) at_top. exp (u * x) :> at_top"
  apply (rule filterlim_compose[of exp at_top at_top "\<lambda>u. u * x" at_top])
  apply (rule exp_at_top)
  apply (subst mult_commute)
  apply (rule filterlim_at_top_at_top[where Q = "\<lambda>x. True" and P = "\<lambda>x. True" and g = "op * (1/x)"])
  apply (rule mult_left_mono)
  apply simp apply (smt pos) apply simp
  apply (smt pos)
  apply simp
  by auto

lemma "((F \<circ> real) ---> T) (at_left (ereal a)) \<longleftrightarrow> (F ---> T) (at_left a)"
  sorry

lemma "((F \<circ> real) ---> T) (at_left \<infinity>) \<longleftrightarrow> (F ---> T) at_top"
  sorry

lemma "((F \<circ> real) ---> T) (at_left (-\<infinity>)) \<longleftrightarrow> (F ---> T) at_bot"
  sorry

lemma "((ereal \<circ> f) ---> ereal a) F \<longleftrightarrow> (f ---> a) F"
  sorry

lemma "((ereal \<circ> f) ---> \<infinity>) F \<longleftrightarrow> (LIM x F. f x :> at_top)"
  sorry

lemma "((ereal \<circ> f) ---> -\<infinity>) F \<longleftrightarrow> (LIM x F. f x :> at_bot)"
  sorry

definition "eint a b = {x. a \<le> ereal x \<and> ereal x \<le> b}"

lemma "eint (ereal a) (ereal b) = {a .. b}"
  by (auto simp: eint_def)

lemma integral_substitution:
  fixes f g g':: "real \<Rightarrow> real" and a b :: ereal
  assumes "a \<le> b"
  assumes deriv_g: "!!x. x \<in> eint a b \<Longrightarrow> (g has_vector_derivative (g' x)) (at x within X)"
  assumes contf: "continuous_on (g ` eint a b) f"
  assumes contg': "continuous_on (eint a b) g'"
  assumes "((ereal \<circ> g \<circ> real) ---> t) (at_left a)"
  assumes "((ereal \<circ> g \<circ> real) ---> b) (at_right b)"
  shows "interval_lebesgue_integral lborel a b (\<lambda>x. (f (g x) * g' x)) = interval_lebesgue_integral lborel t b f"
sorry

lemma interval_integral_FTC:
  fixes f F :: "real \<Rightarrow> real" and a b :: ereal
  assumes "a \<le> b"
  assumes f_borel: "f \<in> borel_measurable borel"
  assumes f: "\<And>x. a \<le> ereal x \<Longrightarrow> ereal x \<le> b \<Longrightarrow> DERIV F x :> f x" 
  assumes nonneg: "\<And>x. a \<le> ereal x \<Longrightarrow> ereal x \<le> b \<Longrightarrow> 0 \<le> f x"
  assumes T: "((F \<circ> real) ---> T) (at_left a)"
  assumes B: "((F \<circ> real) ---> B) (at_right b)"
  shows "interval_lebesgue_integral lborel a b f = T - B"
sorry

lemma interval_integrable_FTC:
  fixes f F :: "real \<Rightarrow> real" and a b :: ereal
  assumes "a \<le> b"
  assumes f_borel: "f \<in> borel_measurable borel"
  assumes f: "\<And>x. a \<le> ereal x \<Longrightarrow> ereal x \<le> b \<Longrightarrow> DERIV F x :> f x" 
  assumes nonneg: "\<And>x. a \<le> ereal x \<Longrightarrow> ereal x \<le> b \<Longrightarrow> 0 \<le> f x"
  assumes T: "((F \<circ> real) ---> T) (at_left a)"
  assumes B: "((F \<circ> real) ---> B) (at_right b)"
  shows "interval_lebesgue_integrable lborel a b f"
sorry

lemma positive_integral_eq_erealD:
  assumes "integral\<^isup>P M f = ereal x"
  assumes "f \<in> borel_measurable M"
  assumes "AE x in M. 0 \<le> f x"
  shows "integrable M f" "integral\<^isup>L M f = x"
  apply (metis PInfty_neq_ereal(1) integrable_nonneg assms)
  by (metis PInfty_neq_ereal(1) assms(1) assms(2) assms(3) integrable_nonneg positive_integral_eq_integral real_of_ereal(2))

(* Should be easier to conclude integrability from calculation of an integral. *)
(* Adapted from proof in Distributions.thy. *)
lemma integral_expneg_alpha_atMost0:
  fixes x::real
  assumes pos: "0 < u"
  shows "LBINT x:{0..}. exp (- (x * u)) = 1/u" (is "?eq")
  and "set_integrable lborel {0..} (\<lambda>x. exp (- (x * u)))" (is ?int)
proof -
  have "(\<integral>\<^isup>+ x. ereal (exp (- (x * u)) * indicator {0..} x) \<partial>lborel) =
    (\<integral>\<^isup>+ x. ereal (exp (- (x * u))) * indicator {0..} x \<partial>lborel)"
    by (intro positive_integral_cong) (auto split: split_indicator)
  also have "\<dots> = ereal (0 - (- 1 / u * exp (- u * 0)))"
    apply (rule positive_integral_FTC_atLeast[where F="\<lambda>x. - 1 / u * exp (- u * x)"])
    apply measurable
    using `0 < u`
    apply (auto intro!: DERIV_intros)
    apply (rule tendsto_eq_intros)
    apply (subst filterlim_at_top_mirror)
    apply (rule tendsto_eq_intros)
    apply (rule filterlim_compose[of exp])
    apply (rule exp_at_bot)
    apply simp_all
    apply (rule filterlim_tendsto_pos_mult_at_bot)
    apply (rule tendsto_const)
    apply (rule `0 < u`)
    apply (rule filterlim_ident)
    apply auto
    done
  finally have *: "(\<integral>\<^isup>+x. ereal (exp (- (x * u)) * indicator {0..} x) \<partial>lborel) = ereal (1 / u)"
    by simp

  show ?eq
    by (rule positive_integral_eq_erealD[OF *]) (simp_all add: mult_nonneg_nonneg)
  show ?int
    by (rule positive_integral_eq_erealD[OF *]) (simp_all add: mult_nonneg_nonneg)
qed

lemma Collect_eq_Icc: "{r. t \<le> r \<and> r \<le> b} = {t .. b}"
  by auto

(* From Billingsley section 18. *)
lemma ex_18_4_1_deriv: "DERIV (\<lambda>x. (1/(1+u^2)) * (1 - exp (-u * x) *
(u * sin x + cos x))) x :> exp (-u * x) * sin x"
  apply (auto intro!: DERIV_intros)
  apply (simp_all add: power2_eq_square field_simps)
  by (metis mult_zero_left not_square_less_zero square_bound_lemma)+

lemma ex_18_4_1:
  assumes "t \<ge> 0"
  shows "LBINT x=0..t. exp (-u * x) * sin x = (1/(1+u^2)) *
  (1 - exp (-u * t) * (u * sin t + cos t))"
  unfolding interval_lebesgue_integral_def
  using integral_FTC_atLeastAtMost[of 0 t "\<lambda>x. (1/(1+u^2)) *
    (1 - exp (-u * x) * (u * sin x + cos x))" "\<lambda>x. exp (-u * x) * sin x"]
    ex_18_4_1_deriv assms by (simp add:  Collect_eq_Icc)

lemma ex_18_4_2_deriv:
  "DERIV (\<lambda>u. 1/x * (1 - exp (-u * x)) * \<bar>sin x\<bar>) u :> \<bar>exp (-u * x) * sin x\<bar>"
  apply (auto simp only: intro!: DERIV_intros)
  by (simp add: abs_mult)

lemma ex_18_4_2_bdd_integral:
  assumes "s \<ge> 0"
  shows "LBINT u=0..s. \<bar>exp (-u * x) * sin x\<bar> =
  1/x * (1 - exp (-s * x)) * \<bar>sin x\<bar>"
using integral_FTC_atLeastAtMost[of 0 s "\<lambda>u. 1/x * (1 - exp (-u * x)) * \<bar>sin x\<bar>" "\<lambda>u. \<bar>exp (-u * x) * sin x\<bar>"] assms
ex_18_4_2_deriv by simp

lemma ex_18_4_2_ubdd_integral:
  fixes x
  assumes pos: "0 < x"
  shows "LBINT u:{0..}. \<bar>exp (-(u * x)) * sin x\<bar> = \<bar>sin x\<bar> / x" (is "LBINT u:{0..}. ?f u = ?sx")
  apply (subst abs_mult)
  apply (subst mult_commute) back
  (* Would be nice not to need to do this explicitly. *)
  apply (subst divide_inverse)
  apply (subst inverse_eq_divide)
  apply (subst integral_expneg_alpha_atMost0[symmetric], rule pos)
  (* Automated tools should get this. *)
  apply (subst mult_assoc)
  apply (subst integral_cmult(2), simp_all)
  (* Want a theorem which says that if we can calculate the integral of something, it is integrable. *)
      

definition sinc :: "real \<Rightarrow> real" where
"sinc t \<equiv> LBINT x:0..t. sin x / x"

lemma sinc_at_top: "(sinc ---> \<pi>/2) at_top"
  sorry

lemma Billingsley_26_15:
  assumes "T \<ge> 0"
  shows "\<And>\<theta>. LBINT t:0..T. sin (t * \<theta>) / t = sgn \<theta> * sinc (T * \<bar>\<theta>\<bar>)"
  sorry

end