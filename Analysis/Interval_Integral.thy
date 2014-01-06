(*
Theory: Interval_Integral.thy
Authors: Jeremy Avigad, Johannes Hölzl, Luke Serafin 

Lebesgue integral over an interval (with endpoints possibly +-\<infinity>)
*)

theory Interval_Integral
  imports Probability Set_Integral
begin

(* 
    Things that belong somewhere else 
*)

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

lemma einterval_nonempty: "a < b \<Longrightarrow> \<exists>c. c \<in> einterval a b"
  by (cases a b rule: ereal2_cases, auto simp: einterval_def intro!: dense gt_ex lt_ex)

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
    eventually_at_right'[OF ereal_less(4)] eventually_at_bot_dense sorry
    (* The following failed: by (auto simp add: ereal_all_split ereal_ex_split) *)

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

(* 
    Approximating a (possibly infinite) interval
*)

lemma ereal_incseq_approx:
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

lemma ereal_decseq_approx:
  fixes a b :: ereal
  assumes "a < b"
  obtains X :: "nat \<Rightarrow> real" where 
    "decseq X" "\<And>i. a < X i" "\<And>i. X i < b" "X ----> a"
proof -
  have "-b < -a" using `a < b` by simp
  from ereal_incseq_approx[OF this] guess X .
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
  from ereal_incseq_approx[OF `c < b`] guess u . note u = this
  from ereal_decseq_approx[OF `a < c`] guess l . note l = this
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

(*
    Notation for integration wrt lebesgue measure on the reals:

      LBINT x. f
      LBINT x : A. f
      LBINT x=a..b. f

    In the last one, a and b are ereals, so they can be \<infinity> or -\<infinity>.

    TODO: keep all these? Need unicode.
*)

syntax
"_lebesgue_borel_integral" :: "pttrn \<Rightarrow> real \<Rightarrow> real"
("(2LBINT _. _)" [0,60] 60)

translations
"LBINT x. f" == "CONST lebesgue_integral CONST lborel (\<lambda>x. f)"

syntax
"_set_lebesgue_borel_integral" :: "pttrn \<Rightarrow> real set \<Rightarrow> real \<Rightarrow> real"
("(3LBINT _:_. _)" [0,60,61] 60)

translations
"LBINT x:A. f" == "CONST set_lebesgue_integral CONST lborel A (\<lambda>x. f)"

(* TODO: in this definition, it would be more natural if einterval a b included a and b when 
   they are real. *)
definition interval_lebesgue_integral :: "real measure \<Rightarrow> ereal \<Rightarrow> ereal \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real" where
  "interval_lebesgue_integral M a b f = (if a \<le> b
    then (\<integral>x. f x * indicator (einterval a b) x \<partial>M)
    else - (\<integral>x. f x * indicator (einterval b a) x \<partial>M))"

definition interval_lebesgue_integrable :: "real measure \<Rightarrow> ereal \<Rightarrow> ereal \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> bool" where
  "interval_lebesgue_integrable M a b f = (if a \<le> b
    then integrable M (\<lambda>x. f x * indicator (einterval a b) x)
    else integrable M (\<lambda>x. f x * indicator (einterval b a) x))"

syntax
  "_ascii_interval_lebesgue_borel_integral" :: "pttrn \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
  ("(4LBINT _=_.._. _)" [0,60,60,61] 60)

translations
  "LBINT x=a..b. f" == "CONST interval_lebesgue_integral CONST lborel a b (\<lambda>x. f)"

(*
    Basic properties of integration over an interval.
*)

lemma interval_lebesgue_integral_add [intro, simp]: 
  fixes M a b f 
  assumes "interval_lebesgue_integrable M a b f"
    "interval_lebesgue_integrable M a b g"
  shows "interval_lebesgue_integrable M a b (\<lambda>x. f x + g x)" and 
    "interval_lebesgue_integral M a b (\<lambda>x. f x + g x) = 
   interval_lebesgue_integral M a b f + interval_lebesgue_integral M a b g"
using assms by (auto simp add: interval_lebesgue_integral_def interval_lebesgue_integrable_def 
    field_simps)

lemma interval_lebesgue_integral_diff [intro, simp]: 
  fixes M a b f 
  assumes "interval_lebesgue_integrable M a b f"
    "interval_lebesgue_integrable M a b g"
  shows "interval_lebesgue_integrable M a b (\<lambda>x. f x - g x)" and 
    "interval_lebesgue_integral M a b (\<lambda>x. f x - g x) = 
   interval_lebesgue_integral M a b f - interval_lebesgue_integral M a b g"
using assms by (auto simp add: interval_lebesgue_integral_def interval_lebesgue_integrable_def 
    field_simps)

lemma interval_lebesgue_integral_cmult [intro, simp]:
   fixes M a b c f 
  assumes "interval_lebesgue_integrable M a b f"
  shows "interval_lebesgue_integrable M a b (\<lambda>x. c * f x)" and 
    "interval_lebesgue_integral M a b (\<lambda>x. c * f x) = 
   c * interval_lebesgue_integral M a b f"
 using assms by (auto simp add: interval_lebesgue_integral_def interval_lebesgue_integrable_def 
    field_simps)

lemma interval_lebesgue_integral_le_eq: 
  fixes a b f
  assumes "a \<le> b"
  shows "interval_lebesgue_integral M a b f = (LINT x : einterval a b | M. f x)"
using assms by (auto simp add: interval_lebesgue_integral_def)

lemma interval_lebesgue_integral_gt_eq: 
  fixes a b f
  assumes "a > b"
  shows "interval_lebesgue_integral M a b f = -(LINT x : einterval b a | M. f x)"
using assms by (auto simp add: interval_lebesgue_integral_def less_imp_le einterval_def)

(*
    Basic properties of integration over an interval wrt lebesgue measure.
*)

lemma interval_integral_const [intro, simp]:
  fixes a b c :: real
  shows "interval_lebesgue_integrable lborel a b (\<lambda>x. c)" and "LBINT x=a..b. c = c * (b - a)" 
using assms unfolding interval_lebesgue_integral_def interval_lebesgue_integrable_def einterval_eq 
by (auto simp add: integral_cmul_indicator less_imp_le field_simps)

lemma interval_integral_endpoints_same [simp]: "(LBINT x=a..a. f x) = 0"
  unfolding interval_lebesgue_integral_def einterval_def apply simp
by (cases a rule: ereal2_cases, auto)

lemma interval_integral_endpoints_reverse: "(LBINT x=a..b. f x) = -(LBINT x=b..a. f x)"
  apply (case_tac "a = b", auto)
by (case_tac "a \<le> b", auto simp add: interval_lebesgue_integral_def)

lemma interval_integral_Icc:
  fixes a b :: real
  assumes "a \<le> b" 
  shows "(LBINT x=a..b. f x) = (LBINT x : {a..b}. f x)"
  
  using assms unfolding interval_lebesgue_integral_def einterval_def apply simp
  apply (rule integral_cong_AE)
  apply (rule AE_I [where N = "{a} \<union> {b}"])
  apply (auto simp add: indicator_def)
by (metis lmeasure_eq_0 negligible_insert negligible_sing)

lemma interval_integral_Icc':
  fixes a b :: ereal
  assumes "a \<le> b"
  shows "(LBINT x=a..b. f x) = (LBINT x : {x. a \<le> ereal x \<and> ereal x \<le> b}. f x)"
using assms unfolding interval_lebesgue_integral_def einterval_def apply simp
apply (rule integral_cong_AE)
apply (cases a rule: ereal_cases, cases b rule: ereal_cases, auto)
proof -
  fix r s :: real assume rs: "r \<le> s"
  show "AE x in lborel. f x = 0 \<or> indicator {x. r < x \<and> x < s} x = indicator {x. r \<le> x \<and> x \<le> s} x"
    apply (rule AE_I[where N = "{r} \<union> {s}"])
    apply (auto simp add: indicator_def)
    by (metis lmeasure_eq_0 negligible_insert negligible_sing)
next
  fix r
  show "AE x in lborel. f x = 0 \<or> indicator (Collect (op < r)) x = indicator (Collect (op \<le> r)) x"
    apply (rule AE_I[where N = "{r}"])
    by (auto simp add: indicator_def)
next
  show "AE x in lborel. f x = 0 \<or> indicator {x. ereal x < b} x = indicator {x. ereal x \<le> b} x"
    apply (cases b rule: ereal_cases, auto)
    proof -
      fix r
      show "AE x in lborel. f x = 0 \<or> indicator {x. x < r} x = indicator {x. x \<le> r} x"
        apply (rule AE_I[where N = "{r}"])
        by (auto simp add: indicator_def)
    qed
qed

lemma interval_integral_Iic:
  fixes a b :: real
  assumes "a \<le> b" 
  shows "(LBINT x=a..b. f x) = (LBINT x : {a<..b}. f x)"
  
  using assms unfolding interval_lebesgue_integral_def einterval_def apply simp
  apply (rule integral_cong_AE)
  apply (rule AE_I [where N = "{b}"])
by (auto simp add: indicator_def)

(* TODO: other versions as well? *) (* Yes: I need the Icc' version. *)
lemma interval_integral_Iic':
  fixes a b :: ereal
  assumes "a \<le> b" 
  shows "(LBINT x=a..b. f x) = (LBINT x : {x. a < ereal x \<and> ereal x \<le> b}. f x)"
  
  using assms unfolding interval_lebesgue_integral_def einterval_def apply simp
  apply (cases b rule: ereal_cases, auto)
  apply (rule integral_cong_AE)
proof -
  fix r
  show  "AE x in lborel. f x * indicator {x. a < ereal x \<and> x < r} x =
                       f x * indicator {x. a < ereal x \<and> x \<le> r} x"
    apply (rule AE_I [where N = "{r}"])
    by (auto simp add: indicator_def)
qed

lemma interval_integral_Ici:
  fixes a b :: real
  assumes "a \<le> b" 
  shows "(LBINT x=a..b. f x) = (LBINT x : {a..<b}. f x)"
  
  using assms unfolding interval_lebesgue_integral_def einterval_def apply simp
  apply (rule integral_cong_AE)
  apply (rule AE_I [where N = "{a}"])
  by (auto simp add: indicator_def)

lemma interval_integral_sum: 
  fixes a b c :: ereal
  assumes integrable: "interval_lebesgue_integrable lborel (min a (min b c)) (max a (max b c)) f" 

  shows "(LBINT x=a..b. f x) + (LBINT x=b..c. f x) = (LBINT x=a..c. f x)"
proof -
  {
    fix a b c :: ereal
    assume local: "a \<le> b" "b \<le> c" "interval_lebesgue_integrable lborel a c f"
    from local have "(LBINT x=a..b. f x) + (LBINT x=b..c. f x) = (LBINT x=a..c. f x)"
      apply (case_tac "b = c", simp)
      apply (cases b rule: ereal_cases, auto)
      apply (subst interval_integral_Iic', assumption)
      using local apply (auto simp add: interval_lebesgue_integral_def einterval_def
        interval_lebesgue_integrable_def) [1]
      apply (subst integral_add(2) [symmetric])
      apply (erule set_integrable_subset, auto)+
      apply (metis dual_order.order_iff_strict ereal_less_eq(3) less_trans)
      apply (erule set_integrable_subset, auto)+
      apply (erule order_le_less_trans, force)
      apply (rule integral_cong)
      apply (subst ring_distribs [symmetric])
      apply (subst indicator_add)
      apply force
      apply (rule arg_cong) back
      apply (rule arg_cong) back
      apply auto
      apply (metis dual_order.order_iff_strict ereal_less_eq(3) less_trans not_le)
      by (erule order_le_less_trans, force)
  } note 1 = this
  {
    fix a b c :: ereal
    assume local: "a \<le> min b c" and
      integ: "interval_lebesgue_integrable lborel (min a (min b c)) (max a (max b c)) f"
    then have
      integ1: "interval_lebesgue_integrable lborel a (max b c) f"
      by (auto simp add: max_absorb2 min_absorb1 max_def)
    have "(LBINT x=a..b. f x) + (LBINT x=b..c. f x) + (LBINT x=c..a. f x) = 0"
      apply (case_tac "b \<le> c")
      apply (subst interval_integral_endpoints_reverse [of c a], simp)
      apply (rule 1)
      (* why aren't max_absorb1 and max_absorb2 simplifier rules? *)
      (* ereal_min and ereal_max go the wrong way when we have comparisons for the reals *)
      using local integ1 apply (auto simp del: ereal_min ereal_max 
        simp add: ereal_min [symmetric] ereal_max [symmetric] max_absorb2) [3]
      apply (subst interval_integral_endpoints_reverse [of c a], 
        subst interval_integral_endpoints_reverse [of b c], simp add: field_simps)
      apply (subst 1)
      using local integ1 by (auto simp del: ereal_min ereal_max 
        simp add: ereal_min [symmetric] ereal_max [symmetric] max_absorb1)
  } note 2 = this
  have "a \<le> min b c | b \<le> min a c | c \<le> min a b" by auto
  moreover have "a \<le> min b c \<Longrightarrow> 
      (LBINT x=a..b. f x) + (LBINT x=b..c. f x) + (LBINT x=c..a. f x) = 0"
    by (frule 2, rule integrable, auto)
  moreover have "b \<le> min a c \<Longrightarrow> 
      (LBINT x=a..b. f x) + (LBINT x=b..c. f x) + (LBINT x=c..a. f x) = 0"
    apply (frule 2)
    (* the ac rules for min and max should be added to the simplifier, no? *)
    using integrable by (auto simp add: min.commute min.left_commute min.assoc
      max.commute max.left_commute max.assoc interval_integral_endpoints_reverse [of c a]
      interval_integral_endpoints_reverse [of b a] 
      interval_integral_endpoints_reverse [of c b])
  moreover have "c \<le> min a b \<Longrightarrow> 
      (LBINT x=a..b. f x) + (LBINT x=b..c. f x) + (LBINT x=c..a. f x) = 0"
    apply (frule 2)
    using integrable by (auto simp add: min.commute min.left_commute min.assoc
      max.commute max.left_commute max.assoc)
  ultimately have "(LBINT x=a..b. f x) + (LBINT x=b..c. f x) + (LBINT x=c..a. f x) = 0"
    by blast
  thus ?thesis
    by (simp add: interval_integral_endpoints_reverse [of c a])
qed

lemma interval_integrable_isCont:
  fixes a b :: real and f
  assumes "a \<le> b" and "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> isCont f x"
  shows "interval_lebesgue_integrable lborel a b f"
using assms unfolding interval_lebesgue_integrable_def apply simp
  by (rule set_integrable_subset, rule borel_integrable_atLeastAtMost [of a b], auto)

lemma set_borel_integral_eq_integral:
  fixes M S
  assumes "set_integrable lborel S f"
  shows "f integrable_on S" "LINT x : S | lborel. f x = integral S f"
proof -
  let ?f = "\<lambda>x. f x * indicator S x"
  have "(?f has_integral LINT x : S | lborel. f x) UNIV"
    by (rule borel_integral_has_integral, rule assms)
  hence 1: "(f has_integral (set_lebesgue_integral lborel S f)) S"
    apply (subst has_integral_restrict_univ [symmetric])
    apply (rule has_integral_eq)
    by auto
  thus "f integrable_on S"
    by (auto simp add: integrable_on_def)
  with 1 have "(f has_integral (integral S f)) S"
    by (intro integrable_integral, auto simp add: integrable_on_def)
  thus "LINT x : S | lborel. f x = integral S f"
    by (intro has_integral_unique [OF 1])
qed

lemma interval_integral_eq_integral: 
  fixes a b :: real
  assumes "a \<le> b"
  assumes "set_integrable lborel {a..b} f"
  shows "LBINT x=a..b. f x = integral {a..b} f"
using assms by (auto simp add: interval_integral_Icc set_borel_integral_eq_integral)  

lemma interval_integral_eq_integral': 
  fixes a b :: ereal
  assumes "a \<le> b"
  assumes "set_integrable lborel (einterval a b) f"
  shows "LBINT x=a..b. f x = integral (einterval a b) f"
unfolding interval_lebesgue_integral_def interval_lebesgue_integrable_def using assms
by (auto simp add: set_borel_integral_eq_integral)  
  
(*
    General limit approximation arguments
*)

lemma interval_integral_Icc_approx_nonneg:
  fixes a b :: ereal
  assumes "a < b"
  fixes u l :: "nat \<Rightarrow> real"
  assumes  approx: "einterval a b = (\<Union>i. {l i .. u i})"
    "incseq u" "decseq l" "\<And>i. l i < u i" "\<And>i. a < l i" "\<And>i. u i < b"
    "l ----> a" "u ----> b"
  fixes f :: "real \<Rightarrow> real"
  assumes f_integrable: "\<And>i. set_integrable lborel {l i..u i} f"
  assumes f_nonneg: "AE x in lborel. a < ereal x \<longrightarrow> ereal x < b \<longrightarrow> 0 \<le> f x"
  assumes f_measurable: "set_borel_measurable lborel (einterval a b) f"
  assumes lbint_lim: "(\<lambda>i. LBINT x=l i.. u i. f x) ----> C"
  shows "(LBINT x=a..b. f x) = C"
proof -
  have "(LBINT x=a..b. f x) = lebesgue_integral lborel (\<lambda>x. f x * indicator (einterval a b) x)"
    using assms by (simp add: interval_lebesgue_integral_def less_imp_le)
  also have "... = C"
  proof (rule integral_monotone_convergence)
    fix i show "set_integrable lborel {l i..u i} f" by (rule f_integrable)
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
  next show "(\<lambda>i. \<integral> x. f x * indicator {l i..u i} x \<partial>lborel) ----> C"
    using lbint_lim by (simp add: interval_integral_Icc approx less_imp_le)
  next show "set_borel_measurable lborel (einterval a b) f" by (rule assms)
  qed
  finally show ?thesis .
qed

lemma interval_integral_Icc_approx_integrable:
  fixes a b :: ereal
  assumes "a < b"
  fixes u l :: "nat \<Rightarrow> real"
  assumes  approx: "einterval a b = (\<Union>i. {l i .. u i})"
    "incseq u" "decseq l" "\<And>i. l i < u i" "\<And>i. a < l i" "\<And>i. u i < b"
    "l ----> a" "u ----> b"
  fixes f :: "real \<Rightarrow> real"
  assumes f_integrable: "set_integrable lborel (einterval a b) f"
  shows "(\<lambda>i. LBINT x=l i.. u i. f x) ----> (LBINT x=a..b. f x)"
proof -
  have indicator_abs: "\<And>A x. ((indicator A x) :: real) = abs (indicator A x)"
    by (auto simp add: indicator_def)
  have 1: "integrable lborel (\<lambda>x. abs (f x) * indicator (einterval a b) x)"
    apply (subst indicator_abs, subst abs_mult [symmetric])
    by (rule integrable_abs, rule assms)
  show ?thesis
    apply (subst interval_integral_Icc, rule less_imp_le, rule approx)
    apply (simp add: interval_lebesgue_integral_le_eq less_imp_le `a < b` approx(4))
    apply (rule integral_dominated_convergence)
    prefer 5 
    apply (rule borel_measurable_integrable, rule f_integrable)
    prefer 3 apply (rule 1)
    apply (rule set_integrable_subset, rule f_integrable)
    apply (auto simp add: assms) [2]
    apply (rule AE_I2, subst abs_mult, rule mult_left_mono, subst indicator_abs [symmetric])
    apply auto
    apply (simp add: indicator_def einterval_def, auto)
    apply (rule order_less_le_trans, rule approx, auto)
    apply (rule order_le_less_trans)
    prefer 2 
    apply (rule approx, auto)
    proof -
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
    qed
qed

(*
  Some useful things, that should be moved elsewhere.
*)

lemma has_vector_derivative_within_eq_DERIV:
  "(f has_vector_derivative y) (at x within s) = (DERIV f x : s :> y)"
  unfolding has_vector_derivative_def real_scaleR_def
by (rule deriv_fderiv [symmetric])

lemma DERIV_cong':
  fixes x D and f g s t
  assumes "x \<in> s" "s \<subseteq> t" 
  and "\<And>x. x \<in> s \<Longrightarrow> f x = g x"
  and "DERIV f x : t :> D"
  shows  "DERIV g x : s :> D"

  using assms apply (auto simp add: deriv_fderiv FDERIV_def)
  apply (subst Lim_cong_within)
  prefer 5 apply (rule tendsto_within_subset [OF _ `s \<subseteq> t`])
by assumption auto

lemma DERIV_chain_within: "DERIV f x : s :> D \<Longrightarrow> DERIV g (f x) : (f ` s) :> E \<Longrightarrow> 
    DERIV (g o f) x : s :> E * D"
  apply (simp add: deriv_fderiv)
  apply (subgoal_tac "(\<lambda>x. x * (E * D)) = (\<lambda>x. x * E) o (\<lambda>x. x * D)")
by (erule ssubst, rule diff_chain_within, auto)

lemma DERIV_chain_within': "DERIV f x : s :> D \<Longrightarrow> DERIV g (f x) : (f ` s) :> E \<Longrightarrow> 
    DERIV (\<lambda>x. g (f x)) x : s :> E * D"
by (drule (1) DERIV_chain_within, simp add: comp_def)

lemma DERIV_within_subset:
  "x \<in> s \<Longrightarrow> s \<subseteq> t \<Longrightarrow> DERIV g x : t :> D \<Longrightarrow> DERIV g x : s :> D"
by (rule DERIV_cong', auto)

lemma DERIV_imp_DERIV_within:
  "x \<in> s \<Longrightarrow> DERIV g x :> D \<Longrightarrow> DERIV g x : s :> D"
by (rule DERIV_within_subset, auto)

lemma has_DERIV_within_open:
  "a \<in> s \<Longrightarrow> open s \<Longrightarrow> DERIV f a : s :> D = DERIV f a :> D"
by (simp add: deriv_fderiv, rule has_derivative_within_open)

lemma has_DERIV_within_openI:
  "a \<in> s \<Longrightarrow> open s \<Longrightarrow> DERIV f a : s :> D \<Longrightarrow> DERIV f a :> D"
by (subst (asm) has_DERIV_within_open)

lemma has_DERIV_within_closed_interval:
  "(a :: real) < x \<Longrightarrow> x < b \<Longrightarrow> DERIV f x : {a..b} :> D \<Longrightarrow> DERIV f x :> D"

  apply (rule has_DERIV_within_openI [of x "{a<..<b}"], auto)
  apply (rule DERIV_within_subset) prefer 3 
by assumption auto

(*
  A slightly stronger version of integral_FTC_atLeastAtMost and related facts, 
  with continuous_on instead of isCont

  TODO: make the older versions corollaries of these (using continuous_at_imp_continuous_on, etc.)
*)

(* compare to isCont_eq_Ub, etc. *)
lemma continuous_on_eq_Ub:
  fixes f :: "real \<Rightarrow> 'a::linorder_topology"
  shows "a \<le> b \<Longrightarrow> continuous_on {a..b} f \<Longrightarrow>
    \<exists>M. (\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> f x \<le> M) \<and> (\<exists>x. a \<le> x \<and> x \<le> b \<and> f x = M)"
  using continuous_attains_sup[of "{a .. b}" f]
  by (auto simp add: Ball_def Bex_def)

lemma continuous_on_eq_Lb:
  fixes f :: "real \<Rightarrow> 'a::linorder_topology"
  shows "a \<le> b \<Longrightarrow> continuous_on {a..b} f \<Longrightarrow>
    \<exists>M. (\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> M \<le> f x) \<and> (\<exists>x. a \<le> x \<and> x \<le> b \<and> f x = M)"
  using continuous_attains_inf[of "{a .. b}" f]
  by (auto simp add: continuous_at_imp_continuous_on Ball_def Bex_def)

lemma continuous_on_Lb_Ub:
  fixes f :: "real \<Rightarrow> real"
  assumes "a \<le> b" and contf: "continuous_on {a..b} f"
  shows "\<exists>L M. (\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> L \<le> f x \<and> f x \<le> M) \<and> 
               (\<forall>y. L \<le> y \<and> y \<le> M \<longrightarrow> (\<exists>x. a \<le> x \<and> x \<le> b \<and> (f x = y)))"
proof -
  obtain M where M: "a \<le> M" "M \<le> b" "\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> f x \<le> f M"
    using continuous_on_eq_Ub[OF assms] by auto
  obtain L where L: "a \<le> L" "L \<le> b" "\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> f L \<le> f x"
    using continuous_on_eq_Lb[OF assms] by auto
  from M L have contf': "continuous_on {M..L} f" "continuous_on {L..M} f"
    by (auto intro!: continuous_on_subset [OF contf])
  show ?thesis
    using IVT'[of f L _ M] IVT2'[of f L _ M] M L `a \<le> b`
    apply (rule_tac x="f L" in exI)
    apply (rule_tac x="f M" in exI)
    apply (cases "L \<le> M")
    apply (simp, metis order_trans contf')
    apply (simp, metis order_trans contf')
    done
qed

lemma borel_integrable_atLeastAtMost':
  fixes a b :: real
  assumes f: "continuous_on {a..b} f"
  shows "set_integrable lborel {a..b} f" (is "integrable _ ?f")
proof cases
  assume "a \<le> b"

  from continuous_on_Lb_Ub[OF `a \<le> b`, of f] f
  obtain M L where
    bounds: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> f x \<le> M" "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> L \<le> f x"
    by auto

  show ?thesis
  proof (rule integrable_bound)
    show "integrable lborel (\<lambda>x. max \<bar>M\<bar> \<bar>L\<bar> * indicator {a..b} x)"
      by (rule integral_cmul_indicator) simp_all
    show "AE x in lborel. \<bar>?f x\<bar> \<le> max \<bar>M\<bar> \<bar>L\<bar> * indicator {a..b} x"
    proof (rule AE_I2)
      fix x show "\<bar>?f x\<bar> \<le> max \<bar>M\<bar> \<bar>L\<bar> * indicator {a..b} x"
        using bounds[of x] by (auto split: split_indicator)
    qed

    let ?g = "\<lambda>x. if x = a then f a else if x = b then f b else if x \<in> {a <..< b} then f x else 0"
    from f have "continuous_on {a <..< b} f"
      by (elim continuous_on_subset, auto)
    then have "?g \<in> borel_measurable borel"
      using borel_measurable_continuous_on_open[of "{a <..< b }" f "\<lambda>x. x" borel 0]
      by (auto intro!: measurable_If[where P="\<lambda>x. x = a"] measurable_If[where P="\<lambda>x. x = b"])
    also have "?g = ?f"
      using `a \<le> b` by (intro ext) (auto split: split_indicator)
    finally show "?f \<in> borel_measurable lborel"
      by simp
  qed
qed simp

lemma integral_FTC_atLeastAtMost':
  fixes a b :: real
  assumes "a \<le> b"
    and F: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> DERIV F x : {a..b} :> f x"
    and f: "continuous_on {a..b} f"
  shows "set_lebesgue_integral lborel {a..b} f = F b - F a"
proof -
  let ?f = "\<lambda>x. f x * indicator {a .. b} x"
  have "(?f has_integral (\<integral>x. ?f x \<partial>lborel)) UNIV"
    apply (rule borel_integral_has_integral)
    by (rule borel_integrable_atLeastAtMost', rule f)
  moreover
  have 1: "(f has_integral F b - F a) {a .. b}"
    apply (rule fundamental_theorem_of_calculus, rule assms)
    apply (subst has_vector_derivative_within_eq_DERIV)
    by (auto intro!: F)
  have "(?f has_integral F b - F a) {a .. b}"
    by (rule has_integral_eq [OF _ 1], auto)
  then have "(?f has_integral F b - F a) UNIV"
    by (intro has_integral_on_superset[where t=UNIV and s="{a..b}"]) auto
  ultimately show "lebesgue_integral lborel ?f = F b - F a"
    by (rule has_integral_unique)
qed

lemma interval_integrable_continuous_on:
  fixes a b :: real and f
  assumes "a \<le> b" and "continuous_on {a..b} f"
  shows "interval_lebesgue_integrable lborel a b f"
using assms unfolding interval_lebesgue_integrable_def apply simp
  by (rule set_integrable_subset, rule borel_integrable_atLeastAtMost' [of a b], auto)

lemma continuous_image_closed_interval:
  fixes a b :: real and f :: "real \<Rightarrow> real"
  assumes "a \<le> b" "continuous_on {a..b} f"
  shows "\<exists>c d. f ` {a..b} = {c..d} \<and> c \<le> d"

  using continuous_on_Lb_Ub [OF `a \<le> b` `continuous_on {a..b} f`] apply safe
  apply (rule_tac x = L in exI)
  apply (rule_tac x = M in exI)
using `a \<le> b` by auto

(*
TODO: many proofs below require inferences like

  a < ereal x \<Longrightarrow> x < y \<Longrightarrow> a < ereal y

where x and y are real. These should be automated.
*)

(*
    The first Fundamental Theorem of Calculus

    First, for finite intervals, and then two versions for arbitrary intervals.
*)

lemma interval_integral_FTC_finite:
  fixes f F :: "real \<Rightarrow> real" and a b :: real
  assumes f: "continuous_on {min a b..max a b} f"
  assumes F: "\<And>x. min a b \<le> x \<Longrightarrow> x \<le> max a b \<Longrightarrow> DERIV F x : {min a b..max a b} :> f x" 
  shows "(LBINT x=a..b. f x) = F b - F a"

  apply (case_tac "a \<le> b")
  apply (subst interval_integral_Icc, auto intro!: 
    integral_FTC_atLeastAtMost' DERIV_within_subset [OF _ _ F] continuous_on_subset [OF f])
  apply (subst interval_integral_endpoints_reverse)
  apply (subst interval_integral_Icc, auto)
by (subst integral_FTC_atLeastAtMost', auto intro!: 
    DERIV_within_subset [OF _ _ F] continuous_on_subset [OF f])

lemma interval_integral_FTC_nonneg:
  fixes f F :: "real \<Rightarrow> real" and a b :: ereal
  assumes "a < b"
  assumes F: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> DERIV F x :> f x" 
  assumes f: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> isCont f x" 
  assumes f_nonneg: "AE x in lborel. a < ereal x \<longrightarrow> ereal x < b \<longrightarrow> 0 \<le> f x"
  assumes A: "((F \<circ> real) ---> A) (at_right a)"
  assumes B: "((F \<circ> real) ---> B) (at_left b)"
  shows "(LBINT x=a..b. f x) = B - A"
proof -
  from einterval_Icc_approximation[OF `a < b`] guess u l . note approx = this
  have [simp]: "\<And>x i. l i \<le> x \<Longrightarrow> a < ereal x"
    by (rule order_less_le_trans, rule approx, force)
  have [simp]: "\<And>x i. x \<le> u i \<Longrightarrow> ereal x < b"
    by (rule order_le_less_trans, subst ereal_less_eq(3), assumption, rule approx)
  have FTCi: "\<And>i. (LBINT x=l i..u i. f x) = F (u i) - F (l i)"
    using assms approx apply (intro interval_integral_FTC_finite)
    apply (auto simp add: less_imp_le min_def max_def)
    apply (rule continuous_at_imp_continuous_on, auto intro!: f)
    by (rule DERIV_imp_DERIV_within, auto intro!: F)
  show ?thesis
  proof (rule interval_integral_Icc_approx_nonneg [OF `a < b` approx _ f_nonneg])
    fix i show "set_integrable lborel {l i .. u i} f"
        using `a < l i` `u i < b`
        by (intro borel_integrable_atLeastAtMost f)
           (auto simp del: ereal_less_eq simp add: ereal_less_eq(3)[symmetric])
    next  
      have "(\<lambda>x. if x \<in> einterval a b then f x else 0) \<in> borel_measurable borel"
        by (rule borel_measurable_continuous_on_open')
           (auto simp add: continuous_on_eq_continuous_at einterval_iff f)
      also have "(\<lambda>x. if x \<in> einterval a b then f x else 0) = (\<lambda>x. f x * indicator (einterval a b) x)"
        by auto
      finally show "set_borel_measurable lborel (einterval a b) f"
        by simp
    next
      show "(\<lambda>i. LBINT x=l i..u i. f x) ----> B - A"
        apply (subst FTCi)
        apply (intro tendsto_intros)
        using B approx unfolding tendsto_at_iff_sequentially comp_def
        apply (elim allE[of _ "\<lambda>i. ereal (u i)"], auto)
        using A approx unfolding tendsto_at_iff_sequentially comp_def
        by (elim allE[of _ "\<lambda>i. ereal (l i)"], auto)
  qed
qed

lemma interval_integral_FTC_integrable:
  fixes f F :: "real \<Rightarrow> real" and a b :: ereal
  assumes "a < b"
  assumes F: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> DERIV F x :> f x" 
  assumes f: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> isCont f x" 
  assumes f_integrable: "set_integrable lborel (einterval a b) f"
  assumes A: "((F \<circ> real) ---> A) (at_right a)"
  assumes B: "((F \<circ> real) ---> B) (at_left b)"
  shows "(LBINT x=a..b. f x) = B - A"
proof -
  from einterval_Icc_approximation[OF `a < b`] guess u l . note approx = this
  have [simp]: "\<And>x i. l i \<le> x \<Longrightarrow> a < ereal x"
    by (rule order_less_le_trans, rule approx, force)
  have [simp]: "\<And>x i. x \<le> u i \<Longrightarrow> ereal x < b"
    by (rule order_le_less_trans, subst ereal_less_eq(3), assumption, rule approx)
  have FTCi: "\<And>i. (LBINT x=l i..u i. f x) = F (u i) - F (l i)"
    using assms approx apply (intro interval_integral_FTC_finite)
    apply (auto simp add: less_imp_le min_def max_def)
    apply (rule continuous_at_imp_continuous_on, auto intro!: f)
    by (rule DERIV_imp_DERIV_within, auto intro!: F)
  have "(\<lambda>i. LBINT x=l i..u i. f x) ----> B - A"
    apply (subst FTCi)
    apply (intro tendsto_intros)
    using B approx unfolding tendsto_at_iff_sequentially comp_def
    apply (elim allE[of _ "\<lambda>i. ereal (u i)"], auto)
    using A approx unfolding tendsto_at_iff_sequentially comp_def
    by (elim allE[of _ "\<lambda>i. ereal (l i)"], auto)
  moreover have "(\<lambda>i. LBINT x=l i..u i. f x) ----> (LBINT x=a..b. f x)"
    by (rule interval_integral_Icc_approx_integrable [OF `a < b` approx f_integrable])
  ultimately show ?thesis
    by (elim LIMSEQ_unique)
qed

(* 
  The second Fundamental Theorem of Calculus and existence of antiderivatives on an
  einterval.
*)

lemma interval_integral_FTC2:
  fixes a b c :: real and f :: "real \<Rightarrow> real"
  assumes "a \<le> c" "c \<le> b"
  and contf: "continuous_on {a..b} f"
  fixes x :: real
  assumes "a \<le> x" and "x \<le> b"
  shows "DERIV (\<lambda>u. LBINT y=c..u. f y) x : {a..b} :> f x"
proof -
  let ?F = "(\<lambda>u. LBINT y=a..u. f y)"
  have intf: "set_integrable lborel {a..b} f"
    by (rule borel_integrable_atLeastAtMost', rule contf)
  have "((\<lambda>u. integral {a..u} f) has_vector_derivative f x) (at x within {a..b})"
    apply (intro integral_has_vector_derivative)
    using `a \<le> x` `x \<le> b` by (intro continuous_on_subset [OF contf], auto)
  hence 1: "DERIV (\<lambda>u. integral {a..u} f) x : {a..b} :> f x"
    by (simp add: has_vector_derivative_within_eq_DERIV)
  have 2: "DERIV ?F x : {a..b} :> f x"
    apply (rule DERIV_cong' [OF _ _ _ 1])
    using assms apply auto
    apply (rule interval_integral_eq_integral [symmetric], auto)
    by (rule set_integrable_subset [OF intf], auto)
  {
    fix u 
    assume "a \<le> u" "u \<le> b"
    then have "(LBINT y=c..a. f y) + (LBINT y=a..u. f y)= (LBINT y=c..u. f y)"
      apply (intro interval_integral_sum)
      using assms apply (auto simp add: interval_lebesgue_integrable_def)
      by (rule set_integrable_subset [OF intf], auto simp add: min_def max_def)
  } note 3 = this
  show ?thesis
    apply (rule DERIV_cong' [OF _ _ 3], auto simp add: assms)
    by (intro DERIV_intros, auto, rule 2)
qed

lemma einterval_antiderivative: 
  fixes a b :: ereal and f :: "real \<Rightarrow> real"
  assumes "a < b" and contf: "\<And>x :: real. a < x \<Longrightarrow> x < b \<Longrightarrow> isCont f x"
  shows "\<exists>F. \<forall>x :: real. a < x \<longrightarrow> x < b \<longrightarrow> DERIV F x :> f x"
proof -
  from einterval_nonempty [OF `a < b`] obtain c :: real where [simp]: "a < c" "c < b" 
    by (auto simp add: einterval_def)
  let ?F = "(\<lambda>u. LBINT y=c..u. f y)"
  show ?thesis
  proof (rule exI, clarsimp)
    fix x :: real
    assume [simp]: "a < x" "x < b"
    have 1: "a < min c x" by simp
    from einterval_nonempty [OF 1] obtain d :: real where [simp]: "a < d" "d < c" "d < x" 
      by (auto simp add: einterval_def)
    have 2: "max c x < b" by simp
    from einterval_nonempty [OF 2] obtain e :: real where [simp]: "c < e" "x < e" "e < b" 
      by (auto simp add: einterval_def)
    show "DERIV ?F x :> f x"
      apply (rule has_DERIV_within_closed_interval [of d _ e], auto)
      apply (rule interval_integral_FTC2, auto simp add: less_imp_le)
      apply (rule continuous_at_imp_continuous_on)
      apply (auto intro!: contf)
      apply (rule order_less_le_trans, rule `a < d`, auto)
      apply (rule order_le_less_trans) prefer 2
      by (rule `e < b`, auto)
  qed
qed

(*
    The substitution theorem

    Once again, three versions: first, for finite intervals, and then two versions for
    arbitrary intervals.
*)

lemma interval_integral_substitution_finite:
  fixes a b :: real and f :: "real \<Rightarrow> real"
  assumes "a \<le> b"
  and derivg: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> DERIV g x : {a..b} :> g' x"
  and contf : "continuous_on (g ` {a..b}) f"
  and contg': "continuous_on {a..b} g'"
  shows "LBINT x=a..b. f (g x) * g' x = LBINT y=(g a)..(g b). f y"
proof-
  have contg [simp]: "continuous_on {a..b} g"
    apply (auto intro!: differentiable_imp_continuous_on Deriv.differentiableI
        simp add: differentiable_on_def)   
    by (rule derivg)
  have 1: "\<And>u. min (g a) (g b) \<le> u \<Longrightarrow> u \<le> max (g a) (g b) \<Longrightarrow> 
      \<exists>x\<in>{a..b}. u = g x"
    apply (case_tac "g a \<le> g b")
    apply (auto simp add: min_def max_def less_imp_le)
    apply (frule (1) IVT' [of g], auto simp add: assms)
    by (frule (1) IVT2' [of g], auto simp add: assms)
  from contg `a \<le> b` have "\<exists>c d. g ` {a..b} = {c..d} \<and> c \<le> d"
    by (elim continuous_image_closed_interval)
  then obtain c d where g_im: "g ` {a..b} = {c..d}" and "c \<le> d" by auto
  have "\<exists>F. \<forall>x\<in>{a..b}. DERIV F (g x) : (g ` {a..b}) :> f (g x)"
    apply (rule exI, auto, subst g_im)
    apply (rule interval_integral_FTC2 [of c c d])
    using `c \<le> d` apply auto
    apply (rule continuous_on_subset [OF contf])
    using g_im by auto
  then guess F ..
  then have derivF: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> DERIV F (g x) : (g ` {a..b}) :> f (g x)" by auto
  have contf2: "continuous_on {min (g a) (g b)..max (g a) (g b)} f"
    apply (rule continuous_on_subset [OF contf])
    apply (auto simp add: image_def)
    by (erule 1)
  have contfg: "continuous_on {a..b} (\<lambda>x. f (g x))"
    apply (rule continuous_on_compose2 [of "g ` {a..b}" f], rule contf)
    apply (subst continuous_on_eq_continuous_within, auto)
    apply (rule Derivative.differentiable_imp_continuous_within)
    apply (rule Deriv.differentiableI)
    by (rule derivg, auto)
  have "LBINT x=a..b. f (g x) * g' x = F (g b) - F (g a)"
    apply (subst interval_integral_Icc, simp add: assms)
    apply (rule integral_FTC_atLeastAtMost'[of a b "\<lambda>x. F (g x)", OF `a \<le> b`])
    apply (rule DERIV_chain_within' [where g = F])
    by (auto intro!: derivF derivg continuous_on_mult contfg contg')
  moreover have "LBINT y=(g a)..(g b). f y = F (g b) - F (g a)"
    apply (rule interval_integral_FTC_finite)
    apply (rule contf2)
    apply (frule (1) 1, auto)
    apply (rule DERIV_within_subset [OF _ _ derivF])
    apply (auto simp add: image_def)
    by (rule 1, auto)
  ultimately show ?thesis by simp
qed

(* TODO: the last two proofs are only slightly different. Factor out common part?
   An alternative: make the second one the main one, and then have another lemma
   that says that if f is nonnegative and all the other hypotheses hold, then it is integrable. *)

lemma interval_integral_substitution_nonneg:
  fixes f g g':: "real \<Rightarrow> real" and a b u v :: ereal
  assumes "a < b" 
  and deriv_g: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> DERIV g x :> g' x"
  and contf: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> isCont f (g x)"
  and contg': "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> isCont g' x"
  and f_nonneg: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> 0 \<le> f (g x)" (* TODO: make this AE? *)
  and g'_nonneg: "\<And>x. a \<le> ereal x \<Longrightarrow> ereal x \<le> b \<Longrightarrow> 0 \<le> g' x"
  and A: "((ereal \<circ> g \<circ> real) ---> A) (at_right a)"
  and B: "((ereal \<circ> g \<circ> real) ---> B) (at_left b)"
  and integrable: "set_integrable lborel (einterval a b) (\<lambda>x. f (g x) * g' x)"
  shows "(LBINT x=A..B. f x) = (LBINT x=a..b. (f (g x) * g' x))"
proof -
  from einterval_Icc_approximation[OF `a < b`] guess u l . note approx [simp] = this
  note less_imp_le [simp]
  have [simp]: "\<And>x i. l i \<le> x \<Longrightarrow> a < ereal x"
    by (rule order_less_le_trans, rule approx, force)
  have [simp]: "\<And>x i. x \<le> u i \<Longrightarrow> ereal x < b"
    by (rule order_le_less_trans, subst ereal_less_eq(3), assumption, rule approx)
  have [simp]: "\<And>i. l i < b" 
    apply (rule order_less_trans) prefer 2 
    by (rule approx, auto, rule approx)
  have [simp]: "\<And>i. a < u i" 
    by (rule order_less_trans, rule approx, auto, rule approx)
  have [simp]: "\<And>i j. i \<le> j \<Longrightarrow> l j \<le> l i" by (rule decseqD, rule approx)
  have [simp]: "\<And>i j. i \<le> j \<Longrightarrow> u i \<le> u j" by (rule incseqD, rule approx)
  have g_nondec [simp]: "\<And>x y. a < x \<Longrightarrow> x \<le> y \<Longrightarrow> y < b \<Longrightarrow> g x \<le> g y"
    apply (erule DERIV_nonneg_imp_nondecreasing, auto)
    apply (rule exI, rule conjI, rule deriv_g)
    apply (erule order_less_le_trans, auto)
    apply (rule order_le_less_trans, subst ereal_less_eq(3), assumption, auto)
    apply (rule g'_nonneg)
    apply (rule less_imp_le, erule order_less_le_trans, auto)
    by (rule less_imp_le, rule le_less_trans, subst ereal_less_eq(3), assumption, auto)
  have "A \<le> B" and un: "einterval A B = (\<Union>i. {g(l i)<..<g(u i)})"
  proof - 
    have A2: "(\<lambda>i. g (l i)) ----> A"
      using A apply (auto simp add: einterval_def tendsto_at_iff_sequentially comp_def)
      by (drule_tac x = "\<lambda>i. ereal (l i)" in spec, auto)
    hence A3: "\<And>i. g (l i) \<ge> A"
      by (intro decseq_le, auto simp add: decseq_def)
    have B2: "(\<lambda>i. g (u i)) ----> B"
      using B apply (auto simp add: einterval_def tendsto_at_iff_sequentially comp_def)
      by (drule_tac x = "\<lambda>i. ereal (u i)" in spec, auto)
    hence B3: "\<And>i. g (u i) \<le> B"
      by (intro incseq_le, auto simp add: incseq_def)
    show "A \<le> B"
      apply (rule order_trans [OF A3 [of 0]])
      apply (rule order_trans [OF _ B3 [of 0]])
      by auto
    { fix x :: real
      assume "A < x" and "x < B"   
      then have "eventually (\<lambda>i. ereal (g (l i)) < x \<and> x < ereal (g (u i))) sequentially"
        apply (intro eventually_conj order_tendstoD)
        by (rule A2, assumption, rule B2, assumption)
      hence "\<exists>i. g (l i) < x \<and> x < g (u i)"
        by (simp add: eventually_sequentially, auto)
    } note AB = this
    show "einterval A B = (\<Union>i. {g(l i)<..<g(u i)})"
      apply (auto simp add: einterval_def)
      apply (erule (1) AB)
      apply (rule order_le_less_trans, rule A3, simp)
      apply (rule order_less_le_trans) prefer 2
      by (rule B3, simp) 
  qed
  (* finally, the main argument *)
  {
     fix i
     have "(LBINT x=l i.. u i. (f (g x) * g' x)) = (LBINT y=g (l i)..g (u i). f y)"
        apply (rule interval_integral_substitution_finite, auto)
        apply (rule DERIV_imp_DERIV_within, auto, rule deriv_g, auto)
        apply (rule continuous_at_imp_continuous_on, auto, rule contf, auto)
        by (rule continuous_at_imp_continuous_on, auto, rule contg', auto)
  } note eq1 = this
  have "(\<lambda>i. LBINT x=l i..u i. f (g x) * g' x)
      ----> (LBINT x=a..b. f (g x) * g' x)"
    apply (rule interval_integral_Icc_approx_integrable [OF `a < b` approx])
    by (rule assms)
  hence 2: "(\<lambda>i. (LBINT y=g (l i)..g (u i). f y)) ----> (LBINT x=a..b. f (g x) * g' x)"
    by (simp add: eq1)
  have incseq: "incseq (\<lambda>i. {g (l i)<..<g (u i)})"
    apply (auto simp add: incseq_def)
    apply (rule order_le_less_trans)
    prefer 2 apply assumption
    apply (rule g_nondec, auto)
    by (erule order_less_le_trans, rule g_nondec, auto)
  have img: "\<And>x i. g (l i) \<le> x \<Longrightarrow> x \<le> g (u i) \<Longrightarrow> \<exists>c \<ge> l i. c \<le> u i \<and> x = g c"
    apply (frule (1) IVT' [of g], auto)   
    apply (rule continuous_at_imp_continuous_on, auto)
    by (rule DERIV_isCont, rule deriv_g, auto)
  have nonneg_f2: "\<And>x i. g (l i) \<le> x \<Longrightarrow> x \<le> g (u i) \<Longrightarrow> 0 \<le> f x"
    by (frule (1) img, auto, rule f_nonneg, auto)
  have contf_2: "\<And>x i. g (l i) \<le> x \<Longrightarrow> x \<le> g (u i) \<Longrightarrow> isCont f x"
    by (frule (1) img, auto, rule contf, auto)
  have "(\<lambda>i. (LBINT y=g (l i)..g (u i). f y)) ----> (LBINT x = A..B. f x)"
    apply (subst interval_lebesgue_integral_le_eq, auto)
    apply (subst interval_lebesgue_integral_le_eq, rule `A \<le> B`)
    apply (subst un, rule set_integral_cont_up, auto)
    apply (rule incseq) 
    apply (rule pos_integrable_to_top, auto)
    apply (subst incseq_mono, rule incseq)
    apply (rule nonneg_f2, erule less_imp_le, erule less_imp_le)
    apply (rule set_integrable_subset)
    apply (rule borel_integrable_atLeastAtMost')
    apply (rule continuous_at_imp_continuous_on)
    apply (clarsimp, erule (1) contf_2, auto)
    apply (erule less_imp_le)+
    using 2 unfolding interval_lebesgue_integral_def
    by auto
  thus ?thesis by (intro LIMSEQ_unique [OF _ 2])
qed

(* TODO: is it possible to lift the assumption here that g' is nonnegative? *)

lemma interval_integral_substitution_integrable:
  fixes f g g':: "real \<Rightarrow> real" and a b u v :: ereal
  assumes "a < b" 
  and deriv_g: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> DERIV g x :> g' x"
  and contf: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> isCont f (g x)"
  and contg': "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> isCont g' x"
  and g'_nonneg: "\<And>x. a \<le> ereal x \<Longrightarrow> ereal x \<le> b \<Longrightarrow> 0 \<le> g' x"
  and A: "((ereal \<circ> g \<circ> real) ---> A) (at_right a)"
  and B: "((ereal \<circ> g \<circ> real) ---> B) (at_left b)"
  and integrable: "set_integrable lborel (einterval a b) (\<lambda>x. f (g x) * g' x)"
  and integrable2: "set_integrable lborel (einterval A B) (\<lambda>x. f x)"
  shows "(LBINT x=A..B. f x) = (LBINT x=a..b. (f (g x) * g' x))"
proof -
  from einterval_Icc_approximation[OF `a < b`] guess u l . note approx [simp] = this
  note less_imp_le [simp]
  have [simp]: "\<And>x i. l i \<le> x \<Longrightarrow> a < ereal x"
    by (rule order_less_le_trans, rule approx, force)
  have [simp]: "\<And>x i. x \<le> u i \<Longrightarrow> ereal x < b"
    by (rule order_le_less_trans, subst ereal_less_eq(3), assumption, rule approx)
  have [simp]: "\<And>i. l i < b" 
    apply (rule order_less_trans) prefer 2 
    by (rule approx, auto, rule approx)
  have [simp]: "\<And>i. a < u i" 
    by (rule order_less_trans, rule approx, auto, rule approx)
  have [simp]: "\<And>i j. i \<le> j \<Longrightarrow> l j \<le> l i" by (rule decseqD, rule approx)
  have [simp]: "\<And>i j. i \<le> j \<Longrightarrow> u i \<le> u j" by (rule incseqD, rule approx)
  have g_nondec [simp]: "\<And>x y. a < x \<Longrightarrow> x \<le> y \<Longrightarrow> y < b \<Longrightarrow> g x \<le> g y"
    apply (erule DERIV_nonneg_imp_nondecreasing, auto)
    apply (rule exI, rule conjI, rule deriv_g)
    apply (erule order_less_le_trans, auto)
    apply (rule order_le_less_trans, subst ereal_less_eq(3), assumption, auto)
    apply (rule g'_nonneg)
    apply (rule less_imp_le, erule order_less_le_trans, auto)
    by (rule less_imp_le, rule le_less_trans, subst ereal_less_eq(3), assumption, auto)
  have "A \<le> B" and un: "einterval A B = (\<Union>i. {g(l i)<..<g(u i)})"
  proof - 
    have A2: "(\<lambda>i. g (l i)) ----> A"
      using A apply (auto simp add: einterval_def tendsto_at_iff_sequentially comp_def)
      by (drule_tac x = "\<lambda>i. ereal (l i)" in spec, auto)
    hence A3: "\<And>i. g (l i) \<ge> A"
      by (intro decseq_le, auto simp add: decseq_def)
    have B2: "(\<lambda>i. g (u i)) ----> B"
      using B apply (auto simp add: einterval_def tendsto_at_iff_sequentially comp_def)
      by (drule_tac x = "\<lambda>i. ereal (u i)" in spec, auto)
    hence B3: "\<And>i. g (u i) \<le> B"
      by (intro incseq_le, auto simp add: incseq_def)
    show "A \<le> B"
      apply (rule order_trans [OF A3 [of 0]])
      apply (rule order_trans [OF _ B3 [of 0]])
      by auto
    { fix x :: real
      assume "A < x" and "x < B"   
      then have "eventually (\<lambda>i. ereal (g (l i)) < x \<and> x < ereal (g (u i))) sequentially"
        apply (intro eventually_conj order_tendstoD)
        by (rule A2, assumption, rule B2, assumption)
      hence "\<exists>i. g (l i) < x \<and> x < g (u i)"
        by (simp add: eventually_sequentially, auto)
    } note AB = this
    show "einterval A B = (\<Union>i. {g(l i)<..<g(u i)})"
      apply (auto simp add: einterval_def)
      apply (erule (1) AB)
      apply (rule order_le_less_trans, rule A3, simp)
      apply (rule order_less_le_trans) prefer 2
      by (rule B3, simp) 
  qed
  (* finally, the main argument *)
  {
     fix i
     have "(LBINT x=l i.. u i. (f (g x) * g' x)) = (LBINT y=g (l i)..g (u i). f y)"
        apply (rule interval_integral_substitution_finite, auto)
        apply (rule DERIV_imp_DERIV_within, auto, rule deriv_g, auto)
        apply (rule continuous_at_imp_continuous_on, auto, rule contf, auto)
        by (rule continuous_at_imp_continuous_on, auto, rule contg', auto)
  } note eq1 = this
  have "(\<lambda>i. LBINT x=l i..u i. f (g x) * g' x)
      ----> (LBINT x=a..b. f (g x) * g' x)"
    apply (rule interval_integral_Icc_approx_integrable [OF `a < b` approx])
    by (rule assms)
  hence 2: "(\<lambda>i. (LBINT y=g (l i)..g (u i). f y)) ----> (LBINT x=a..b. f (g x) * g' x)"
    by (simp add: eq1)
  have incseq: "incseq (\<lambda>i. {g (l i)<..<g (u i)})"
    apply (auto simp add: incseq_def)
    apply (rule order_le_less_trans)
    prefer 2 apply (assumption, auto)
    by (erule order_less_le_trans, rule g_nondec, auto)
  have "(\<lambda>i. (LBINT y=g (l i)..g (u i). f y)) ----> (LBINT x = A..B. f x)"
    apply (subst interval_lebesgue_integral_le_eq, auto)
    apply (subst interval_lebesgue_integral_le_eq, rule `A \<le> B`)
    apply (subst un, rule set_integral_cont_up, auto)
    apply (rule incseq)
    apply (subst un [symmetric])
    by (rule integrable2)
  thus ?thesis by (intro LIMSEQ_unique [OF _ 2])
qed

end
