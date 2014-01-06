(*
Theory: Some_Calculus.thy
Authors: Jeremy Avigad, Luke Serafin

Some routine calculations from undergraduate calculus.
*)

theory Sinc

imports Interval_Integral

begin

(** Derivatives and integrals for CLT. **)

lemma integral_expneg_alpha_atLeast0:
  fixes u :: real
  assumes pos: "0 < u"
  shows "LBINT x=0..\<infinity>. exp (-x * u) = 1/u"
apply (subst interval_integral_FTC_nonneg[of _ _ "\<lambda>x. -(1/u) * exp (-x * u)" _ "-(1/u)" 0])
using pos apply (auto intro!: DERIV_intros)
apply (subgoal_tac "(((\<lambda>x. - (exp (- (x * u)) / u)) \<circ> real) ---> - (1 / u)) (at 0)")
apply (subst (asm) filterlim_at_split, force)
apply (subst zero_ereal_def)
apply (subst filterlim_at_split)
apply (simp_all add: ereal_tendsto_simps)
apply (subst filterlim_at_split[symmetric])
apply (auto intro!: tendsto_intros)
apply (subst exp_zero[symmetric])
apply (rule tendsto_compose[of exp])
using isCont_exp unfolding isCont_def apply metis
apply (subst tendsto_minus_cancel_left[symmetric], simp)
apply (rule tendsto_mult_left_zero, rule tendsto_ident_at)
apply (subst divide_inverse, subst minus_mult_left)
apply (rule tendsto_mult_left_zero)
apply (subst tendsto_minus_cancel_left[symmetric], simp)
apply (rule filterlim_compose[of exp _ at_bot])
apply (rule exp_at_bot)
apply (subst filterlim_uminus_at_top [symmetric])
apply (subst mult_commute)
apply (rule filterlim_tendsto_pos_mult_at_top [OF _ pos])
apply auto
by (rule filterlim_ident)

lemma Collect_eq_Icc: "{r. t \<le> r \<and> r \<le> b} = {t .. b}"
  by auto

(* From Billingsley section 18. *)
lemma ex_18_4_1:
  assumes "t \<ge> 0"
  shows "LBINT x=0..t. exp (-u * x) * sin x = (1/(1+u^2)) *
  (1 - exp (-u * t) * (u * sin t + cos t))"

  apply (subst zero_ereal_def)
  apply (subst interval_integral_FTC_finite 
      [where F = "(\<lambda>x. (1/(1+u^2)) * (1 - exp (-u * x) * (u * sin x + cos x)))"])
  apply (auto intro: continuous_at_imp_continuous_on)
  apply (rule DERIV_imp_DERIV_within, auto)
  apply (auto intro!: DERIV_intros)
by (simp_all add: power2_eq_square field_simps)

lemma ex_18_4_2_deriv:
  "DERIV (\<lambda>u. 1/x * (1 - exp (-u * x)) * \<bar>sin x\<bar>) u :> \<bar>exp (-u * x) * sin x\<bar>"
  apply (auto simp only: intro!: DERIV_intros)
  by (simp add: abs_mult)

(*** not needed ***)
lemma ex_18_4_2_bdd_integral:
  assumes "s \<ge> 0"
  shows "LBINT u=0..s. \<bar>exp (-u * x) * sin x\<bar> =
  1/x * (1 - exp (-s * x)) * \<bar>sin x\<bar>"

  apply (subst zero_ereal_def)
  apply (subst interval_integral_FTC_finite 
      [where F = "\<lambda>u. 1/x * (1 - exp (-u * x)) * \<bar>sin x\<bar>"])
  apply (auto intro: continuous_at_imp_continuous_on) [1]
  apply (rule DERIV_imp_DERIV_within, force)
  (* curiously, just copying the proof of ex_18_4_2_deriv doesn't work *)
  apply (rule ex_18_4_2_deriv)
  apply auto
done

(* clean this up! it should be shorter *)
lemma ex_18_4_2_ubdd_integral:
  fixes x
  assumes pos: "0 < x"
  shows "LBINT u=0..\<infinity>. \<bar>exp (-u * x) * sin x\<bar> = \<bar>sin x\<bar> / x" 

  apply (subst interval_integral_FTC_nonneg [where F = "\<lambda>u. 1/x * (1 - exp (-u * x)) * \<bar>sin x\<bar>"
    and A = 0 and B = "abs (sin x) / x"])
  apply force
  apply (rule ex_18_4_2_deriv)
  apply auto
  (* this is a little annoying -- having to replace 0 by "ereal 0" *)
  apply (subst zero_ereal_def)+
  apply (simp_all add: ereal_tendsto_simps)
  (* What follows are two simple limit calculations. Clean these up -- they should be
  shorter. *)
  apply (rule filterlim_mono [of _ "nhds 0" "at 0"], auto)
  prefer 2
  apply (rule at_le, simp)
  apply (subst divide_real_def)
  apply (rule tendsto_mult_left_zero)+
  apply (subgoal_tac "0 = 1 - 1")
  apply (erule ssubst)
  apply (rule tendsto_diff, auto)
  apply (subgoal_tac "1 = exp 0")
  apply (erule ssubst)
  apply (rule tendsto_compose) back
  apply (subst isCont_def [symmetric], auto)
  apply (rule tendsto_minus_cancel, auto)
  apply (rule tendsto_mult_left_zero, rule tendsto_ident_at)
  (* this is the second *)
  apply (subst divide_real_def)+
  apply (subgoal_tac "abs (sin x) * inverse x = 1 * abs (sin x) * inverse x")
  apply (erule ssubst)
  apply (rule tendsto_mult)+
  apply auto
  apply (subgoal_tac "1 = 1 - 0")
  apply (erule ssubst) back
  apply (rule tendsto_diff, auto)
  apply (rule filterlim_compose) back
  apply (rule exp_at_bot)
  apply (subst filterlim_uminus_at_top [symmetric])
  apply (subst mult_commute)
  apply (rule filterlim_tendsto_pos_mult_at_top [OF _ pos])
  apply auto
by (rule filterlim_ident)

lemma Billingsley_ex_17_5: "LBINT x=-\<infinity>..\<infinity>. inverse (1 + x^2) = pi"
  apply (subst interval_integral_substitution_nonneg[of "-pi/2" "pi/2" tan "\<lambda>x. 1 + (tan x)^2"])
  apply (auto intro: DERIV_intros)
  apply (subst tan_sec)
  using pi_half cos_is_zero
  apply (metis cos_gt_zero_pi less_divide_eq_numeral1(1) less_numeral_extra(3))
  using DERIV_tan
  apply (metis cos_gt_zero_pi less_divide_eq_numeral1(1) power2_less_0 power_inverse power_zero_numeral)
  apply (rule isCont_add, force)
  apply (subst power2_eq_square)
  apply (subst isCont_mult)
  apply (rule isCont_tan)
  (* Following line duplicated from above. *)
  using pi_half cos_is_zero
  apply (metis cos_gt_zero_pi less_divide_eq_numeral1(1) less_numeral_extra(3))
  apply (simp_all add: ereal_tendsto_simps filterlim_tan_at_left)
  apply (subst minus_divide_left)+
  by (rule filterlim_tan_at_right)

definition sinc :: "real \<Rightarrow> real" where "sinc t \<equiv> LBINT x=0..t. sin x / x"

(* Put in Interval_Integral. *)
lemma interval_integral_endpoint_split:
  fixes a b c :: ereal
  fixes f :: "real \<Rightarrow> real"
  assumes "interval_lebesgue_integrable lborel a b f" "a \<le> c" "c \<le> b"
  shows "LBINT x=a..b. f x = (LBINT x=a..c. f x) + (LBINT x=c..b. f x)"
unfolding interval_lebesgue_integral_def einterval_def apply (auto intro: assms)
apply (subgoal_tac "{x. a < ereal x \<and> ereal x < b} = {x. a < ereal x \<and> x < c} \<union>
                    {x. a < ereal x \<and> ereal x = c \<and> ereal x < b} \<union> {x. c < x \<and> ereal x < b}")
apply (auto intro: order_less_imp_le)
apply (subst set_integral_Un, auto)
apply (rule set_integrable_subset[where A = "{x. a < ereal x \<and> ereal x < b}"])
using assms(1) unfolding interval_lebesgue_integrable_def einterval_def apply auto
apply (rule set_integrable_subset[where A = "{x. a < ereal x \<and> ereal x < b}"])
using assms(1) unfolding interval_lebesgue_integrable_def einterval_def apply auto
apply (subst set_integral_Un, auto)
apply (subst set_integrable_subset[where A = "{x. a < ereal x \<and> ereal x < b}"])
using assms(1) unfolding interval_lebesgue_integrable_def einterval_def apply auto
apply (subst set_integrable_subset[where A = "{x. a < ereal x \<and> ereal x < b}"])
using assms(1) unfolding interval_lebesgue_integrable_def einterval_def apply auto
apply (cases c rule: ereal_cases, auto)
proof -
  fix r
  show "set_lebesgue_integral lborel {x. x = r \<and> a < ereal x \<and> ereal x < b} f = 0"
    apply (subgoal_tac "0 = (LBINT x. 0)")
    apply (erule ssubst)
    apply (rule integral_cong_AE)
    by (rule AE_I[where N = "{r}"], auto simp add: indicator_def)
qed

(** Add to main Lebesgue integration library; does not require integrability as hypothesis, which in
my experience greatly increases usability. **)
lemma positive_integral_eq_integral_measurable:
  assumes f: "f \<in> borel_measurable M" and I: "integral\<^sup>L M f \<noteq> 0"
  assumes nonneg: "AE x in M. 0 \<le> f x" 
  shows "(\<integral>\<^sup>+ x. ereal (f x) \<partial>M) = ereal (integral\<^sup>L M f)"
proof -
  have "(\<integral>\<^sup>+ x. ereal (- f x) \<partial>M) = (\<integral>\<^sup>+ x. max 0 (ereal (- f x)) \<partial>M)"
    using positive_integral_max_0 by metis
  also have "... = (\<integral>\<^sup>+ x. 0 \<partial>M)"
    using nonneg by (intro positive_integral_cong_AE) (auto split: split_max)
  also have "... = 0" by (subst zero_ereal_def) (subst positive_integral_eq_integral, auto)
  finally have "real (\<integral>\<^sup>+ x. ereal (f x) \<partial>M) = integral\<^sup>L M f"
    using real_of_ereal_0 unfolding lebesgue_integral_def by auto
  thus ?thesis
    apply (subst (asm) ereal.inject[symmetric])
    apply (subst (asm) ereal_real)
    using I ereal_eq_0 by metis
qed

(* Partially modified from Interval_Integral version; a more general substitution lemma is needed. *)
lemma interval_integral_substitution_nonneg':
  fixes f g g':: "real \<Rightarrow> real" and a b u v :: ereal
  assumes "a < b" 
  and deriv_g: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> DERIV g x :> g' x"
  and contf: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> isCont f (g x)"
  and contg': "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> isCont g' x"
  and f_nonneg: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> 0 \<le> f (g x)" (* TODO: make this AE? *)
  and g'_nonneg: "\<And>x. a \<le> ereal x \<Longrightarrow> ereal x \<le> b \<Longrightarrow> g' x \<le> 0"
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
  have g_nondec [simp]: "\<And>x y. a < x \<Longrightarrow> x \<le> y \<Longrightarrow> y < b \<Longrightarrow> g y \<le> g x"
    apply (erule DERIV_nonpos_imp_nonincreasing, auto)
    apply (rule exI, rule conjI, rule deriv_g)
    apply (erule order_less_le_trans, auto)
    apply (rule order_le_less_trans, subst ereal_less_eq(3), assumption, auto)
    apply (rule g'_nonneg)
    apply (rule less_imp_le, erule order_less_le_trans, auto)
    by (rule less_imp_le, rule le_less_trans, subst ereal_less_eq(3), assumption, auto)
  have "A \<ge> B" and un: "einterval B A = (\<Union>i. {g(u i)<..<g(l i)})"
  proof - 
    have A2: "(\<lambda>i. g (l i)) ----> A"
      using A apply (auto simp add: einterval_def tendsto_at_iff_sequentially comp_def)
      by (drule_tac x = "\<lambda>i. ereal (l i)" in spec, auto)
    hence A3: "\<And>i. g (l i) \<le> A"
      by (intro incseq_le, auto simp add: incseq_def)
    have B2: "(\<lambda>i. g (u i)) ----> B"
      using B apply (auto simp add: einterval_def tendsto_at_iff_sequentially comp_def)
      by (drule_tac x = "\<lambda>i. ereal (u i)" in spec, auto)
    hence B3: "\<And>i. g (u i) \<ge> B"
      by (intro decseq_le, auto simp add: decseq_def)
    show "A \<ge> B"
      apply (rule order_trans [OF B3 [of 0]])
      apply (rule order_trans [OF _ A3 [of 0]])
      by auto
    { fix x :: real
      assume "B < x" and "x < A"   
      then have "eventually (\<lambda>i. ereal (g (u i)) < x \<and> x < ereal (g (l i))) sequentially"
        apply (intro eventually_conj order_tendstoD)
        by (rule B2, assumption, rule A2, assumption)
      hence "\<exists>i. g (u i) < x \<and> x < g (l i)"
        by (simp add: eventually_sequentially, auto)
    } note AB = this
    show "einterval B A = (\<Union>i. {g(u i)<..<g(l i)})"
      apply (auto simp add: einterval_def)
      apply (erule (1) AB)
      apply (rule order_le_less_trans, rule B3, simp)
      apply (rule order_less_le_trans) prefer 2
      by (rule A3, simp) 
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
  have incseq: "incseq (\<lambda>i. {g (u i)<..<g (l i)})"
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
  have "(\<lambda>i. (LBINT y=g (u i)..g (l i). f y)) ----> (LBINT x = B..A. f x)"
    apply (subst interval_lebesgue_integral_le_eq, auto)
    apply (subst interval_lebesgue_integral_le_eq, rule `B \<le> A`)
    apply (subst un, rule set_integral_cont_up, auto)
    apply (rule incseq)
    apply (rule pos_integrable_to_top, auto)
    apply (subst incseq_mono, rule incseq) sorry
    (**
    apply (rule nonneg_f2, erule less_imp_le, erule less_imp_le)
    apply (rule set_integrable_subset)
    apply (rule borel_integrable_atLeastAtMost')
    apply (rule continuous_at_imp_continuous_on)
    apply (clarsimp, erule (1) contf_2, auto)
    apply (erule less_imp_le)+
    using 2 unfolding interval_lebesgue_integral_def
    by auto
    **)
  thus ?thesis using LIMSEQ_unique [OF _ 2] sorry
qed
    
lemma sinc_at_top_lemma:
  fixes t :: real
  assumes "t \<ge> 0"
  shows "sinc t = pi / 2 - (LBINT u=0..\<infinity>. inverse (1 + u^2) * exp (-u * t) * (u * sin t + cos t))"
proof -
  have 179: "LBINT x=0..\<infinity>. inverse (1 + x^2) = pi / 2"
  proof -
    have "LBINT x=-\<infinity>..\<infinity>. inverse (1 + x^2) = (LBINT x=-\<infinity>..0. inverse (1 + x^2)) +
                                               (LBINT x=0..\<infinity>. inverse (1 + x^2))"
      apply (rule interval_integral_endpoint_split[of "-\<infinity>" "\<infinity>" "\<lambda>x. inverse (1 + x^2)" 0], auto)
      apply (unfold interval_lebesgue_integrable_def einterval_def integrable_def, auto)
      apply (subst power2_eq_square, auto)
      apply (subst (asm) positive_integral_eq_integral_measurable)
      apply (subst power2_eq_square, auto)
      using Billingsley_ex_17_5 unfolding interval_lebesgue_integral_def einterval_def apply auto
      apply (subst (asm) positive_integral_max_0[symmetric])
      apply (subst (asm) power2_eq_square)
    proof -
      have *: "\<And>x. max 0 (ereal (- inverse (1 + x * x))) = 0"
        by (metis comm_semiring_1_class.normalizing_semiring_rules(4) ereal_max_0
            inverse_minus_eq inverse_nonpositive_iff_nonpositive le_add_same_cancel1 max.boundedE
            max.order_iff neg_le_0_iff_le zero_ereal_def zero_le_double_add_iff_zero_le_single_add
            zero_le_square)
        assume "\<integral>\<^sup>+ x. max 0 (ereal (- inverse (1 + x * x))) \<partial>lborel = \<infinity>"
        thus False by (subst (asm) *) auto
    qed
    moreover have "(LBINT x=-\<infinity>..0. inverse (1 + x^2)) = (LBINT x=0..\<infinity>. inverse (1 + x^2))"
      apply (subst mult_1_right[of "LBINT x=-\<infinity>..0. inverse (1 + x^2)",symmetric])
      apply (subst mult_1_right[of "LBINT x=-\<infinity>..0. inverse (1 + x^2)",symmetric])
      apply (subst mult_assoc)
      apply (subst minus_mult_minus[of 1 1,symmetric])
      apply (subst mult_assoc[symmetric])
      apply (subst mult_commute)
      apply (subst interval_lebesgue_integral_cmult(2)[of lborel "-\<infinity>" 0 "\<lambda>x. inverse (1 + x^2)" "-1",symmetric])
      prefer 2
      apply (subst mult_commute)
      apply (subst power2_eq_square)
      apply (subst minus_mult_minus[symmetric])
      apply (subst power2_eq_square[symmetric])
      apply (subst interval_integral_substitution_nonneg'[of "-\<infinity>" 0 uminus "\<lambda>x. -1" "\<lambda>x. inverse (1 + x^2)" \<infinity> 0,symmetric])
      apply (auto intro!: DERIV_intros)
      apply (auto simp add: ereal_tendsto_simps filterlim_uminus_at_top_at_bot)
      apply (subst zero_ereal_def)+
      apply (auto simp add: ereal_tendsto_simps)
      apply (metis (hide_lams, no_types) filterlim_at filterlim_at_split filterlim_def
             filtermap_at_minus minus_zero order_refl)
      prefer 2 apply (subst interval_integral_endpoints_reverse[symmetric], rule refl)
      (* For some reason get the same subgoal twice here. *)
      unfolding interval_lebesgue_integrable_def einterval_def apply auto
      apply (tactic {* distinct_subgoals_tac *})
      apply (rule set_integrable_subset[of lborel _ UNIV _], auto)
      apply (unfold integrable_def, subst power2_eq_square, auto)
      apply (subst (asm) positive_integral_eq_integral_measurable)
      apply (subst power2_eq_square, auto)
      using Billingsley_ex_17_5 unfolding interval_lebesgue_integral_def einterval_def
      apply auto
    proof -
      have *: "\<And>x. max 0 (ereal (- inverse (1 + x * x))) = 0"
        by (metis comm_semiring_1_class.normalizing_semiring_rules(4) ereal_max_0
            inverse_minus_eq inverse_nonpositive_iff_nonpositive le_add_same_cancel1 max.boundedE
            max.order_iff neg_le_0_iff_le zero_ereal_def zero_le_double_add_iff_zero_le_single_add
            zero_le_square)
      assume "\<integral>\<^sup>+ x. ereal (- inverse (1 + x\<^sup>2)) \<partial>lborel = \<infinity>"
      hence "\<integral>\<^sup>+ x. max 0 (ereal (- inverse (1 + x\<^sup>2))) \<partial>lborel = \<infinity>"
        by (auto simp add: positive_integral_max_0)
      thus False by (auto simp add: * power2_eq_square)
    qed
    ultimately show ?thesis using Billingsley_ex_17_5 by simp
  qed
  have "AE x \<in> {0..} in lborel. LBINT u=0..\<infinity>. exp (-u * x) = 1/x"
    apply (rule AE_I[where N = "{0}"], auto)
    apply (subst (asm) minus_mult_left)
    using integral_expneg_alpha_atLeast0 using less_eq_real_def by metis
  hence "sinc t = LBINT x=0..t. sin x * (LBINT u=0..\<infinity>. exp (-u * x))" sorry
  also have "... = LBINT x=0..t. (LBINT u=0..\<infinity>. sin x * exp (-u * x))"
    apply (subst interval_lebesgue_integral_cmult(2))
    unfolding interval_lebesgue_integrable_def einterval_def integrable_def apply auto
    using integral_expneg_alpha_atLeast0 positive_integral_eq_integral_measurable sorry
  also have "... = LBINT u=0..\<infinity>. (LBINT x=0..t. sin x * exp (-u * x))"
    using pair_sigma_finite.Fubini_integral (* Need an interval_integral version of this. *) sorry
  also have "... = (LBINT u=0..\<infinity>. inverse (1 + u^2)) - (LBINT u=0..\<infinity>. inverse (1 + u^2) *
    exp (-u * t) * (u * sin t + cos t))" sorry
  finally show "sinc t = pi / 2 - (LBINT u=0..\<infinity>. inverse (1 + u^2) * exp (-u * t) *
    (u * sin t + cos t))" using 179 by simp
qed

lemma sinc_at_top: "(sinc ---> pi / 2) at_top"
  sorry

lemma Billingsley_26_15:
  assumes "T \<ge> 0"
  shows "\<And>\<theta>. LBINT t=0..T. sin (t * \<theta>) / t = sgn \<theta> * sinc (T * \<bar>\<theta>\<bar>)"
  sorry

end