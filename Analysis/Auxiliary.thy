(* Auxiliary lemmas to formalize distributions
   Author: Sudeep Kanav
   Author: Johannes Hölzl *)

theory Auxiliary
  imports Probability
begin

interpretation lborel_pair!: pair_sigma_finite lborel lborel
  proof qed

subsection {* ereal lemmas *}

lemma ereal_mult1_left[simp]:
  fixes a::ereal
  shows "ereal 1 * a = a"
  by (metis monoid_mult_class.mult.left_neutral one_ereal_def)

lemma ereal_mult1_right[simp]:
  fixes a::ereal
  shows "a * ereal 1 = a"
  by (metis monoid_mult_class.mult.right_neutral one_ereal_def)

subsection {* measurable lemmas *}

lemma measurable_lborel_Pair1[simp]: "measurable (lborel  \<Otimes>\<^sub>M lborel) M = measurable (borel \<Otimes>\<^sub>M borel) M"
  by (intro measurable_cong_sets sets_pair_measure_cong sets_lborel refl)
  
lemma measurable_lborel_Pair2[simp]: "measurable M (lborel  \<Otimes>\<^sub>M lborel) = measurable M (borel \<Otimes>\<^sub>M borel)"
  by (intro measurable_cong_sets sets_pair_measure_cong sets_lborel refl)

lemma borel_measurable_power[measurable]: "f \<in> borel_measurable M \<Longrightarrow> (\<lambda>x. f x ^ k :: real) \<in> borel_measurable M"
  by (induct k) auto

lemma borel_measurable_isCont: 
  fixes f :: "real \<Rightarrow> real"
  shows "\<forall>x. isCont f x \<Longrightarrow> f \<in> borel_measurable borel"
  by (simp add: borel_measurable_continuous_on1 continuous_at_imp_continuous_on)

subsection {* finite measure lemmas *}

lemma (in finite_measure) finite_measure_distr:
  assumes f: "f \<in> measurable M M'" 
  shows "finite_measure (distr M M' f)"
proof (rule finite_measureI)
  have "f -` space M' \<inter> space M = space M" using f by (auto dest: measurable_space)
  with f show "emeasure (distr M M' f) (space (distr M M' f)) \<noteq> \<infinity>" by (auto simp: emeasure_distr)
qed

lemma finite_measure_pair_measure:
  assumes "finite_measure M" "finite_measure N"
  shows "finite_measure (N  \<Otimes>\<^sub>M M)"
proof (rule finite_measureI)
  interpret M: finite_measure M by fact
  interpret N: finite_measure N by fact
  show "emeasure (N  \<Otimes>\<^sub>M M) (space (N  \<Otimes>\<^sub>M M)) \<noteq> \<infinity>"
    by (auto simp: space_pair_measure M.emeasure_pair_measure_Times)
qed

lemma (in finite_measure) borel_measurable_positive_integral[measurable (raw)]:
  "split f \<in> borel_measurable (N  \<Otimes>\<^sub>M M) \<Longrightarrow> (\<lambda>x. \<integral>\<^sup>+ y. f x y \<partial>M) \<in> borel_measurable N"
  by (rule borel_measurable_positive_integral)

subsection {* positive integral lemmas *}


lemma positive_integral_ereal_indicator_mult:
  fixes f :: "real =>real"
  shows "integral\<^sup>P lborel (\<lambda>x. ereal (f x) * indicator A x) = integral\<^sup>P lborel (\<lambda>x. ereal (f x * indicator A x))"
  by (auto intro!: positive_integral_cong split:split_indicator)


lemma positive_integral_real_affine:
  fixes c :: real 
  assumes c: "c \<noteq> 0" and f: "f \<in> borel_measurable borel" "AE x in M. 0 \<le> f x"
  shows "(\<integral>\<^sup>+ x. f x \<partial> lborel) = \<bar>c\<bar> * (\<integral>\<^sup>+x. f (t + c * x) \<partial>lborel)"
  by (subst lebesgue_real_affine[OF c, of t])
     (simp add: assms positive_integral_density positive_integral_distr positive_integral_cmult)

lemma positive_integral_indicator_partition:
  fixes f::"real \<Rightarrow> real"
  assumes  f[measurable]: "f \<in> borel_measurable lborel"
  assumes [simp,arith]: "\<And>x. 0 \<le> f x"
  shows  "integral\<^sup>P lborel f = integral\<^sup>P lborel (\<lambda>x. f x * indicator {0..} x) + integral\<^sup>P lborel (\<lambda>x. f x * indicator {..0} x)"
  by (auto intro!: positive_integral_cong_AE AE_I[where N= "{0}"]
  simp:mult_nonneg_nonneg positive_integral_add[symmetric] split:split_indicator)

lemma positive_integral_even_function_eq:
  fixes f :: "real \<Rightarrow> real" 
  assumes [simp, measurable]: "f \<in> borel_measurable borel" "\<And>x. 0 \<le> f x" 
  assumes even: "\<And>x. f x = f (- x)"
  shows "integral\<^sup>P lborel (\<lambda>x. f x * indicator {0..} x) = integral\<^sup>P lborel (\<lambda>x. f x * indicator {..0} x)"
  apply (subst positive_integral_real_affine[where c="-1" and t="0" and M="lborel"])
  using even
  by (auto intro!: positive_integral_cong simp: borel_measurable_indicator split:split_indicator)

lemma positive_integral_even_function:
  fixes f :: "real \<Rightarrow> real" 
  assumes [simp, measurable]: "f \<in> borel_measurable borel" "\<And>x. 0 \<le> f x" 
  assumes even: "\<And>x. f x = f (- x)"
  shows "integral\<^sup>P lborel f = 2 * integral\<^sup>P lborel (\<lambda>x. f x * indicator {0..} x)"
  apply (auto simp: positive_integral_indicator_partition) 
  using even
  apply (subst positive_integral_even_function_eq[symmetric], auto)
  by (cases "\<integral>\<^sup>+ x. ereal (f x * indicator {0..} x) \<partial>lborel", auto)

lemma positive_integral_power_nat:
  fixes x::real
  fixes k:: nat
  assumes [simp, arith]: "0 \<le> x" 
  shows "integral\<^sup>P lborel (\<lambda>y. ereal (y^k) * indicator {0..x} y) = x^(1 + k) / (1 + k)"  
proof-
  let ?F = "\<lambda>x. x^(1 + k) / (1 + k)"
  have "integral\<^sup>P lborel (\<lambda>y. ereal( y^ k) * indicator {0..x} y) = ereal( ?F x) - ereal( ?F 0)"
  by (rule positive_integral_FTC_atLeastAtMost)   
    (auto intro!:DERIV_intros positive_integral_FTC_atLeastAtMost simp del: power_Suc) 
  also have "... = x^ (1 + k) / (1 + k)" by force
  finally show ?thesis by fast
qed

subsection {* independence *}

lemma (in prob_space) prob_indep_random_variable:
  assumes ind[simp]: "indep_var N X N Y"
  assumes [simp]: "A \<in> sets N" "B:sets N"
  shows "\<P>(x in M. (X x)\<in>A \<and>  (Y x)\<in> B ) = \<P>(x in M. (X x)\<in>A) * \<P>(x in M. (Y x)\<in>B)"
proof-
  have  " \<P>(x in M. (X x)\<in>A \<and>  (Y x)\<in> B ) = prob ((\<lambda>x. (X x, Y x)) -` (A \<times> B) \<inter> space M)" 
    by (auto intro!:arg_cong[where f= prob])
  also have "...=  prob (X -` A \<inter> space M) * prob (Y -` B \<inter> space M)"  
    by (auto intro!: indep_varD[where Ma=N and Mb=N])     
  also have "... = \<P>(x in M. (X x)\<in>A) * \<P>(x in M. (Y x)\<in>B)"
    by (auto intro!: arg_cong2[where f= "op *"] arg_cong[where f= prob])
  finally show ?thesis .
qed

lemma random_vars_insert:
  fixes X:: "'a \<Rightarrow> 'b \<Rightarrow> real"
  shows "\<And>x. {X j x | j. j \<in> insert i I} = insert (X i x) {X i x | i. i \<in> I}"
  by auto

lemma borel_measurable_Min:
  fixes X:: "'a \<Rightarrow> 'b \<Rightarrow> real"
  assumes finI: "finite I"
  assumes *: "\<And>i. i \<in> I \<Longrightarrow> X i \<in> borel_measurable M"
  shows "(\<lambda>x. Min {X i x | i. i \<in> I}) \<in> borel_measurable M"
  using assms apply (induct I, simp)
  apply (case_tac "F={}", simp)
  apply (subst random_vars_insert)
  by (subst Min_insert) auto

lemma (in prob_space) indep_var_compose:
  assumes "indep_var M1 X1 M2 X2" "Y1 \<in> measurable M1 N1" "Y2 \<in> measurable M2 N2"
  shows "indep_var N1 (Y1 \<circ> X1) N2 (Y2 \<circ> X2)"
proof -
  have "indep_vars (bool_case N1 N2) (\<lambda>b. bool_case Y1 Y2 b \<circ> bool_case X1 X2 b) UNIV"
    using assms
    by (intro indep_vars_compose[where M'="bool_case M1 M2"])
       (auto simp: indep_var_def split: bool.split)
  also have "(\<lambda>b. bool_case Y1 Y2 b \<circ> bool_case X1 X2 b) = bool_case (Y1 \<circ> X1) (Y2 \<circ> X2)"
    by (simp add: fun_eq_iff split: bool.split)
  finally show ?thesis
    unfolding indep_var_def .
qed

lemma (in prob_space) indep_vars_restrict:
  assumes ind: "indep_vars M' X I" and K: "\<And>j. j \<in> L \<Longrightarrow> K j \<subseteq> I" and J: "disjoint_family_on K L"
  shows "indep_vars (\<lambda>j. PiM (K j) M') (\<lambda>j \<omega>. restrict (\<lambda>i. X i \<omega>) (K j)) L"
  unfolding indep_vars_def
proof safe
  fix j assume "j \<in> L" then show "random_variable (Pi\<^sub>M (K j) M') (\<lambda>\<omega>. \<lambda>i\<in>K j. X i \<omega>)"
    using K ind by (auto simp: indep_vars_def intro!: measurable_restrict)
next
  have X: "\<And>i. i \<in> I \<Longrightarrow> X i \<in> measurable M (M' i)"
    using ind by (auto simp: indep_vars_def)
  let ?proj = "\<lambda>j S. {(\<lambda>\<omega>. \<lambda>i\<in>K j. X i \<omega>) -` A \<inter> space M |A. A \<in> S}"
  let ?UN = "\<lambda>j. sigma_sets (space M) (\<Union>i\<in>K j. { X i -` A \<inter> space M| A. A \<in> sets (M' i) })"
  show "indep_sets (\<lambda>i. sigma_sets (space M) (?proj i (sets (Pi\<^sub>M (K i) M')))) L"
  proof (rule indep_sets_mono_sets[rotated])
    fix j assume j: "j \<in> L"
    have "sigma_sets (space M) (?proj j (sets (Pi\<^sub>M (K j) M'))) = 
      sigma_sets (space M) (sigma_sets (space M) (?proj j (prod_algebra (K j) M')))"
      using j K X[THEN measurable_space] unfolding sets_PiM
      by (subst sigma_sets_vimage_commute) (auto simp add: Pi_iff)
    also have "\<dots> = sigma_sets (space M) (?proj j (prod_algebra (K j) M'))"
      by (rule sigma_sets_sigma_sets_eq) auto
    also have "\<dots> \<subseteq> ?UN j"
    proof (rule sigma_sets_mono, safe del: disjE elim!: prod_algebraE)
      fix J E assume J: "finite J" "J \<noteq> {} \<or> K j = {}"  "J \<subseteq> K j" and E: "\<forall>i. i \<in> J \<longrightarrow> E i \<in> sets (M' i)"
      show "(\<lambda>\<omega>. \<lambda>i\<in>K j. X i \<omega>) -` prod_emb (K j) M' J (Pi\<^sub>E J E) \<inter> space M \<in> ?UN j"
      proof cases
        assume "K j = {}" with J show ?thesis
          by (auto simp add: sigma_sets_empty_eq prod_emb_def)
      next
        assume "K j \<noteq> {}" with J have "J \<noteq> {}"
          by auto
        { interpret sigma_algebra "space M" "?UN j"
            by (rule sigma_algebra_sigma_sets) auto 
          have "\<And>A. (\<And>i. i \<in> J \<Longrightarrow> A i \<in> ?UN j) \<Longrightarrow> INTER J A \<in> ?UN j"
            using `finite J` `J \<noteq> {}` by (rule finite_INT) blast }
        note INT = this

        from `J \<noteq> {}` J K E[rule_format, THEN sets.sets_into_space] j
        have "(\<lambda>\<omega>. \<lambda>i\<in>K j. X i \<omega>) -` prod_emb (K j) M' J (Pi\<^sub>E J E) \<inter> space M
          = (\<Inter>i\<in>J. X i -` E i \<inter> space M)"
          apply (subst prod_emb_PiE[OF _ ])
          apply auto []
          apply auto []
          apply (auto simp add: Pi_iff intro!: X[THEN measurable_space])
          apply (erule_tac x=i in ballE)
          apply auto
          done
        also have "\<dots> \<in> ?UN j"
          apply (rule INT)
          apply (rule sigma_sets.Basic)
          using `J \<subseteq> K j` E
          apply auto
          done
        finally show ?thesis .
      qed
    qed
    finally show "sigma_sets (space M) (?proj j (sets (Pi\<^sub>M (K j) M'))) \<subseteq> ?UN j" .
  next
    show "indep_sets ?UN L"
    proof (rule indep_sets_collect_sigma)
      show "indep_sets (\<lambda>i. {X i -` A \<inter> space M |A. A \<in> sets (M' i)}) (\<Union>j\<in>L. K j)"
      proof (rule indep_sets_mono_index)
        show "indep_sets (\<lambda>i. {X i -` A \<inter> space M |A. A \<in> sets (M' i)}) I"
          using ind unfolding indep_vars_def2 by auto
        show "(\<Union>l\<in>L. K l) \<subseteq> I"
          using K by auto
      qed
    next
      fix l i assume "l \<in> L" "i \<in> K l"
      show "Int_stable {X i -` A \<inter> space M |A. A \<in> sets (M' i)}"
        apply (auto simp: Int_stable_def)
        apply (rule_tac x="A \<inter> Aa" in exI)
        apply auto
        done
    qed fact
  qed
qed

lemma (in prob_space) indep_var_restrict:
  assumes ind: "indep_vars M' X I" and AB: "A \<inter> B = {}" "A \<subseteq> I" "B \<subseteq> I"
  shows "indep_var (PiM A M') (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) A) (PiM B M') (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) B)"
proof -
  have *:
    "bool_case (Pi\<^sub>M A M') (Pi\<^sub>M B M') = (\<lambda>b. PiM (bool_case A B b) M')"
    "bool_case (\<lambda>\<omega>. \<lambda>i\<in>A. X i \<omega>) (\<lambda>\<omega>. \<lambda>i\<in>B. X i \<omega>) = (\<lambda>b \<omega>. \<lambda>i\<in>bool_case A B b. X i \<omega>)"
    by (simp_all add: fun_eq_iff split: bool.split)
  show ?thesis
    unfolding indep_var_def * using AB
    by (intro indep_vars_restrict[OF ind]) (auto simp: disjoint_family_on_def split: bool.split)
qed

lemma (in prob_space) indep_vars_Min:
  fixes X :: "'i \<Rightarrow> 'a \<Rightarrow> real"
  assumes I: "finite I" "i \<notin> I" and indep: "indep_vars (\<lambda>_. borel) X (insert i I)"
  shows "indep_var borel (X i) borel (\<lambda>\<omega>. Min {X i \<omega> | i. i \<in> I})"
proof -
  have "indep_var
    borel ((\<lambda>f. f i) \<circ> (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) {i}))
    borel ((\<lambda>f. Min {f i | i. i \<in> I}) \<circ> (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) I))"
    using I by (intro indep_var_compose[OF indep_var_restrict[OF indep]] borel_measurable_Min) auto
  also have "((\<lambda>f. f i) \<circ> (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) {i})) = X i"
    by auto
  also have "((\<lambda>f. Min {f i | i. i \<in> I}) \<circ> (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) I)) = (\<lambda>\<omega>. Min {X i \<omega> | i. i \<in> I})"
    by (auto cong: rev_conj_cong)
  finally show ?thesis
    unfolding indep_var_def .
qed

(* had to use lborel as borel was not working. I don't know why *)
lemma (in prob_space) indep_vars_setsum:
  fixes X :: "'i \<Rightarrow> 'a \<Rightarrow> real"
  assumes I: "finite I" "i \<notin> I" and indep: "indep_vars (\<lambda>_. borel) X (insert i I)"
  shows "indep_var lborel (X i) lborel (\<lambda>\<omega>. \<Sum>i\<in>I. X i \<omega>)"
proof -
  have "indep_var 
    lborel ((\<lambda>f. f i) \<circ> (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) {i}))
    lborel ((\<lambda>f. \<Sum>i\<in>I. f i) \<circ> (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) I))"
    using I by (intro indep_var_compose[OF indep_var_restrict[OF indep]] ) auto
  also have "((\<lambda>f. f i) \<circ> (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) {i})) = X i"
    by auto
  also have "((\<lambda>f. \<Sum>i\<in>I. f i) \<circ> (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) I)) = (\<lambda>\<omega>. \<Sum>i\<in>I. X i \<omega>)"
    by (auto cong: rev_conj_cong)
  finally show ?thesis .
qed

lemma (in prob_space) indep_vars_subset:
  assumes "indep_vars M' X I" "J \<subseteq> I"
  shows "indep_vars M' X J"
  using assms unfolding indep_vars_def indep_sets_def
  by auto

lemma setsum_pos_pos:
  fixes f::"_ \<Rightarrow> real"
  assumes "finite I" "I \<noteq> {}" 
  assumes "\<And>i. i \<in> I \<Longrightarrow> 0 < f i"
  shows "0 < (\<Sum>i\<in>I. f i )"
  using assms apply (induct I rule: finite_ne_induct)
  by (auto simp:setsum_insert)  fastforce

(* should make it more general for any space M rather than lborel *)
lemma  prob_space_density_positive_integral[intro, simp]:
assumes [simp, measurable]:"f \<in> borel_measurable lborel"
assumes "prob_space (density lborel f)"
shows "integral\<^sup>P lborel f = ereal 1"
proof-
  let ?F = "(density lborel f)"
  have "integral\<^sup>P lborel f = emeasure ?F UNIV"
    by (subst emeasure_density[of f lborel UNIV], auto)
  also have "... = emeasure ?F (space ?F)" by auto
  also have "... = 1" using assms(2) prob_space.emeasure_space_1 by blast
  finally show ?thesis by(simp add: one_ereal_def)
qed

lemma (in prob_space) indep_var_neg:
  assumes [simp]:"indep_var lborel X lborel Y"
  shows "indep_var lborel X lborel (\<lambda>x. - Y x)"
proof -
  have "indep_var lborel ( (\<lambda>x. x) o X) lborel ((\<lambda>x. - x) o Y)"
    by (auto intro!: indep_var_compose assms) 
  then show ?thesis by (simp add: o_def)
qed

lemma
  assumes "integral\<^sup>P M f = ereal x" "AE x in M. 0 \<le> f x" "f \<in> borel_measurable M"
  shows integrable_if_positive_integral: "integrable M f"
  and lebesgue_integral_eq_positive_integral: "integral\<^sup>L M f = x"
  using assms
  apply (metis PInfty_neq_ereal(1) integrable_nonneg)
  by (metis (full_types) PInfty_neq_ereal(1) assms(1) assms(2) assms(3) integrable_nonneg positive_integral_eq_integral real_of_ereal(2))

lemma integrable_affine:
  fixes f :: "real \<Rightarrow> real"
  assumes [arith]: "c \<noteq> 0"
  shows "integrable lborel f = integrable lborel (\<lambda>x. f (t + c * x))"
proof(auto)
  assume *: "integrable lborel f" 
  then have **: "f \<in> borel_measurable lborel" by (simp add: integrable_def)

  have [simp]: "(\<integral>\<^sup>+ x. ereal (f x / \<bar>c\<bar>) \<partial>lborel) = (1/ \<bar>c\<bar>) * \<integral>\<^sup>+ x. ereal (f x) \<partial>lborel"
       "(\<integral>\<^sup>+ x. ereal (- (f x / \<bar>c\<bar>)) \<partial>lborel) = (1 / \<bar>c\<bar>) * \<integral>\<^sup>+ x. ereal (- f x ) \<partial>lborel" 
    using ** by (auto intro!: positive_integral_cong simp: positive_integral_cmult[symmetric])
  
  show "integrable lborel (\<lambda>x. f (t + c * x))"
    using *
    apply (subst lebesgue_real_affine[where c= "1 / c" and t = "- t / c"], simp)
    unfolding integrable_def apply safe 
    by (simp_all add: positive_integral_density positive_integral_distr field_simps)
next
  { assume "(\<lambda>x. f (t + x * c)) \<in> borel_measurable borel"
    then have "(\<lambda>x. f (t + ((x - t) / c) * c)) \<in> borel_measurable borel"
      by (rule measurable_compose[rotated]) simp
    also have "(\<lambda>x. f (t + ((x - t) / c) * c)) = f"
      by simp
    finally have "f \<in> borel_measurable borel" . }
  note 1[simp] = this

  assume *: "integrable lborel (\<lambda>x. f (t + c * x))"
  then have **: "f \<in> borel_measurable lborel" by (simp add: integrable_def field_simps)

  have [simp]: "(\<integral>\<^sup>+ x. ereal (f x / \<bar>c\<bar>) \<partial>lborel) = (1/ \<bar>c\<bar>) * \<integral>\<^sup>+ x. ereal (f x) \<partial>lborel"
       "(\<integral>\<^sup>+ x. ereal (- (f x / \<bar>c\<bar>)) \<partial>lborel) = (1 / \<bar>c\<bar>) * \<integral>\<^sup>+ x. ereal (- f x ) \<partial>lborel" 
    using ** by (auto intro!: positive_integral_cong simp: positive_integral_cmult[symmetric])

  show "integrable lborel f"
    using *
    apply (subst(asm) lebesgue_real_affine[where c= "1/ c" and t = "- t / c"], simp)
    unfolding integrable_def apply safe
    by (simp_all add: positive_integral_density positive_integral_distr field_simps)
qed

lemma (in prob_space) distributed_density_integrable:
  assumes D: "distributed M lborel X f"
  assumes [simp]: "prob_space (density lborel f)"
  shows "integrable lborel f"
  using D unfolding distributed_def
  by (auto intro!: integrable_if_positive_integral[where x = 1] simp: borel_measurable_ereal_iff)

lemma (in prob_space) prob_space_distributed_density_lebesgue_integral[intro]:
  assumes D:"distributed M lborel X f"
  assumes [simp]: "prob_space (density lborel f)"
  assumes [simp, measurable]: "f \<in> borel_measurable lborel"
  shows "integral\<^sup>L lborel f = 1"
  apply (subst lebesgue_integral_eq_positive_integral[OF prob_space_density_positive_integral])
  using D unfolding distributed_def by auto

lemma (in prob_space) expectation_affine[simp]:
  fixes f :: "real \<Rightarrow> real"
  assumes D: "distributed M lborel X f"
  assumes [simp]: "prob_space (density lborel f)"
  assumes [simp]: " integrable lborel (\<lambda>x. x * f x)"
  shows "expectation (\<lambda>x. a +  b* X x) = a + b * expectation X"
  apply (subst distributed_integral[OF D, of "\<lambda>x. a +  b * x", symmetric])
  apply (simp_all add: distrib_left comm_semiring_1_class.normalizing_semiring_rules(19))
  apply (subst integral_add)
  apply (auto simp: mult_commute distributed_density_integrable[OF D])
  apply (subst(3) mult_commute)
  using D distributed_def
  by (auto intro!: prob_space_distributed_density_lebesgue_integral[OF D assms(2)] simp: distributed_integral[OF D, of "\<lambda>x. x"])

subsection {* Variance *}

abbreviation (in prob_space) "variance X \<equiv> integral\<^sup>L M (\<lambda>x. (X x - expectation X)\<^sup>2)"

lemma (in prob_space) variance_eq:
  assumes I[simp]: "integrable M X"
  assumes [simp]: "integrable M (\<lambda>x. (X x)\<^sup>2)"  (* this seems to be the problem, as I cannot prove it for generic densities which means
I can not use it freely *)
  shows "variance X = expectation (\<lambda>x. (X x)\<^sup>2) - (expectation X)\<^sup>2"
  apply (simp add: power2_diff)
  apply(subst comm_semiring_1_class.normalizing_semiring_rules(16))
  by (simp_all add:prob_space power2_eq_square[symmetric])

lemma (in prob_space) variance_affine:
  fixes f::"real \<Rightarrow> real"
  assumes [arith]: "b \<noteq> 0"
  assumes D[intro]: "distributed M lborel X f"
  assumes [simp]: "prob_space (density lborel f)"
  assumes I[simp]: "integrable M X"
  assumes I2[simp]: "integrable M (\<lambda>x. (X x)\<^sup>2)" 
  shows "variance (\<lambda>x. a +  b* X x) = b\<^sup>2 * variance X"
  apply(subst variance_eq)
  by (auto simp:power2_sum power_mult_distrib prob_space variance_eq right_diff_distrib)

lemma (in prob_space) variance_positive: "0 \<le> variance X"
  by (auto intro!: lebesgue_integral_nonneg)

lemma a3_minus_b3:
  fixes a::real 
  fixes b::real
  shows "a^3 - b^3 = (a - b) * (a\<^sup>2 + a * b + b\<^sup>2)"
  by (auto simp: power3_eq_cube power2_eq_square left_diff_distrib distrib_left)

lemma integral_by_parts_integrable:
  fixes f g F G::"real \<Rightarrow> real"
  assumes "a \<le> b"
  assumes cont_f[intro]: "!!x. a \<le>x \<Longrightarrow> x\<le>b \<Longrightarrow> isCont f x"
  assumes cont_g[intro]: "!!x. a \<le>x \<Longrightarrow> x\<le>b \<Longrightarrow> isCont g x"
  assumes [intro]: "!!x. DERIV F x :> f x"
  assumes [intro]: "!!x. DERIV G x :> g x"
  shows  "integrable lborel (\<lambda>x.((F x) * (g x) + (f x) * (G x)) * indicator {a .. b} x)"
  by (auto intro!: borel_integrable_atLeastAtMost isCont_intros) (auto intro!: DERIV_isCont)

lemma integral_by_parts:
  fixes f g F G::"real \<Rightarrow> real"
  assumes [arith]: "a \<le> b"
  assumes cont_f[intro]: "!!x. a \<le>x \<Longrightarrow> x\<le>b \<Longrightarrow> isCont f x"
  assumes cont_g[intro]: "!!x. a \<le>x \<Longrightarrow> x\<le>b \<Longrightarrow> isCont g x"
  assumes [intro]: "!!x. DERIV F x :> f x"
  assumes [intro]: "!!x. DERIV G x :> g x"
  shows "(\<integral>x. (F x * g x) * indicator {a .. b} x \<partial>lborel)
            =  F b * G b - F a * G a - \<integral>x. (f x * G x) * indicator {a .. b} x \<partial>lborel" 
proof-
  have 0: "(\<integral>x. (F x * g x + f x * G x) * indicator {a .. b} x \<partial>lborel) = F b * G b - F a * G a"
    by (rule integral_FTC_atLeastAtMost, auto intro!: DERIV_intros isCont_intros) (auto intro!: DERIV_isCont)

  have "(\<integral>x. (F x * g x + f x * G x) * indicator {a .. b} x \<partial>lborel) =
    (\<integral>x. (F x * g x) * indicator {a .. b} x \<partial>lborel) + \<integral>x. (f x * G x) * indicator {a .. b} x \<partial>lborel"
    apply (subst integral_add(2)[symmetric])
    apply (auto intro!: borel_integrable_atLeastAtMost isCont_intros)
    by (auto intro!: DERIV_isCont integral_cong split:split_indicator)

  thus ?thesis using 0 by auto
qed

lemma ln_sqrt: "0< x \<Longrightarrow> ln (sqrt x) = ln x / 2"
  by (simp add: ln_powr powr_numeral ln_powr[symmetric] mult_commute)

lemma tendsto_mult_indicator:
  fixes f :: "real \<Rightarrow> real"
  assumes [simp, intro]: "\<And>x. isCont f x"
  assumes [simp, arith]: "\<And>x. 0\<le> f x"  (* not happy about this condition. i dont think its required *)
  assumes [simp]: "integrable lborel f"
  assumes [measurable]: "f \<in> borel_measurable borel"
  shows "((\<lambda>x. \<integral>xa. f xa * indicator {0..x} xa \<partial>lborel) ---> \<integral>xa. f xa * indicator {0..} xa \<partial>lborel) at_top"
  apply (auto intro!: borel_integrable_atLeastAtMost monoI integral_mono tendsto_at_topI_sequentially  
    split:split_indicator)
  apply (rule integral_dominated_convergence[where w = " \<lambda>x. f x * indicator {0..} x"])
  unfolding LIMSEQ_def  
  apply (auto intro!: AE_I2 tendsto_mult integrable_mult_indicator split: split_indicator)
  by (metis ge_natfloor_plus_one_imp_gt less_imp_le)

lemma filterlim_power2_at_top[intro]: "filterlim (\<lambda>(x::real). x\<^sup>2) at_top at_top"
  by (auto intro!: filterlim_at_top_mult_at_top filterlim_ident simp: power2_eq_square)

lemma (in prob_space) uniform_distributed_variance:
  fixes a b :: real
  assumes D: "distributed M lborel X (\<lambda>x. indicator {a .. b} x / measure lborel {a .. b})"
  shows "variance X = (b - a)\<^sup>2 / 12"
proof (subst distributed_integral[OF D, of "(\<lambda>x. (x - expectation X)\<^sup>2)", symmetric])
  let ?\<mu> = "expectation X"
  have [arith]: "a < b" using uniform_distributed_bounds[OF D] .
  
  have "(\<integral>x. indicator {a .. b} x / measure lborel {a .. b} * (x - ?\<mu>)\<^sup>2 \<partial>lborel) 
        = \<integral>x. ((x - ?\<mu>)\<^sup>2 / measure lborel {a .. b}) * indicator {a .. b} x \<partial>lborel"
    by (intro integral_cong) auto
  also have "... = \<integral> x. (x\<^sup>2 / measure lborel {a .. b}) * indicator {(a - ?\<mu>) .. (b - ?\<mu>)} x \<partial>lborel"
    apply (subst lebesgue_integral_real_affine[where t= ?\<mu> and c = 1], auto)
    unfolding indicator_def by (auto intro!: integral_cong)
  also have "(\<integral>x. (x\<^sup>2 / measure lborel {a .. b}) * indicator {(a- ?\<mu>) .. (b- ?\<mu>)} x \<partial>lborel) = (b - a)\<^sup>2 / 12"
  proof (subst integral_FTC_atLeastAtMost)
    fix x
    show "DERIV (\<lambda>x. x^3 / (3 * measure lborel {a..b})) x :> x\<^sup>2 / measure lborel {a..b}"
      using uniform_distributed_params[OF D] by (auto intro!: DERIV_intros)

    show "isCont (\<lambda>x. x\<^sup>2 / Sigma_Algebra.measure lborel {a..b}) x"
      using uniform_distributed_params[OF D] by (auto intro!: isCont_divide)

    have 1:"(b - expectation X) ^ 3 / (3 * measure lborel {a..b}) -
            (a - expectation X) ^ 3 / (3 * measure lborel {a..b}) = ((b - a) / 2)\<^sup>2 / 3"
      using `a < b`
      apply (auto simp: measure_def diff_divide_distrib[symmetric])
      apply (simp only: left_diff_distrib[symmetric] right_diff_distrib[symmetric] nonzero_mult_divide_mult_cancel_right2
              a3_minus_b3 uniform_distributed_expectation[OF D] diff_divide_eq_iff power2_eq_square) 
      by (auto simp: field_simps)

    show "(b - expectation X) ^ 3 / (3 * measure lborel {a..b}) -
        (a - expectation X) ^ 3 / (3 * measure lborel {a..b}) = (b - a)\<^sup>2 / 12"
      by (subst 1, auto simp: field_simps power2_eq_square)
  qed (insert `a < b`, simp)

  finally show "(\<integral>x. indicator {a..b} x / measure lborel {a..b} * (x - expectation X)\<^sup>2 \<partial>lborel) = (b - a)\<^sup>2 / 12" .
qed auto


lemma distr_cong: "M = K \<Longrightarrow> sets N = sets L \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> f x = g x) \<Longrightarrow> distr M N f = distr K L g"
  using sets_eq_imp_space_eq[of N L] by (simp add: distr_def Int_def cong: rev_conj_cong)

lemma AE_borel_affine: 
  fixes P :: "real \<Rightarrow> bool"
  shows "c \<noteq> 0 \<Longrightarrow> Measurable.pred borel P \<Longrightarrow> AE x in lborel. P x \<Longrightarrow> AE x in lborel. P (t + c * x)"
  by (subst lebesgue_real_affine[where t="- t / c" and c="1 / c"])
     (simp_all add: AE_density AE_distr_iff field_simps)

lemma density_distr:
  assumes [measurable]: "f \<in> borel_measurable N" "X \<in> measurable M N"
  shows "density (distr M N X) f = distr (density M (\<lambda>x. f (X x))) N X"
  by (intro measure_eqI)
     (auto simp add: emeasure_density positive_integral_distr emeasure_distr
           split: split_indicator intro!: positive_integral_cong)

lemma (in prob_space) distributed_affine:
  fixes f :: "real \<Rightarrow> ereal"
  assumes f: "distributed M lborel X f"
  assumes c: "c \<noteq> 0"
  shows "distributed M lborel (\<lambda>x. t + c * X x) (\<lambda>x. f ((x - t) / c) / \<bar>c\<bar>)"
  unfolding distributed_def
proof safe
  have [measurable]: "f \<in> borel_measurable borel"
    using f by (simp add: distributed_def)
  have [measurable]: "X \<in> borel_measurable M"
    using f by (simp add: distributed_def)

  show "(\<lambda>x. f ((x - t) / c) / \<bar>c\<bar>) \<in> borel_measurable lborel"
    by simp
  show "random_variable lborel (\<lambda>x. t + c * X x)"
    by simp
  
  have "AE x in lborel. 0 \<le> f x"
    using f by (simp add: distributed_def)
  from AE_borel_affine[OF _ _ this, where c="1/c" and t="- t / c"] c
  show "AE x in lborel. 0 \<le> f ((x - t) / c) / ereal \<bar>c\<bar>"
    by (auto simp add: field_simps)

  have eq: "\<And>x. ereal \<bar>c\<bar> * (f x / ereal \<bar>c\<bar>) = f x"
    using c by (simp add: divide_ereal_def mult_ac)
    
  have "density lborel f = distr M lborel X"
    using f by (simp add: distributed_def)
  with c show "distr M lborel (\<lambda>x. t + c * X x) = density lborel (\<lambda>x. f ((x - t) / c) / ereal \<bar>c\<bar>)"
    by (subst (2) lebesgue_real_affine[where c="c" and t="t"])
       (simp_all add: density_density_eq density_distr distr_distr field_simps eq cong: distr_cong)
qed

lemma (in prob_space) distributed_affineI:
  fixes f :: "real \<Rightarrow> ereal"
  assumes f: "distributed M lborel (\<lambda>x. (X x - t) / c) (\<lambda>x. \<bar>c\<bar> * f (x * c + t))"
  assumes c: "c \<noteq> 0"
  shows "distributed M lborel X f"
proof -
  have eq: "\<And>x. f x * ereal \<bar>c\<bar> / ereal \<bar>c\<bar> = f x"
    using c by (simp add: divide_ereal_def mult_ac)

  show ?thesis
    using distributed_affine[OF f c, where t=t] c
    by (simp add: field_simps eq)
qed


end
