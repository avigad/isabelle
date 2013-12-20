(*  
Theory: Real_to_Complex.thy
Authors: Jeremy Avigad, Luke Serafin 

Differentiation and integration for functions from the reals to the complex numbers.
*)

theory Real_to_Complex

imports Library_Misc

begin

(** Real and complex parts of a function. **)

abbreviation RE :: "('a \<Rightarrow> complex) \<Rightarrow> 'a \<Rightarrow> real" where
"RE f \<equiv> (\<lambda>x. Re (f x))"

abbreviation IM :: "('a \<Rightarrow> complex) \<Rightarrow> 'a \<Rightarrow> real" where
"IM f \<equiv> (\<lambda>x. Im (f x))"

lemma isCont_RE_IM_iff: "isCont f z = (isCont (RE f) z \<and> isCont (IM f) z)"
  unfolding isCont_def
  apply (auto intro: tendsto_intros)
  apply (frule tendsto_Complex[where f = "RE f" and g = "IM f"])
  by auto

lemma Re_part_setsum:
  assumes "finite S"
  shows "Re (\<Sum>x\<in>S. f x) = (\<Sum>x\<in>S. RE f x)"
  apply (rule finite_induct) using assms by auto

lemma Im_part_setsum:
  assumes "finite S"
  shows "Im (\<Sum>x\<in>S. f x) = (\<Sum>x\<in>S. IM f x)"
  apply (rule finite_induct) using assms by auto


(** Function e^(ix). **)

abbreviation iexp :: "real \<Rightarrow> complex" where
  "iexp \<equiv> (\<lambda>x. expi (\<i> * of_real x))"

declare [[coercion "complex_of_real :: real \<Rightarrow> complex"]]

lemma isCont_new_expir [simp]: "isCont (\<lambda>x. exp (Complex 0 x)) x"
apply (rule isCont_exp')
apply (subgoal_tac "Complex 0 = (\<lambda>x. ii * x)")
apply (erule ssubst)
apply (rule isCont_mult)
apply auto
done


(** Differentiation of functions of type real \<Rightarrow> complex. **)

definition complex_deriv :: "[real \<Rightarrow> complex, real, complex] \<Rightarrow> bool"
("(CDERIV (_)/ (_)/ :> (_))" [1000, 1000, 60] 60) where
  "CDERIV f z :> D \<equiv> (DERIV (RE f) z :> Re D) \<and> (DERIV (IM f) z :> Im D)"

lemma Re_has_derivative: "FDERIV Re x :> Re"
  apply (rule FDERIV_I, auto)
  by (rule bounded_linearI [of _ 1], auto simp add: abs_Re_le_cmod)

lemma Im_has_derivative: "FDERIV Im x :> Im"
  apply (rule FDERIV_I, auto)
  by (rule bounded_linearI [of _ 1], auto simp add: abs_Im_le_cmod)

lemma complex_of_real_has_derivative: 
    "FDERIV complex_of_real x :> complex_of_real"
  apply (rule FDERIV_I, auto)
  by (rule bounded_linearI [of _ 1], auto simp add: scaleR_conv_of_real)

lemma has_vector_derivative_complex_mul:
  "(f has_vector_derivative f') net ==> ((\<lambda>x. (c\<Colon>complex) * f x) has_vector_derivative (c * f')) net"
  unfolding has_vector_derivative_def
  apply (subst mult_scaleR_right [symmetric])
  by (rule FDERIV_mult_right)

lemma CDERIV_has_vector_derivative: "(CDERIV f z :> D) = (f has_vector_derivative D) (at z)"
proof (auto simp add: complex_deriv_def)
  assume "(DERIV (RE f) z :> Re D)"
  hence 1: "FDERIV (RE f) z :> op * (Re D)" by (simp add: DERIV_conv_has_derivative)
  have 2: "((\<lambda>x. complex_of_real (Re (f x))) has_vector_derivative 
      (complex_of_real (Re D))) (at z)"
    apply (subst has_vector_derivative_def, subst scaleR_conv_of_real)
    apply (subst of_real_mult [symmetric], subst mult_commute)
    by (rule FDERIV_compose [OF 1 "complex_of_real_has_derivative" [of _]])
  assume "DERIV (IM f) z :> Im D"
  hence 3: "FDERIV (IM f) z :> op * (Im D)" by (simp add: DERIV_conv_has_derivative)
  have 4: "((\<lambda>x. complex_of_real (Im (f x))) has_vector_derivative 
      (complex_of_real (Im D))) (at z)"
    apply (subst has_vector_derivative_def, subst scaleR_conv_of_real)
    apply (subst of_real_mult [symmetric], subst mult_commute)
    by (rule FDERIV_compose [OF 3 "complex_of_real_has_derivative" [of _]])
  have feq: "f = (\<lambda>x. complex_of_real (Re (f x)) + ii * complex_of_real (Im (f x)))"
    by simp
  have "D = complex_of_real (Re D) + ii * complex_of_real (Im D)" by simp
  thus "(f has_vector_derivative D) (at z)"
    apply (elim ssubst, subst feq)
    apply (rule has_vector_derivative_add [OF 2])
    by (rule has_vector_derivative_complex_mul [OF 4])
next
  assume "(f has_vector_derivative D) (at z)"
  hence 1: "FDERIV f z :> (\<lambda>x. x *\<^sub>R D)" by (simp add: has_vector_derivative_def)
  from FDERIV_compose [OF 1, OF Re_has_derivative] 
  show "DERIV (RE f) z :> Re D"
    apply (simp add: DERIV_conv_has_derivative)
    by (subst (asm) mult_commute)
  from FDERIV_compose [OF 1, OF Im_has_derivative] 
  show "DERIV (IM f) z :> Im D"
    apply (simp add: DERIV_conv_has_derivative)
    by (subst (asm) mult_commute)
qed
 
lemma CDERIV_iexp: "CDERIV iexp x :> \<i> * iexp x"
  apply (unfold complex_deriv_def)
  apply (auto intro!: DERIV_intros)
  apply (simp_all add: cis_conv_exp[symmetric])
  done

lemma CDERIV_const: "CDERIV (\<lambda>x. c) x :> 0"
  unfolding complex_deriv_def by (auto intro!: DERIV_intros)

lemma CDERIV_add: "\<lbrakk> CDERIV f x :> Da; CDERIV g x :> Db\<rbrakk> \<Longrightarrow>
  CDERIV (\<lambda>x. f x + g x) x :> Da + Db"
  unfolding complex_deriv_def by (auto intro!: DERIV_intros)

lemma CDERIV_minus: "CDERIV f x :> D \<Longrightarrow> CDERIV (\<lambda>x. - f x) x :> - D"
  unfolding complex_deriv_def by (auto intro!: DERIV_intros)

lemma CDERIV_diff: "\<lbrakk>CDERIV f x :> Da; CDERIV g x :> Db\<rbrakk> \<Longrightarrow>
  CDERIV (\<lambda>x. f x - g x) x :> Da - Db"
  unfolding complex_deriv_def by (auto intro!: DERIV_intros)

lemma CDERIV_mult: "\<lbrakk>CDERIV f x :> Da; CDERIV g x :> Db\<rbrakk> \<Longrightarrow>
  CDERIV (\<lambda>x. f x * g x) x :> (Da * (g x)) + (Db * (f x))"
  unfolding complex_deriv_def by (auto intro!: DERIV_intros)

lemma RE_deriv: "CDERIV f x :> f' x \<Longrightarrow> DERIV (RE f) x :> (RE f') x"
  unfolding complex_deriv_def by auto

lemma IM_deriv: "CDERIV f x :> f' x \<Longrightarrow> DERIV (IM f) x :> (IM f') x"
  unfolding complex_deriv_def by auto

lemma CDERIV_rect: "\<lbrakk>DERIV (RE f) x :> Da; DERIV (IM f) x :> Db\<rbrakk> \<Longrightarrow>
  CDERIV f x :> Complex Da Db"
  unfolding complex_deriv_def by auto

lemma CDERIV_isCont: "CDERIV f x :> D \<Longrightarrow> isCont f x"
  unfolding complex_deriv_def
  apply (subst isCont_RE_IM_iff)
  apply (auto intro: DERIV_isCont)
  done

lemma CDERIV_unique: "\<lbrakk>CDERIV f x :> Da; CDERIV f x :> Db\<rbrakk> \<Longrightarrow> Da = Db"
  unfolding complex_deriv_def
  apply (subst complex_eq_iff)
  apply (auto intro: DERIV_unique)
  done

lemma CDERIV_setsum:
  assumes "finite S"
  and "\<And>n. n \<in> S \<Longrightarrow> CDERIV (\<lambda>x. f x n) x :> (f' x n)"
  shows "CDERIV (\<lambda>x. setsum (f x) S) x :> setsum (f' x) S"
  using assms CDERIV_const by induct (auto intro!: CDERIV_add)

lemma CDERIV_of_real [simp]: "DERIV f x :> u \<Longrightarrow>
   (CDERIV (%x. complex_of_real (f x)) x :> complex_of_real u)"
  unfolding complex_deriv_def by auto



(*
    It probably makes more sense for us to say that a function
    from the reals to the complex numbers is integrable iff
    the real and imaginary parts are. Modulo a few sorry's,
    the last lemma in this section shows that to be equivalent to the def
    currently in Complex_Integration.thy
*)

lemma borel_measurable_Re [simp]: "Re \<in> borel_measurable borel"
apply (rule borel_measurable_continuous_on1)
apply (simp add: continuous_on_def)
apply (rule allI)
apply (rule tendsto_Re)
apply (rule tendsto_ident_at)
done

lemma borel_measurable_Im [simp]: "Im \<in> borel_measurable borel"
apply (rule borel_measurable_continuous_on1)
apply (simp add: continuous_on_def)
apply (rule allI)
apply (rule tendsto_Im)
apply (rule tendsto_ident_at)
done

lemma isCont_complex_of_real: "\<And>x. isCont complex_of_real x"
  using tendsto_Complex by auto

lemma borel_measurable_complex_of_real [simp]: "complex_of_real \<in> 
  borel_measurable borel"
apply (rule borel_measurable_continuous_on1)
apply (rule continuous_at_imp_continuous_on)
apply (unfold continuous_def)
apply (simp add: netlimit_at)
using isCont_complex_of_real unfolding isCont_def by auto


(* This needs to be adapted from Borel_Space.thy *)
(*
lemma complex_borel_measurable_add[simp, intro]:
  fixes f :: "'a \<Rightarrow> complex"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. f x + g x) \<in> borel_measurable M"
sorry

lemma complex_borel_measurable_cmult:
  fixes f :: "'a \<Rightarrow> complex"
  assumes f: "f \<in> borel_measurable M"
  shows "(\<lambda>x. c * f x) \<in> borel_measurable M"
sorry
*)
(* this could be made more efficient. *)
(*
lemma complex_borel_measurable_eq: "f \<in> borel_measurable M = 
  ((RE f \<in> borel_measurable M) \<and> (IM f \<in> borel_measurable M))"
apply (auto simp add: RE_def IM_def)
apply (subgoal_tac "(%x. Re (f x)) = Re o f")
prefer 2 apply force 
apply (erule ssubst)
apply (erule measurable_comp)
apply (rule borel_measurable_Re)
apply (subgoal_tac "(%x. Im (f x)) = Im o f")
prefer 2 apply force 
apply (erule ssubst)
apply (erule measurable_comp)
apply (rule borel_measurable_Im)
apply (subgoal_tac "f = (%x. complex_of_real (Re (f x)) + 
    ii * complex_of_real (Im (f x)))")
prefer 2 apply force
apply (erule ssubst) 
apply (rule complex_borel_measurable_add)
apply (subgoal_tac "(%x. complex_of_real (Re (f x))) = complex_of_real o
    (%x. Re (f x))")
prefer 2 apply force
apply (erule ssubst)
apply (erule measurable_comp)
apply (rule borel_measurable_complex_of_real)
apply (rule complex_borel_measurable_cmult)
apply (subgoal_tac "(%x. complex_of_real (Im (f x))) = complex_of_real o
    (%x. Im (f x))")
prefer 2 apply force
apply (erule ssubst)
apply (erule measurable_comp)
apply (rule borel_measurable_complex_of_real)
done

lemma complex_integrable_eq: 
  "complex_integrable M f = (integrable M (RE f) \<and>
    integrable M (IM f))"
by (auto simp add: complex_integrable_def integrable_def RE_def IM_def
   complex_borel_measurable_eq)
*)

(*
  Linearity facts transported from real case. 
  (There's more stuff like this in Lebesgue_Integration.thy.)
*)

(** Need to fix complex integral syntax. **)

definition complex_integrable :: "'a measure \<Rightarrow> ('a \<Rightarrow> complex) \<Rightarrow> bool" where
  "complex_integrable M f \<equiv> integrable M (RE f) \<and> integrable M (IM f)"

definition complex_lebesgue_integral :: "'a measure \<Rightarrow> ('a \<Rightarrow> complex) \<Rightarrow> complex" ("integral\<^sup>C") where
  "integral\<^sup>C M f = of_real (\<integral>x. (RE f) x \<partial>M) + ii * of_real (\<integral>x. (IM f) x \<partial>M)"

syntax
  "_complex_lebesgue_integral" :: "pttrn \<Rightarrow> complex \<Rightarrow> 'a measure \<Rightarrow> complex"
 ("\<integral>\<^sup>C _. _ \<partial>_" [60,61] 110)

translations
  "\<integral>\<^sup>Cx. f \<partial>M" == "CONST complex_lebesgue_integral M (\<lambda>x. f)"

lemma Re_integral_push: "Re (integral\<^sup>C M f) = integral\<^sup>L M (RE f)"
  by (unfold complex_lebesgue_integral_def, auto)

lemma Im_integral_push: "Im (integral\<^sup>C M f) = integral\<^sup>L M (IM f)"
  by (unfold complex_lebesgue_integral_def, auto)

lemma complex_integral_cong:
  assumes "\<forall>x. x \<in> space M \<longrightarrow> f x = g x"
  shows "integral\<^sup>C M f = integral\<^sup>C M g"
using assms unfolding complex_lebesgue_integral_def by (auto intro: integral_cong)

lemma complex_integral_cong_AE:
  assumes "AE x in M. f x = g x"
  shows "integral\<^sup>C M f = integral\<^sup>C M g"
using assms unfolding complex_lebesgue_integral_def by (auto intro: integral_cong_AE)

lemma RE_complex_indicator [simp]:
  "(RE (\<lambda>x. f x * complex_of_real (indicator {a..b} x))) =
    (\<lambda>x. RE f x * (indicator {a..b} x))"
 by auto

lemma IM_complex_indicator [simp]:
  "(IM (\<lambda>x. f x * complex_of_real (indicator {a..b} x))) =
    (\<lambda>x. IM f x * (indicator {a..b} x))"
by auto

lemma borel_integral_FTC_complex:
  fixes a b :: real
  assumes "a \<le> b" 
    and F: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> CDERIV F x :> f x"
    and cont: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> isCont f x"
  shows "(\<integral>\<^sup>C x. f x * of_real(indicator {a .. b} x) \<partial>lborel) = F b - F a"
apply (unfold complex_lebesgue_integral_def, simp)
apply (subgoal_tac "F b - F a = Complex (RE F b - RE F a) (IM F b - IM F a)")
apply (erule ssubst)
apply (rule arg_cong2) back back
apply (rule integral_FTC_atLeastAtMost, rule assms)
apply (frule F, assumption)
apply (simp add: complex_deriv_def)
using cont apply (subst (asm) isCont_RE_IM_iff, auto)
apply (rule integral_FTC_atLeastAtMost, rule assms)
apply (frule F, assumption)
apply (simp add: complex_deriv_def)
using cont apply (subst (asm) isCont_RE_IM_iff, auto)
by (simp add: complex_diff [symmetric])

lemma complex_integral_add [simp]: 
  assumes "complex_integrable M f" "complex_integrable M g"
  shows "complex_integrable M (\<lambda>t. f t + g t)"
  and "(\<integral>\<^sup>Ct. f t + g t \<partial>M) = integral\<^sup>C M f + integral\<^sup>C M g"
using assms by (auto simp add: complex_integrable_def
  complex_lebesgue_integral_def complex_of_real_def)

lemma complex_integral_zero [simp]:
  shows "complex_integrable M (\<lambda>x. 0)" 
  and "(\<integral>\<^sup>C x. 0 \<partial>M)  = 0"
by (auto simp add: complex_integrable_def complex_lebesgue_integral_def
  complex_of_real_def)

(* is integrability really needed for the second fact? *)
lemma complex_integral_cmult [simp]:
  assumes "complex_integrable M f"
  shows "complex_integrable M (\<lambda>t. a * f t)"
  and "(\<integral>\<^sup>C t. a * f t \<partial>M) = a * complex_lebesgue_integral M f"
using assms apply (auto simp add: complex_integrable_def
  complex_lebesgue_integral_def complex_of_real_def complex_surj complex_mult)
by (metis complex_mult complex_surj)


(* is there are corresponding one for the usual integral? *)
lemma complex_integral_cdiv [simp]:
  assumes "complex_integrable M f"
  shows "complex_integrable M (\<lambda>t. f t / a)"
  and "(\<integral>\<^sup>C t. f t / a \<partial>M) = complex_lebesgue_integral M f / a"
using assms
apply (simp_all only: complex_divide_def)
apply (subst mult_commute, force)
by (subst mult_commute, simp)

lemma complex_integral_uminus [simp, intro]:
  "(\<integral>\<^sup>Cx. - f x \<partial>M) = - complex_lebesgue_integral M f"
unfolding complex_lebesgue_integral_def
by (auto simp add: lebesgue_integral_uminus complex_of_real_def)

lemma complex_integral_minus[intro, simp]:
  assumes "complex_integrable M f"
  shows "complex_integrable M (\<lambda>x. - f x)" 
(*  and "(\<integral>\<^sup>Cx. - f x \<partial>M) = - complex_lebesgue_integral M f" *)
using assms
by (auto simp add: complex_integrable_def complex_lebesgue_integral_def
  complex_of_real_def)

lemma complex_integral_diff[simp, intro]:
  assumes f: "complex_integrable M f" and g: "complex_integrable M g"
  shows "complex_integrable M (\<lambda>t. f t - g t)"
  and "(\<integral>\<^sup>C t. f t - g t \<partial>M) = complex_lebesgue_integral M f - 
    complex_lebesgue_integral M g"
using complex_integral_add[OF f complex_integral_minus(1) [OF g]]
unfolding diff_conv_add_uminus complex_integral_minus[OF g]
by auto

abbreviation
  "set_complex_lebesgue_integral M A f == 
    complex_lebesgue_integral M (\<lambda>x. f x * complex_of_real (indicator A x))"

syntax
  "_set_complex_lebesgue_integral" ::
  "'a set \<Rightarrow> pttrn \<Rightarrow> real \<Rightarrow> 'a measure \<Rightarrow> real"
("\<integral>\<^bsup>C\<^esup>\<^bsub>_\<^esub> _. _ \<partial>_" [0,60,61] 110)

translations
  "\<integral>\<^bsup>C\<^esup>\<^bsub>A\<^esub> x. f \<partial>M" == "CONST set_complex_lebesgue_integral M A (\<lambda>x. f)"

(*
abbreviation 
  "cl_interval_complex_lebesgue_integral M a b f == (if a \<le> b then
  set_complex_lebesgue_integral M {a..b} f
  else - set_complex_lebesgue_integral M {b..a} f)"
*)

definition
  cmp_conn_complex_lebesgue_integral :: "real measure \<Rightarrow> real \<Rightarrow> real \<Rightarrow>
    (real \<Rightarrow> complex) \<Rightarrow> complex"
where
  "cmp_conn_complex_lebesgue_integral M a b f == (if a \<le> b then
  set_complex_lebesgue_integral M {a..b} f
  else - set_complex_lebesgue_integral M {b..a} f)"

syntax
  "_cmp_conn_complex_lebesgue_integral" :: "ereal \<Rightarrow> ereal \<Rightarrow> pttrn \<Rightarrow> real \<Rightarrow> 
  real measure \<Rightarrow> real" ("\<integral>\<^bsup>C\<^esup>\<^bsub>_\<^esub>\<^bsup>_\<^esup> _. _ \<partial>_" [0,0,60,61] 110)

translations
  "\<integral>\<^bsup>C\<^esup>\<^bsub>a\<^esub>\<^bsup>b\<^esup> x. f \<partial>M" == "CONST cmp_conn_complex_lebesgue_integral M a b (\<lambda>x. f)"

definition 
  irange :: "real \<Rightarrow> real \<Rightarrow> real set"
where 
  "irange a b \<equiv> if a \<le> b then {a..b} else {b..a}"

lemma cmp_conn_complex_lebesgue_interval_simps [simp]:
  shows
   "a \<le> b \<Longrightarrow> \<integral>\<^bsup>C\<^esup>\<^bsub>a\<^esub>\<^bsup>b\<^esup> x. f x \<partial>M = set_complex_lebesgue_integral M {a..b} f" and
   "~(a \<le> b) \<Longrightarrow> \<integral>\<^bsup>C\<^esup>\<^bsub>a\<^esub>\<^bsup>b\<^esup> x. f x \<partial>M = -set_complex_lebesgue_integral M {b..a} f"
  unfolding cmp_conn_complex_lebesgue_integral_def by auto

lemma irange_simps [simp]:
  shows
    "a \<le> b \<Longrightarrow> irange a b = {a..b}" and
    "~(a \<le> b) \<Longrightarrow> irange a b = {b..a}"
unfolding irange_def by auto

theorem cmp_conn_complex_integral_FTC:
  "(\<And>x. x \<in> irange a b \<Longrightarrow> CDERIV F x :> f x) \<Longrightarrow>
   (\<And>x. x \<in> irange a b \<Longrightarrow> isCont f x) \<Longrightarrow>
    \<integral>\<^bsup>C\<^esup>\<^bsub>a\<^esub>\<^bsup>b\<^esup> x. f x \<partial>lborel = F b - F a"
apply (case_tac "a \<le> b")
apply simp
apply (erule borel_integral_FTC_complex, auto)
apply (subgoal_tac "set_complex_lebesgue_integral lborel {b..a} f = F a - F b")
apply force
apply (rule borel_integral_FTC_complex)
by auto

(*
  Repeating things for the integral with bounds 
*)

lemma cmp_conn_complex_integral_add [intro, simp]: 
  assumes "complex_integrable M (%x. f x * 
      complex_of_real (indicator (irange a b) x))" 
    and "complex_integrable M (%x. g x * 
      complex_of_real (indicator (irange a b) x))"
  shows "(\<integral>\<^bsup>C\<^esup>\<^bsub>a\<^esub>\<^bsup>b\<^esup> t. f t + g t \<partial>M) = (\<integral>\<^bsup>C\<^esup>\<^bsub>a\<^esub>\<^bsup>b\<^esup> t. f t \<partial>M) + (\<integral>\<^bsup>C\<^esup>\<^bsub>a\<^esub>\<^bsup>b\<^esup> t. g t \<partial>M)"
using assms unfolding cmp_conn_complex_lebesgue_integral_def
by (auto simp add: ring_distribs)

lemma cmp_conn_complex_integral_cmult [simp]: 
  assumes "complex_integrable M (%x. f x * 
      complex_of_real (indicator (irange a b) x))" 
  shows "(\<integral>\<^bsup>C\<^esup>\<^bsub>a\<^esub>\<^bsup>b\<^esup> t. c * f t \<partial>M) = c * (\<integral>\<^bsup>C\<^esup>\<^bsub>a\<^esub>\<^bsup>b\<^esup> t. f t \<partial>M)"
using assms unfolding cmp_conn_complex_lebesgue_integral_def
by (auto simp add: mult_assoc)

lemma cmp_conn_complex_integral_cdiv [simp]:
  assumes "complex_integrable M (%x. f x * 
      complex_of_real (indicator (irange a b) x))" 
  shows "(\<integral>\<^bsup>C\<^esup>\<^bsub>a\<^esub>\<^bsup>b\<^esup> t. f t / c \<partial>M) = (\<integral>\<^bsup>C\<^esup>\<^bsub>a\<^esub>\<^bsup>b\<^esup> t. f t \<partial>M) / c"
using assms unfolding cmp_conn_complex_lebesgue_integral_def
by auto

lemma cmp_conn_complex_integral_minus [simp]:
    "(\<integral>\<^bsup>C\<^esup>\<^bsub>a\<^esub>\<^bsup>b\<^esup> t. - f t \<partial>M) = - (\<integral>\<^bsup>C\<^esup>\<^bsub>a\<^esub>\<^bsup>b\<^esup> t. f t \<partial>M)"
unfolding cmp_conn_complex_lebesgue_integral_def
by (auto simp add: complex_integral_uminus)

lemma cmp_conn_complex_integral_diff [simp]:
   assumes "complex_integrable M (%x. f x * 
      complex_of_real (indicator (irange a b) x))" 
    and "complex_integrable M (%x. g x * 
      complex_of_real (indicator (irange a b) x))"
  shows "(\<integral>\<^bsup>C\<^esup>\<^bsub>a\<^esub>\<^bsup>b\<^esup> t. f t - g t \<partial>M) = (\<integral>\<^bsup>C\<^esup>\<^bsub>a\<^esub>\<^bsup>b\<^esup> t. f t \<partial>M) - (\<integral>\<^bsup>C\<^esup>\<^bsub>a\<^esub>\<^bsup>b\<^esup> t. g t \<partial>M)"
using assms unfolding cmp_conn_complex_lebesgue_integral_def
by (auto simp add: ring_distribs)

(* fix this *)
lemma cl_interval_complex_integral_cong:
  "\<forall>x. x \<in> space M \<longrightarrow> f x = g x \<Longrightarrow> (\<integral>\<^bsup>C\<^esup>\<^bsub>a\<^esub>\<^bsup>b\<^esup> t. f t \<partial>M) = (\<integral>\<^bsup>C\<^esup>\<^bsub>a\<^esub>\<^bsup>b\<^esup> t. g t \<partial>M)"
unfolding cmp_conn_complex_lebesgue_integral_def
by (auto intro: complex_integral_cong)


lemma cmp_conn_complex_integrable_isCont: 
  "(\<And>x. x \<in> irange (a::real) b \<Longrightarrow> isCont f x) \<Longrightarrow>
    complex_integrable lborel 
      (\<lambda>x. f x * complex_of_real (indicator (irange a b) x))"
  by (auto intro!: integrable_atLeastAtMost_isCont 
    simp add: complex_integrable_def irange_def)



lemma integral_expir:
  fixes x y :: real
  shows "\<integral>\<^bsup>C\<^esup>\<^bsub>x\<^esub>\<^bsup>y\<^esup> s.
    expir s \<partial>lborel = ii * expir x - ii * expir y"
apply (subst cmp_conn_complex_integral_FTC [where F = "%x. -ii * expir x"])
apply (rule CDERIV_cong)
apply (rule CDERIV_mult)
apply (rule CDERIV_minus)
apply (rule CDERIV_const)
apply (rule CDERIV_expi)
apply (auto simp add: field_simps)
done

definition complex_integrable :: "'a measure \<Rightarrow> ('a \<Rightarrow> complex) \<Rightarrow> bool" where
"complex_integrable M f \<longleftrightarrow> integrable M (RE f) \<and> integrable M (IM f)"

definition complex_lebesgue_integral ::
"'a measure \<Rightarrow> ('a \<Rightarrow> complex) \<Rightarrow> complex" where "complex_lebesgue_integral M f =
  Complex (\<integral> x. RE f x \<partial>M) (\<integral> x. IM f x \<partial>M)"

syntax
"_complex_lebesgue_integral" :: "pttrn \<Rightarrow> 'a measure \<Rightarrow> complex \<Rightarrow> complex"
("(3CLINT _|_. _)" [0,110,61] 60)

translations
"CLINT x|M. f" == "CONST complex_lebesgue_integral M (\<lambda>x. f)"

syntax
"_complex_lebesgue_borel_integral" :: "pttrn \<Rightarrow> complex \<Rightarrow> complex"
("(2CLBINT _. _)" [0,61] 60)

translations
"CLBINT x. f" == "CONST complex_lebesgue_integral CONST lborel (\<lambda>x. f)"

abbreviation
"complex_set_lebesgue_integral M A f \<equiv>
complex_lebesgue_integral M (\<lambda>x. f x * indicator A x)"

syntax
"_complex_set_lebesgue_integral" ::
"pttrn \<Rightarrow> 'a set \<Rightarrow> 'a measure \<Rightarrow> complex \<Rightarrow> complex"
("(4CLINT _:_|_. _)" [0,60,110,60] 60)

translations
"CLINT x:A|M. f" == "CONST complex_set_lebesgue_integral M A (\<lambda>x. f)"

syntax
"_complex_set_lebesgue_borel_integral" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> complex \<Rightarrow> complex"
("(3CLBINT _:_. _)" [0,60,60] 60)

translations
"CLBINT x:A. f" == "CONST complex_set_lebesgue_integral CONST lborel A (\<lambda>x. f)"

abbreviation
"complex_cmp_conn_lebesgue_integral M a b f \<equiv>
if (a \<le> b) then (CLINT x:{a..b}|M. f x) else -(CLINT x:{a..b}|M. f x)"

syntax
"_complex_cmp_conn_lebesgue_borel_integral" ::
"pttrn \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex \<Rightarrow> complex"
("(4CLBINT _:_.._. _)" [0,60,60,61] 60)

translations
"CLBINT x:a..b. f" ==
"CONST complex_cmp_conn_lebesgue_integral CONST lborel a b (\<lambda>x. f)"

lemma complex_integral_cong:
  assumes "\<forall>x. x \<in> space M \<longrightarrow> f x = g x"
  shows "CLINT x|M. f x = CLINT x|M. g x"
  by (metis (no_types) assms complex_lebesgue_integral_def integral_cong)

lemma complex_integral_cong_AE:
  assumes "AE x in M. f x = g x"
  shows "CLINT x|M. f x = CLINT x|M. g x"
proof-
  have "AE x in M. RE f x = RE g x" using assms by auto
  hence Re_eq: "integral\<^sup>L M (RE f) = integral\<^sup>L M (RE g)"
    using integral_cong_AE[of "RE f" "RE g"] by auto
  have "AE x in M. IM f x = IM g x" using assms by auto
  hence Im_eq: "integral\<^sup>L M (IM f) = integral\<^sup>L M (IM g)"
    using integral_cong_AE[of "IM f" "IM g"] by auto
  with Re_eq Im_eq show ?thesis unfolding complex_lebesgue_integral_def by auto
qed

lemma integral_FTC_atLeastAtMost_real_to_complex:
  fixes a b :: real
  assumes "a \<le> b"
  and F: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> CDERIV F x :> f x"
  and cont: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> isCont f x"
  shows "CLBINT x:a..b. f x = F b - F a"
proof-
  have "(LBINT x:a..b. RE f x) = RE F b - RE f a"
    unfolding complex_lebesgue_integral_def
    using assms integral_FTC_atLeastAtMost[of a b "RE F" "RE f"]
    sorry
    (* How to make this proof trivial? *)


end