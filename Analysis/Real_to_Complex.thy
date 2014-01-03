(*  
Theory: Real_to_Complex.thy
Authors: Jeremy Avigad, Luke Serafin 

Differentiation and integration for functions from the reals to the complex numbers. Also transfers
notation from Interval_Integral.thy.

*)

theory Real_to_Complex

imports Library_Misc Interval_Integral

begin

(* Move these to Borel_Sets.thy *)

lemma borel_measurable_root [measurable (raw)]:
  "f \<in> borel_measurable M \<Longrightarrow> (\<lambda>x. root n (f x)) \<in> borel_measurable M"
apply (rule borel_measurable_continuous_on) back
by (rule continuous_at_imp_continuous_on, auto, rule isCont_real_root)

lemma borel_measurable_sqrt [measurable (raw)]:
  "f \<in> borel_measurable M \<Longrightarrow> (\<lambda>x. sqrt (f x)) \<in> borel_measurable M"
unfolding sqrt_def by measurable

lemma borel_measurable_power [measurable (raw)]:
   fixes f :: "_ \<Rightarrow> 'b::{power,real_normed_algebra}"
   assumes f: "f \<in> borel_measurable M"
   shows "(\<lambda>x. (f x) ^ n) \<in> borel_measurable M"
apply (rule borel_measurable_continuous_on [OF _ f])
by (rule continuous_on_power, rule continuous_on_id)

(** Real and complex parts of a function. **)

abbreviation RE :: "('a \<Rightarrow> complex) \<Rightarrow> 'a \<Rightarrow> real" where
"RE f \<equiv> (\<lambda>x. Re (f x))"

abbreviation IM :: "('a \<Rightarrow> complex) \<Rightarrow> 'a \<Rightarrow> real" where
"IM f \<equiv> (\<lambda>x. Im (f x))"

abbreviation Cnj :: "('a \<Rightarrow> complex) \<Rightarrow> 'a \<Rightarrow> complex" where
"Cnj f \<equiv> (\<lambda>x. cnj (f x))"

lemma isCont_RE_IM_iff: "isCont f z = (isCont (RE f) z \<and> isCont (IM f) z)"
  unfolding isCont_def
  apply (auto intro: tendsto_intros)
  by (frule tendsto_Complex[where f = "RE f" and g = "IM f"], auto)

lemma continuous_RE_IM: "continuous (at x within s) (RE f) \<Longrightarrow>
    continuous (at x within s) (IM f) \<Longrightarrow>
    continuous (at x within s) f"
  unfolding continuous_def
by (frule tendsto_Complex[where f = "RE f" and g = "IM f"], auto)

lemma continuous_RE_IM_iff: "continuous (at x within s) f = 
    (continuous (at x within s) (RE f) \<and> continuous (at x within s) (IM f))"
  apply (auto intro: continuous_RE_IM)
  unfolding continuous_def
by (auto intro: tendsto_intros)

(* TODO: versions of the above for continuous_on? Below we use continuous_on_eq_continuous_within
   to avoid this, but it is a pain in the neck *)

declare [[coercion "complex_of_real :: real \<Rightarrow> complex"]]

lemma real_to_complex_expand: "f = (\<lambda>x. (RE f) x + ii * (IM f) x)"
  by auto 

lemma Re_setsum:
  assumes "finite S"
  shows "Re (\<Sum>x\<in>S. f x) = (\<Sum>x\<in>S. RE f x)"
  apply (rule finite_induct) using assms by auto

lemma Im_setsum:
  assumes "finite S"
  shows "Im (\<Sum>x\<in>S. f x) = (\<Sum>x\<in>S. IM f x)"
  apply (rule finite_induct) using assms by auto


(** Function e^(ix). **)

(* it is unfortunate the the complex exponential is named expi, because that would
   be a good name for this function.
*)

abbreviation iexp :: "real \<Rightarrow> complex" where
  "iexp \<equiv> (\<lambda>x. expi (\<i> * of_real x))"

lemma isCont_iexp [simp]: "isCont iexp x"
  by (rule isCont_exp', rule isCont_mult, auto)


(** Differentiation of functions of type real \<Rightarrow> complex. **)

(* compare to FDERIV *)
abbreviation complex_deriv_within :: 
  "(real \<Rightarrow> complex) \<Rightarrow> real \<Rightarrow> real set \<Rightarrow> complex \<Rightarrow> bool"
  ("(CDERIV (_)/ (_)/ : (_)/ :> (_))" [1000, 1000, 1000, 60] 60)
where
  "CDERIV f x : s :> D \<equiv> (f has_vector_derivative D) (at x within s)"

abbreviation complex_deriv :: "[real \<Rightarrow> complex, real, complex] \<Rightarrow> bool"
("(CDERIV (_)/ (_)/ :> (_))" [1000, 1000, 60] 60) where
  "CDERIV f z :> D \<equiv> CDERIV f z : UNIV :> D"

(* previously:
abbreviation complex_deriv :: "[real \<Rightarrow> complex, real, complex] \<Rightarrow> bool"
("(CDERIV (_)/ (_)/ :> (_))" [1000, 1000, 60] 60) where
  "CDERIV f z :> D \<equiv> (f has_vector_derivative D) (at z)"
*)

lemma Re_has_derivative: "FDERIV Re x : s :> Re"
  apply (rule FDERIV_I, auto)
  by (rule bounded_linearI [of _ 1], auto simp add: abs_Re_le_cmod)

lemma Im_has_derivative: "FDERIV Im x : s :> Im"
  apply (rule FDERIV_I, auto)
  by (rule bounded_linearI [of _ 1], auto simp add: abs_Im_le_cmod)

lemma complex_of_real_has_derivative: 
    "FDERIV complex_of_real x : s :> complex_of_real"
  apply (rule FDERIV_I, auto)
  by (rule bounded_linearI [of _ 1], auto simp add: scaleR_conv_of_real)

lemma has_vector_derivative_complex_mul:
  "(f has_vector_derivative f') net \<Longrightarrow> 
    ((\<lambda>x. (c\<Colon>complex) * f x) has_vector_derivative (c * f')) net"
  unfolding has_vector_derivative_def
  apply (subst mult_scaleR_right [symmetric])
  by (rule FDERIV_mult_right)

(* this is an instance of the previous lemma *)
lemma CDERIV_cmult: "(CDERIV f z : s :> D) \<Longrightarrow> (CDERIV (\<lambda>x. c * f x) z : s :> c * D)"
  by (erule has_vector_derivative_complex_mul)

(* is this a bad name? *)
lemma CDERIV_def: "(CDERIV f z : s :> D) = 
    (DERIV (RE f) z : s :> Re D \<and> DERIV (IM f) z : s :> Im D)"
proof (auto)
  assume "(CDERIV f z : s :> D)"
  hence 1: "FDERIV f z : s :> (\<lambda>x. x *\<^sub>R D)" by (simp add: has_vector_derivative_def)
  from FDERIV_compose [OF 1, OF Re_has_derivative] 
  show "DERIV (RE f) z : s :> Re D" by (simp add: deriv_fderiv)
  from FDERIV_compose [OF 1, OF Im_has_derivative] 
  show "DERIV (IM f) z : s :> Im D" by (simp add: deriv_fderiv)
next
  assume "(DERIV (RE f) z : s :> Re D)"
  hence 1: "FDERIV (RE f) z : s :> (\<lambda>x. x * Re D)" by (simp add: deriv_fderiv)
  have 2: "CDERIV (\<lambda>x. complex_of_real (RE f x)) z : s :> complex_of_real (Re D)"
    apply (subst has_vector_derivative_def, subst scaleR_conv_of_real)
    apply (subst of_real_mult [symmetric])
    apply (rule FDERIV_in_compose [OF 1])
    by (rule complex_of_real_has_derivative)
  assume "DERIV (IM f) z : s :> Im D"
  hence 3: "FDERIV (IM f) z : s :> (\<lambda>x. x * Im D)" by (simp add: deriv_fderiv)
  have 4: "CDERIV (\<lambda>x. complex_of_real (IM f x)) z : s :> complex_of_real (Im D)"
    apply (subst has_vector_derivative_def, subst scaleR_conv_of_real)
    apply (subst of_real_mult [symmetric])
    apply (rule FDERIV_in_compose [OF 3])
    by (rule complex_of_real_has_derivative)
  assume "DERIV (IM f) z : s :> Im D"
  hence 3: "FDERIV (IM f) z : s :> (\<lambda>x. x * Im D)" by (simp add: deriv_fderiv)
  have feq: "f = (\<lambda>x. complex_of_real (Re (f x)) + ii * complex_of_real (Im (f x)))"
    by simp
  have "D = complex_of_real (Re D) + ii * complex_of_real (Im D)" by simp
  thus "(CDERIV f z : s :> D)"
    apply (elim ssubst, subst feq)
    apply (rule has_vector_derivative_add [OF 2])
    by (rule has_vector_derivative_complex_mul [OF 4])
qed

lemma CDERIV_iexp: "CDERIV iexp x : s :> \<i> * iexp x"
  unfolding CDERIV_def
  by (auto intro!: DERIV_intros simp add: cis_conv_exp[symmetric])

(* These are merely instances of the corresponding facts for has_vector_derivative.
   But is it too much to expect the user to know that CDERIV is an abbreviation for 
   has_vector_derivative? *)

lemma CDERIV_unique: "\<lbrakk>CDERIV f x :> Da; CDERIV f x :> Db\<rbrakk> \<Longrightarrow> Da = Db"
  by (erule vector_derivative_unique_at)

lemma CDERIV_const: "CDERIV (\<lambda>x. c) x : s :> 0"
  by (rule has_vector_derivative_const)

lemma CDERIV_add: "\<lbrakk> CDERIV f x : s :> Da; CDERIV g x : s :> Db\<rbrakk> \<Longrightarrow>
  CDERIV (\<lambda>x. f x + g x) x : s :> Da + Db"
  by (rule has_vector_derivative_add)

lemma CDERIV_neg: "CDERIV f x : s :> D \<Longrightarrow> CDERIV (\<lambda>x. - f x) x : s :> - D"
  by (rule has_vector_derivative_neg)

lemma CDERIV_sub: "\<lbrakk>CDERIV f x : s :> Da; CDERIV g x : s :> Db\<rbrakk> \<Longrightarrow>
  CDERIV (\<lambda>x. f x - g x) x : s :> Da - Db"
  by (rule has_vector_derivative_sub)

(* These are *not* instances of corresponding facts for has_vector_derivative *)

lemma CDERIV_mult: "\<lbrakk>CDERIV f x : s :> Da; CDERIV g x : s :> Db\<rbrakk> \<Longrightarrow>
  CDERIV (\<lambda>x. f x * g x) x : s :> (Da * (g x)) + (Db * (f x))"
  unfolding CDERIV_def by (auto intro!: DERIV_intros)

lemma RE_deriv: "CDERIV f x : s :> f' x \<Longrightarrow> DERIV (RE f) x : s :> (RE f') x"
  unfolding CDERIV_def by (erule conjE)

lemma IM_deriv: "CDERIV f x : s :> f' x \<Longrightarrow> DERIV (IM f) x : s :> (IM f') x"
  unfolding CDERIV_def by (erule conjE)

lemma CDERIV_rect: "\<lbrakk>DERIV (RE f) x : s :> Da; DERIV (IM f) x : s :> Db\<rbrakk> \<Longrightarrow>
  CDERIV f x : s :> Complex Da Db"
  unfolding CDERIV_def by auto

lemma CDERIV_isCont: "CDERIV f x :> D \<Longrightarrow> isCont f x"
  unfolding CDERIV_def
  by (subst isCont_RE_IM_iff, auto intro: DERIV_isCont)

lemma CDERIV_continuous: "CDERIV f x : s :> D \<Longrightarrow> continuous (at x within s) f"
  unfolding CDERIV_def apply (erule conjE)
  apply (drule DERIV_continuous)+
by (erule continuous_RE_IM)

lemma CDERIV_setsum:
  assumes "finite S"
  and "\<And>n. n \<in> S \<Longrightarrow> CDERIV (\<lambda>x. f x n) x :> (f' x n)"
  shows "CDERIV (\<lambda>x. setsum (f x) S) x :> setsum (f' x) S"
  using assms CDERIV_const by induct (auto intro!: CDERIV_add)

lemma CDERIV_of_real [simp]: "DERIV f x :> u \<Longrightarrow>
   (CDERIV (%x. complex_of_real (f x)) x :> complex_of_real u)"
  unfolding CDERIV_def by auto

(* measurability of functions from real to complex *)

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

lemma borel_measurable_complex_of_real [simp]: "complex_of_real \<in> 
  borel_measurable borel"
apply (rule borel_measurable_continuous_on1)
apply (rule continuous_at_imp_continuous_on)
by auto

lemma complex_borel_measurable_eq: "f \<in> borel_measurable M = 
  (RE f \<in> borel_measurable M \<and> IM f \<in> borel_measurable M)"
  apply auto
  apply (erule measurable_compose, rule borel_measurable_Re)
  apply (erule measurable_compose, rule borel_measurable_Im)
  apply (subst real_to_complex_expand)
  apply (rule borel_measurable_add)
  apply (erule measurable_compose, rule borel_measurable_complex_of_real)
  apply (rule borel_measurable_times)
  apply (rule borel_measurable_const)
by (erule measurable_compose, rule borel_measurable_complex_of_real)


(* 
  Integration of functions from real to complex
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

lemma Re_integral_eq: "Re (integral\<^sup>C M f) = integral\<^sup>L M (RE f)"
  by (unfold complex_lebesgue_integral_def, auto)

lemma Im_integral_eq: "Im (integral\<^sup>C M f) = integral\<^sup>L M (IM f)"
  by (unfold complex_lebesgue_integral_def, auto)

lemma complex_integral_cong:
  assumes "\<forall>x. x \<in> space M \<longrightarrow> f x = g x"
  shows "integral\<^sup>C M f = integral\<^sup>C M g"
using assms unfolding complex_lebesgue_integral_def by (auto intro: integral_cong)

lemma complex_integral_cong_AE:
  assumes "AE x in M. f x = g x"
  shows "integral\<^sup>C M f = integral\<^sup>C M g"
using assms unfolding complex_lebesgue_integral_def by (auto intro: integral_cong_AE)

lemma complex_integrable_conj [simp]:
  "complex_integrable M (Cnj f) = complex_integrable M f"
unfolding complex_integrable_def by auto

lemma complex_integral_conj [simp]:
  "complex_lebesgue_integral M (Cnj f) = cnj (complex_lebesgue_integral M f)"
unfolding complex_lebesgue_integral_def by (auto simp add: lebesgue_integral_uminus)
(* lebesgue_integral_uminus should be a simp rule *)

(*
  Linearity facts transported from real case. 
  (There's more stuff like this in Lebesgue_Integration.thy.)
*)

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
apply (simp add: CDERIV_def)
using cont apply (subst (asm) isCont_RE_IM_iff, auto)
apply (rule integral_FTC_atLeastAtMost, rule assms)
apply (frule F, assumption)
apply (simp add: CDERIV_def)
using cont apply (subst (asm) isCont_RE_IM_iff, auto)
by (simp add: complex_diff [symmetric])

(*
  Integration over a set -- compare to Set_Integral.thy
*)

syntax
"_ascii_complex_lebesgue_integral" :: "pttrn \<Rightarrow> 'a measure \<Rightarrow> real \<Rightarrow> real"
("(3CLINT _|_. _)" [0,110,60] 60)

translations
"CLINT x|M. f" == "CONST complex_lebesgue_integral M (\<lambda>x. f)"

abbreviation "complex_set_integrable M A f \<equiv> complex_integrable M (\<lambda>x. f x * indicator A x)"

abbreviation "complex_set_lebesgue_integral M A f \<equiv> 
    complex_lebesgue_integral M (\<lambda>x. f x * indicator A x)"

syntax
"_ascii_complex_set_lebesgue_integral" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'a measure \<Rightarrow> real \<Rightarrow> real"
("(4CLINT _:_|_. _)" [0,60,110,61] 60)

translations
"CLINT x:A|M. f" == "CONST complex_set_lebesgue_integral M A (\<lambda>x. f)"

lemma RE_indicator [simp]: "RE (indicator A) = indicator A"
  by (rule ext, simp split: split_indicator)

lemma Re_indicator [simp]: "Re (indicator A x) = indicator A x"
  by (simp split: split_indicator)

lemma IM_indicator [simp]: "IM (indicator A) = (\<lambda>x. 0)"
  by (rule ext, simp split: split_indicator)

lemma Im_indicator [simp]: "Im (indicator A x) = 0"
  by (simp split: split_indicator)

lemma Cnj_indicator: "Cnj (indicator A) = indicator A"
  by (rule ext, simp split: split_indicator)

lemma cnj_indicator: "Cnj (indicator A) x = indicator A x"
  by (simp split: split_indicator)

lemma complex_set_integrable_iff: "complex_set_integrable M A f \<equiv> 
    (set_integrable M A (RE f) \<and> set_integrable M A (IM f))"
unfolding complex_integrable_def by auto

lemma complex_set_lebesgue_integral_eq: 
  "(CLINT x:A|M. f x) = (LINT x:A|M. (RE f) x) + ii * (LINT x:A|M. (IM f) x)"
unfolding complex_lebesgue_integral_def by auto

lemma complex_set_integrable_Cnj: "complex_set_integrable M A (Cnj f) =
    complex_set_integrable M A f"
  apply (subst (1) Cnj_indicator [symmetric])
by (simp add: complex_cnj_mult [symmetric])

lemma complex_set_integral_cnj: "(CLINT x:A|M. cnj (f x)) = cnj (CLINT x:A|M. f x)"
  apply (subst (1) Cnj_indicator [symmetric])
by (simp add: complex_cnj_mult [symmetric])
   
lemma complex_set_integrable_subset: 
  fixes M A B f
  assumes "complex_set_integrable M A f" "B \<in> sets M" "B \<subseteq> A"  
  shows "complex_set_integrable M B f"
using assms unfolding complex_set_integrable_iff by (auto intro: set_integrable_subset)

lemma complex_set_integral_cmult [simp, intro]:
  assumes "complex_set_integrable M A f"
  shows "complex_set_integrable M A (\<lambda>t. a * f t)"
  and "CLINT t:A|M. a * f t = a * (CLINT t:A|M. f t)"
using assms by (auto simp add: mult_assoc)

lemma complex_set_integral_add [simp, intro]:
  assumes "complex_set_integrable M A f" "complex_set_integrable M A g"
  shows "complex_set_integrable M A (\<lambda>x. f x + g x)" and "CLINT x:A|M. f x + g x =
    (CLINT x:A|M. f x) + (CLINT x:A|M. g x)"
using assms by (auto simp add: field_simps)

lemma complex_set_integral_diff [simp, intro]:
  assumes "complex_set_integrable M A f" "complex_set_integrable M A g"
  shows "complex_set_integrable M A (\<lambda>x. f x - g x)" and "CLINT x:A|M. f x - g x =
    (CLINT x:A|M. f x) - (CLINT x:A|M. g x)"
using assms by (auto simp add: field_simps)

lemma complex_set_integrable_cmod: "complex_set_integrable M A f \<Longrightarrow> A \<in> sets M \<Longrightarrow>
    set_integrable M A (\<lambda>x. cmod (f x))"
unfolding complex_set_integrable_iff
proof (auto)
  fix M and A :: "'a set" and f
  assume *: "set_integrable M A (RE f)" "set_integrable M A (IM f)" "A \<in> sets M"
  { 
    fix x :: 'a
    have "cmod (f x) \<le> abs (RE f x) + abs (IM f x)"
      unfolding cmod_def by (rule sqrt_sum_squares_le_sum_abs)
  }
  have 1: "set_integrable M A (\<lambda>x. \<bar>RE f x\<bar> + \<bar>IM f x\<bar>)"
    apply (rule set_integral_add)
    by (rule set_integrable_abs, rule *)+
  { fix x 
    have "\<bar>cmod (f x) * indicator A x\<bar> \<le> (\<bar>RE f x\<bar> + \<bar>IM f x\<bar>) * indicator A x"
      by (auto simp add: abs_mult cmod_def intro: mult_right_mono sqrt_sum_squares_le_sum_abs)
  } note 2 = this
  have "(\<lambda>x. cmod (f x) * indicator A x) = 
       (\<lambda>x. sqrt ((RE f x * indicator A x)^2 + (IM f x * indicator A x)^2))"
    by (rule ext, auto simp add: cmod_def split: split_indicator)
  also have "\<dots> \<in> borel_measurable M"
    using * by measurable
  finally have 3: "set_borel_measurable M A (\<lambda>x. cmod (f x))" .
  show "set_integrable M A (\<lambda>x. cmod (f x))"
    apply (rule integrable_bound [OF 1 _ 3]) 
    by (rule AE_I', rule null_sets.empty_sets, clarsimp, rule 2)
qed

lemma complex_set_integrable_Un:
  assumes "complex_set_integrable M A f" "complex_set_integrable M B f"
    "A \<in> sets M" "B \<in> sets M"
  shows "complex_set_integrable M (A \<union> B) f"
using assms unfolding complex_integrable_def by (auto intro: set_integrable_Un)

lemma complex_set_integrable_UN:
  assumes "finite I" "\<And>i. i\<in>I \<Longrightarrow> complex_set_integrable M (A i) f"
    "\<And>i. i\<in>I \<Longrightarrow> A i \<in> sets M"
  shows "complex_set_integrable M (\<Union>i\<in>I. A i) f"
using assms by (induct I, auto intro!: complex_set_integrable_Un)

lemma complex_set_integral_Un:
  assumes "A \<inter> B = {}"
  and "complex_set_integrable M A f"
  and "complex_set_integrable M B f"
  shows "CLINT x:A\<union>B|M. f x = (CLINT x:A|M. f x) + (CLINT x:B|M. f x)"
by (auto simp add: indicator_union_arith indicator_inter_arith[symmetric]
      distrib_left assms)

lemma complex_set_integral_finite_Union:
  assumes "finite I" "disjoint_family_on A I"
    and "\<And>i. i \<in> I \<Longrightarrow> complex_set_integrable M (A i) f" "\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets M"
  shows "(CLINT x:(\<Union>i\<in>I. A i)|M. f x) = (\<Sum>i\<in>I. CLINT x:A i|M. f x)"

  using assms
  apply induct
  apply (auto intro!: complex_set_integral_Un complex_set_integrable_Un 
    complex_set_integrable_UN simp: disjoint_family_on_def)
by (subst complex_set_integral_Un, auto intro: complex_set_integrable_UN)

(* TODO: also translate lebesgue_integral_countable_add and set_integral_at_point
   from Set_Integral.thy? *)

(* 
  Integration over an interval -- compare to Interval_Integral.thy 
*)

syntax
"_complex_lebesgue_borel_integral" :: "pttrn \<Rightarrow> real \<Rightarrow> complex"
("(2CLBINT _. _)" [0,60] 60)

translations
"CLBINT x. f" == "CONST complex_lebesgue_integral CONST lborel (\<lambda>x. f)"

syntax
"_complex_set_lebesgue_borel_integral" :: "pttrn \<Rightarrow> real set \<Rightarrow> real \<Rightarrow> complex"
("(3CLBINT _:_. _)" [0,60,61] 60)

translations
"CLBINT x:A. f" == "CONST complex_set_lebesgue_integral CONST lborel A (\<lambda>x. f)"

definition complex_interval_lebesgue_integral :: 
    "real measure \<Rightarrow> ereal \<Rightarrow> ereal \<Rightarrow> (real \<Rightarrow> complex) \<Rightarrow> complex" where
  "complex_interval_lebesgue_integral M a b f = (if a \<le> b
    then (\<integral>\<^sup>C x. f x * indicator (einterval a b) x \<partial>M)
    else - (\<integral>\<^sup>C x. f x * indicator (einterval b a) x \<partial>M))"

definition complex_interval_lebesgue_integrable :: 
  "real measure \<Rightarrow> ereal \<Rightarrow> ereal \<Rightarrow> (real \<Rightarrow> complex) \<Rightarrow> bool" where
  "complex_interval_lebesgue_integrable M a b f = (if a \<le> b
    then complex_integrable M (\<lambda>x. f x * indicator (einterval a b) x)
    else complex_integrable M (\<lambda>x. f x * indicator (einterval b a) x))"

syntax
  "_ascii_complex_interval_lebesgue_borel_integral" :: "pttrn \<Rightarrow> ereal \<Rightarrow> ereal \<Rightarrow> real \<Rightarrow> complex"
  ("(4CLBINT _=_.._. _)" [0,60,60,61] 60)

translations
  "CLBINT x=a..b. f" == "CONST complex_interval_lebesgue_integral CONST lborel a b (\<lambda>x. f)"

lemma complex_interval_lebesgue_integrable_iff:
  "complex_interval_lebesgue_integrable M a b f = 
    (interval_lebesgue_integrable M a b (RE f) \<and> interval_lebesgue_integrable M a b (IM f))"
unfolding complex_interval_lebesgue_integrable_def interval_lebesgue_integrable_def
  by (auto simp add: complex_set_integrable_iff)

lemma complex_interval_integral_eq:
  "complex_interval_lebesgue_integral M a b f = interval_lebesgue_integral M a b (RE f) + 
    ii * (interval_lebesgue_integral M a b (IM f))"
unfolding complex_interval_lebesgue_integral_def interval_lebesgue_integral_def 
  by (auto simp add: complex_set_lebesgue_integral_eq field_simps)

lemma complex_interval_lebesgue_integral_add [intro, simp]: 
  fixes M a b f g 
  assumes "complex_interval_lebesgue_integrable M a b f"
    "complex_interval_lebesgue_integrable M a b g"
  shows "complex_interval_lebesgue_integrable M a b (\<lambda>x. f x + g x)" and 
    "complex_interval_lebesgue_integral M a b (\<lambda>x. f x + g x) = 
   complex_interval_lebesgue_integral M a b f + complex_interval_lebesgue_integral M a b g"
using assms unfolding complex_interval_lebesgue_integrable_iff complex_interval_integral_eq
  by (auto simp add: complex_of_real_def)

lemma complex_interval_lebesgue_integral_diff [intro, simp]: 
  fixes M a b f 
  assumes "complex_interval_lebesgue_integrable M a b f"
    "complex_interval_lebesgue_integrable M a b g"
  shows "complex_interval_lebesgue_integrable M a b (\<lambda>x. f x - g x)" and 
    "complex_interval_lebesgue_integral M a b (\<lambda>x. f x - g x) = 
   complex_interval_lebesgue_integral M a b f - complex_interval_lebesgue_integral M a b g"
using assms unfolding complex_interval_lebesgue_integrable_iff complex_interval_integral_eq
  by (auto simp add: complex_of_real_def)

lemma complex_interval_lebesgue_integral_cmult [intro, simp]:
   fixes M a b c f 
  assumes "complex_interval_lebesgue_integrable M a b f"
  shows "complex_interval_lebesgue_integrable M a b (\<lambda>x. c * f x)" and 
    "complex_interval_lebesgue_integral M a b (\<lambda>x. c * f x) = 
   c * complex_interval_lebesgue_integral M a b f"
using assms by (auto simp add: complex_interval_lebesgue_integral_def complex_interval_lebesgue_integrable_def 
    field_simps)

lemma complex_interval_integral_const [intro, simp]:
  fixes a b c :: real
  shows "complex_interval_lebesgue_integrable lborel a b (\<lambda>x. c)" and 
    "CLBINT x=a..b. c = c * (b - a)" 
unfolding complex_interval_lebesgue_integrable_iff complex_interval_integral_eq
  by (auto simp add: complex_of_real_def)

lemma complex_interval_integral_endpoints_same [simp]: "(CLBINT x=a..a. f x) = 0"
unfolding complex_interval_integral_eq by auto

lemma complex_interval_integral_endpoints_reverse: "(CLBINT x=a..b. f x) = -(CLBINT x=b..a. f x)"
unfolding complex_interval_integral_eq by (auto intro: interval_integral_endpoints_reverse)

lemma complex_interval_integral_Icc:
  fixes a b :: real
  assumes "a \<le> b" 
  shows "(CLBINT x=a..b. f x) = (CLBINT x : {a..b}. f x)"
unfolding complex_interval_integral_eq complex_set_lebesgue_integral_eq 
  using assms by (auto simp add: interval_integral_Icc)

lemma complex_interval_integral_Iic:
  fixes a b :: real
  assumes "a \<le> b" 
  shows "(CLBINT x=a..b. f x) = (CLBINT x : {a<..b}. f x)"
unfolding complex_interval_integral_eq complex_set_lebesgue_integral_eq 
  using assms by (auto simp add: interval_integral_Iic)

lemma complex_interval_integral_Iic':
  fixes a b :: ereal
  assumes "a \<le> b" 
  shows "(CLBINT x=a..b. f x) = (CLBINT x : {x. a < ereal x \<and> ereal x \<le> b}. f x)"
unfolding complex_interval_integral_eq complex_set_lebesgue_integral_eq 
  using assms by (auto simp add: interval_integral_Iic')

lemma complex_interval_integral_Ici:
  fixes a b :: real
  assumes "a \<le> b" 
  shows "(CLBINT x=a..b. f x) = (CLBINT x : {a..<b}. f x)"
unfolding complex_interval_integral_eq complex_set_lebesgue_integral_eq 
  using assms by (auto simp add: interval_integral_Ici)

lemma complex_interval_integral_sum: 
  fixes a b c :: ereal
  assumes integrable: "complex_interval_lebesgue_integrable lborel (min a (min b c)) (max a (max b c)) f" 

  shows "(CLBINT x=a..b. f x) + (CLBINT x=b..c. f x) = (CLBINT x=a..c. f x)"
using assms unfolding complex_interval_integral_eq complex_interval_lebesgue_integrable_iff
by (auto intro: interval_integral_sum)

lemma complex_interval_integrable_isCont:
  fixes a b :: real and f
  assumes "a \<le> b" and "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> isCont f x"
  shows "complex_interval_lebesgue_integrable lborel a b f"
using assms unfolding complex_interval_integral_eq complex_interval_lebesgue_integrable_iff
by (auto intro: interval_integrable_isCont)

lemma complex_interval_integral_FTC_finite:
  fixes f F :: "real \<Rightarrow> complex" and a b :: real
  assumes f: "continuous_on {min a b..max a b} f"
  assumes F: "\<And>x. min a b \<le> x \<Longrightarrow> x \<le> max a b \<Longrightarrow> CDERIV F x : {min a b..max a b} :> f x" 
  shows "(CLBINT x=a..b. f x) = F b - F a"
using assms unfolding complex_interval_integral_eq CDERIV_def 
  apply (subst real_to_complex_expand [of F])
  apply (subst real_to_complex_expand [of F]) back back
  apply auto
  apply (subst interval_integral_FTC_finite [of _ _ "RE f" "RE F"])
  apply (auto simp add: continuous_on_eq_continuous_within continuous_RE_IM_iff)
  apply (subst interval_integral_FTC_finite [of _ _ "IM f" "IM F"])
  apply (auto simp add: continuous_on_eq_continuous_within continuous_RE_IM_iff)
(* fighting with the simplifier here *)
by (auto simp del: complex_Re_diff complex_Im_diff
    simp add: complex_Re_diff [symmetric] complex_Im_diff [symmetric])

lemma complex_interval_integral_FTC_integrable:
  fixes f F :: "real \<Rightarrow> complex" and a b :: ereal
  assumes "a < b"
  assumes F: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> CDERIV F x :> f x" 
  assumes f: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> isCont f x" 
  assumes f_integrable: "complex_set_integrable lborel (einterval a b) f"
  assumes A: "((F \<circ> real) ---> A) (at_right a)"
  assumes B: "((F \<circ> real) ---> B) (at_left b)"
  shows "(CLBINT x=a..b. f x) = B - A"
using assms unfolding complex_interval_integral_eq complex_interval_lebesgue_integrable_iff CDERIV_def 
  apply auto
  apply (subst interval_integral_FTC_integrable [of _ _ "RE F" "RE f" "Re A" "Re B"])
  apply (auto simp add: complex_set_integrable_iff)
  unfolding comp_def apply (rule filterlim_compose [of _ _ "nhds A"])
  apply (rule tendsto_Re, rule filterlim_ident)
  using A unfolding comp_def apply assumption
  unfolding comp_def apply (rule filterlim_compose [of _ _ "nhds B"])
  apply (rule tendsto_Re, rule filterlim_ident)
  using B unfolding comp_def apply assumption
  apply (subst interval_integral_FTC_integrable [of _ _ "IM F" "IM f" "Im A" "Im B"])
  apply (auto simp add: complex_set_integrable_iff)
  unfolding comp_def apply (rule filterlim_compose [of _ _ "nhds A"])
  apply (rule tendsto_Im, rule filterlim_ident)
  using A unfolding comp_def apply assumption
  unfolding comp_def apply (rule filterlim_compose [of _ _ "nhds B"])
  apply (rule tendsto_Im, rule filterlim_ident)
  using B unfolding comp_def apply assumption
by (auto simp del: complex_Re_diff complex_Im_diff
    simp add: complex_Re_diff [symmetric] complex_Im_diff [symmetric])

lemma complex_interval_integral_FTC2:
  fixes a b c :: real and f :: "real \<Rightarrow> complex"
  assumes "a \<le> c" "c \<le> b"
  and contf: "continuous_on {a..b} f"
  fixes x :: real
  assumes "a \<le> x" and "x \<le> b"
  shows "CDERIV (\<lambda>u. CLBINT y=c..u. f y) x : {a..b} :> f x"
using assms unfolding complex_interval_integral_eq
  apply (subst real_to_complex_expand [of f]) back back
  apply (rule CDERIV_add)
  apply (subst CDERIV_def)
  apply auto [1]
  apply (rule interval_integral_FTC2)
  apply auto [5]
  apply (auto simp add: continuous_on_eq_continuous_within continuous_RE_IM_iff) [1]
  apply (rule CDERIV_cmult)
  apply (subst CDERIV_def)
  apply auto [1]
  apply (rule interval_integral_FTC2)
  apply auto [5]
by (auto simp add: continuous_on_eq_continuous_within continuous_RE_IM_iff) [1]

lemma complex_einterval_antiderivative: 
  fixes a b :: ereal and f :: "real \<Rightarrow> complex"
  assumes "a < b" and contf: "\<And>x :: real. a < x \<Longrightarrow> x < b \<Longrightarrow> isCont f x"
  shows "\<exists>F. \<forall>x :: real. a < x \<longrightarrow> x < b \<longrightarrow> CDERIV F x :> f x"

proof -
  { fix x :: real
    assume 1: "a < x" and 2: "x < b"
    from contf [OF 1 2] have "isCont (RE f) x"
      by (subst (asm) isCont_RE_IM_iff, auto) 
  }
  from einterval_antiderivative [OF `a < b` this] obtain F_RE where
    3 [rule_format]: "\<forall>x. a < ereal x \<longrightarrow> ereal x < b \<longrightarrow> DERIV F_RE x :> RE f x" by auto
  { fix x :: real
    assume 1: "a < x" and 2: "x < b"
    from contf [OF 1 2] have "isCont (IM f) x"
      by (subst (asm) isCont_RE_IM_iff, auto) 
  }
  from einterval_antiderivative [OF `a < b` this] obtain F_IM where
    4 [rule_format]: "\<forall>x. a < ereal x \<longrightarrow> ereal x < b \<longrightarrow> DERIV F_IM x :> IM f x" by auto
  let ?F = "\<lambda>x. F_RE x + ii * F_IM x"
  have "\<forall>x :: real. a < x \<longrightarrow> x < b \<longrightarrow> CDERIV ?F x :> f x"
    by (auto simp add: CDERIV_def 3 4)
  thus ?thesis by (elim exI)
qed

lemma complex_interval_integral_substitution_finite:
  fixes a b :: real and f :: "real \<Rightarrow> complex"
  assumes "a \<le> b"
  and derivg: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> DERIV g x : {a..b} :> g' x"
  and contf : "continuous_on (g ` {a..b}) f"
  and contg': "continuous_on {a..b} g'"
  shows "CLBINT x=a..b. f (g x) * g' x = CLBINT y=(g a)..(g b). f y"
using assms apply (auto simp add: complex_interval_integral_eq)
  apply (rule interval_integral_substitution_finite, auto)
  apply (simp add: continuous_on_eq_continuous_within continuous_RE_IM_iff)
  apply (rule interval_integral_substitution_finite, auto)
by (simp add: continuous_on_eq_continuous_within continuous_RE_IM_iff)


lemma complex_interval_integral_substitution_integrable:
  fixes f :: "real \<Rightarrow> complex" and g g':: "real \<Rightarrow> real" and a b u v :: ereal
  assumes "a < b" 
  and deriv_g: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> DERIV g x :> g' x"
  and contf: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> isCont f (g x)"
  and contg': "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> isCont g' x"
  and g'_nonneg: "\<And>x. a \<le> ereal x \<Longrightarrow> ereal x \<le> b \<Longrightarrow> 0 \<le> g' x"
  and A: "((ereal \<circ> g \<circ> real) ---> A) (at_right a)"
  and B: "((ereal \<circ> g \<circ> real) ---> B) (at_left b)"
  and integrable: "complex_set_integrable lborel (einterval a b) (\<lambda>x. f (g x) * g' x)"
  and integrable2: "complex_set_integrable lborel (einterval A B) (\<lambda>x. f x)"
  shows "(CLBINT x=A..B. f x) = (CLBINT x=a..b. (f (g x) * g' x))"

using assms unfolding complex_interval_integral_eq complex_set_lebesgue_integral_eq
    complex_set_integrable_iff
  apply auto 
by (rule interval_integral_substitution_integrable, auto)+

(*
  First application of the FTC: integrating e^ix
*)

lemma interval_integral_iexp:
  fixes a b :: real
  shows "(CLBINT x=a..b. iexp x) = ii * iexp a - ii * iexp b"

  apply (subst complex_interval_integral_FTC_finite [where F = "\<lambda>x. -ii * iexp x"])
  apply (rule continuous_on_exp, rule continuous_on_mult, rule continuous_on_const)
  apply (rule continuous_on_of_real, rule continuous_on_id)
  apply (subgoal_tac "expi (\<i> * complex_of_real x) = -ii * (ii * expi (\<i> * complex_of_real x))")
  apply (erule ssubst)
  apply (rule CDERIV_cmult)
  apply (rule CDERIV_iexp)
by auto

end