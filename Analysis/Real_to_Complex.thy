theory Real_to_Complex
imports Library_Misc "~~/src/HOL/Multivariate_Analysis/Derivative"
"~~/src/HOL/Probability/Lebesgue_Integration"

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

(** Inequality for difference of complex products. **)

(* Is this a good idea? *)
declare complex_diff_def [symmetric, simp]

(*lemma prod_complex_leq_unit_cmod:
  fixes z :: "nat \<Rightarrow> complex" m :: nat
  assumes "\<forall>i < m. cmod (z i) \<le> 1"
  shows "\<Prod> i < m. cmod (z i) \<le> 1" *)
  

(* probably generalizes to real_normed_algebra_1,(comm_)monoid_mult *)
lemma complex_prod_diff [rule_format]:
  fixes 
    z :: "nat \<Rightarrow> complex" and
    w :: "nat \<Rightarrow> complex" and
    m :: nat
  shows "(\<forall> i < m. cmod (z i) \<le> 1) & (\<forall> i < m. cmod (w i) \<le> 1) \<longrightarrow> 
    norm ((\<Prod> i < m. z i) - (\<Prod> i < m. w i)) \<le> (\<Sum> i < m. cmod (z i - w i))" 
      (is "?H1 m & ?H2 m \<longrightarrow> ?P m") 
proof (induct m)
  let "?Q m" = "?H1 m & ?H2 m \<longrightarrow> ?P m"
  show "?Q 0" by auto
  next
    let "?Q m" = "?H1 m & ?H2 m \<longrightarrow> ?P m"
    fix m
    assume ih: "?Q m"
    show "?Q (Suc m)"
    proof (clarify)
      assume zbnd: "?H1 (Suc m)"
         and wbnd : "?H2 (Suc m)"
      with ih have ih1: "?P m" by auto
      show "?P (Suc m)"

      proof -
        have "cmod ((\<Prod> i < Suc m. z i) - (\<Prod> i < Suc m. w i)) = 
          cmod ((\<Prod> i < Suc m. z i) - w m * (\<Prod> i < m. z i) + w m *
          (\<Prod> i < m. z i) - (\<Prod> i < Suc m. w i))"
          by auto
        also have "... = cmod ((\<Prod> i < m. z i) * (z m - w m) + 
          ((\<Prod> i < m. z i) - (\<Prod> i < m. w i)) * w m)"
          (is "?lhs = cmod (?t1 + ?t2)")
          by (auto simp add: field_simps)
        also have "... \<le> cmod(?t1) + cmod(?t2)"
          by (rule norm_triangle_ineq)
        also have "cmod(?t1) \<le> cmod(z m - w m)"
          apply (subst norm_mult)
          apply (rule mult_left_le_one_le, auto)
          apply (subst norm_setprod)
          apply (subst setprod_1 [symmetric])
          apply simp
          apply (rule order_trans)
          apply (rule setprod_mono[of "{..<m}" "\<lambda>i. cmod (z i)" "\<lambda>i. 1"])
          apply (auto intro: zbnd [rule_format])
          done
        also have "cmod(?t2) \<le> cmod((\<Prod> i < m. z i) - (\<Prod> i < m. w i))"
          apply (subst norm_mult)
          apply (rule mult_right_le_one_le)
          apply (auto simp add: wbnd)
          done
        also have "... \<le> (\<Sum> i < m. cmod (z i - w i))"
          by (rule ih1)
        finally show ?thesis
          by (auto simp add: add_ac)
        
      qed
    qed
  qed

(** Function e^(ix). **)

abbreviation iexp :: "real \<Rightarrow> complex" where
  "iexp \<equiv> (\<lambda>x. expi (\<i> * of_real x))"

  (** Differentiation of functions of type real \<Rightarrow> complex. **)

  (* As suggested by Johannes Hölzl, has_vector_derivative dispenses with the
  need for the following definition; however, I do not see how to take the
  derivative of an exponential using has_vector derivative at this time. *)

definition complex_deriv :: "[real \<Rightarrow> complex, real, complex] \<Rightarrow> bool"
("(CDERIV (_)/ (_)/ :> (_))" [1000, 1000, 60] 60) where
  "CDERIV f z :> D \<equiv> (DERIV (RE f) z :> Re D) \<and> (DERIV (IM f) z :> Im D)"

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

declare [[coercion "complex_of_real :: real \<Rightarrow> complex"]]

lemma CDERIV_of_real [simp]: "DERIV f x :> u \<Longrightarrow>
   (CDERIV (%x. complex_of_real (f x)) x :> complex_of_real u)"
  unfolding complex_deriv_def by auto

lemma isCont_new_expir [simp]: "isCont (\<lambda>x. exp (Complex 0 x)) x"
apply (rule isCont_exp')
apply (subgoal_tac "Complex 0 = (\<lambda>x. ii * x)")
apply (erule ssubst)
apply (rule isCont_mult)
apply auto
done

(****** Since exp_i_times_real is an abbreviation, shouldn't need this? *****
lemma expir_0 [simp]: "expir 0 = 1"
unfolding expir_def by simp *)

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
 
lemma complex_integral_add [simp]: 
  assumes "complex_integrable M f" "complex_integrable M g"
  shows "complex_integrable M (\<lambda>t. f t + g t)"
  and "(\<integral>\<^isup>C t. f t + g t \<partial>M) = integral\<^isup>C M f + integral\<^isup>C M g"
using assms by (auto simp add: complex_integrable_def
  complex_lebesgue_integral_def complex_of_real_def)

lemma complex_integral_zero [simp]:
  shows "complex_integrable M (\<lambda>x. 0)" 
  and "(\<integral>\<^isup>C x. 0 \<partial>M)  = 0"
by (auto simp add: complex_integrable_def complex_lebesgue_integral_def
  complex_of_real_def)

(* is integrability really needed for the second fact? *)
lemma complex_integral_cmult [simp]:
  assumes "complex_integrable M f"
  shows "complex_integrable M (\<lambda>t. a * f t)"
  and "(\<integral>\<^isup>C t. a * f t \<partial>M) = a * complex_lebesgue_integral M f"
using assms apply (auto simp add: complex_integrable_def
  complex_lebesgue_integral_def complex_of_real_def complex_surj complex_mult)
by (metis complex_mult complex_surj)


(* is there are corresponding one for the usual integral? *)
lemma complex_integral_cdiv [simp]:
  assumes "complex_integrable M f"
  shows "complex_integrable M (\<lambda>t. f t / a)"
  and "(\<integral>\<^isup>C t. f t / a \<partial>M) = complex_lebesgue_integral M f / a"
using assms
apply (simp_all only: complex_divide_def)
apply (subst mult_commute, force)
by (subst mult_commute, simp)

lemma complex_integral_uminus [simp, intro]:
  "(\<integral>\<^isup>Cx. - f x \<partial>M) = - complex_lebesgue_integral M f"
unfolding complex_lebesgue_integral_def
by (auto simp add: lebesgue_integral_uminus complex_of_real_def)

lemma complex_integral_minus[intro, simp]:
  assumes "complex_integrable M f"
  shows "complex_integrable M (\<lambda>x. - f x)" 
(*  and "(\<integral>\<^isup>Cx. - f x \<partial>M) = - complex_lebesgue_integral M f" *)
using assms
by (auto simp add: complex_integrable_def complex_lebesgue_integral_def
  complex_of_real_def)

lemma complex_integral_diff[simp, intro]:
  assumes f: "complex_integrable M f" and g: "complex_integrable M g"
  shows "complex_integrable M (\<lambda>t. f t - g t)"
  and "(\<integral>\<^isup>C t. f t - g t \<partial>M) = complex_lebesgue_integral M f - 
    complex_lebesgue_integral M g"
using complex_integral_add[OF f complex_integral_minus(1) [OF g]]
unfolding diff_minus complex_integral_minus[OF g]
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

(*
  Finally, getting to Equation 26.1.
*)

lemma fact1: "CDERIV (%s. complex_of_real(-((x - s) ^ (Suc n) / (Suc n))) * e\<^bsup>\<i>s\<^esup>)
 s :> complex_of_real((x - s)^n) * e\<^bsup>\<i>s\<^esup> + (ii * e\<^bsup>\<i>s\<^esup>) * 
      complex_of_real(-((x - s) ^ (Suc n) / (Suc n)))"
apply (rule CDERIV_mult)
apply (rule CDERIV_of_real)
apply (auto intro!: DERIV_intros simp del: power_Suc)
apply (subst i_complex_of_real[symmetric])+
apply (rule CDERIV_expi)
done

lemma cmp_conn_complex_integrable_isCont: 
  "(\<And>x. x \<in> irange (a::real) b \<Longrightarrow> isCont f x) \<Longrightarrow>
    complex_integrable lborel 
      (\<lambda>x. f x * complex_of_real (indicator (irange a b) x))"
  by (auto intro!: integrable_atLeastAtMost_isCont 
    simp add: complex_integrable_def irange_def)

(* need CDERIV_intros *)
lemma CDERIV_cong: "\<lbrakk>CDERIV f x :> X; X = Y\<rbrakk> \<Longrightarrow> CDERIV f x :> Y"
  by simp

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
  hence Re_eq: "integral\<^isup>L M (RE f) = integral\<^isup>L M (RE g)"
    using integral_cong_AE[of "RE f" "RE g"] by auto
  have "AE x in M. IM f x = IM g x" using assms by auto
  hence Im_eq: "integral\<^isup>L M (IM f) = integral\<^isup>L M (IM g)"
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