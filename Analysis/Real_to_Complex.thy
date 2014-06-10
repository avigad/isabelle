(*  
Theory: Real_to_Complex.thy
Authors: Jeremy Avigad, Luke Serafin 

Differentiation and integration for functions from the reals to the complex numbers. Also transfers
notation from Interval_Integral.thy.

TODO: make this uniform with library for reals.

*)

theory Real_to_Complex

imports Library_Misc Interval_Integral

begin

(* Move these to Borel_Sets.thy *)

lemma has_vector_derivative_setsum[derivative_intros]:
  "(\<And>i. i \<in> I \<Longrightarrow> (f i has_vector_derivative f' i) net) \<Longrightarrow>
    ((\<lambda>x. \<Sum>i\<in>I. f i x) has_vector_derivative (\<Sum>i\<in>I. f' i)) net"
  by (auto simp: has_vector_derivative_def fun_eq_iff scaleR_setsum_right intro!: derivative_eq_intros)

(** Real and complex parts of a function. **)

abbreviation RE :: "('a \<Rightarrow> complex) \<Rightarrow> 'a \<Rightarrow> real" where
"RE f \<equiv> (\<lambda>x. Re (f x))"

abbreviation IM :: "('a \<Rightarrow> complex) \<Rightarrow> 'a \<Rightarrow> real" where
"IM f \<equiv> (\<lambda>x. Im (f x))"

abbreviation Cnj :: "('a \<Rightarrow> complex) \<Rightarrow> 'a \<Rightarrow> complex" where
"Cnj f \<equiv> (\<lambda>x. cnj (f x))"

lemma isCont_RE_IM_iff: "isCont f z = (isCont (RE f) z \<and> isCont (IM f) z)"
  unfolding isCont_def tendsto_complex_iff ..

lemma continuous_RE_IM: "continuous (at x within s) (RE f) \<Longrightarrow>
    continuous (at x within s) (IM f) \<Longrightarrow>
    continuous (at x within s) f"
  unfolding Topological_Spaces.continuous_def tendsto_complex_iff ..

lemma continuous_RE_IM_iff: "continuous (at x within s) f = 
    (continuous (at x within s) (RE f) \<and> continuous (at x within s) (IM f))"
  by (auto intro: continuous_RE_IM)


(* TODO: versions of the above for continuous_on? Below we use continuous_on_eq_continuous_within
   to avoid this, but it is a pain in the neck *)

declare [[coercion "complex_of_real :: real \<Rightarrow> complex"]]

lemma real_to_complex_expand: "f = (\<lambda>x. (RE f) x + ii * (IM f) x)"
  by (simp add: fun_eq_iff complex_eq_iff)

lemma complex_expand: "a = Re a + ii * Im a"
  by (simp add: fun_eq_iff complex_eq_iff)

(* measurability of functions from real to complex *)

lemma complex_borel_measurable_eq: "f \<in> borel_measurable M = 
  (RE f \<in> borel_measurable M \<and> IM f \<in> borel_measurable M)"
  apply auto
  apply (subst real_to_complex_expand)
  apply (rule borel_measurable_add borel_measurable_times measurable_compose[OF _ borel_measurable_of_real] 
    | simp)+
  done

(* move this to Complex *)
lemma cmod_le: "cmod z \<le> abs (Re z) + abs (Im z)"
  apply (subst complex_expand)
  apply (rule order_trans)
  apply (rule norm_triangle_ineq)
  apply (simp add: norm_mult)
  done

abbreviation iexp :: "real \<Rightarrow> complex" where
  "iexp \<equiv> (\<lambda>x. expi (\<i> * of_real x))"

lemma isCont_iexp [simp]: "isCont iexp x"
  by (intro continuous_intros)

(* hmm... should we turn off the rule that reduces ii * x to Complex 0 x? *)
lemma cmod_iexp [simp]: "cmod (expi (\<i> * (x::real))) = 1"
  by (simp add: expi_def )

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

lemma has_vector_derivative_complex_mul:
  "(f has_vector_derivative f') net \<Longrightarrow> 
    ((\<lambda>x. (c\<Colon>complex) * f x) has_vector_derivative (c * f')) net"
  unfolding has_vector_derivative_def
  apply (subst mult_scaleR_right [symmetric])
by (rule mult_right_has_derivative)

(* TODO: this is an instance of the previous lemma, but that is not obvious. *)
(* Keep it? *)
lemma CDERIV_cmult: "(CDERIV f z : s :> D) \<Longrightarrow> (CDERIV (\<lambda>x. c * f x) z : s :> c * D)"
  by (erule has_vector_derivative_complex_mul)

lemma DERIV_Re[derivative_intros]:
  "(f has_vector_derivative D) F \<Longrightarrow> ((RE f) has_field_derivative (Re D)) F"
  by (auto intro!: derivative_eq_intros simp add: fun_eq_iff has_vector_derivative_def has_field_derivative_def)

lemma DERIV_Im[derivative_intros]:
  "(f has_vector_derivative D) F \<Longrightarrow> ((IM f) has_field_derivative (Im D)) F"
  by (auto intro!: derivative_eq_intros simp add: fun_eq_iff has_vector_derivative_def has_field_derivative_def)

lemma DERIV_complex_of_real[derivative_intros]:
  "(f has_field_derivative D) F \<Longrightarrow> ((\<lambda>x. of_real (f x)) has_vector_derivative (of_real D)) F"
  by (auto intro!: derivative_eq_intros
           simp add: fun_eq_iff has_vector_derivative_def has_field_derivative_def of_real_def)

(* is this a bad name? *)
(* TODO: eliminate the notation for CDERIV *)
lemma CDERIV_def: "(CDERIV f z : s :> D) = 
    (((RE f) has_field_derivative (Re D)) (at z within s) \<and> 
    ((IM f) has_field_derivative (Im D)) (at z within s))"
proof (auto)
  assume *: "(CDERIV f z : s :> D)"
  then show "((RE f) has_field_derivative (Re D)) (at z within s)"
    "((IM f) has_field_derivative (Im D)) (at z within s)"
    by (auto intro: derivative_intros)
next
  assume *: "((RE f) has_field_derivative (Re D)) (at z within s)" "((IM f) has_field_derivative (Im D)) (at z within s)"
  have "CDERIV (\<lambda>x. RE f x + ii * IM f x) z : s :> Re D + ii * Im D"
    by (rule * derivative_intros has_vector_derivative_complex_mul)+
  also have "(\<lambda>x. RE f x + ii * IM f x) = f"
    by (auto simp: fun_eq_iff complex_eq_iff)
  also have "Re D + ii * Im D = D"
    by (simp add: complex_eq_iff)
  finally show "(CDERIV f z : s :> D)" .
qed

lemma CDERIV_iexp: "CDERIV iexp x : s :> \<i> * iexp x"
  unfolding CDERIV_def
  by (auto intro!: derivative_eq_intros simp add: cis_conv_exp[symmetric])

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

lemma CDERIV_setsum:
  assumes "\<And>n. n \<in> S \<Longrightarrow> CDERIV (\<lambda>x. f x n) x :> (f' x n)"
  shows "CDERIV (\<lambda>x. setsum (f x) S) x :> setsum (f' x) S"
  by (rule has_vector_derivative_setsum) fact

(* These are *not* instances of corresponding facts for has_vector_derivative *)

lemma CDERIV_mult: "\<lbrakk>CDERIV f x : s :> Da; CDERIV g x : s :> Db\<rbrakk> \<Longrightarrow>
  CDERIV (\<lambda>x. f x * g x) x : s :> (Da * (g x)) + (Db * (f x))"
  using has_vector_derivative_mult[of f Da x s g Db] by (simp add: ac_simps)

lemma CDERIV_isCont: "CDERIV f x :> D \<Longrightarrow> isCont f x"
  unfolding CDERIV_def
  by (subst isCont_RE_IM_iff, auto intro: DERIV_isCont)

lemma CDERIV_continuous: "CDERIV f x : s :> D \<Longrightarrow> continuous (at x within s) f"
  by (auto intro: has_derivative_continuous simp: has_vector_derivative_def)

lemma CDERIV_of_real [simp]: "(f has_field_derivative u) (at x within s) \<Longrightarrow>
   (CDERIV (%x. complex_of_real (f x)) x : s :> complex_of_real u)"
  unfolding CDERIV_def by auto


(* 
  Integration of functions from real to complex
*)

(** Need to fix complex integral syntax. **)

abbreviation complex_integrable :: "'a measure \<Rightarrow> ('a \<Rightarrow> complex) \<Rightarrow> bool" where
  "complex_integrable M f \<equiv> integrable M f"

abbreviation complex_lebesgue_integral :: "'a measure \<Rightarrow> ('a \<Rightarrow> complex) \<Rightarrow> complex" ("integral\<^sup>C") where
  "integral\<^sup>C M f == integral\<^sup>L M f"

syntax
  "_complex_lebesgue_integral" :: "pttrn \<Rightarrow> complex \<Rightarrow> 'a measure \<Rightarrow> complex"
 ("\<integral>\<^sup>C _. _ \<partial>_" [60,61] 110)

translations
  "\<integral>\<^sup>Cx. f \<partial>M" == "CONST complex_lebesgue_integral M (\<lambda>x. f)"

syntax
  "_ascii_complex_lebesgue_integral" :: "pttrn \<Rightarrow> 'a measure \<Rightarrow> real \<Rightarrow> real"
  ("(3CLINT _|_. _)" [0,110,60] 60)

translations
  "CLINT x|M. f" == "CONST complex_lebesgue_integral M (\<lambda>x. f)"

lemma complex_integrable_cnj [simp]:
  "complex_integrable M (Cnj f) \<longleftrightarrow> complex_integrable M f"
proof
  assume "complex_integrable M (Cnj f)"
  then have "complex_integrable M (Cnj (Cnj f))"
    by (rule integrable_cnj)
  then show "complex_integrable M f"
    by simp
qed simp

lemma complex_of_real_integrable_eq:
  "complex_integrable M (\<lambda>x. complex_of_real (f x)) \<longleftrightarrow> integrable M f"
proof
  assume "complex_integrable M (\<lambda>x. complex_of_real (f x))"
  then have "integrable M (RE (\<lambda>x. complex_of_real (f x)))"
    by (rule integrable_Re)
  then show "integrable M f"
    by simp
qed simp

(*
  Integration over a set -- compare to Set_Integral.thy
*)

abbreviation complex_set_integrable :: "'a measure \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> complex) \<Rightarrow> bool" where
  "complex_set_integrable M A f \<equiv> set_integrable M A f"

abbreviation complex_set_lebesgue_integral :: "'a measure \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> complex) \<Rightarrow> complex" where
  "complex_set_lebesgue_integral M A f \<equiv> set_lebesgue_integral M A f"

syntax
"_ascii_complex_set_lebesgue_integral" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'a measure \<Rightarrow> real \<Rightarrow> real"
("(4CLINT _:_|_. _)" [0,60,110,61] 60)

translations
"CLINT x:A|M. f" == "CONST complex_set_lebesgue_integral M A (\<lambda>x. f)"

lemma cmod_mult: "cmod ((a :: real) * (x :: complex)) = abs a * cmod x"
  by (subst norm_mult, auto)

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

abbreviation complex_interval_lebesgue_integral :: 
    "real measure \<Rightarrow> ereal \<Rightarrow> ereal \<Rightarrow> (real \<Rightarrow> complex) \<Rightarrow> complex" where
  "complex_interval_lebesgue_integral M a b f \<equiv> interval_lebesgue_integral M a b f"

abbreviation complex_interval_lebesgue_integrable :: 
  "real measure \<Rightarrow> ereal \<Rightarrow> ereal \<Rightarrow> (real \<Rightarrow> complex) \<Rightarrow> bool" where
  "complex_interval_lebesgue_integrable M a b f \<equiv> interval_lebesgue_integrable M a b f"

syntax
  "_ascii_complex_interval_lebesgue_borel_integral" :: "pttrn \<Rightarrow> ereal \<Rightarrow> ereal \<Rightarrow> real \<Rightarrow> complex"
  ("(4CLBINT _=_.._. _)" [0,60,60,61] 60)

translations
  "CLBINT x=a..b. f" == "CONST complex_interval_lebesgue_integral CONST lborel a b (\<lambda>x. f)"

lemma interval_integral_norm:
  fixes f :: "real \<Rightarrow> 'a :: {banach, second_countable_topology}"
  shows "interval_lebesgue_integrable lborel a b f \<Longrightarrow> a \<le> b \<Longrightarrow>
    norm (LBINT t=a..b. f t) \<le> LBINT t=a..b. norm (f t)"
  using integral_norm_bound[of lborel "\<lambda>x. indicator (einterval a b) x *\<^sub>R f x"]
  by (auto simp add: interval_lebesgue_integral_def interval_lebesgue_integrable_def)

lemma interval_integral_norm2:
  "interval_lebesgue_integrable lborel a b f \<Longrightarrow> 
    norm (LBINT t=a..b. f t) \<le> abs (LBINT t=a..b. norm (f t))"
proof (induct a b rule: linorder_wlog)
  case (sym a b) then show ?case
    by (simp add: interval_integral_endpoints_reverse[of a b] interval_integrable_endpoints_reverse[of a b])
next
  case (le a b) 
  then have "\<bar>LBINT t=a..b. norm (f t)\<bar> = LBINT t=a..b. norm (f t)"  
    using integrable_norm[of lborel "\<lambda>x. indicator (einterval a b) x *\<^sub>R f x"]
    by (auto simp add: interval_lebesgue_integral_def interval_lebesgue_integrable_def
             intro!: integral_nonneg_AE abs_of_nonneg)
  then show ?case
    using le by (simp add: interval_integral_norm)
qed

(*
  First application of the FTC: integrating e^ix
*)

lemma interval_integral_iexp:
  fixes a b :: real
  shows "(CLBINT x=a..b. iexp x) = ii * iexp a - ii * iexp b"
  apply (subst interval_integral_FTC_finite [where F = "\<lambda>x. -ii * iexp x"])
  apply (rule continuous_on_exp, rule continuous_on_mult, rule continuous_on_const)
  apply (rule continuous_on_of_real, rule continuous_on_id)
  apply (subgoal_tac "expi (\<i> * complex_of_real x) = -ii * (ii * expi (\<i> * complex_of_real x))")
  apply (erule ssubst)
  apply (rule CDERIV_cmult)
  apply (rule CDERIV_iexp)
  apply auto
  done

end