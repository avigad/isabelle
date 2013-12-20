(*
Theory: Inversion.thy
Authors: Jeremy Avigad, Luke Serafin
*)

theory Inversion

imports Weak_Convergence Real_to_Complex

begin


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



end
