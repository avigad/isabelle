(*
Theory: Central_Limit_Theorem.thy
Authors: Jeremy Avigad, Luke Serafin
*)

theory Central_Limit_Theorem

imports Library_Misc Weak_Convergence

begin

(** Inequality for difference of complex products. **)
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


end
