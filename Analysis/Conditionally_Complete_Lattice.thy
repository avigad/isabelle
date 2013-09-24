theory Conditionally_Complete_Lattice

imports Complex_Main

begin

context ord
begin

definition "bdd_above A \<equiv> \<exists>M. \<forall>x \<in> A. x \<le> M"
definition "bdd_below A \<equiv> \<exists>m. \<forall>x \<in> A. m \<le> x"

end

context order
begin

abbreviation "is_Sup s A \<equiv> (\<forall>x \<in> A. x \<le> s) \<and> (\<forall>M. (\<forall>x \<in> A. x \<le> M) \<longrightarrow> s \<le> M)"
abbreviation "is_Inf i A \<equiv> (\<forall>x \<in> A. i \<le> x) \<and> (\<forall>m. (\<forall>x \<in> A. m \<le> x) \<longrightarrow> m \<le> i)"
abbreviation "has_Sup A \<equiv> \<exists>s. is_Sup s A"
abbreviation "has_Inf A \<equiv> \<exists>i. is_Inf i A"

end

context lattice
begin

lemma bdd_above_insert [simp]: "bdd_above (insert a A) = bdd_above A"
unfolding bdd_above_def apply auto
apply (rule_tac x = "sup a M" in exI)
by (auto intro: le_supI2 sup_ge1)

lemma bdd_below_insert [simp]: "bdd_below (insert a A) = bdd_below A"
unfolding bdd_below_def apply auto
apply (rule_tac x = "inf a m" in exI)
by (auto intro: le_infI2 inf_le1)

lemma bdd_above_Un [simp]: "bdd_above (A \<union> B) = (bdd_above A \<and> bdd_above B)"
proof
  assume "bdd_above (A \<union> B)"
  thus "bdd_above A \<and> bdd_above B" unfolding bdd_above_def by auto
next
  assume "bdd_above A \<and> bdd_above B"
  then obtain a b where "\<forall>x\<in>A. x \<le> a" "\<forall>x\<in>B. x \<le> b" unfolding bdd_above_def by auto
  hence "\<forall>x \<in> A \<union> B. x \<le> sup a b" by (auto intro: Un_iff le_supI1 le_supI2)
  thus "bdd_above (A \<union> B)" unfolding bdd_above_def ..
qed

lemma bdd_below_Un [simp]: "bdd_below (A \<union> B) = (bdd_below A \<and> bdd_below B)"
proof
  assume "bdd_below (A \<union> B)"
  thus "bdd_below A \<and> bdd_below B" unfolding bdd_below_def by auto
next
  assume "bdd_below A \<and> bdd_below B"
  then obtain a b where "\<forall>x\<in>A. a \<le> x" "\<forall>x\<in>B. b \<le> x" unfolding bdd_below_def by auto
  hence "\<forall>x \<in> A \<union> B. inf a b \<le> x" by (auto intro: Un_iff le_infI1 le_infI2)
  thus "bdd_below (A \<union> B)" unfolding bdd_below_def ..
qed

lemma subset_bdd_above:
  assumes "bdd_above B"
  and "A \<subseteq> B"
  shows "bdd_above A"
unfolding bdd_above_def using assms
by (metis (full_types) ord.bdd_above_def order_class.le_neq_trans psubsetD)

lemma subset_bdd_below:
  assumes "bdd_below B"
  and "A \<subseteq> B"
  shows "bdd_below A"
unfolding bdd_below_def using assms by (metis ord.bdd_below_def order_class.le_neq_trans psubsetD)

lemma intersection_bdd_above [simp]:
  assumes "bdd_above A"
  shows "bdd_above (A \<inter> B)"
using subset_bdd_above assms by auto

lemma intersection_bdd_below [simp]:
  assumes "bdd_below A"
  shows "bdd_below (A \<inter> B)"
using subset_bdd_below assms by auto

lemma empty_bdd_above [simp]: "bdd_above {}"
  unfolding bdd_above_def by auto

lemma empty_bdd_below [simp]: "bdd_below {}"
  unfolding bdd_below_def by auto

lemma bdd_finite [simp]:
  assumes "finite A"
  shows "bdd_above A" and "bdd_below A"
using assms by (induct rule: finite_induct, auto)

end

(* Why does trying to use a locale here result in superfluous types? *)
class conditionally_complete_lattice = lattice +
  assumes bdd_nonempty_Sup: "\<And>A. A \<noteq> {} \<Longrightarrow> bdd_above A \<Longrightarrow> has_Sup A"
  and bdd_nonempty_Inf: "\<And>A. A \<noteq> {} \<Longrightarrow> bdd_below A \<Longrightarrow> has_Inf A"
  begin

notation inf (infixl "\<sqinter>" 70) and sup (infixl "\<squnion>" 65)

definition Sup :: "'a set \<Rightarrow> 'a" ("\<Squnion>_" [900] 900) where "Sup A = (THE S. is_Sup S A)"
definition Inf :: "'a set \<Rightarrow> 'a" ("\<Sqinter>_" [900] 900) where "Inf A = (THE s. is_Inf s A)"

lemma Sup_is_Sup:
  fixes A
  assumes "has_Sup A"
  shows "is_Sup (Sup A) A"
proof -
  from assms obtain s where sup_s: "is_Sup s A" by auto
  show ?thesis
    unfolding Sup_def apply (rule theI2, rule sup_s)
    using sup_s apply (metis eq_iff sup_s)
    by auto
qed

lemma Sup_unique:
  fixes A s
  assumes "is_Sup s A"
  shows "s = Sup A"
proof -
  from assms Sup_is_Sup have "Sup A \<le> s" by auto
  moreover from assms Sup_is_Sup have "s \<le> Sup A" by blast
  ultimately show ?thesis by auto
qed

lemma Inf_is_Inf: 
  fixes A
  assumes "has_Inf A"
  shows "is_Inf (Inf A) A"
proof -
  from assms obtain i where inf_i: "is_Inf i A" by auto
  show ?thesis
    unfolding Inf_def apply (rule theI2, rule inf_i)
    using inf_i apply (metis eq_iff inf_i)
    by auto
qed

lemma Inf_unique:
  fixes A i
  assumes "is_Inf i A"
  shows "i = Inf A"
proof -
  from assms Inf_is_Inf have "i \<le> Inf A" by auto
  moreover from assms Inf_is_Inf have "Inf A \<le> i" by blast
  ultimately show ?thesis by auto
qed

lemma Sup_upper:
  fixes A x
  assumes "bdd_above A" and "x \<in> A"
  shows "x \<le> Sup A"
proof -
  from assms have "A \<noteq> {}" by auto
  thus ?thesis using assms bdd_nonempty_Sup Sup_is_Sup by auto
qed

(* This also works when A = {}, provided the lattice has a bottom. *)
lemma Sup_least:
  fixes A M
  assumes "A \<noteq> {}" and M_upper: "\<And>x. x \<in> A \<Longrightarrow> x \<le> M"
  shows "Sup A \<le> M"
proof -
  from M_upper have "bdd_above A" using bdd_above_def by auto
  with assms bdd_nonempty_Sup Sup_is_Sup show ?thesis by auto
qed
    
lemma Inf_lower: 
  fixes A x
  assumes "bdd_below A" and "x \<in> A"
  shows "Inf A \<le> x"
proof -
  from assms have "A \<noteq> {}" by auto
  thus ?thesis using assms bdd_nonempty_Inf Inf_is_Inf by auto
qed

(* This also works if A = {}, provided the lattice has a top. *)
lemma Inf_greatest: 
  fixes A m
  assumes "A \<noteq> {}" and m_lower: "\<And>x. x \<in> A \<Longrightarrow> m \<le> x"
  shows "m \<le> Inf A"
proof -
  from m_lower have "bdd_below A" using bdd_below_def by auto
  with assms bdd_nonempty_Inf Inf_is_Inf show ?thesis by auto
qed

lemma bdd_nonempty_Sup_subset_mono:
  fixes A B
  assumes "A \<noteq> {}" and "bdd_above B" and "A \<subseteq> B"
  shows "Sup A \<le> Sup B"
proof -
  from assms Sup_upper have "\<forall>x\<in>A. x \<le> Sup B" by auto
  thus ?thesis using assms Sup_least by auto
qed

lemma bdd_nonempty_Inf_superset_mono:
  fixes A B
  assumes "B \<noteq> {}" and "bdd_below A" and "B \<subseteq> A"
  shows "Inf A \<le> Inf B"
proof -
  from assms Inf_lower have "\<forall>x\<in>B. Inf A \<le> x" by auto
  thus ?thesis using assms Inf_greatest by auto
qed

lemma dual_conditionally_complete_lattice:
  "class.conditionally_complete_lattice sup (op \<ge>) (op >) inf"
  apply (unfold_locales)
  apply (auto intro: Sup_is_Sup Sup_upper Sup_least Inf_is_Inf Inf_lower Inf_greatest)
  unfolding bdd_above_def bdd_below_def apply (metis less_le)
  apply (metis (lifting) bdd_below_def bdd_nonempty_Inf empty_iff ord.bdd_above_def)
  by (metis (lifting) Sup_least Sup_upper bdd_above_def empty_iff ord.bdd_below_def)

definition InfI :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a" where "InfI A f = \<Sqinter>(f ` A)"

definition SupR :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a" where "SupR A f = \<Squnion>(f ` A)"

(** Left out "foundation_dual" lemmata from Complete_Lattices.thy; do not see how they make sense. **)

lemma InfI_lower:
  fixes A f x
  assumes "bdd_below (f ` A)" and "x \<in> A"
  shows "InfI A f \<le> f x"
by (metis InfI_def Inf_lower assms image_eqI)

lemma InfI_greatest:
  fixes A f m
  assumes "A \<noteq> {}" and "\<And>x. x \<in> A \<Longrightarrow> m \<le> f x"
  shows "m \<le> InfI A f"
by (metis (hide_lams, mono_tags) InfI_def Inf_greatest assms empty_is_image image_iff)
  
lemma SupR_upper:
  fixes A f x
  assumes "x \<in> A" and "bdd_above (f ` A)"
  shows "f x \<le> SupR A f"
by (metis (full_types) SupR_def Sup_upper assms image_eqI)

lemma SupR_least:
  fixes A f
  assumes "A \<noteq> {}" and "\<And>x. x \<in> A \<Longrightarrow> f x \<le> M"
  shows "SupR A f \<le> M"
by (metis (hide_lams, mono_tags) SupR_def Sup_least assms empty_is_image image_iff)

lemma Inf_lower2:
  fixes A u v
  assumes "bdd_below A" and "u \<in> A" and "u \<le> v"
  shows "\<Sqinter>A \<le> v"
by (metis Inf_lower assms order_trans)

lemma InfI_lower2:
  fixes A f x u
  assumes "bdd_below (f ` A)" and "x \<in> A" and "f x \<le> u"
  shows "InfI A f \<le> u"
by (auto intro: InfI_lower assms order_trans)

lemma Sup_upper2:
  fixes A u v
  assumes "bdd_above A" and "u \<in> A" and "v \<le> u"
  shows "v \<le> \<Squnion>A"
by (metis Sup_upper assms order_trans)

lemma SupR_upper2:
  fixes A f x u
  assumes "bdd_above (f ` A)" and "x \<in> A" and "u \<le> f x"
  shows "u \<le> SupR A f"
by (auto intro: SupR_upper assms order_trans)

(* Can weaken assumptions to "has_Inf A". *)
lemma le_Inf_iff:
  fixes A b
  assumes "A \<noteq> {}" and "bdd_below A"
  shows "b \<le> \<Sqinter>A \<longleftrightarrow> (\<forall>a\<in>A. b \<le> a)"
by (metis Inf_greatest Inf_lower assms order_trans)

lemma le_InfI_iff:
  fixes A f u
  assumes "A \<noteq> {}" and "bdd_below (f ` A)"
  shows "u \<le> InfI A f \<longleftrightarrow> (\<forall>x\<in>A. u \<le> f x)"
by (metis InfI_greatest InfI_lower assms order_trans)

lemma Sup_le_iff:
  fixes A b
  assumes "A \<noteq> {}" and "bdd_above A"
  shows "\<Squnion>A \<le> b \<longleftrightarrow> (\<forall>a\<in>A. a \<le> b)"
by (metis Sup_least Sup_upper assms order_trans)

lemma SupR_le_iff:
  fixes A f u
  assumes "A \<noteq> {}" and "bdd_above (f ` A)"
  shows "SupR A f \<le> u \<longleftrightarrow> (\<forall>x\<in>A. f x \<le> u)"
by (metis SupR_least SupR_upper assms order_trans)

lemma Inf_insert [simp]:
  fixes A a
  assumes "A \<noteq> {}" and "bdd_below A"
  shows "\<Sqinter>insert a A = a \<sqinter> \<Sqinter>A"
apply (rule antisym)
prefer 2 apply (rule Inf_greatest, auto)
apply (rule le_infI2)
apply (rule Inf_lower)
using assms apply auto [2]
by (auto simp add: assms le_Inf_iff Inf_lower)

lemma InfI_insert:
  fixes A f a
  assumes "A \<noteq> {}" and "bdd_below (f ` A)"
  shows "InfI (insert a A) f = f a \<sqinter> InfI A f"
by (smt InfI_def Inf_insert assms empty_is_image image_insert)

lemma Sup_insert [simp]:
  fixes A a
  assumes "A \<noteq> {}" and "bdd_above A"
  shows "\<Squnion>insert a A = a \<squnion> \<Squnion>A"
apply (rule antisym)
apply (rule Sup_least, auto)
apply (rule le_supI2)
apply (rule Sup_upper)
using assms apply auto [2]
by (auto simp add: assms Sup_le_iff Sup_upper)

lemma SupR_insert: 
  fixes A a f
  assumes "A \<noteq> {}" and "bdd_above (f ` A)" 
  shows "SupR (insert a A) f = f a \<squnion> SupR A f"
by (smt SupR_def Sup_insert assms empty_is_image image_insert)

lemma InfI_image [simp]: "InfI (f`A) g = InfI A (g \<circ> f)"
using InfI_def image_compose by metis

lemma SupR_image [simp]: "SupR (f`A) g = SupR A (g \<circ> f)"
using SupR_def image_compose by metis

lemma Inf_Sup: 
  assumes "A \<noteq> {}" and "bdd_below A" and "{b. \<forall>a \<in> A. b \<le> a} \<noteq> {}"
  shows "\<Sqinter>A = \<Squnion>{b. \<forall>a \<in> A. b \<le> a}"
proof -
  have "\<And>b. (\<forall>a \<in> A. b \<le> a) \<Longrightarrow> b \<le> Inf A" using assms Inf_greatest by simp
  moreover have "\<And>M. (\<And>b. (\<forall>a \<in> A. b \<le> a) \<Longrightarrow> b \<le> M) \<Longrightarrow> Inf A \<le> M" using assms Inf_lower by auto
  ultimately show ?thesis using Sup_unique by auto
qed

(**** More theorems to transfer from Complete_Lattices.thy. *)

(* Perhaps obtain this as dual of preceding theorem. *)
lemma Sup_Inf:  
  assumes "A \<noteq> {}" and "bdd_above A" and "{b. \<forall>a \<in> A. a \<le> b} \<noteq> {}"
  shows "\<Squnion>A = \<Sqinter>{b. \<forall>a \<in> A. a \<le> b}"
proof -
  have "\<And>b. (\<forall>a \<in> A. a \<le> b) \<Longrightarrow> Sup A \<le> b" using assms Sup_least by simp
  moreover have "\<And>m. (\<And>b. (\<forall>a \<in> A. a \<le> b) \<Longrightarrow> m \<le> b) \<Longrightarrow> m \<le> Sup A" using assms Sup_upper by auto
  ultimately show ?thesis using Inf_unique by auto
qed

lemma InfI_cong: "A = B \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> C x = D x) \<Longrightarrow> InfI A C = InfI B D"
  by (metis (full_types) InfI_def image_cong)

lemma SUP_cong:
  "A = B \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> C x = D x) \<Longrightarrow> SupR A C = SupR B D"
  by (metis (full_types) SupR_def image_cong)

lemma Inf_mono:
  assumes "A \<noteq> {}" and "bdd_below A"
  and "B \<noteq> {}"
  and "\<And>b. b \<in> B \<Longrightarrow> \<exists>a\<in>A. a \<le> b"
  shows "\<Sqinter>A \<le> \<Sqinter>B"
proof (rule Inf_greatest)
  fix b assume "b \<in> B"
  with assms obtain a where "a \<in> A" and "a \<le> b" by blast
  from `a \<in> A` have "\<Sqinter>A \<le> a" using assms Inf_lower by auto
  with `a \<le> b` show "\<Sqinter>A \<le> b" by auto
qed (rule assms)

lemma InfI_mono:
  assumes "A \<noteq> {}" and "bdd_below (f ` A)" 
  and "B \<noteq> {}" 
  shows "(\<And>m. m \<in> B \<Longrightarrow> \<exists>n\<in>A. f n \<le> g m) \<Longrightarrow> InfI A f \<le> InfI B g"
  unfolding InfI_def using assms by (auto intro: Inf_mono)

lemma Sup_mono:
  assumes "A \<noteq> {}" 
  and "B \<noteq> {}" and "bdd_above B"
  and "\<And>a. a \<in> A \<Longrightarrow> \<exists>b\<in>B. a \<le> b"
  shows "\<Squnion>A \<le> \<Squnion>B"
proof (rule Sup_least)
  fix a assume "a \<in> A"
  with assms obtain b where "b \<in> B" and "a \<le> b" by blast
  from `b \<in> B` have "b \<le> \<Squnion>B" using assms Sup_upper by auto
  with `a \<le> b` show "a \<le> \<Squnion>B" by auto
qed (rule assms)

lemma SupR_mono:
  assumes "A \<noteq> {}"
  and "B \<noteq> {}" and "bdd_above (g ` B)"
  shows "(\<And>n. n \<in> A \<Longrightarrow> \<exists>m\<in>B. f n \<le> g m) \<Longrightarrow> SupR A f \<le> SupR B g"
unfolding SupR_def using assms by (auto intro: Sup_mono)

(* TODO: Cleanup. *)
lemma SupR_subset_mono:
  assumes "A \<noteq> {}" and "bdd_above (g ` B)"
  and "A \<subseteq> B"
  and "\<And>x. x \<in> B \<Longrightarrow> f x \<le> g x"
  shows "SupR A f \<le> SupR B g"
apply (rule SupR_mono)
apply (rule assms)
using assms apply force
apply (rule assms)
using subset_bdd_above assms by force

lemma Inf_less_eq:
  assumes "\<And>v. v \<in> A \<Longrightarrow> v \<le> u"
    and "A \<noteq> {}" and "bdd_below A"
  shows "\<Sqinter>A \<le> u"
proof -
  from `A \<noteq> {}` obtain v where "v \<in> A" by blast
  moreover with assms have "v \<le> u" by blast
  ultimately show ?thesis using assms Inf_lower2 by auto
qed

lemma less_eq_Sup:
  assumes "\<And>v. v \<in> A \<Longrightarrow> u \<le> v"
  and "A \<noteq> {}" and "bdd_above A"
  shows "u \<le> \<Squnion>A"
proof -
  from `A \<noteq> {}` obtain v where "v \<in> A" by blast
  moreover with assms have "u \<le> v" by blast
  ultimately show ?thesis using assms Sup_upper2 by auto
qed

lemma less_eq_Inf_inter:
  assumes "bdd_below A" and "bdd_below B" and "A \<inter> B \<noteq> {}"
  shows "\<Sqinter>A \<squnion> \<Sqinter>B \<le> \<Sqinter>(A \<inter> B)"
using intersection_bdd_below Inf_greatest Inf_lower assms
by (metis bdd_nonempty_Inf_superset_mono lattice_class.inf_sup_ord(1) lattice_class.inf_sup_ord(2) le_supI)

lemma Sup_inter_less_eq: 
  assumes "bdd_above A" and "bdd_above B" and "A \<inter> B \<noteq> {}"
  shows "\<Squnion>(A \<inter> B) \<le> \<Squnion>A \<sqinter> \<Squnion>B "
using intersection_bdd_above Inf_greatest Inf_lower assms
by (metis bdd_nonempty_Sup_subset_mono lattice_class.inf_sup_ord(1) lattice_class.inf_sup_ord(2) le_infI)

lemma Inf_union_distrib: 
  assumes "A \<noteq> {}" and "bdd_below A"
  and "B \<noteq> {}" and "bdd_below B"
  shows "\<Sqinter>(A \<union> B) = \<Sqinter>A \<sqinter> \<Sqinter>B"
proof (rule antisym, auto)
  from bdd_nonempty_Inf_superset_mono assms show "\<Sqinter>(A \<union> B) \<le> \<Sqinter>A" by auto
  from bdd_nonempty_Inf_superset_mono assms show "\<Sqinter>(A \<union> B) \<le> \<Sqinter>B" by auto
  show "\<Sqinter>A \<sqinter> \<Sqinter>B \<le> \<Sqinter>(A \<union> B)"
    using Inf_greatest Inf_lower le_infI1 le_infI2 assms by (metis (full_types) Un_empty Un_iff)
qed

lemma InfI_union:
  assumes "A \<noteq> {}" and "bdd_below (f`A)"
  and "B \<noteq> {}" and "bdd_below (f`B)"
  shows "InfI (A \<union> B) f = (InfI A f) \<sqinter> (InfI B f)"
unfolding InfI_def using assms by (auto simp add: image_Un intro: Inf_union_distrib)

lemma Sup_union_distrib:
  assumes "A \<noteq> {}" and "bdd_above A"
  and "B \<noteq> {}" and "bdd_above B"
  shows "\<Squnion>(A \<union> B) = \<Squnion>A \<squnion> \<Squnion>B"
proof (rule antisym, auto)
  from bdd_nonempty_Sup_subset_mono assms show "\<Squnion>A \<le> \<Squnion>(A \<union> B)" by auto
  from bdd_nonempty_Sup_subset_mono assms show "\<Squnion>B \<le> \<Squnion>(A \<union> B)" by auto
  show "\<Squnion>(A \<union> B) \<le> \<Squnion>A \<squnion> \<Squnion>B"
    using Sup_least Sup_upper le_supI1 le_supI2 assms by (metis (full_types) Un_empty Un_iff)
qed

lemma SupR_union:
  assumes "A \<noteq> {}" and "bdd_above (f`A)"
  and "B \<noteq> {}" and "bdd_above (f`B)"
  shows "SupR (A \<union> B) f = SupR A f \<squnion> SupR B f"
unfolding SupR_def using assms by (auto simp add: image_Un intro: Sup_union_distrib)

lemma InfI_inf_distrib:
  assumes "A \<noteq> {}" and "bdd_below (f`A)" and "bdd_below (g`A)"
  shows "InfI A f \<sqinter> InfI A g = InfI A (\<lambda>a. f a \<sqinter> g a)" (is "?L = ?R")
proof (rule antisym)
  show "?L \<le> ?R"
    by (rule InfI_greatest, rule assms) (auto intro: assms le_infI1 le_infI2 InfI_lower)
  show "?R \<le> ?L"
  proof -
    have "bdd_below ((\<lambda>a. f a \<sqinter> g a) ` A)" unfolding bdd_below_def
    proof -
      let ?m = "Inf (f`A) \<sqinter> Inf (g`A)"
      { fix x assume "x\<in>((\<lambda>a. f a \<sqinter> g a) ` A)"
        then obtain a where a: "a \<in> A" and x: "x = f a \<sqinter> g a" by auto
        from a have "?m \<le> f a" using assms InfI_lower InfI_def le_infI1 by metis
        moreover from a have "?m \<le> g a" using assms InfI_lower InfI_def le_infI2 by metis
        ultimately have "?m \<le> x" using x by auto
      } note lb = this
      from lb show "\<exists>m. \<forall>x\<in>(\<lambda>a. f a \<sqinter> g a) ` A. m \<le> x" by blast
    qed
    moreover have "InfI A (\<lambda>a. f a \<sqinter> g a) \<le> InfI A f"
      by (metis (lifting, full_types) InfI_mono assms(1) calculation inf_le1)
    moreover have "InfI A (\<lambda>a. f a \<sqinter> g a) \<le> InfI A g"
      by (metis (lifting, full_types) InfI_mono assms(1) calculation(1) inf_le2)
    ultimately show ?thesis using le_infI by auto
  qed
qed

lemma SUP_sup_distrib: 
  assumes "A \<noteq> {}" and "bdd_above (f`A)" and "bdd_above (g`A)"
  shows "SupR A f \<squnion> SupR A g = SupR A (\<lambda>a. f a \<squnion> g a)" (is "?L = ?R")
proof (rule antisym)
  show "?L \<le> ?R"
  proof -
    have "bdd_above ((\<lambda>a. f a \<squnion> g a) ` A)" unfolding bdd_above_def
    proof -
      let ?M = "Sup (f`A) \<squnion> Sup (g`A)"
      { fix x assume "x\<in>((\<lambda>a. f a \<squnion> g a) ` A)"
        then obtain a where a: "a \<in> A" and x: "x = f a \<squnion> g a" by auto
        from a have "f a \<le> ?M" using assms SupR_upper SupR_def le_supI1 by metis
        moreover from a have "g a \<le> ?M" using assms SupR_upper SupR_def le_supI2 by metis
        ultimately have "x \<le> ?M" using x by auto
      } note ub = this
      from ub show "\<exists>M. \<forall>x\<in>(\<lambda>a. f a \<squnion> g a) ` A. x \<le> M" by blast
    qed
    moreover have "SupR A f \<le> SupR A (\<lambda>a. f a \<squnion> g a)"
      by (metis (lifting, full_types) SupR_mono assms(1) calculation sup_ge1)
    moreover have "SupR A g \<le> SupR A (\<lambda>a. f a \<squnion> g a)"
      by (metis (lifting, full_types) SupR_mono assms(1) calculation(1) sup_ge2)
    ultimately show ?thesis using le_supI by auto
  qed
next
  show "?R \<le> ?L"
  by (rule SupR_least, rule assms) (auto intro: assms le_supI1 le_supI2 SupR_upper)
qed


end

instantiation real :: conditionally_complete_lattice
begin

instance proof
  fix A :: "real set" assume "A \<noteq> {}" and "bdd_above A"
  thus "has_Sup A" unfolding bdd_above_def using complete_real by auto
next
  fix A :: "real set" assume nonempty: "A \<noteq> {}" and bdd: "bdd_below A"
  have "has_Sup (uminus ` A)"
  proof -
    from bdd have "bdd_above (uminus ` A)"
      unfolding bdd_below_def bdd_above_def by (metis image_iff le_minus_iff minus_minus)
    (* Better way to use result of previous assertion in next-separated proof? *)
    thus ?thesis unfolding bdd_above_def using nonempty bdd complete_real[of "uminus ` A"] by auto
  qed
  thus "has_Inf A"
  proof -
    have "is_Inf (Inf_class.Inf A) A" using nonempty bdd
      by (metis (full_types) Inf_ge SupInf.Inf_lower bdd_below_def setgeI)
    thus ?thesis by auto
  qed
qed

end

locale conditionally_complete_lattice_with_top = conditionally_complete_lattice + top

locale conditionally_complete_lattice_with_bot = conditionally_complete_lattice + bot

end
