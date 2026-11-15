theory LambdaTypesRecursion
  imports recursion
begin

section \<open>Mechanization of Section 3 of main.tex: Simply Typed Lambda-Calculus Types via Recursion\<close>

text \<open>
  In Section 3 of main.tex ("Implementation of simply typed lambda-calculus"),
  given a set of type variables Var, a set of type constructors Const, and a
  single-step word/type formation operator W_step(X, Const) \<subseteq> U, we define the
  cumulative hierarchy of simple types over an ambient universe U (with Var \<subseteq> U)
  by primitive recursion on nat using recursionthm from recursion.thy:
    f`0 = Var
    f`succ(n) = f`n \<union> W_step(f`n)
    Types = \<Union> {f`n . n \<in> nat}
\<close>

definition type_step_rel :: "[i, i] \<Rightarrow> i" where
  "type_step_rel(U, W) \<equiv> {\<langle>\<langle>X, n\<rangle>, X \<union> (W ` X)\<rangle> . \<langle>X, n\<rangle> \<in> Pow(U) \<times> nat}"

lemma type_step_rel_fun:
  assumes W_fun: "W \<in> Pow(U) \<rightarrow> Pow(U)"
  shows "type_step_rel(U, W) \<in> (Pow(U) \<times> nat) \<rightarrow> Pow(U)"
proof -
  have "\<forall>p \<in> Pow(U) \<times> nat. (fst(p) \<union> (W ` fst(p))) \<in> Pow(U)"
  proof
    fix p assume "p \<in> Pow(U) \<times> nat"
    then obtain X n where "p = \<langle>X, n\<rangle>" and X_in: "X \<in> Pow(U)" and "n \<in> nat" by auto
    moreover from W_fun X_in have "W ` X \<in> Pow(U)" by (rule apply_funtype)
    ultimately show "(fst(p) \<union> (W ` fst(p))) \<in> Pow(U)" by auto
  qed
  then show ?thesis
    unfolding type_step_rel_def Pi_def function_def by auto
qed

theorem simple_types_hierarchy_exists:
  assumes Var_sub: "Var \<in> Pow(U)"
    and W_fun: "W \<in> Pow(U) \<rightarrow> Pow(U)"
  shows "\<exists>f \<in> nat \<rightarrow> Pow(U).
    f ` 0 = Var \<and>
    (\<forall>n \<in> nat. f ` succ(n) = (f ` n) \<union> (W ` (f ` n)))"
proof -
  let ?g = "type_step_rel(U, W)"
  have g_fun: "?g \<in> (Pow(U) \<times> nat) \<rightarrow> Pow(U)"
    using type_step_rel_fun[OF W_fun] .
  have rec: "\<exists>f \<in> nat \<rightarrow> Pow(U). f ` 0 = Var \<and> (\<forall>n \<in> nat. f ` succ(n) = ?g ` \<langle>f ` n, n\<rangle>)"
    using recursionthm[OF Var_sub g_fun] .
  then obtain f where f_fun: "f \<in> nat \<rightarrow> Pow(U)"
    and f_0: "f ` 0 = Var"
    and f_succ: "\<forall>n \<in> nat. f ` succ(n) = ?g ` \<langle>f ` n, n\<rangle>"
    by blast
  have "\<forall>n \<in> nat. f ` succ(n) = (f ` n) \<union> (W ` (f ` n))"
  proof
    fix n assume n_in: "n \<in> nat"
    have fn_in: "f ` n \<in> Pow(U)"
      using apply_funtype[OF f_fun n_in] .
    have pair_in: "\<langle>f ` n, n\<rangle> \<in> Pow(U) \<times> nat"
      using fn_in n_in by blast
    have "?g ` \<langle>f ` n, n\<rangle> = (f ` n) \<union> (W ` (f ` n))"
      using pair_in unfolding type_step_rel_def by (simp add: apply_equality[OF _ g_fun])
    with f_succ n_in show "f ` succ(n) = (f ` n) \<union> (W ` (f ` n))"
      by simp
  qed
  with f_fun f_0 show ?thesis by blast
qed

definition SimpleTypes :: "[i, i] \<Rightarrow> i" where
  "SimpleTypes(f, N) \<equiv> \<Union> {f ` n . n \<in> N}"

lemma SimpleTypes_base_subset:
  assumes "0 \<in> N" and "f ` 0 = Var"
  shows "Var \<subseteq> SimpleTypes(f, N)"
  using assms unfolding SimpleTypes_def by blast

end
