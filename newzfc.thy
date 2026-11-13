theory newzfc imports ZFC_in_HOL.ZFC_in_HOL
begin

axiomatization Collect :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set" \<comment> \<open>comprehension\<close>
  and member :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" \<comment> \<open>membership\<close>
  where mem_Collect_eq [iff, code_unfold]: "member a (Collect P) = P a"
    and Collect_mem_eq [simp]: "Collect (\<lambda>x. member x A) = A"

(*
syntax
  "_Coll" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a set"    ("(1{_./ _})")
translations
  "{x. P}" \<rightleftharpoons> "CONST Collect (\<lambda>x. P)"

class top =
  fixes top :: 'a ("\<top>")
*)
(*
definition image :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set"    (infixr "`" 90)
  where "f ` A = {y. \<exists>x\<in>A. y = f x}"
*)
abbreviation UNIV :: "'a set"
  where "UNIV \<equiv> top"

abbreviation range :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b set"  \<comment> \<open>of function\<close>
  where "range f \<equiv> f ` UNIV"

class Sup =
  fixes Sup :: "'a set \<Rightarrow> 'a"  ("\<Squnion>")

(*
abbreviation Union :: "'a set set \<Rightarrow> 'a set"  ("\<Union>")
  where "\<Union>S \<equiv> \<Squnion>S"
*)
definition Pow :: "'a set \<Rightarrow> 'a set set"
  where Pow_def: "Pow A = {B. B \<subseteq> A}"

definition inv_into :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a)" where
"inv_into A f = (\<lambda>x. SOME y. y \<in> A \<and> f y = x)"

lemma inv_into_def2: "inv_into A f x = (SOME y. y \<in> A \<and> f y = x)"
by(simp add: inv_into_def)

abbreviation inv :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a)" where
"inv \<equiv> inv_into UNIV"

definition wf :: "('a \<times> 'a) set \<Rightarrow> bool"
  where "wf r \<longleftrightarrow> (\<forall>P. (\<forall>x. (\<forall>y. (y, x) \<in> r \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> (\<forall>x. P x))"

(*
  Alignment with Paulson's ZFC_in_HOL cumulative hierarchy:
  The cumulative hierarchy type V, element extractor elts :: "V \<Rightarrow> V set",
  and set constructor vset :: "V set \<Rightarrow> V" are provided directly by ZFC_in_HOL.
  Axiomatic properties (extensionality, foundation, separation/downwards closure,
  powerset, union, replacement, infinity) are established theorems in ZFC_in_HOL.
*)

theorem t1 : \<open>A \<Longrightarrow> A\<close>
proof -
  assume H:\<open>A\<close>
  show \<open>A\<close>
    by (rule  H)
qed

axiomatization qwe :: "bool set"

theorem t2 : \<open>elts 0 = elts 0\<close>
  by (rule refl)

end