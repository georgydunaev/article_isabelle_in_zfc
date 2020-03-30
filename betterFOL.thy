
section \<open>Intuitionistic first-order logic\<close>

theory betterFOL
imports Pure
begin

ML \<open>\<^assert> (not (can ML \<open>open RunCall\<close>))\<close>
ML_file \<open>~~/src/Tools/misc_legacy.ML\<close>
ML_file \<open>~~/src/Provers/splitter.ML\<close>
ML_file \<open>~~/src/Provers/hypsubst.ML\<close>
ML_file \<open>~~/src/Tools/IsaPlanner/zipper.ML\<close>
ML_file \<open>~~/src/Tools/IsaPlanner/isand.ML\<close>
ML_file \<open>~~/src/Tools/IsaPlanner/rw_inst.ML\<close>
ML_file \<open>~~/src/Provers/quantifier1.ML\<close>
ML_file \<open>~~/src/Tools/intuitionistic.ML\<close>
ML_file \<open>~~/src/Tools/project_rule.ML\<close>
ML_file \<open>~~/src/Tools/atomize_elim.ML\<close>


subsection \<open>Syntax and axiomatic basis\<close>

setup Pure_Thy.old_appl_syntax_setup

class "term"
default_sort \<open>term\<close>

typedecl o

judgment
  Trueprop :: \<open>o \<Rightarrow> prop\<close>  (\<open>(_)\<close> 5)


subsubsection \<open>Equality\<close>

axiomatization
  eq :: \<open>['a, 'a] \<Rightarrow> o\<close>  (infixl \<open>=\<close> 50)
where
  refl: \<open>a = a\<close> and
  subst: \<open>a = b \<Longrightarrow> P(a) \<Longrightarrow> P(b)\<close>


subsubsection \<open>Propositional logic\<close>

axiomatization
  False :: \<open>o\<close> and
  conj :: \<open>[o, o] => o\<close>  (infixr \<open>\<and>\<close> 35) and
  disj :: \<open>[o, o] => o\<close>  (infixr \<open>\<or>\<close> 30) and
  imp :: \<open>[o, o] => o\<close>  (infixr \<open>\<longrightarrow>\<close> 25)

axiomatization
where
  mp: \<open>\<lbrakk>P \<longrightarrow> Q; P\<rbrakk> \<Longrightarrow> Q\<close> and
  a1: \<open>A \<longrightarrow> (B \<longrightarrow> A)\<close> and
  a2: \<open>(A \<longrightarrow> (B \<longrightarrow> C))\<longrightarrow>((A \<longrightarrow> B)\<longrightarrow>(A \<longrightarrow> C))\<close>

theorem Ded: \<open>(P \<Longrightarrow> Q) \<Longrightarrow> P \<longrightarrow> Q\<close>

(*

  conjI: \<open>\<lbrakk>P;  Q\<rbrakk> \<Longrightarrow> P \<and> Q\<close> and
  conjunct1: \<open>P \<and> Q \<Longrightarrow> P\<close> and
  conjunct2: \<open>P \<and> Q \<Longrightarrow> Q\<close> and

  disjI1: \<open>P \<Longrightarrow> P \<or> Q\<close> and
  disjI2: \<open>Q \<Longrightarrow> P \<or> Q\<close> and
  disjE: \<open>\<lbrakk>P \<or> Q; P \<Longrightarrow> R; Q \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R\<close> and

  impI: \<open>(P \<Longrightarrow> Q) \<Longrightarrow> P \<longrightarrow> Q\<close> and
  mp: \<open>\<lbrakk>P \<longrightarrow> Q; P\<rbrakk> \<Longrightarrow> Q\<close> and

  FalseE: \<open>False \<Longrightarrow> P\<close>
*)

