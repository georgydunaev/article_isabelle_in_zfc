# [ARTICLE_ISABELLE_IN_ZFC] Ticket 7474: Isabelle Theory Proof Completion and Oops Discharge

**Repository:** `article_isabelle_in_zfc`  
**Status:** `OPEN`  
**Created:** `2026-11-13T22:00:00Z`  

## Problem Description
A structural audit of the Isabelle theories in this repository revealed several unfinished lemma proofs marked with `oops`, as well as primitive signature gaps:

1. `recursion.thy`:
   - `theorem domuncomp`:
     ```isabelle
     theorem domuncomp: 
       assumes H0:\<open>compatset(S)\<close>
       assumes W:\<open>f\<in>S\<close>
       shows \<open>domain(f)\<subseteq>domain(\<Union>S)\<close>
       oops
     ```
     This theorem states that any function in a set has its domain included in the domain of the union. It was left with `oops` despite being a standard consequence of subset monotonicity of domain in ZF (`f \<in> S \<Longrightarrow> f \<subseteq> \<Union>S \<Longrightarrow> domain(f) \<subseteq> domain(\<Union>S)`).

2. `better.thy`:
   - `theorem pairone` (`\<forall>x. \<forall>y. \<exists>!p. \<forall>z. z \<in> p \<longleftrightarrow> z = x \<or> z = y`) ends with `oops`.
   - `Ind_def` refers to `0` and `succ(y)`, but constants `0` and `succ` are not declared or axiomatized in `better.thy`.

3. `additional.thy`:
   - Contains exploratory development (`addg2fun`, `mychoice`, `kjhg`, `plus`) left with `oops` and commented-out `sorry` blocks.

4. `newzfc.thy`:
   - Re-axiomatizes `elts :: "V \<Rightarrow> V set"` when importing `ZFC_in_HOL.ZFC_in_HOL`, creating redundant or conflicting definitions with Paulson's `V` cumulative hierarchy.
   - `theorem t2 : \<open>elts 0 = elts 0\<close>` is left as `oops`.

## Actionable Solutions
1. Complete `domuncomp` in `recursion.thy` using Isabelle/ZF foundation lemmas `Union_upper` and `domain_mono`.
2. In `better.thy`, either prove `pairone` from `axpair` and `subst` or explicitly axiomatize equality uniqueness, and declare `0` and `succ` primitives.
3. Clean up exploratory proofs in `additional.thy`, discharging `addg2fun` or isolating scratch work.
4. Align `newzfc.thy` with `ZFC_in_HOL` definitions instead of re-axiomatizing primitive symbols on type `V`.
