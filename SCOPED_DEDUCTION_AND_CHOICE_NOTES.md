# Scoped Deduction Theorem and Constructive Choice in Isabelle/ZF

<!--
  Provenance Header:
  Source files: /botworkspace/article_isabelle_in_zfc/betterFOL.thy, /botworkspace/article_isabelle_in_zfc/additional.thy, /botworkspace/article_isabelle_in_zfc/ScopedDeductionAndChoice.thy
  Generator: Cross-System Set Theory Bridge Specialist
-->

## 1. Resolution of `theorem Ded` in `betterFOL.thy`

In [betterFOL.thy](file:///botworkspace/article_isabelle_in_zfc/betterFOL.thy#L69-L70), the meta-implication form of the Deduction Theorem:
```isabelle
theorem Ded: "(P \<Longrightarrow> Q) \<Longrightarrow> P \<longrightarrow> Q"
  oops
```
cannot be discharged directly inside `betterFOL.thy` for two reasons:
1. **Absence of Internal Derivation Reflection in `Pure`**: In a Hilbert calculus axiomatized over `Isabelle/Pure` via `mp`, `a1`, and `a2`, the judgment `P \<Longrightarrow> Q` is a meta-level implication of the logical framework rather than an inductive object-level derivation tree.
2. **Unconstrained Universal Generalization (`Gen`)**: In first-order Hilbert systems, if universal generalization (`P \<Longrightarrow> \<forall>x. P`) is applied to open assumptions without tracking free variables in the assumption context $\Gamma$, the deduction theorem fails on open formulas such as $P(x) \vdash \forall x.\, P(x)$.

### Solution in `ScopedDeductionAndChoice.thy`

In [ScopedDeductionAndChoice.thy](file:///botworkspace/article_isabelle_in_zfc/ScopedDeductionAndChoice.thy#L13-L234), we internalize Hilbert derivations over an object formula carrier `Fm` and implication operator `ImpOp(ImpGraph, p, q)` via the inductive intersection closure predicate `PrfCtx(Fm, ImpGraph, Gamma, q)`:
- `ClosedUnderHilbert(Fm, ImpGraph, Gamma, D)` states that $D \subseteq \mathrm{Fm}$ contains the assumption context $\Gamma$, all instances of the Frege-Lukasiewicz axioms $a_1 : a \to (b \to a)$ and $a_2 : (a \to (b \to c)) \to ((a \to b) \to (a \to c))$, and is closed under Modus Ponens (`mp`) and context-scoped rules where any quantified variable $v$ satisfies $v \notin \mathrm{FV}(\Gamma)$.
- We prove `PrfCtx_imp_refl` ($\Gamma \vdash p \to p$) via the $S K K$ combinatory derivation and prove the **Scoped Deduction Theorem** (`theorem Ded_scoped`) unconditionally without `oops`:
  $$\mathrm{PrfCtx}(\mathrm{Fm}, \mathrm{ImpGraph}, \mathrm{cons}(p, \Gamma), q) \Longrightarrow \mathrm{PrfCtx}(\mathrm{Fm}, \mathrm{ImpGraph}, \Gamma, \mathrm{ImpOp}(\mathrm{ImpGraph}, p, q)).$$
  The proof constructs the relativized deductively closed carrier $D_{\mathrm{ext}} = \{x \in \mathrm{Fm} \mid \mathrm{ImpOp}(\mathrm{ImpGraph}, p, x) \in D\}$ for any Hilbert-closed $D \supseteq \Gamma$ and verifies that $D_{\mathrm{ext}}$ contains $\mathrm{cons}(p, \Gamma)$ and is closed under $a_1$, $a_2$, and Modus Ponens.

---

## 2. Functional Graph Extension and Unique Graph Characterizations (`addg2fun`, `kjhg`, `kjhg_fun`)

In [additional.thy](file:///botworkspace/article_isabelle_in_zfc/additional.thy#L68-L87), `addg2fun` proves `function(add_g2)` for a concrete successor graph on $(\mathrm{nat} \times \mathrm{nat}) \times \mathrm{nat}$, while lines 377-385 contain commented-out exploratory statements `kjhg` and `kjhg_fun`.

In [ScopedDeductionAndChoice.thy](file:///botworkspace/article_isabelle_in_zfc/ScopedDeductionAndChoice.thy#L237-L316), we prove the general theorems:
1. **`fun_extend_fresh_pair`**: Extending any functional graph `f` (`function(f)`) by a pair `\langle a, b \rangle` with fresh domain key `a \<notin> domain(f)` preserves functionality: `function(cons(\<langle>a, b\<rangle>, f))`.
2. **`fun_space_extend_fresh`**: If `f \<in> A \<rightarrow> B`, `a \<notin> A`, and `b \<in> B`, then `cons(\<langle>a, b\<rangle>, f) \<in> cons(a, A) \<rightarrow> B`.
3. **`kjhg_unique_rel_in_Pi`**: If `\<forall>x\<in>A. \<exists>!y. y \<in> B(x) \<and> P(x, y)`, then the comprehension graph `{p \<in> Sigma(A, B). P(fst(p), snd(p))}` belongs to `Pi(A, B)`.
4. **`kjhg_fun_characterization`**: If `f \<subseteq> A \<times> B` and `\<forall>x\<in>A. \<exists>!y. y \<in> B \<and> \<langle>x, y\<rangle> \<in> f`, then `f \<in> A \<rightarrow> B`.

---

## 3. Constructive Selector Choice vs. Axiom of Choice (`mychoice`)

In [additional.thy](file:///botworkspace/article_isabelle_in_zfc/additional.thy#L220-L229), `mychoice` states the full Axiom of Choice (`\<forall>x\<in>A. \<exists>y. y \<in> B(x) \<Longrightarrow> \<exists>f. f \<in> Pi(A, B)`), which is independent of pure `ZF`.

In [ScopedDeductionAndChoice.thy](file:///botworkspace/article_isabelle_in_zfc/ScopedDeductionAndChoice.thy#L319-L347), we establish the two constructive choice principles provable in pure `Isabelle/ZF`:
1. **`mychoice_canonical_selector` and `mychoice_selector_exists`**: Whenever a family $B$ over $A$ admits a definable witness selector $\mathrm{sel}(x) \in B(x)$ for all $x \in A$ (such as the least ordinal in $B(x)$ or a recursive step value), the lambda abstraction $(\lambda x \in A.\, \mathrm{sel}(x))$ belongs to $\Pi(A, B)$.
2. **`mychoice_unique_witness`**: Whenever each fiber $B(x)$ has a unique element ($\forall x \in A.\, \exists! y.\, y \in B(x)$), $\Sigma(A, B) \in \Pi(A, B)$ provides the canonical choice function in pure ZF without invoking the Axiom of Choice.
