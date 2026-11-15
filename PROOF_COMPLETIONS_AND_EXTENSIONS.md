# Proof Completions and Mathematical Extensions: article_isabelle_in_zfc

## 1. Overview of Completed Proofs and Companion Modules

This document details the Phase 2 completions for `article_isabelle_in_zfc`, addressing the open questions and unmechanized manuscript sections identified in [MANUSCRIPT_AND_PROOF_INDEX.md](file:///botworkspace/article_isabelle_in_zfc/MANUSCRIPT_AND_PROOF_INDEX.md):

1. **Mechanization of Section 3 of [main.tex](file:///botworkspace/article_isabelle_in_zfc/main.tex#L103-L126) in [LambdaTypesRecursion.thy](file:///botworkspace/article_isabelle_in_zfc/LambdaTypesRecursion.thy)**:
   - Section 3 of `main.tex` (*"Implementation of simply typed $\lambda$-calculus"*) defines the cumulative hierarchy of simple types by primitive recursion on $\mathbb{N}$:
     $$f(0) = \mathrm{Var}, \qquad f(n+1) = f(n) \cup W(f(n)), \qquad \mathrm{Types} = \bigcup_{n \in \mathbb{N}} f(n).$$
   - In [LambdaTypesRecursion.thy](file:///botworkspace/article_isabelle_in_zfc/LambdaTypesRecursion.thy), we import `recursion` and instantiate `recursionthm` on the power-set carrier $\mathcal{P}(U)$ with step relation `type_step_rel(U, W)`, proving:
     - `Lemma type_step_rel_fun`: $\mathrm{type\_step\_rel}(U, W) \in (\mathcal{P}(U) \times \mathrm{nat}) \to \mathcal{P}(U)$ whenever $W \in \mathcal{P}(U) \to \mathcal{P}(U)$.
     - `Theorem simple_types_hierarchy_exists`: Constructively establishes the existence of $f \in \mathrm{nat} \to \mathcal{P}(U)$ satisfying $f\text{`}0 = \mathrm{Var}$ and $\forall n \in \mathrm{nat}.\,f\text{`}\mathrm{succ}(n) = (f\text{`}n) \cup (W\text{`}(f\text{`}n))$.
     - `Lemma SimpleTypes_base_subset`: Verifies that $\mathrm{Var} \subseteq \mathrm{SimpleTypes}(f, \mathrm{nat})$.

2. **Object-Level Hilbert Self-Implication in [betterFOL.thy](file:///botworkspace/article_isabelle_in_zfc/betterFOL.thy#L66-L68)**:
   - Added `theorem imp_refl: "P \<longrightarrow> P"` proved purely from the Frege-Lukasiewicz Hilbert axioms `a1` ($A \longrightarrow (B \longrightarrow A)$), `a2` ($(A \longrightarrow (B \longrightarrow C)) \longrightarrow ((A \longrightarrow B) \longrightarrow (A \longrightarrow C))$), and Modus Ponens `mp` via the combinatory $S K K$ proof term `mp [OF mp [OF a2 a1] a1]`.

3. **Resolution Analysis of Auxiliary Scratchpads (`additional.thy` and `newzfc.thy`)**:
   - In [additional.thy](file:///botworkspace/article_isabelle_in_zfc/additional.thy), `lemma1` ($\forall x.\,(\exists y.\,\langle x, y \rangle \in f) \longrightarrow \exists u \in f.\,\exists c \in u.\,x \in c$) is already proved completely without `sorry` in [recursion.thy](file:///botworkspace/article_isabelle_in_zfc/recursion.thy) as `theorem sinup` (using `upairI1` and `upairI2` on Kuratowski pairs $\langle x, y \rangle = \{\{x\}, \{x, y\}\}$).
   - `mychoice` in `additional.thy` (line 221) states the full Axiom of Choice over arbitrary non-empty set families without importing `ZFC`; in `Isabelle/ZF`, `recursion.thy` completely avoids the Axiom of Choice by proving `partcomp_uniq` and `partcomp_ex` deterministically by mathematical induction on $\mathrm{nat}$.
