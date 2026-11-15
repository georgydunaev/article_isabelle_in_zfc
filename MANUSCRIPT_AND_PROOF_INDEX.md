# Manuscript and Proof Index: article_isabelle_in_zfc

## 1. Repository Overview and Scope

`article_isabelle_in_zfc` contains the formalization and accompanying LaTeX manuscripts for the **Recursion Theorem on Natural Numbers** and arithmetic addition in Zermelo-Fraenkel set theory (`Isabelle/ZF`), together with foundational experiments in custom first-order logic (`my_IFOL.thy`, `betterFOL.thy`) and standalone ZFC axiomatizations (`better.thy`, `newzfc.thy`). The main development mechanizes the proof of the primitive recursion theorem from Karel Hrbacek and Thomas Jech's *Introduction to Set Theory*, establishing that compatible families of partial approximations on $\omega$ (`nat`) have a functional union whose domain is $\omega$, and applying this theorem to construct Peano arithmetic addition.

---

## 2. Inventory of Source Manuscript and Proof Files

| File | Lines | Language / System | Role and Contents |
| :--- | :--- | :--- | :--- |
| `main.tex` | 130 | LaTeX | Standalone research article *"Set-Theoretic Foundations of Mathematics"* by Georgy Dunaev. Presents the definitions and theorems of compatible functions (`compat`), compatible families (`compatset`), domain monotonicity (`domuncomp`), the Compatible Function Union Theorem (`compatsetunionfun`, `valofunion`), the Master Recursion Theorem on $\mathbb{N}$ (`recursionthm`, `recuniq`), arithmetic addition (`addition`), and the inductive construction of simple types (`\Types`) via word formation operators. |
| `document/root.tex` | 34 | LaTeX | Isabelle session document wrapper titled *"Recursion Theorem"* by Georgy Dunaev, configured for `isabelle build` PDF generation with `document/root.bib`. |
| `document/root.bib` | 18 | BibTeX | Bibliography citing Hrbacek & Jech (*Introduction to Set Theory*, 1999) and Paulson, Nipkow & Wenzel (*Isabelle: A Generic Proof Assistant*, LNCS 2283, 2002). |
| `ROOT` | 37 | Isabelle Build | Archive of Formal Proofs (`AFP`) style session definition for session `"Recursion-Addition"` built on top of `ZF`, compiling `recursion.thy` and generating the LaTeX document. |
| `Makefile` | 39 | Make | Build orchestration for LaTeX (`pdflatex` + `bibtex` on `main.tex`), Isabelle session checking, and Python verification tests. |
| `recursion.thy` | 1540 | Isabelle/ZF | **Primary Verified Theory (0 `sorry`, 0 `oops`)**. Imports `ZF`. Proves natural number order and transitivity properties, compatible function pairs and families (`compat`, `compatset`), the Compatible Function Union Theorem (`compatsetunionfun`), domain monotonicity (`domuncomp`), partial computations of length $n$ (`satpc`, `partcomp`), existence and uniqueness of $n$-step approximations (`partcomp_ex`, `partcomp_uniq`), the Master Recursion Theorem (`recursionthm`) and its uniqueness (`recuniq`), and Peano addition (`addition`, `add_zero`, `add_succ`). |
| `additional.thy` | 606 | Isabelle/ZF | Exploratory companion theory importing `ZF`. Contains alternative formulations of addition step functions (`add_g2`, `addg2subpow`, `addg2dom`, `addg2fun`), bounded and unbounded uniqueness quantifiers (`Only1`, `Bonly`, `Bex1`), conditional expressions (`fite`, `ite`, `ite1`, `ite2`), and exploratory Choice/Sigma-domain lemmas (`mychoice`, `basedomsig`, `domsig`, `fuch`, `bfuch`, `mkfun`). |
| `my_IFOL.thy` | 1006 | Isabelle/Pure | Custom intuitionistic first-order logic built directly on `Pure`. Defines type `o` of propositions, equality (`=`), falsehood (`False`), universal quantifier (`All`), derived connectives (`Not`, `&`, `|`, `-->`, `<->`), uniqueness quantifier `Only1` (`?`), unique existence `Ex1` (`?!`), natural deduction rules, and intuitionistic proof automation (`IntPr` / `fast_tac`, `best_tac`). |
| `better.thy` | 148 | Isabelle/Pure | Experimental first-order ZFC axiomatization built on `my_IFOL`. Axiomatizes membership (`mem`), extensionality, unordered pairing (`Pair`, `upair_ax`), union (`Union`, `union_ax`), empty set (`Zero`), infinity (`Ind`, `inf_ax`), and explores defining `Pair` via the uniqueness quantifier `One` (`?`) and dual `Eno` (`?!`). |
| `betterFOL.thy` | 86 | Isabelle/Pure | Minimal Hilbert-style first-order calculus over `Pure` with implication (`-->`), equality (`=`), falsehood (`False`), Modus Ponens (`mp`), and Frege-Lukasiewicz axioms (`a1`, `a2`). |
| `newzfc.thy` | 70 | Isabelle/HOL | Experimental set theory over `HOL` axiomatizing `Collect` comprehension, defining `image`, `Pow`, `inv_into`, and well-founded relations (`wf`), and testing Russell-style comprehension limits (`qwe`, `t1`, `t2`). |
| `tests/test_isabelle_in_zfc.py` | 145 | Python | Automated test suite verifying theory integrity, absence of `sorry`/`oops` in `recursion.thy`, LaTeX-to-Isabelle cross-reference alignment, and BibTeX citation consistency. |

---

## 3. Core Mathematical Results Established

### 3.1 Arithmetic and Ordinal Order on $\omega$ (`recursion.thy` lines 1--185)
- `nat_induct_bound`, `nat_Tr`: Mathematical induction on $n \in \mathrm{nat}$ and transitivity of every natural number ($x \in n \implies x \subseteq n$).
- `nat_transitive`, `nat_xninx`, `nat_asym`, `nat_linord`: Strict membership order on $\mathrm{nat}$ is transitive, irreflexive ($x \notin x$), asymmetric, and trichotomous/linearly ordered (`zeroleq`, `zerolesucc`, `succ_le`, `succ_le2`, `le_succ`).

### 3.2 Compatible Families of Functions (`recursion.thy` lines 186--420, `main.tex` Section 2)
- **Definitions**:
  - `compat(f1, f2)`: $\forall x \in \mathrm{dom}(f_1) \cap \mathrm{dom}(f_2).\,\forall y_1\,y_2.\,\langle x, y_1 \rangle \in f_1 \land \langle x, y_2 \rangle \in f_2 \implies y_1 = y_2$.
  - `compatset(S)`: $\forall f_1 \in S.\,\forall f_2 \in S.\,\mathrm{compat}(f_1, f_2)$.
- **Theorems**:
  - `Theorem compatsetunionfun`: If $\mathrm{compatset}(F)$ and every $f \in F$ is a function (`f : A -> B`), then $\bigcup F$ is a function on $\bigcup_{f \in F} \mathrm{dom}(f)$.
  - `Theorem domuncomp`: For any family $S$ and $f \in S$, $\mathrm{dom}(f) \subseteq \mathrm{dom}(\bigcup S)$ (resolved cleanly without `oops` in `recursion.thy`).
  - `Theorem valofunion`: If $\mathrm{compatset}(F)$, $f \in F$, and $x \in \mathrm{dom}(f)$, then $(\bigcup F)\text{`}x = f\text{`}x$.

### 3.3 The Master Recursion Theorem on $\mathbb{N}$ (`recursion.thy` lines 421--1380, `main.tex` Section 2)
- **Partial Computations (`satpc`, `partcomp`)**:
  - For a target set $A$, base element $a \in A$, and step function $g \in (A \times \mathrm{nat}) \to A$, a partial approximation $t$ satisfies `partcomp(A, a, g, n, t)` when $t \in \mathrm{succ}(n) \to A$, $t\text{`}0 = a$, and $\forall k \in n.\,t\text{`}\mathrm{succ}(k) = g\text{`}\langle t\text{`}k, k \rangle$.
- **Uniqueness and Compatibility of Approximations**:
  - `partcomp_compat`: Any two partial approximations $t_1$ (up to $n_1$) and $t_2$ (up to $n_2$) are compatible (`compat(t1, t2)`), proved by induction on $\mathrm{nat}$ using trichotomy.
  - `partcomp_ex`: For every $n \in \mathrm{nat}$, there exists a partial approximation $t$ on $\mathrm{succ}(n)$ (constructed by extending the approximation on $n$ with the single ordered pair $\langle \mathrm{succ}(n), g\text{`}\langle t\text{`}n, n \rangle \rangle$).
- **Master Recursion Theorem (`recursionthm` and `recuniq`)**:
  - Taking $F = \{t \in \mathcal{P}(\mathrm{nat} \times A) : \exists n \in \mathrm{nat}.\,\mathrm{partcomp}(A, a, g, n, t)\}$ and $f = \bigcup F$, `recursionthm` proves that $f \in \mathrm{nat} \to A$, $f\text{`}0 = a$, and $\forall n \in \mathrm{nat}.\,f\text{`}\mathrm{succ}(n) = g\text{`}\langle f\text{`}n, n \rangle$.
  - `recuniq` proves that any two functions $f_1, f_2 \in \mathrm{nat} \to A$ satisfying the recursion equations are equal ($f_1 = f_2$).

### 3.4 Peano Addition via Set-Theoretic Recursion (`recursion.thy` lines 1381--1540)
- Applying `recursionthm` with $A = \mathrm{nat} \to \mathrm{nat}$, base function $\mathrm{id}(\mathrm{nat})$, and step combinator composing with successor yields the addition operation (`addition`), proving $a + 0 = a$ and $a + \mathrm{succ}(n) = \mathrm{succ}(a + n)$ for all $a, n \in \mathrm{nat}$.

---

## 4. Open Questions and Unresolved Proof Obligations

1. **Discharging Exploratory `sorry` and `oops` Steps in `additional.thy` and `betterFOL.thy` (Ticket 7474)**:
   - While the flagship theory `recursion.thy` and `my_IFOL.thy` are 100% free of `sorry` and `oops`, the auxiliary scratchpad `additional.thy` contains 4 `sorry` steps (lines 6, 598, 601, 604 in `lemma1` and `ite2`) and 5 abandoned `oops` blocks (lines 10, 228, 380, 385, 390, including an unproved Axiom of Choice statement `mychoice` at line 221 without importing `ZFC`).
   - In `betterFOL.thy` (line 67), the object-level self-implication theorem `Ded` ($p \longrightarrow p$, derivable from Frege-Lukasiewicz axioms `a1` and `a2` via the $S K K$ combinator pattern) is terminated with `oops`.
2. **Inconsistency Demonstration in `newzfc.thy`**:
   - `newzfc.thy` intentionally axiomatizes unrestricted comprehension `Collect` (line 4) and an arbitrary set `qwe` (line 65) to illustrate Russell's paradox (`t1`, `t2`) when separation is replaced by naive comprehension. Isolating this file clearly as a negative counterexample session in `ROOT` (Ticket 7475) prevents confusion with consistent `Isabelle/ZF` theories.
3. **Mechanizing Section 3 of `main.tex` (Simply Typed $\lambda$-Calculus Syntax via Recursion)**:
   - Section 3 of `main.tex` (lines 103--126) defines the alphabet $\mathcal{A} = \mathrm{Var} \sqcup \mathrm{Const} \sqcup \mathrm{Spec}$, the word formation operator $W(X, c)$, and the recursive family $f(0) = \mathrm{Var}$, $f(n+1) = f(n) \cup W(f(n))[\mathrm{Const}]$ whose union is the set of simple types $\mathrm{Types} = \bigcup_{n \in \mathbb{N}} f(n)$. Formalizing this instantiation of `recursionthm` inside `recursion.thy` is the natural next step connecting the Recursion Theorem to formal syntax of type theories.
