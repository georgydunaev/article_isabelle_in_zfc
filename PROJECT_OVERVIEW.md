# Project Overview: Embedding Isabelle/Pure and First-Order Set Theory in ZFC (`article_isabelle_in_zfc`)

## 1. Purpose and Scope
`article_isabelle_in_zfc` (`/botworkspace/article_isabelle_in_zfc`) contains Isabelle theories and a LaTeX research article (`main.tex`) developing intuitionistic and classical first-order logic (`my_IFOL.thy`, `betterFOL.thy`), Zermelo-Fraenkel set theory (`newzfc.thy`, `better.thy`, `additional.thy`), Dedekind primitive recursion (`recursion.thy`), and set-theoretic lambda abstractions (`LambdaTypesRecursion.thy`).

## 2. Architecture and Key Files
- [my_IFOL.thy](file:///botworkspace/article_isabelle_in_zfc/my_IFOL.thy) and [betterFOL.thy](file:///botworkspace/article_isabelle_in_zfc/betterFOL.thy) — Minimal intuitionistic and classical first-order logic developments built directly on Isabelle/Pure.
- [newzfc.thy](file:///botworkspace/article_isabelle_in_zfc/newzfc.thy), [better.thy](file:///botworkspace/article_isabelle_in_zfc/better.thy), and [additional.thy](file:///botworkspace/article_isabelle_in_zfc/additional.thy) — Axiomatization of ZFC set theory, ordered pairs, relations, functions, and cardinal/ordinal preliminaries.
- [recursion.thy](file:///botworkspace/article_isabelle_in_zfc/recursion.thy) and [LambdaTypesRecursion.thy](file:///botworkspace/article_isabelle_in_zfc/LambdaTypesRecursion.thy) — Mechanized proof of the primitive recursion theorem over natural numbers in ZF and typed set-theoretic function spaces.
- [main.tex](file:///botworkspace/article_isabelle_in_zfc/main.tex) and `document/` — LaTeX article manuscript.
- [MANUSCRIPT_AND_PROOF_INDEX.md](file:///botworkspace/article_isabelle_in_zfc/MANUSCRIPT_AND_PROOF_INDEX.md) and [PROOF_COMPLETIONS_AND_EXTENSIONS.md](file:///botworkspace/article_isabelle_in_zfc/PROOF_COMPLETIONS_AND_EXTENSIONS.md) — Complete theorem catalog.
- `tests/` — Automated verification test suite.

## 3. Verification
```bash
python3 -m unittest discover -s /botworkspace/article_isabelle_in_zfc/tests -p "test_*.py"
```
