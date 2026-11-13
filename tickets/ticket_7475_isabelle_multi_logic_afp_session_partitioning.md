# [ARTICLE_ISABELLE_IN_ZFC] Ticket 7475: Multi-Logic Session Hierarchy and AFP Root Configuration

**Repository:** `article_isabelle_in_zfc`  
**Status:** `OPEN`  
**Created:** `2026-11-13T22:00:00Z`  

## Problem Description
The repository houses formalizations targeting three mutually incompatible Isabelle object logics:

1. **Isabelle/ZF**:
   - `recursion.thy` (imports `ZF`)
   - `additional.thy` (imports `recursion`)

2. **Isabelle/Pure and FOL**:
   - `my_IFOL.thy` (imports `Pure`)
   - `betterFOL.thy` (imports `Pure`)
   - `better.thy` (imports `FOL`)

3. **Isabelle/HOL (ZFC in HOL)**:
   - `newzfc.thy` (imports `ZFC_in_HOL.ZFC_in_HOL`)

Currently, `ROOT` specifies only:
```isabelle
session "Recursion-Addition" (AFP) = ZF +
  options [timeout = 600]
  theories
    recursion
  document_files
    "root.bib"
    "root.tex"
```
Under Archive of Formal Proofs guidelines, every theory in a submission directory must belong to at least one declared session. Attempting to include `my_IFOL.thy`, `betterFOL.thy`, or `newzfc.thy` inside the `Recursion-Addition` session will fail because their base logic images (`Pure`, `FOL`, `HOL`) differ from `ZF`.

## Actionable Solutions
1. Restructure the `ROOT` file to declare distinct sessions:
   - `session "Recursion-Addition" (AFP) = ZF + theories recursion additional`
   - `session "FOL-Foundations" = Pure + theories my_IFOL betterFOL`
   - `session "ZFC-in-HOL-Extensions" = "ZFC_in_HOL" + theories newzfc`
2. Optionally organize theory files into subdirectories matching their logical foundation:
   - `zf/` for `recursion.thy` and `additional.thy`
   - `fol/` for `my_IFOL.thy`, `betterFOL.thy`, and `better.thy`
   - `hol/` for `newzfc.thy`
3. Document session dependencies clearly in `README.md`.
