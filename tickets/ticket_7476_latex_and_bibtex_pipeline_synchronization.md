# [ARTICLE_ISABELLE_IN_ZFC] Ticket 7476: LaTeX Document Pipeline and Bibliography Synchronization

**Repository:** `article_isabelle_in_zfc`  
**Status:** `RESOLVED`  
**Created:** `2026-11-13T22:00:00Z`  
**Resolved:** `2026-11-13T23:51:00Z`  

## Problem Description
The document generation pipeline contains discrepancies between the TeX sources, Isabelle document session configuration, and standalone paper:

1. **BibTeX Integration in Isabelle Session**:
   - `ROOT` previously had `"root.bib"` commented out, causing BibTeX failure when `document/root.tex` invoked `\bibliography{root}`.
   - `document/root.bib` contained only `LNCS2283`, omitting the primary literature source cited in the abstract: Karel Hrbacek and Thomas Jech, "Introduction to Set Theory".
   - `document/root.tex` had no citation to `root.bib` entries, causing BibTeX warning on missing citations.

2. **Standalone Paper (`main.tex`) Synchronization**:
   - `main.tex` presents "Set-Theoretic Foundations of Mathematics" covering compatible function unions and simple type theory, but does not cite literature or cross-reference the verified Isabelle theorem identifiers in `recursion.thy` (e.g. `uncompat`, `valofunion`, `steprel`).
   - `main.tex` lacks a bibliography section and automated build target in `Makefile`.

3. **Build Toolchain Portability (`Makefile`)**:
   - Hardcoded paths to `/home/user/Downloads/Isabelle2020/bin/isabelle` prevented portable execution on machines where `isabelle` is located in the standard PATH or custom location.

## Actionable Solutions
1. Maintain synchronization between `ROOT` document_files and `document/root.bib`, ensuring all cited bibliography entries (`HrbacekJech`, `LNCS2283`) exist in `root.bib`.
2. Add theorem name cross-reference notes in `main.tex` mapping mathematical lemmas directly to Isabelle theorem names (`uncompat`, `valofunion`, `recursion_theorem`).
3. Add a target in `Makefile` for compiling `main.tex` to PDF when `pdflatex` or `latexmk` is present, while preserving configurable `ISABELLE_BIN ?= isabelle`.

## Resolution Details
1. **BibTeX Synchronization**:
   - Cleaned up `document/root.bib` with valid BibTeX syntax (braced publishers and series), eliminating BibTeX string macro warnings.
   - Updated `document/root.tex` to cite both `HrbacekJech` and `LNCS2283`, ensuring full reference resolution.
2. **Standalone Paper (`main.tex`)**:
   - Added abstract and literature citations (`HrbacekJech`, `LNCS2283`).
   - Added explicit cross-references mapping mathematical concepts to verified Isabelle theorems in `recursion.thy` and `additional.thy`: `compat_def`, `compatset_def`, `sinup`, `lemma1`, `lemma2`, `domuncomp`, `compatsetunionfun`, `valofunion`, `recursionthm`, `recuniq`, and `addition`.
   - Added bibliography directive pointing to `document/root.bib`.
3. **Build Toolchain and Makefile**:
   - Added `paper` target to compile `main.tex` to PDF using `pdflatex` and `bibtex` (or `latexmk`), and `clean` target to remove intermediate auxiliary files.
   - Preserved configurable `ISABELLE_BIN ?= isabelle`.
   - Updated `.gitignore` to prevent tracking of intermediate auxiliary files and PDFs, respecting the rule on immutability of compiled binaries and PDFs.
4. **Verification**:
   - Verified that `main.tex` compiles with `pdflatex` and `bibtex` with zero errors.
   - Expanded unit tests in `tests/test_isabelle_in_zfc.py` covering citations, cross-references, and Makefile targets.
   - 100% pass rate on test suite.
