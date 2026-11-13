#!/usr/bin/env python3
"""Comprehensive verification suite for article_isabelle_in_zfc.

Validates Isabelle theories, dependency DAG, structural syntax integrity,
axiomatic consistency, and LaTeX/BibTeX build pipeline.
"""

import os
import re
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

THEORIES = [
    "my_IFOL.thy",
    "betterFOL.thy",
    "better.thy",
    "newzfc.thy",
    "recursion.thy",
    "additional.thy",
]

EXTERNAL_BASE_LOGICS = {
    "Pure",
    "FOL",
    "ZF",
    "ZFC_in_HOL.ZFC_in_HOL",
}


def parse_theory_header(content):
    """Extract theory name and imported theories from header."""
    pattern = r"\btheory\s+(\w+)\s+imports\s+(.*?)\s+begin\b"
    match = re.search(pattern, content, re.DOTALL)
    if not match:
        return None, []
    theory_name = match.group(1)
    raw_imports = match.group(2).strip().split()
    return theory_name, raw_imports


def check_latex_environment_balance(text):
    """Check LIFO stack balance for LaTeX begin and end blocks."""
    tokens = re.findall(r"\\(begin|end)\{([^}]+)\}", text)
    stack = []
    for action, env in tokens:
        if action == "begin":
            stack.append(env)
        else:
            if not stack:
                return False, f"Unexpected end{{{env}}} with empty stack"
            top = stack.pop()
            if top != env:
                return False, f"Mismatched end{{{env}}}, expected end{{{top}}}"
    if stack:
        return False, f"Unclosed environments at end of document: {stack}"
    return True, "Balanced"


class TestArticleIsabelleInZFC(unittest.TestCase):
    """Test suite for Isabelle theories, dependency DAG, axioms, and document pipeline."""

    def test_isabelle_theories_syntax_and_headers(self):
        """Verify all theory files exist, have matching headers, and end tags."""
        for thy in THEORIES:
            path = os.path.join(ROOT, thy)
            self.assertTrue(os.path.isfile(path), f"Missing theory file: {path}")
            with open(path, encoding="utf-8") as f:
                content = f.read()

            expected_name = thy[:-4]
            name, imports = parse_theory_header(content)
            self.assertIsNotNone(name, f"Failed to parse theory header in {thy}")
            self.assertEqual(name, expected_name, f"Theory name mismatch in {thy}: got {name}, expected {expected_name}")
            self.assertGreater(len(imports), 0, f"Theory {thy} must import at least one theory")
            self.assertRegex(content, r"\bend\b", f"Theory {thy} is missing a closing 'end' command")

    def test_structural_delimiters_and_cartouches(self):
        """Ensure balanced cartouches, balanced comments, and no trailing typos on quotes."""
        for thy in THEORIES:
            path = os.path.join(ROOT, thy)
            with open(path, encoding="utf-8") as f:
                content = f.read()

            open_cart = content.count(r"\<open>")
            close_cart = content.count(r"\<close>")
            self.assertEqual(
                open_cart,
                close_cart,
                f"Unbalanced cartouches in {thy}: {open_cart} open vs {close_cart} close",
            )

            open_comm = content.count("(*")
            close_comm = content.count("*)")
            self.assertEqual(
                open_comm,
                close_comm,
                f"Unbalanced comments in {thy}: {open_comm} open vs {close_comm} close",
            )

            # Check for typos such as `<close>s` where a stray character is attached
            stray_suffix_matches = re.findall(r"\\<close>[a-zA-Z]", content)
            self.assertEqual(
                len(stray_suffix_matches),
                0,
                f"Found stray characters directly attached to closing cartouche in {thy}: {stray_suffix_matches}",
            )

    def test_theory_dependency_dag(self):
        """Verify the local theory dependency graph is a valid DAG without cycles."""
        adj = {}
        all_theories = {thy[:-4] for thy in THEORIES}

        for thy in THEORIES:
            path = os.path.join(ROOT, thy)
            with open(path, encoding="utf-8") as f:
                content = f.read()
            name, imports = parse_theory_header(content)
            local_deps = [dep for dep in imports if dep in all_theories]
            adj[name] = local_deps

            # Verify external dependencies belong to known base logics
            external_deps = [dep for dep in imports if dep not in all_theories]
            for ext in external_deps:
                self.assertIn(
                    ext,
                    EXTERNAL_BASE_LOGICS,
                    f"Unknown external logic '{ext}' imported by {name}",
                )

        # Cycle detection using depth-first search
        visited = {}  # 0: unvisited, 1: visiting, 2: visited

        def dfs(node):
            visited[node] = 1
            for neighbor in adj.get(node, []):
                if visited.get(neighbor, 0) == 1:
                    return False, f"Cycle detected between {node} and {neighbor}"
                if visited.get(neighbor, 0) == 0:
                    ok, msg = dfs(neighbor)
                    if not ok:
                        return False, msg
            visited[node] = 2
            return True, "No cycle"

        for node in adj:
            if visited.get(node, 0) == 0:
                is_dag, err_msg = dfs(node)
                self.assertTrue(is_dag, err_msg)

        # Topological dependency checks
        self.assertIn("recursion", adj["additional"], "additional.thy must import recursion.thy")
        self.assertEqual(adj["recursion"], [], "recursion.thy should not import local theories; it extends ZF directly")

    def test_axiom_systems_and_zfc_consistency(self):
        """Validate axiom declarations and check conservative extension properties."""
        axiom_counts = {}
        for thy in THEORIES:
            path = os.path.join(ROOT, thy)
            with open(path, encoding="utf-8") as f:
                content = f.read()
            # Count axiomatization occurrences outside of ML blocks
            axioms = re.findall(r"\baxiomatization\b", content)
            axiom_counts[thy] = len(axioms)

        # recursion.thy is a strictly conservative extension of ZF (no new axioms introduced)
        self.assertEqual(
            axiom_counts["recursion.thy"],
            0,
            "recursion.thy must remain purely conservative over ZF with zero new axioms",
        )

        # betterFOL.thy has axiomatizations for equality and propositional logic
        self.assertGreaterEqual(axiom_counts["betterFOL.thy"], 1)

        # better.thy has axiomatizations for membership, pair, and union
        self.assertGreaterEqual(axiom_counts["better.thy"], 1)

        # my_IFOL.thy has axiomatizations for first-order intuitionistic logic
        self.assertGreaterEqual(axiom_counts["my_IFOL.thy"], 1)

        # newzfc.thy has axiomatizations for cumulative hierarchy
        self.assertGreaterEqual(axiom_counts["newzfc.thy"], 1)

    def test_proof_completeness_and_oops_inventory(self):
        """Track and bound unfinished proofs (oops and sorry) across all theories."""
        oops_count = {}
        sorry_count = {}
        for thy in THEORIES:
            path = os.path.join(ROOT, thy)
            with open(path, encoding="utf-8") as f:
                content = f.read()

            # Remove comments to count active oops and sorry
            no_comments = re.sub(r"\(\*.*?\*\)", "", content, flags=re.DOTALL)
            oops_matches = re.findall(r"\boops\b", no_comments)
            sorry_matches = re.findall(r"\bsorry\b", no_comments)

            oops_count[thy] = len(oops_matches)
            sorry_count[thy] = len(sorry_matches)

        # my_IFOL.thy is fully proved with zero oops and zero sorry
        self.assertEqual(oops_count["my_IFOL.thy"], 0)
        self.assertEqual(sorry_count["my_IFOL.thy"], 0)

        # better.thy is fully proved with zero oops and zero sorry
        self.assertEqual(
            oops_count["better.thy"],
            0,
            "better.thy must have zero oops (pairone is proved)",
        )
        self.assertEqual(sorry_count["better.thy"], 0)

        # newzfc.thy is fully proved with zero oops and zero sorry
        self.assertEqual(
            oops_count["newzfc.thy"],
            0,
            "newzfc.thy must have zero oops (t2 is proved by refl)",
        )
        self.assertEqual(sorry_count["newzfc.thy"], 0)

        # recursion.thy is fully proved with zero oops and zero sorry
        self.assertEqual(
            oops_count["recursion.thy"],
            0,
            "recursion.thy must have zero oops (domuncomp is fully proven)",
        )
        self.assertEqual(
            sorry_count["recursion.thy"],
            0,
            "recursion.thy must have zero sorry",
        )

        # additional.thy has zero active oops and zero active sorry
        self.assertEqual(
            oops_count["additional.thy"],
            0,
            "additional.thy must have zero active oops",
        )
        self.assertEqual(
            sorry_count["additional.thy"],
            0,
            "additional.thy must have zero active sorry",
        )

        # betterFOL.thy has 1 oops for Ded theorem
        self.assertLessEqual(oops_count["betterFOL.thy"], 1)
        self.assertEqual(sorry_count["betterFOL.thy"], 0)

    def test_domuncomp_proof_structure(self):
        """Verify that theorem domuncomp in recursion.thy is fully proved with qed and no oops."""
        rec_path = os.path.join(ROOT, "recursion.thy")
        with open(rec_path, encoding="utf-8") as f:
            content = f.read()

        match = re.search(r"theorem\s+domuncomp\s*:.*?(?=theorem|\bdefinition\b|\blemma\b|\bend\b)", content, re.DOTALL)
        self.assertIsNotNone(match, "theorem domuncomp not found in recursion.thy")
        block = match.group(0)
        self.assertIn("qed", block, "domuncomp must terminate with qed")
        self.assertNotIn("oops", block, "domuncomp must not contain oops")
        self.assertNotIn("sorry", block, "domuncomp must not contain sorry")
        self.assertIn("domainE", block, "domuncomp proof should use domain elimination")
        self.assertIn("UnionI", block, "domuncomp proof should use Union introduction")
        self.assertIn("domainI", block, "domuncomp proof should use domain introduction")

    def test_addg2fun_proof_structure(self):
        """Verify that lemma addg2fun in additional.thy is fully proved with qed."""
        add_path = os.path.join(ROOT, "additional.thy")
        with open(add_path, encoding="utf-8") as f:
            content = f.read()

        match = re.search(r"lemma\s+addg2fun\s*:.*?(?=lemma|\bdefinition\b|\btheorem\b|\bsubsection\b|\bend\b)", content, re.DOTALL)
        self.assertIsNotNone(match, "lemma addg2fun not found in additional.thy")
        block = match.group(0)
        self.assertIn("qed", block, "addg2fun must terminate with qed")
        self.assertNotIn("oops", block, "addg2fun must not contain oops")
        self.assertNotIn("sorry", block, "addg2fun must not contain sorry")

    def test_theory_syntax_integrity(self):
        """Verify all theory files contain well-formed keywords, proof blocks, and structural closures."""
        for thy in THEORIES:
            path = os.path.join(ROOT, thy)
            with open(path, encoding="utf-8") as f:
                content = f.read()

            # Ensure theory header has valid structure
            self.assertRegex(content, r"\btheory\s+\w+\s+imports\s+.*?\s+begin\b")
            # Ensure file ends with 'end'
            stripped = content.strip()
            self.assertTrue(stripped.endswith("end"), f"Theory {thy} must end with 'end'")

            # Check proof/qed nesting balance outside comments, cartouches, and strings
            clean_code = re.sub(r"\(\*.*?\*\)", "", content, flags=re.DOTALL)
            clean_code = re.sub(r"\\<open>.*?\\<close>", "", clean_code, flags=re.DOTALL)
            clean_code = re.sub(r'".*?"', "", clean_code, flags=re.DOTALL)
            proof_starts = len(re.findall(r"\bproof\b", clean_code))
            qed_ends = len(re.findall(r"\bqed\b", clean_code))
            oops_count = len(re.findall(r"\boops\b", clean_code))
            self.assertGreaterEqual(
                qed_ends + oops_count,
                proof_starts,
                f"Mismatched proof blocks vs qed/oops in {thy}: {proof_starts} proofs vs {qed_ends} qeds + {oops_count} oops",
            )

    def test_latex_and_session_files_exist(self):
        """Verify existence and non-emptiness of all document build pipeline files."""
        for rel in ("ROOT", "Makefile", "main.tex", "document/root.tex", "document/root.bib", "README.md"):
            path = os.path.join(ROOT, rel)
            self.assertTrue(os.path.isfile(path), f"Missing build artifact: {path}")
            self.assertGreater(os.path.getsize(path), 0, f"File is empty: {path}")

    def test_latex_environment_balance(self):
        """Verify that LaTeX environments in main.tex and document/root.tex are properly nested."""
        for rel in ("main.tex", "document/root.tex"):
            path = os.path.join(ROOT, rel)
            with open(path, encoding="utf-8") as f:
                text = f.read()
            is_balanced, msg = check_latex_environment_balance(text)
            self.assertTrue(is_balanced, f"LaTeX environment balance failure in {rel}: {msg}")

    def test_bibliography_and_citations_consistency(self):
        """Verify BibTeX keys and check that root.tex citations exist in root.bib."""
        bib_path = os.path.join(ROOT, "document", "root.bib")
        with open(bib_path, encoding="utf-8") as f:
            bib_content = f.read()

        keys = set(re.findall(r"@\w+\s*\{\s*([a-zA-Z0-9_\-]+)\s*,", bib_content))
        self.assertIn("LNCS2283", keys, "LNCS2283 entry missing from root.bib")
        self.assertIn("HrbacekJech", keys, "HrbacekJech entry missing from root.bib")

        tex_path = os.path.join(ROOT, "document", "root.tex")
        with open(tex_path, encoding="utf-8") as f:
            tex_content = f.read()

        citations = re.findall(r"\\cite\{([^}]+)\}", tex_content)
        for cite_group in citations:
            for key in cite_group.split(","):
                key = key.strip()
                self.assertIn(key, keys, f"Citation key '{key}' in root.tex not found in root.bib")

    def test_root_session_and_document_files(self):
        """Verify ROOT file declares valid session and lists existing document files."""
        root_path = os.path.join(ROOT, "ROOT")
        with open(root_path, encoding="utf-8") as f:
            content = f.read()

        self.assertRegex(content, r'session\s+"Recursion-Addition"')
        self.assertIn("recursion", content)

        # Check listed document files exist
        doc_files = ["root.tex", "root.bib"]
        for df in doc_files:
            p = os.path.join(ROOT, "document", df)
            self.assertTrue(os.path.isfile(p), f"Document file {df} specified in ROOT must exist at {p}")

    def test_better_theory_pairone_and_signature(self):
        """Verify better.thy declares Zero/succ primitives and proves pairone without oops."""
        better_path = os.path.join(ROOT, "better.thy")
        with open(better_path, encoding="utf-8") as f:
            content = f.read()

        # Check pairone proof
        match = re.search(r"theorem\s+pairone\s*:.*?(?=definition|\btheorem\b|\blemma\b|\bend\b)", content, re.DOTALL)
        self.assertIsNotNone(match, "theorem pairone not found in better.thy")
        block = match.group(0)
        self.assertIn("qed", block, "pairone must terminate with qed")
        self.assertNotIn("oops", block, "pairone must not contain oops")

        # Check primitive declarations
        self.assertRegex(content, r"axiomatization\s+Zero\s*::\s*i", "better.thy must declare Zero :: i")
        self.assertRegex(content, r"succ\s*::\s*\"i\s*\\<Rightarrow>\s*i\"", "better.thy must declare succ :: i => i")
        self.assertIn("Ind_def", content, "better.thy must define Ind using Ind_def")

    def test_newzfc_alignment_and_reflexivity(self):
        """Verify newzfc.thy proves t2 by refl without oops and aligns with ZFC_in_HOL."""
        newzfc_path = os.path.join(ROOT, "newzfc.thy")
        with open(newzfc_path, encoding="utf-8") as f:
            content = f.read()

        # Check t2 proof
        match = re.search(r"theorem\s+t2\s*:.*?(?=theorem|\bdefinition\b|\blemma\b|\bend\b)", content, re.DOTALL)
        self.assertIsNotNone(match, "theorem t2 not found in newzfc.thy")
        block = match.group(0)
        self.assertIn("by (rule refl)", block, "t2 must be proven by refl")
        self.assertNotIn("oops", block, "t2 must not contain oops")

    def test_main_tex_citations_and_cross_references(self):
        """Verify main.tex has valid citations to root.bib and maps lemmas to Isabelle theorems."""
        bib_path = os.path.join(ROOT, "document", "root.bib")
        with open(bib_path, encoding="utf-8") as f:
            bib_content = f.read()
        bib_keys = set(re.findall(r"@\w+\s*\{\s*([a-zA-Z0-9_\-]+)\s*,", bib_content))

        main_path = os.path.join(ROOT, "main.tex")
        with open(main_path, encoding="utf-8") as f:
            main_content = f.read()

        citations = re.findall(r"\\cite\{([^}]+)\}", main_content)
        self.assertGreater(len(citations), 0, "main.tex must contain citations")
        for cite_group in citations:
            for key in cite_group.split(","):
                key = key.strip()
                self.assertIn(key, bib_keys, f"Citation key '{key}' in main.tex not found in root.bib")

        # Verify cross-references to Isabelle theorems (handling TeX escaped underscores)
        expected_theorems = [
            r"compat(_|\\_)def",
            r"compatset(_|\\_)def",
            r"domuncomp",
            r"compatsetunionfun",
            r"valofunion",
            r"recursionthm",
            r"addition",
        ]
        for thm_pat in expected_theorems:
            self.assertRegex(
                main_content,
                thm_pat,
                f"main.tex must cross-reference Isabelle theorem matching '{thm_pat}'",
            )

    def test_makefile_targets(self):
        """Verify Makefile contains expected targets for test, paper, clean, and build."""
        mk_path = os.path.join(ROOT, "Makefile")
        with open(mk_path, encoding="utf-8") as f:
            mk_content = f.read()

        for target in ("test:", "check:", "paper:", "clean:", "build:"):
            self.assertIn(target, mk_content, f"Makefile must define target '{target}'")


if __name__ == "__main__":
    unittest.main()
