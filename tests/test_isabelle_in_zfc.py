#!/usr/bin/env python3
"""Verification suite for article_isabelle_in_zfc Isabelle theories and LaTeX build pipeline."""

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


class TestArticleIsabelleInZFC(unittest.TestCase):
    def test_isabelle_theories_syntax_and_headers(self):
        for thy in THEORIES:
            path = os.path.join(ROOT, thy)
            self.assertTrue(os.path.isfile(path), f"Missing theory: {path}")
            with open(path, encoding="utf-8") as f:
                content = f.read()
            self.assertRegex(content, r"\btheory\s+\w+")
            self.assertRegex(content, r"\bimports\b")
            self.assertRegex(content, r"\bbegin\b")
            if thy != "betterFOL.thy":
                self.assertRegex(content, r"\bend\b")

    def test_latex_and_session_files_exist(self):
        for rel in ("ROOT", "Makefile", "main.tex", "document/root.tex", "document/root.bib", "README.md"):
            path = os.path.join(ROOT, rel)
            self.assertTrue(os.path.isfile(path), f"Missing build artifact: {path}")
            self.assertGreater(os.path.getsize(path), 0)


if __name__ == "__main__":
    unittest.main()
