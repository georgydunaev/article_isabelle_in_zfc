ISABELLE_BIN ?= isabelle

.PHONY: test check build buildold paper clean

test:
	python3 -m unittest discover -s tests -p 'test_*.py'

check: test

paper:
	@if command -v pdflatex >/dev/null 2>&1; then \
		pdflatex -interaction=nonstopmode main.tex; \
		if command -v bibtex >/dev/null 2>&1; then bibtex main || true; fi; \
		pdflatex -interaction=nonstopmode main.tex; \
		pdflatex -interaction=nonstopmode main.tex; \
	elif command -v latexmk >/dev/null 2>&1; then \
		latexmk -pdf main.tex; \
	else \
		echo "Neither pdflatex nor latexmk found; skipping PDF compilation"; \
	fi

clean:
	rm -f main.aux main.log main.bbl main.blg main.out main.toc main.pdf

build:
	@if command -v $(ISABELLE_BIN) >/dev/null 2>&1; then \
		$(ISABELLE_BIN) build -o browser_info -o document=pdf -d . Recursion-Addition; \
	elif [ -x /home/user/Downloads/Isabelle2020/bin/isabelle ]; then \
		/home/user/Downloads/Isabelle2020/bin/isabelle build -o browser_info -o document=pdf -d . Recursion-Addition; \
	else \
		echo "Isabelle executable not found (checked $(ISABELLE_BIN) and /home/user/Downloads/Isabelle2020/bin/isabelle)"; \
		exit 1; \
	fi

buildold:
	/home/user/Downloads/Isabelle2019/bin/isabelle build -o browser_info -o document=pdf -d . Recursion-Addition



