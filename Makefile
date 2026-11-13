ISABELLE_BIN ?= isabelle

.PHONY: test check build buildold

test:
	python3 -m unittest discover -s tests -p 'test_*.py'

check: test

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


