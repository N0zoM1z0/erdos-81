SHELL := /bin/bash
PYTHON ?= .venv/bin/python

.PHONY: check replay audit lean paper references

check: replay lean paper

replay:
	python3 preparations/erdos81_stability_closure/replay.py
	python3 preparations/erdos81_rigidity_addendum/replay.py

audit:
	@test -x "$(PYTHON)" || { \
		echo "Create .venv and install requirements-audit.txt first." >&2; \
		exit 1; \
	}
	$(PYTHON) preparations/erdos81_stability_closure/audit.py
	$(PYTHON) preparations/erdos81_rigidity_addendum/audit.py

lean:
	cd lean && ./check.sh

paper:
	$(MAKE) -C manuscript check

references:
	./scripts/fetch_references.sh
