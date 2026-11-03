PROJECT_DIR := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
PROJECT_FILE := $(PROJECT_DIR)_RocqProject
PROJECT_NAMESPACE ?=
COQMAKEFILE ?= $(PROJECT_DIR)CoqMakefile
DOC_DIR ?= $(PROJECT_DIR)doc
ALECTRYON_DIR ?= $(PROJECT_DIR)alectryon
ALECTRYON_STYLE ?= $(PROJECT_DIR)alectryon-style.css
ALECTRYON_PROOF_TOGGLE ?= $(PROJECT_DIR)alectryon-proof-toggle.js
ALECTRYON ?= $(shell command -v alectryon 2>/dev/null || command -v "$(HOME)/Library/Python/3.9/bin/alectryon" 2>/dev/null || printf alectryon)
ALECTRYON_COQ_DRIVER ?= coqc_time
SITE_DIR ?= $(PROJECT_DIR)site

.PHONY: all coq check pico check-pico doc doc-clean alectryon-doc alectryon-clean site site-clean clean

all: coq

$(COQMAKEFILE): $(PROJECT_FILE)
	cd "$(PROJECT_DIR)" && coq_makefile -f _RocqProject -o CoqMakefile

coq: $(COQMAKEFILE)
	$(MAKE) -C "$(PROJECT_DIR)" -f CoqMakefile

check: coq
	python3 "$(PROJECT_DIR)scripts/check-no-axioms-admits.py" "$(PROJECT_DIR)"
	python3 "$(PROJECT_DIR)scripts/check-public-assumptions.py" "$(PROJECT_DIR)"

pico:
	$(MAKE) -C "$(PROJECT_DIR)PICO"

check-pico:
	$(MAKE) -C "$(PROJECT_DIR)PICO" check

doc:
	mkdir -p "$(DOC_DIR)"
	cd "$(PROJECT_DIR)" && awk '/[.]v$$/ { print }' _RocqProject | \
	  xargs rocq doc --html --toc -Q . "$(PROJECT_NAMESPACE)" -d "$(DOC_DIR)"

doc-clean:
	rm -rf "$(DOC_DIR)"

alectryon-doc: coq
	@command -v "$(ALECTRYON)" >/dev/null 2>&1 || { \
	  echo "alectryon not found. Install it with opam or pip, then rerun: make alectryon-doc"; \
	  exit 127; \
	}
	mkdir -p "$(ALECTRYON_DIR)"
	cp "$(ALECTRYON_STYLE)" "$(ALECTRYON_DIR)/project-alectryon.css"
	cp "$(ALECTRYON_PROOF_TOGGLE)" "$(ALECTRYON_DIR)/project-proof-toggle.js"
	printf '%s\n' \
	  '<!doctype html>' \
	  '<html lang="en">' \
	  '<head>' \
	  '  <meta charset="utf-8">' \
	  '  <title>GAIT (Rocq) — Alectryon Docs</title>' \
	  '  <link href="project-alectryon.css" rel="stylesheet">' \
	  '  <style>' \
	  '    body { max-width: 980px; margin: 3rem auto; padding: 0 1.5rem; font-family: system-ui, sans-serif; line-height: 1.5; }' \
	  '    h1 { margin-bottom: 0.25rem; }' \
	  '    h2 { margin-top: 2rem; border-bottom: 1px solid #ddd; padding-bottom: 0.25rem; }' \
	  '    ul { padding-left: 1.4rem; }' \
	  '    li { margin: 0.35rem 0; }' \
	  '    a { text-decoration: none; }' \
	  '    a:hover { text-decoration: underline; }' \
	  '  </style>' \
	  '</head>' \
	  '<body>' \
	  '  <h1>GAIT (Rocq) — Alectryon Docs</h1>' \
	  '  <p>Rendered Rocq sources of the GAIT mechanization, in build order.</p>' \
	  '  <ul>' \
	  > "$(ALECTRYON_DIR)/index.html"
	cd "$(PROJECT_DIR)" && awk '/[.]v$$/ { m = $$0; sub(/[.]v$$/, "", m); gsub("/", ".", m); printf "    <li><a href=\"%s.html\">%s</a></li>\n", m, m }' _RocqProject >> "$(ALECTRYON_DIR)/index.html"
	printf '%s\n' '  </ul>' '</body>' '</html>' >> "$(ALECTRYON_DIR)/index.html"
	set -e; cd "$(PROJECT_DIR)" && awk '/[.]v$$/ { print }' _RocqProject | \
	  while IFS= read -r f; do \
	    out="$$(printf '%s\n' "$$f" | sed 's#[/]#.#g; s#[.]v$$#.html#')"; \
	    "$(ALECTRYON)" --frontend coqdoc --coq-driver "$(ALECTRYON_COQ_DRIVER)" --backend webpage --rocq-arg=-exclude-dir --rocq-arg=_opam -Q . "$(PROJECT_NAMESPACE)" "$$f" -o "$(ALECTRYON_DIR)/$$out"; \
	    perl -0pi -e 's#<script src="alectryon.js"></script>#<link href="project-alectryon.css" rel="stylesheet"><script src="alectryon.js"></script><script src="project-proof-toggle.js"></script>#' "$(ALECTRYON_DIR)/$$out"; \
	    perl -pi -e 's/[ \t]+$$//' "$(ALECTRYON_DIR)/$$out"; \
	  done

alectryon-clean:
	rm -rf "$(ALECTRYON_DIR)"

site:
	$(MAKE) ALECTRYON_DIR="$(SITE_DIR)/proofs" alectryon-doc

site-clean:
	rm -rf "$(SITE_DIR)/proofs"

clean:
	-if [ -f "$(COQMAKEFILE)" ]; then $(MAKE) -C "$(PROJECT_DIR)" -f CoqMakefile clean; fi
	rm -f "$(COQMAKEFILE)" "$(PROJECT_DIR)CoqMakefile.conf" "$(PROJECT_DIR)".*.d
