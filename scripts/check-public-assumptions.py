#!/usr/bin/env python3
"""Audit the explicit public-theorem manifest and its kernel assumptions."""

import re
import subprocess
import sys
from pathlib import Path


DECLARATION_RE = re.compile(
    r"^\s*(Theorem|Lemma|Corollary)\s+([A-Za-z_][A-Za-z0-9_']*)\b",
    re.MULTILINE,
)
QUALIFIED_NAME_RE = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+$"
)


def project_sources(root: Path) -> list[Path]:
    project = root / "_RocqProject"
    sources = []
    for raw_line in project.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if line.endswith(".v"):
            sources.append(root / line)
    return sources


def strip_rocq_comments(source: str) -> str:
    """Remove nested Rocq comments while retaining line boundaries."""
    result = []
    depth = 0
    index = 0
    while index < len(source):
        pair = source[index:index + 2]
        if pair == "(*":
            depth += 1
            result.extend("  ")
            index += 2
        elif pair == "*)" and depth:
            depth -= 1
            result.extend("  ")
            index += 2
        else:
            character = source[index]
            result.append(character if depth == 0 or character == "\n" else " ")
            index += 1
    return "".join(result)


def source_results(root: Path, sources: list[Path]) -> tuple[list[str], list[str]]:
    results = []
    theorems = []
    for source in sources:
        module = source.relative_to(root).with_suffix("").as_posix().replace("/", ".")
        contents = strip_rocq_comments(source.read_text(encoding="utf-8"))
        for kind, name in DECLARATION_RE.findall(contents):
            qualified_name = f"{module}.{name}"
            results.append(qualified_name)
            if kind == "Theorem":
                theorems.append(qualified_name)
    return results, theorems


def manifest_theorems(root: Path) -> tuple[list[str], list[str]]:
    manifest = root / "scripts" / "public-theorems.txt"
    failures = []
    if not manifest.is_file():
        return [], [f"missing public theorem manifest: {manifest}"]

    theorems = []
    for line_number, raw_line in enumerate(
        manifest.read_text(encoding="utf-8").splitlines(), start=1
    ):
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        if not QUALIFIED_NAME_RE.fullmatch(line):
            failures.append(
                f"invalid qualified theorem name at {manifest}:{line_number}: {line}"
            )
        theorems.append(line)

    duplicates = sorted({name for name in theorems if theorems.count(name) > 1})
    if duplicates:
        failures.append("duplicate manifest entries: " + ", ".join(duplicates))
    return theorems, failures


def main() -> int:
    root = Path(sys.argv[1] if len(sys.argv) > 1 else ".").resolve()
    sources = project_sources(root)
    modules = [source.relative_to(root).with_suffix("").as_posix().replace("/", ".")
               for source in sources]
    manifest, failures = manifest_theorems(root)
    declared_results, source_theorems = source_results(root, sources)

    manifest_set = set(manifest)
    declared_set = set(declared_results)
    theorem_set = set(source_theorems)
    unlisted = sorted(theorem_set - manifest_set)
    missing = sorted(manifest_set - declared_set)
    if unlisted:
        failures.append(
            "source Theorem declarations missing from the manifest: "
            + ", ".join(unlisted)
        )
    if missing:
        failures.append(
            "manifest entries that do not resolve to source Theorem, Lemma, or "
            "Corollary declarations: "
            + ", ".join(missing)
        )

    if failures:
        print("Public theorem manifest audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"- {failure}", file=sys.stderr)
        return 1

    commands = [f"Require Import {' '.join(modules)}."]
    commands.extend(f"Print Assumptions {theorem}." for theorem in manifest)
    commands.append("Quit.")
    result = subprocess.run(
        [
            "rocq",
            "repl",
            "-quiet",
            "-exclude-dir",
            "_opam",
            "-Q",
            str(root),
            "",
        ],
        cwd=root,
        input="\n".join(commands) + "\n",
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    output = result.stdout
    failures = []
    if result.returncode != 0:
        failures.append(f"rocq repl exited with status {result.returncode}")
    if "Error:" in output:
        failures.append("Rocq reported an error while resolving public theorems")
    if "Axioms:" in output:
        failures.append("at least one public theorem depends on a global axiom")
    closed_count = output.count("Closed under the global context")
    if closed_count != len(manifest):
        failures.append(
            f"expected {len(manifest)} closed theorems, observed {closed_count}"
        )

    if failures:
        print("Public theorem assumption audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"- {failure}", file=sys.stderr)
        print(output, file=sys.stderr)
        return 1

    print(
        f"All {len(manifest)} manifest-listed public results are "
        "closed under the global context; the manifest matches every source "
        "Theorem declaration."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
