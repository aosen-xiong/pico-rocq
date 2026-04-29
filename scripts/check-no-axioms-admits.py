#!/usr/bin/env python3
"""
Check for forbidden Axiom/admit usage in Coq source files.
"""

import re
import sys
import argparse
from pathlib import Path


def check_no_axioms_admits(root_dir: Path) -> bool:
    """
    Search for forbidden patterns in .v files.
    
    Returns:
        True if no violations found, False otherwise
    """
    # Pattern to match Axiom, Admitted, or admit as whole words
    pattern = re.compile(r'(^|[^A-Za-z0-9_\'])(Axiom|Admitted|admit)([^A-Za-z0-9_\']|$)')
    
    # Files to exclude
    excluded_files = {'LibTactics.v'}
    excluded_dirs = {'.git', '_build', '.dune'}
    
    violations = []
    
    for v_file in root_dir.rglob('*.v'):
        # Skip excluded files
        if v_file.name in excluded_files:
            continue
        
        # Skip files in excluded directories
        if any(part in excluded_dirs for part in v_file.parts):
            continue
        
        try:
            with open(v_file, 'r', encoding='utf-8', errors='ignore') as f:
                for line_num, line in enumerate(f, start=1):
                    if pattern.search(line):
                        violations.append(f"{v_file}:{line_num}: {line.rstrip()}")
        except OSError as e:
            print(f"Warning: Could not read {v_file}: {e}", file=sys.stderr)
    
    if violations:
        print("Found forbidden Axiom/admit usage:", file=sys.stderr)
        for violation in violations:
            print(violation, file=sys.stderr)
        return False
    
    print("No forbidden Axiom/admit usage found.")
    return True


def main():
    parser = argparse.ArgumentParser(
        description='Check Coq source files for forbidden axioms and admits'
    )
    parser.add_argument(
        'root_dir',
        nargs='?',
        default='.',
        type=Path,
        help='Root directory to search (default: current directory)'
    )
    
    args = parser.parse_args()
    
    if not check_no_axioms_admits(args.root_dir):
        sys.exit(1)


if __name__ == '__main__':
    main()
