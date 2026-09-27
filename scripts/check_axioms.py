#!/usr/bin/env python3
"""Validate the actual output of Lean's #print axioms commands."""
from __future__ import annotations

import re
import sys
from pathlib import Path

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
ROOT = Path(__file__).resolve().parents[1]


def main() -> int:
    if len(sys.argv) != 2:
        print('Usage: python3 scripts/check_axioms.py PATH_TO_LEAN_AUDIT_LOG', file=sys.stderr)
        return 2
    text = Path(sys.argv[1]).read_text(encoding='utf-8')
    expected = re.findall(
        r'^#print axioms (\S+)',
        (ROOT / 'OR/AxiomAudit.lean').read_text(encoding='utf-8'),
        re.MULTILINE,
    )
    found: dict[str, set[str]] = {}
    for match in re.finditer(
        r"['\"]([^'\"]+)['\"] depends on axioms:\s*\[([^\]]*)\]", text, re.DOTALL
    ):
        found[match.group(1)] = {s.strip() for s in match.group(2).split(',') if s.strip()}
    for match in re.finditer(
        r"['\"]([^'\"]+)['\"] does not depend on any axioms", text
    ):
        found[match.group(1)] = set()
    bad = False
    for name in expected:
        if name not in found:
            print(f'MISSING: no parsed Lean axiom report for {name}')
            bad = True
        elif found[name] - ALLOWED:
            print(f'UNEXPECTED AXIOMS: {name}: {sorted(found[name] - ALLOWED)}')
            bad = True
        else:
            print(f'PASS: {name}: {sorted(found[name])}')
    if re.search(r'\bsorryAx\b|\berror:', text):
        print('FAIL: the Lean output contains an error or an unfinished proof dependency')
        bad = True
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
