#!/usr/bin/env python3
"""Conservative source checks. These are NOT Lean parsing or kernel checking."""
from __future__ import annotations

import json
import re
import shutil
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]


def code_only(text: str) -> str:
    """Blank nested Lean comments and double-quoted strings; preserve line numbers."""
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    while i < len(text):
        c = text[i]
        if depth:
            if text.startswith('/-', i):
                depth += 1
                out.extend('  ')
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                out.extend('  ')
                i += 2
            else:
                out.append('\n' if c == '\n' else ' ')
                i += 1
        elif in_string:
            if c == '\\' and i + 1 < len(text):
                out.extend('  ')
                i += 2
            elif c == '"':
                in_string = False
                out.append(' ')
                i += 1
            else:
                out.append('\n' if c == '\n' else ' ')
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            out.extend('  ')
            i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            if end < 0:
                end = len(text)
            out.extend(' ' * (end - i))
            i = end
        elif c == '"':
            in_string = True
            out.append(' ')
            i += 1
        else:
            out.append(c)
            i += 1
    if depth or in_string:
        raise ValueError('Unclosed block comment or string')
    return ''.join(out)


def main() -> int:
    files = sorted([ROOT / 'OR.lean', *ROOT.joinpath('OR').glob('*.lean')])
    prohibited = re.compile(
        r'\b(?:sorry|admit|sorryAx|axiom|unsafe|native_decide|implemented_by|extern)\b'
        r'|\b(?:exact|apply|aesop)\?'
    )
    errors: list[str] = []
    graph: dict[str, list[str]] = {}
    details: list[dict[str, Any]] = []
    for path in files:
        text = path.read_text(encoding='utf-8')
        try:
            code = code_only(text)
        except ValueError as exc:
            errors.append(f'{path.relative_to(ROOT)}: {exc}')
            continue
        for match in prohibited.finditer(code):
            line = code.count('\n', 0, match.start()) + 1
            errors.append(f'{path.relative_to(ROOT)}:{line}: prohibited token {match.group()}')
        openings = {'(': ')', '[': ']', '{': '}', '⟨': '⟩'}
        closing = set(openings.values())
        stack: list[tuple[str, int]] = []
        for offset, char in enumerate(code):
            if char in openings:
                stack.append((char, offset))
            elif char in closing:
                if not stack or openings[stack[-1][0]] != char:
                    line = code.count('\n', 0, offset) + 1
                    errors.append(f'{path.relative_to(ROOT)}:{line}: unmatched delimiter {char}')
                else:
                    stack.pop()
        if stack:
            errors.append(f'{path.relative_to(ROOT)}: unclosed delimiters {stack}')
        declarations = list(re.finditer(
            r'\b(?:theorem|def|abbrev|instance|structure|inductive|class)\s+', code
        ))
        for i, declaration in enumerate(declarations):
            if not declaration.group().startswith('theorem'):
                continue
            end = declarations[i + 1].start() if i + 1 < len(declarations) else len(code)
            if ':=' not in code[declaration.end():end]:
                line = code.count('\n', 0, declaration.start()) + 1
                errors.append(f'{path.relative_to(ROOT)}:{line}: no theorem body delimiter found')
        imports = re.findall(r'^import\s+([\w.]+)\s*$', code, re.MULTILINE)
        module = '.'.join(path.relative_to(ROOT).with_suffix('').parts)
        local = [name for name in imports if name == 'OR' or name.startswith('OR.')]
        graph[module] = local
        for name in imports:
            if name == 'Mathlib' or name.startswith('Mathlib.'):
                continue
            if name not in local:
                errors.append(f'{module}: unexpected external import {name}')
            elif not ROOT.joinpath(*name.split('.')).with_suffix('.lean').exists():
                errors.append(f'{module}: missing local import {name}')
        details.append({
            'file': str(path.relative_to(ROOT)),
            'lines': len(text.splitlines()),
            'theorems': len(re.findall(r'\btheorem\s+', code)),
            'definitions': len(re.findall(r'\b(?:def|abbrev)\s+', code)),
            'imports': imports,
        })
    visited: set[str] = set()
    active: set[str] = set()
    order: list[str] = []

    def visit(name: str) -> None:
        if name in active:
            errors.append(f'Import cycle at {name}')
            return
        if name in visited:
            return
        active.add(name)
        for dep in graph.get(name, []):
            visit(dep)
        active.remove(name)
        visited.add(name)
        order.append(name)

    for name in graph:
        visit(name)
    report = {
        'audit_kind': 'static source checks only',
        'lean_typechecking_performed': False,
        'lean_executable_found': shutil.which('lean') is not None,
        'status': 'PASS' if not errors else 'FAIL',
        'lean_files': len(details),
        'source_lines': sum(item['lines'] for item in details),
        'theorem_declarations': sum(item['theorems'] for item in details),
        'definition_declarations': sum(item['definitions'] for item in details),
        'dependency_order': order,
        'errors': errors,
        'files': details,
    }
    print(json.dumps(report, indent=2))
    return 1 if errors else 0


if __name__ == '__main__':
    sys.exit(main())
