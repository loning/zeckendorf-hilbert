#!/usr/bin/env python3
"""Extract definition and theorem statements from docs/the-matrix into prompts.txt."""
from __future__ import annotations

import re
from collections import OrderedDict
from pathlib import Path

BASE_DIR = Path('docs/the-matrix')
OUTPUT_FILE = BASE_DIR / 'prompts.txt'

START_RE = re.compile(
    r'^(?:\s*[-*+>]\s*)?(?:\s*\d+\.\s*)?(?:#{1,6}\s*)?(?:\*\*)?'  # optional markers
    r'(?:定义|定理)'
)
PROOF_RE = re.compile(r'^(?:\s*[-*+>]\s*)?(?:\s*\d+\.\s*)?(?:\*\*)?(证明|Proof)')
MATH_TEXT_RE = re.compile(r'^[A-Za-z0-9_\\^{}=+\-*/(),.:&\s]+$')


def is_math_line(stripped: str) -> bool:
    if not stripped:
        return False
    if stripped.startswith(('$$', '\\[', '\\(')):
        return True
    if stripped.startswith(('\\begin{', '\\end{')):
        return True
    if MATH_TEXT_RE.match(stripped) and '=' in stripped:
        return True
    return False


def is_statement_start(line: str) -> bool:
    stripped = line.strip()
    if not stripped:
        return False
    if '定义' not in stripped and '定理' not in stripped:
        return False
    return START_RE.match(stripped) is not None


def main() -> None:
    statements_by_file: "OrderedDict[Path, list[list[str]]]" = OrderedDict()

    for path in sorted(BASE_DIR.rglob('*.md')):
        rel_path = path.relative_to(BASE_DIR)
        with path.open('r', encoding='utf-8') as handle:
            lines = handle.readlines()

        i = 0
        collected: list[list[str]] = []
        while i < len(lines):
            line = lines[i]
            if not is_statement_start(line):
                i += 1
                continue

            buffer: list[str] = [line.rstrip()]
            i += 1
            proof_hit = False
            dollar_block = False
            env_depth = 0
            text_lines = 0

            while i < len(lines):
                current_line = lines[i]
                stripped = current_line.strip()

                if PROOF_RE.match(stripped):
                    proof_hit = True
                    break

                if is_statement_start(current_line):
                    break

                if stripped.startswith('#'):
                    hash_count = len(stripped) - len(stripped.lstrip('#'))
                    if hash_count >= 3:
                        heading_text = stripped[hash_count:].strip()
                        if heading_text:
                            if text_lines < 3:
                                buffer.append(heading_text)
                                text_lines += 1
                                i += 1
                                continue
                            break
                        i += 1
                        continue
                    break

                if stripped.startswith('**') and not (
                    stripped.startswith('**定义') or stripped.startswith('**定理')
                ):
                    break

                if not stripped:
                    if dollar_block or env_depth > 0:
                        buffer.append('')
                        i += 1
                        continue

                    if len(buffer) > 1:
                        break

                    i += 1
                    continue

                if stripped.startswith(('-', '*', '+')) and text_lines > 0:
                    break

                in_math_block = dollar_block or env_depth > 0
                is_math = is_math_line(stripped)

                if in_math_block or is_math:
                    buffer.append(current_line.rstrip())
                else:
                    if text_lines < 3:
                        buffer.append(current_line.rstrip())
                        text_lines += 1
                    else:
                        break

                i += 1

                if stripped == '$$':
                    dollar_block = not dollar_block
                else:
                    if stripped.startswith('$$') and not stripped.endswith('$$'):
                        dollar_block = True
                    if stripped.endswith('$$') and not stripped.startswith('$$'):
                        dollar_block = False

                env_depth += stripped.count('\\begin{') - stripped.count('\\end{')
                if env_depth < 0:
                    env_depth = 0

            while buffer and not buffer[-1].strip():
                buffer.pop()

            if len(buffer) > 1:
                collected.append(buffer)

            if proof_hit:
                i += 1
                continue

        if collected:
            statements_by_file[rel_path] = collected

    with OUTPUT_FILE.open('w', encoding='utf-8') as output:
        for rel_path, statements in statements_by_file.items():
            output.write(f"# {rel_path}\n")
            for statement in statements:
                for entry in statement:
                    output.write(f"{entry}\n")
                output.write("\n")


if __name__ == '__main__':
    main()
