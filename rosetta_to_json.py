import json
import re
import sys
from pathlib import Path


def split_statement_id(statement, line_number):
    match = re.match(r"^(\d+(?:\.\d+)*)(?:\.)?\s+(.+)$", statement, re.S)
    if match is None:
        raise ValueError(
            f"line {line_number}: statement must start with a book id, e.g. 1.1.2."
        )
    return match.group(1), match.group(2).strip()


def read_fenced_block(lines, start_index, expected_language):
    if start_index >= len(lines):
        raise ValueError(f"expected ```{expected_language}, got end of file")

    opener = lines[start_index].strip()
    expected_opener = f"```{expected_language}"
    if opener != expected_opener:
        raise ValueError(
            f"line {start_index + 1}: expected {expected_opener}, got {opener!r}"
        )

    block_lines = []
    index = start_index + 1
    while index < len(lines):
        if lines[index].strip() == "```":
            return "\n".join(block_lines).rstrip(), index + 1
        block_lines.append(lines[index].rstrip("\n"))
        index += 1

    raise ValueError(f"line {start_index + 1}: missing closing fence")


def parse_rosetta_markdown(markdown_text):
    lines = markdown_text.splitlines()
    entries = []
    index = 0

    while index < len(lines):
        while index < len(lines) and lines[index].strip() == "":
            index += 1
        if index >= len(lines):
            break

        statement_start_line = index + 1
        statement_lines = []
        while index < len(lines) and lines[index].strip() != "```litex":
            statement_lines.append(lines[index].rstrip())
            index += 1

        statement = "\n".join(statement_lines).strip()
        if not statement:
            raise ValueError(f"line {statement_start_line}: empty statement")
        statement_id, statement_body = split_statement_id(statement, statement_start_line)

        litex_code, index = read_fenced_block(lines, index, "litex")

        while index < len(lines) and lines[index].strip() == "":
            index += 1

        lean_code, index = read_fenced_block(lines, index, "lean")

        entries.append(
            {
                "id": statement_id,
                "statement": statement_body,
                "litex": litex_code,
                "lean": lean_code,
            }
        )

    return entries


def main():
    script_dir = Path(__file__).resolve().parent
    input_path = Path(sys.argv[1]) if len(sys.argv) > 1 else script_dir / "litex_lean_rosetta.md"
    output_path = Path(sys.argv[2]) if len(sys.argv) > 2 else script_dir / "litex_lean_rosetta.json"

    entries = parse_rosetta_markdown(input_path.read_text())
    output_path.write_text(json.dumps(entries, indent=2, ensure_ascii=False) + "\n")
    print(f"wrote {len(entries)} entries to {output_path}")


if __name__ == "__main__":
    main()
